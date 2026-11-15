// Paramo1d's application tunnel forwards only explicitly selected services.
package main

import (
	"crypto/ecdh"
	"crypto/ed25519"
	"crypto/hmac"
	"crypto/sha256"
	"crypto/subtle"
	"encoding/hex"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"github.com/amnezia-vpn/amneziawg-go/v3/conn"
	"github.com/amnezia-vpn/amneziawg-go/v3/device"
	"github.com/amnezia-vpn/amneziawg-go/v3/tun"
	"github.com/gorilla/websocket"
	"github.com/ignotusnemo/paramo1d/tunnel/client"
	"github.com/ignotusnemo/paramo1d/tunnel/internal/idleconn"
	"github.com/ignotusnemo/paramo1d/tunnel/internal/wsstream"
	"io"
	"net"
	"net/http"
	"os"
	"os/exec"
	"os/signal"
	"path/filepath"
	"strings"
	"sync"
	"syscall"
	"time"
)

type Peer struct {
	Key     string `json:"public_key"`
	Address string `json:"address"`
}
type Config struct {
	PrivateKey string            `json:"private_key"`
	Endpoint   string            `json:"endpoint"`
	Parameters map[string]string `json:"parameters"`
}
type Relay struct {
	mu       sync.Mutex
	dev      *device.Device
	config   Config
	public   string
	peers    map[string]Peer
	state    string
	slots    chan struct{}
	active   map[string]int
	maxPeers int
	perPeer  int
}

func nextAddress(peers map[string]Peer, wide bool) (string, error) {
	used := make(map[string]bool, len(peers))
	for _, peer := range peers {
		used[peer.Address] = true
	}
	first, last := 2, 250
	if wide {
		first, last = 257, 65535
	}
	for i := first; i < last; i++ {
		address := fmt.Sprintf("10.80.%d.%d", i/256, i%256)
		if !used[address] {
			return address, nil
		}
	}
	return "", errors.New("address capacity reached")
}

func (r *Relay) acquire(address string) (func(), bool) {
	r.mu.Lock()
	defer r.mu.Unlock()
	if r.active[address] >= r.perPeer {
		return nil, false
	}
	select {
	case r.slots <- struct{}{}:
		if r.active == nil {
			r.active = make(map[string]int)
		}
		r.active[address]++
		return func() {
			r.mu.Lock()
			r.active[address]--
			if r.active[address] == 0 {
				delete(r.active, address)
			}
			<-r.slots
			r.mu.Unlock()
		}, true
	default:
		return nil, false
	}
}

func writeJSON(path string, v any) error {
	b, e := json.MarshalIndent(v, "", "  ")
	if e != nil {
		return e
	}
	f, e := os.OpenFile(path+".pending", os.O_CREATE|os.O_TRUNC|os.O_WRONLY, 0600)
	if e != nil {
		return e
	}
	if _, e = f.Write(b); e != nil {
		f.Close()
		return e
	}
	e = f.Sync()
	f.Close()
	if e != nil {
		return e
	}
	return os.Rename(path+".pending", path)
}
func (r *Relay) enroll(w http.ResponseWriter, q *http.Request) {
	if q.Method != "POST" {
		http.Error(w, "POST required", 405)
		return
	}
	var request struct {
		ID          string `json:"id"`
		Key         string `json:"public_key"`
		Time        int64  `json:"time_ms"`
		Signature   string `json:"signature"`
		AddressBits int    `json:"address_bits,omitempty"`
	}
	decoder := json.NewDecoder(http.MaxBytesReader(w, q.Body, 8192))
	decoder.DisallowUnknownFields()
	if e := decoder.Decode(&request); e != nil {
		http.Error(w, "Invalid enrollment", 400)
		return
	}
	if request.AddressBits != 0 && request.AddressBits != 24 && request.AddressBits != 16 {
		http.Error(w, "Unsupported address range", 400)
		return
	}
	id, e := hex.DecodeString(request.ID)
	if e != nil || len(id) != 32 {
		http.Error(w, "Invalid identity", 400)
		return
	}
	key, e := hex.DecodeString(request.Key)
	if e != nil || len(key) != 32 || request.Key == strings.Repeat("0", 64) {
		http.Error(w, "Invalid key", 400)
		return
	}
	sig, e := hex.DecodeString(request.Signature)
	delta := time.Now().UnixMilli() - request.Time
	if e != nil || delta > 300000 || delta < -300000 || !ed25519.Verify(id, []byte(fmt.Sprintf("Paramo1d/Courier/inbox/1\x00/v1/tunnel/%s\x00%d", request.Key, request.Time)), sig) {
		http.Error(w, "Authentication required", 401)
		return
	}
	r.mu.Lock()
	defer r.mu.Unlock()
	peer, exists := r.peers[request.ID]
	if !exists {
		if len(r.peers) >= r.maxPeers {
			http.Error(w, "Enrollment capacity reached", 503)
			return
		}
		peer.Address, e = nextAddress(r.peers, request.AddressBits == 16)
		if e != nil {
			http.Error(w, "Enrollment capacity reached", 503)
			return
		}
	}
	if peer.Key != request.Key {
		if peer.Key != "" {
			if e = r.dev.IpcSet("public_key=" + peer.Key + "\nremove=true\n"); e != nil {
				http.Error(w, "Tunnel busy", 503)
				return
			}
		}
		if e = r.dev.IpcSet("public_key=" + request.Key + "\nreplace_allowed_ips=true\nallowed_ip=" + peer.Address + "/32\n"); e != nil {
			http.Error(w, "Tunnel busy", 503)
			return
		}
		prior := peer
		peer.Key = request.Key
		r.peers[request.ID] = peer
		if e = writeJSON(filepath.Join(r.state, "peers.json"), r.peers); e != nil {
			delete(r.peers, request.ID)
			r.dev.IpcSet("public_key=" + request.Key + "\nremove=true\n")
			if exists {
				r.peers[request.ID] = prior
				r.dev.IpcSet("public_key=" + prior.Key + "\nallowed_ip=" + prior.Address + "/32\n")
			}
			http.Error(w, "Storage unavailable", 503)
			return
		}
	}
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]any{"relay_id": request.ID, "relay_token": r.token(request.ID, peer.Key), "server_public_key": r.public, "endpoint": r.config.Endpoint, "address": peer.Address, "parameters": r.config.Parameters})
}
func (r *Relay) token(id, key string) string {
	secret, _ := hex.DecodeString(r.config.PrivateKey)
	mac := hmac.New(sha256.New, secret)
	mac.Write([]byte("Paramo1d/relay/1/" + id + "/" + key))
	return hex.EncodeToString(mac.Sum(nil))
}
func (r *Relay) websocket(w http.ResponseWriter, q *http.Request) {
	credentials := strings.Split(strings.TrimPrefix(q.Header.Get("Authorization"), "Bearer "), ":")
	if len(credentials) != 2 || len(credentials[0]) != 64 || len(credentials[1]) != 64 {
		http.Error(w, "Authentication required", 401)
		return
	}
	r.mu.Lock()
	peer, exists := r.peers[credentials[0]]
	r.mu.Unlock()
	if !exists || subtle.ConstantTimeCompare([]byte(r.token(credentials[0], peer.Key)), []byte(credentials[1])) != 1 {
		http.Error(w, "Authentication required", 401)
		return
	}
	destination, e := target(q.URL.Query().Get("target"))
	if e != nil {
		http.Error(w, "Service unavailable on application route", 403)
		return
	}
	release, admitted := r.acquire(peer.Address)
	if !admitted {
		http.Error(w, "Connection limit", 503)
		return
	}
	defer release()
	remote, e := net.DialTimeout("tcp", destination, 10*time.Second)
	if e != nil {
		http.Error(w, "Destination unavailable", 502)
		return
	}
	remote = idleconn.New(remote, 8*time.Minute)
	defer remote.Close()
	upgrade := websocket.Upgrader{ReadBufferSize: 32768, WriteBufferSize: 32768, CheckOrigin: func(q *http.Request) bool { return q.Header.Get("Origin") == "" }}
	socket, e := upgrade.Upgrade(w, q, nil)
	if e != nil {
		return
	}
	local := wsstream.New(socket)
	defer local.Close()
	done := make(chan struct{})
	go func() { io.Copy(remote, local); remote.Close(); close(done) }()
	io.Copy(local, remote)
	local.Close()
	<-done
}
func target(value string) (string, error) {
	host, port, e := net.SplitHostPort(value)
	if e != nil {
		return "", errors.New("invalid target")
	}
	host = strings.ToLower(host)
	if host == "chat.parano1d.org" && port == "443" {
		return "127.0.0.1:443", nil
	}
	if port != "9600" || (host != "mseed1.parano1d.org" && host != "mseed2.parano1d.org" && host != "mseed3.parano1d.org" && host != "mseed4.parano1d.org") {
		return "", errors.New("service is outside the application route")
	}
	ips, e := net.LookupIP(host)
	if e != nil {
		return "", errors.New("peer discovery unavailable")
	}
	for _, ip := range ips {
		if ip.To4() != nil && ip.IsGlobalUnicast() && !ip.IsPrivate() && !ip.IsLoopback() {
			return net.JoinHostPort(ip.String(), port), nil
		}
	}
	return "", errors.New("peer discovery unavailable")
}
func (r *Relay) proxy(w http.ResponseWriter, q *http.Request) {
	if q.Method != "CONNECT" {
		http.Error(w, "CONNECT required", 405)
		return
	}
	destination, e := target(q.Host)
	if e != nil {
		http.Error(w, "Service unavailable on application route", 403)
		return
	}
	address, _, e := net.SplitHostPort(q.RemoteAddr)
	if e != nil {
		http.Error(w, "Invalid peer address", 400)
		return
	}
	release, admitted := r.acquire(address)
	if !admitted {
		http.Error(w, "Connection limit", 503)
		return
	}
	defer release()
	remote, e := net.DialTimeout("tcp", destination, 10*time.Second)
	if e != nil {
		http.Error(w, "Destination unavailable", 502)
		return
	}
	remote = idleconn.New(remote, 8*time.Minute)
	defer remote.Close()
	local, buffer, e := w.(http.Hijacker).Hijack()
	if e != nil {
		return
	}
	defer local.Close()
	fmt.Fprint(buffer, "HTTP/1.1 200 Connection Established\r\n\r\n")
	buffer.Flush()
	done := make(chan struct{})
	go func() { io.Copy(remote, buffer); remote.Close(); close(done) }()
	io.Copy(local, remote)
	local.Close()
	<-done
}
func publicEndpoint(value string) (string, error) {
	address, err := net.ResolveUDPAddr("udp4", value)
	if err != nil || address.Port <= 0 || !address.IP.IsGlobalUnicast() || address.IP.IsPrivate() {
		return "", errors.New("invalid public UDP endpoint")
	}
	return address.String(), nil
}

func main() {
	state := flag.String("state", "/var/lib/paramo1d-tunnel", "Private state directory")
	endpoint := flag.String("endpoint", "chat.parano1d.org:443", "Public UDP endpoint")
	maxPeers := flag.Int("max-peers", 4096, "Maximum registered devices")
	maxStreams := flag.Int("max-streams", 4096, "Maximum concurrent transport streams")
	perPeer := flag.Int("streams-per-peer", 16, "Concurrent transport streams per device")
	flag.Parse()
	if *maxPeers < 1 || *maxPeers > 65278 || *maxStreams < 1 || *maxStreams > 16384 || *perPeer < 1 || *perPeer > *maxStreams {
		panic("Invalid tunnel capacity")
	}
	if e := os.MkdirAll(*state, 0700); e != nil {
		panic("Cannot open tunnel state")
	}
	path := filepath.Join(*state, "server.json")
	var config Config
	b, e := os.ReadFile(path)
	if os.IsNotExist(e) {
		resolved, err := publicEndpoint(*endpoint)
		if err != nil {
			panic("Cannot resolve public UDP endpoint")
		}
		pair, e := client.Keypair()
		if e != nil {
			panic("Key generation failed")
		}
		config = Config{pair["private_key"], resolved, map[string]string{"jc": "4", "jmin": "40", "jmax": "120", "s1": "37", "s2": "53", "s3": "11", "s4": "17", "h1": "173451001", "h2": "283451002", "h3": "393451003", "h4": "493451004"}}
		if e = writeJSON(path, config); e != nil {
			panic("Cannot save tunnel configuration")
		}
	} else if e != nil || json.Unmarshal(b, &config) != nil {
		panic("Cannot load tunnel configuration")
	}
	raw, e := hex.DecodeString(config.PrivateKey)
	if e != nil {
		panic("Invalid tunnel key")
	}
	key, e := ecdh.X25519().NewPrivateKey(raw)
	if e != nil {
		panic("Invalid tunnel key")
	}
	parameters, e := client.Parameters(config.Parameters)
	if e != nil {
		panic("Invalid tunnel parameters")
	}
	devtun, e := tun.CreateTUN("pmrelay0", 1280)
	if e != nil {
		panic("Cannot create tunnel device")
	}
	dev := device.NewDevice(devtun, conn.NewDefaultBind(), device.NewLogger(device.LogLevelSilent, ""))
	defer dev.Close()
	if e = dev.IpcSet("private_key=" + config.PrivateKey + "\nlisten_port=443\n" + parameters); e != nil {
		panic("Tunnel configuration rejected")
	}
	peers := map[string]Peer{}
	if b, e = os.ReadFile(filepath.Join(*state, "peers.json")); e == nil {
		if json.Unmarshal(b, &peers) != nil {
			panic("Invalid peer state")
		}
	} else if !os.IsNotExist(e) {
		panic("Cannot read peer state")
	}
	for _, peer := range peers {
		if e = dev.IpcSet("public_key=" + peer.Key + "\nallowed_ip=" + peer.Address + "/32\n"); e != nil {
			panic("Peer configuration rejected")
		}
	}
	if e = dev.Up(); e != nil {
		panic("Cannot start tunnel")
	}
	for _, args := range [][]string{{"address", "replace", "10.80.0.1/16", "dev", "pmrelay0"}, {"link", "set", "dev", "pmrelay0", "up"}} {
		if e = exec.Command("ip", args...).Run(); e != nil {
			panic("Cannot configure tunnel interface")
		}
	}
	relay := &Relay{dev: dev, config: config, public: hex.EncodeToString(key.PublicKey().Bytes()), peers: peers, state: *state, slots: make(chan struct{}, *maxStreams), maxPeers: *maxPeers, perPeer: *perPeer, active: make(map[string]int)}
	api := http.NewServeMux()
	api.HandleFunc("/v1/tunnel/enroll", relay.enroll)
	api.HandleFunc("/v1/tunnel/connect", relay.websocket)
	api.HandleFunc("/healthz", func(w http.ResponseWriter, q *http.Request) {
		relay.mu.Lock()
		defer relay.mu.Unlock()
		w.Header().Set("Content-Type", "application/json")
		json.NewEncoder(w).Encode(map[string]any{"ok": true, "registered_devices": len(relay.peers), "active_streams": len(relay.slots), "stream_limit": cap(relay.slots), "device_limit": relay.maxPeers, "streams_per_device": relay.perPeer})
	})
	control := &http.Server{Addr: "127.0.0.1:9713", Handler: api, ReadHeaderTimeout: 8 * time.Second, MaxHeaderBytes: 8192}
	proxy := &http.Server{Addr: "10.80.0.1:1081", Handler: http.HandlerFunc(relay.proxy), ReadHeaderTimeout: 8 * time.Second, MaxHeaderBytes: 8192}
	go func() {
		if e := control.ListenAndServe(); e != http.ErrServerClosed {
			os.Exit(1)
		}
	}()
	go func() {
		if e := proxy.ListenAndServe(); e != http.ErrServerClosed {
			os.Exit(1)
		}
	}()
	fmt.Println("Application tunnel ready")
	signals := make(chan os.Signal, 1)
	signal.Notify(signals, syscall.SIGINT, syscall.SIGTERM)
	<-signals
	control.Close()
	proxy.Close()
}
