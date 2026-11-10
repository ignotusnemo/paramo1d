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
	mu     sync.Mutex
	dev    *device.Device
	config Config
	public string
	peers  map[string]Peer
	state  string
	slots  chan struct{}
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
		ID        string `json:"id"`
		Key       string `json:"public_key"`
		Time      int64  `json:"time_ms"`
		Signature string `json:"signature"`
	}
	decoder := json.NewDecoder(http.MaxBytesReader(w, q.Body, 8192))
	decoder.DisallowUnknownFields()
	if e := decoder.Decode(&request); e != nil {
		http.Error(w, "Invalid enrollment", 400)
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
		if len(r.peers) >= 240 {
			http.Error(w, "Enrollment capacity reached", 503)
			return
		}
		used := map[string]bool{}
		for _, p := range r.peers {
			used[p.Address] = true
		}
		for i := 2; i < 250; i++ {
			a := fmt.Sprintf("10.80.0.%d", i)
			if !used[a] {
				peer.Address = a
				break
			}
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
	select {
	case r.slots <- struct{}{}:
		defer func() { <-r.slots }()
	default:
		http.Error(w, "Connection limit", 503)
		return
	}
	remote, e := net.DialTimeout("tcp", destination, 10*time.Second)
	if e != nil {
		http.Error(w, "Destination unavailable", 502)
		return
	}
	defer remote.Close()
	upgrade := websocket.Upgrader{ReadBufferSize: 32768, WriteBufferSize: 32768, CheckOrigin: func(q *http.Request) bool { return q.Header.Get("Origin") == "" }}
	socket, e := upgrade.Upgrade(w, q, nil)
	if e != nil {
		return
	}
	local := wsstream.New(socket)
	defer local.Close()
	local.SetDeadline(time.Now().Add(8 * time.Minute))
	remote.SetDeadline(time.Now().Add(8 * time.Minute))
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
	select {
	case r.slots <- struct{}{}:
		defer func() { <-r.slots }()
	default:
		http.Error(w, "Connection limit", 503)
		return
	}
	remote, e := net.DialTimeout("tcp", destination, 10*time.Second)
	if e != nil {
		http.Error(w, "Destination unavailable", 502)
		return
	}
	defer remote.Close()
	local, buffer, e := w.(http.Hijacker).Hijack()
	if e != nil {
		return
	}
	defer local.Close()
	local.SetDeadline(time.Now().Add(8 * time.Minute))
	remote.SetDeadline(time.Now().Add(8 * time.Minute))
	fmt.Fprint(buffer, "HTTP/1.1 200 Connection Established\r\n\r\n")
	buffer.Flush()
	done := make(chan struct{})
	go func() { io.Copy(remote, buffer); remote.Close(); close(done) }()
	io.Copy(local, remote)
	local.Close()
	<-done
}
func main() {
	state := flag.String("state", "/var/lib/paramo1d-tunnel", "Private state directory")
	endpoint := flag.String("endpoint", "159.198.45.62:443", "Public UDP endpoint")
	flag.Parse()
	if e := os.MkdirAll(*state, 0700); e != nil {
		panic("Cannot open tunnel state")
	}
	path := filepath.Join(*state, "server.json")
	var config Config
	b, e := os.ReadFile(path)
	if os.IsNotExist(e) {
		pair, e := client.Keypair()
		if e != nil {
			panic("Key generation failed")
		}
		config = Config{pair["private_key"], *endpoint, map[string]string{"jc": "4", "jmin": "40", "jmax": "120", "s1": "37", "s2": "53", "s3": "11", "s4": "17", "h1": "173451001", "h2": "283451002", "h3": "393451003", "h4": "493451004"}}
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
	}
	for _, peer := range peers {
		if e = dev.IpcSet("public_key=" + peer.Key + "\nallowed_ip=" + peer.Address + "/32\n"); e != nil {
			panic("Peer configuration rejected")
		}
	}
	if e = dev.Up(); e != nil {
		panic("Cannot start tunnel")
	}
	for _, args := range [][]string{{"address", "replace", "10.80.0.1/24", "dev", "pmrelay0"}, {"link", "set", "dev", "pmrelay0", "up"}} {
		if e = exec.Command("ip", args...).Run(); e != nil {
			panic("Cannot configure tunnel interface")
		}
	}
	relay := &Relay{dev: dev, config: config, public: hex.EncodeToString(key.PublicKey().Bytes()), peers: peers, state: *state, slots: make(chan struct{}, 96)}
	api := http.NewServeMux()
	api.HandleFunc("/v1/tunnel/enroll", relay.enroll)
	api.HandleFunc("/v1/tunnel/connect", relay.websocket)
	api.HandleFunc("/healthz", func(w http.ResponseWriter, q *http.Request) { fmt.Fprint(w, "{\"ok\":true}") })
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
