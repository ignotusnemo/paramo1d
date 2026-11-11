// Package client provides an application-owned AmneziaWG network stack.
package client

import (
	"bufio"
	"bytes"
	"context"
	"crypto/ecdh"
	"crypto/rand"
	"crypto/subtle"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/netip"
	"net/url"
	"os"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/amnezia-vpn/amneziawg-go/v3/conn"
	"github.com/amnezia-vpn/amneziawg-go/v3/device"
	"github.com/amnezia-vpn/amneziawg-go/v3/tun/netstack"
	"github.com/gorilla/websocket"
	"github.com/ignotusnemo/paramo1d/tunnel/internal/idleconn"
	"github.com/ignotusnemo/paramo1d/tunnel/internal/wsstream"
)

type Config struct {
	Network     uint64            `json:"network_handle"`
	Roots       []string          `json:"root_certificates"`
	PreferHTTPS bool              `json:"prefer_https"`
	RelayID     string            `json:"relay_id"`
	RelayToken  string            `json:"relay_token"`
	PrivateKey  string            `json:"private_key"`
	PublicKey   string            `json:"server_public_key"`
	Address     string            `json:"address"`
	Endpoint    string            `json:"endpoint"`
	Parameters  map[string]string `json:"parameters"`
	Token       string            `json:"token"`
}
type Client struct {
	ctx         context.Context
	cancel      context.CancelFunc
	dev         *device.Device
	listener    net.Listener
	server      *http.Server
	transport   *http.Transport
	port        int
	token       string
	slots       chan struct{}
	mu          sync.Mutex
	connections map[net.Conn]bool
	fallback    atomic.Bool
}

var parameterNames = map[string]bool{"jc": true, "jmin": true, "jmax": true, "s1": true, "s2": true, "s3": true, "s4": true, "h1": true, "h2": true, "h3": true, "h4": true}

func Parameters(values map[string]string) (string, error) {
	var text strings.Builder
	if len(values) > len(parameterNames) {
		return "", errors.New("unsupported tunnel parameters")
	}
	for k, v := range values {
		if !parameterNames[k] || len(v) > 32 || strings.ContainsAny(v, "\r\n=") {
			return "", errors.New("invalid tunnel parameters")
		}
		text.WriteString(k + "=" + v + "\n")
	}
	return text.String(), nil
}
func Keypair() (map[string]string, error) {
	k, e := ecdh.X25519().GenerateKey(rand.Reader)
	if e != nil {
		return nil, e
	}
	return map[string]string{"private_key": hex.EncodeToString(k.Bytes()), "public_key": hex.EncodeToString(k.PublicKey().Bytes())}, nil
}
func Start(config Config) (*Client, error) {
	for _, key := range []string{config.PrivateKey, config.PublicKey, config.Token} {
		b, e := hex.DecodeString(key)
		if e != nil || len(b) != 32 {
			return nil, errors.New("invalid tunnel key or token")
		}
	}
	address, e := netip.ParseAddr(config.Address)
	if e != nil || !netip.MustParsePrefix("10.80.0.0/24").Contains(address) || address == netip.MustParseAddr("10.80.0.1") {
		return nil, errors.New("invalid tunnel address")
	}
	endpoint, e := netip.ParseAddrPort(config.Endpoint)
	if e != nil || endpoint.Addr().IsPrivate() || !endpoint.Addr().IsGlobalUnicast() {
		return nil, errors.New("invalid tunnel endpoint")
	}
	roots, e := x509.SystemCertPool()
	if e != nil || roots == nil {
		roots = x509.NewCertPool()
	}
	if len(config.Roots) > 2000 {
		return nil, errors.New("too many trust anchors")
	}
	for _, encoded := range config.Roots {
		der, e := base64.StdEncoding.DecodeString(encoded)
		if e != nil || len(der) > 32768 {
			return nil, errors.New("invalid trust anchor")
		}
		certificate, e := x509.ParseCertificate(der)
		if e != nil {
			return nil, errors.New("invalid trust anchor")
		}
		roots.AddCert(certificate)
	}
	parameters, e := Parameters(config.Parameters)
	if e != nil {
		return nil, e
	}
	tun, network, e := netstack.CreateNetTUN([]netip.Addr{address}, nil, 1280)
	if e != nil {
		return nil, errors.New("could not create application tunnel")
	}
	level := device.LogLevelSilent
	if os.Getenv("PARAMO1D_TUNNEL_DIAGNOSTICS") == "1" {
		level = device.LogLevelVerbose
	}
	dev := device.NewDevice(tun, &networkBind{Bind: conn.NewDefaultBind(), network: config.Network}, device.NewLogger(level, "app tunnel: "))
	settings := "private_key=" + config.PrivateKey + "\n" + parameters + "public_key=" + config.PublicKey + "\nendpoint=" + config.Endpoint + "\nallowed_ip=10.80.0.1/32\npersistent_keepalive_interval=25\n"
	if e = dev.IpcSet(settings); e != nil {
		dev.Close()
		return nil, errors.New("tunnel configuration rejected")
	}
	if !config.PreferHTTPS {
		if e = dev.Up(); e != nil {
			dev.Close()
			return nil, errors.New("could not start tunnel")
		}
	}
	listener, e := net.Listen("tcp4", "127.0.0.1:0")
	if e != nil {
		dev.Close()
		return nil, e
	}
	ctx, cancel := context.WithCancel(context.Background())
	c := &Client{ctx: ctx, cancel: cancel, dev: dev, listener: listener, port: listener.Addr().(*net.TCPAddr).Port, token: config.Token, slots: make(chan struct{}, 12), connections: map[net.Conn]bool{}}
	wgDial := func(ctx context.Context, _, target string) (net.Conn, error) {
		if _, _, e := net.SplitHostPort(target); e != nil {
			return nil, errors.New("invalid tunnel target")
		}
		ctx, cancel := context.WithTimeout(ctx, 4*time.Second)
		defer cancel()
		stream, e := network.DialContext(ctx, "tcp", "10.80.0.1:1081")
		if e != nil {
			return nil, errors.New("protected connection is unavailable")
		}
		stream.SetDeadline(time.Now().Add(15 * time.Second))
		request := &http.Request{Method: http.MethodConnect, URL: &url.URL{Opaque: target}, Host: target, Header: make(http.Header)}
		if e = request.Write(stream); e != nil {
			stream.Close()
			return nil, e
		}
		reader := bufio.NewReader(stream)
		response, e := http.ReadResponse(reader, request)
		if e != nil || response.StatusCode != 200 {
			stream.Close()
			return nil, errors.New("protected connection could not reach this service")
		}
		stream.SetDeadline(time.Time{})
		return &bufferedConn{Conn: stream, reader: reader}, nil
	}

	dial := func(ctx context.Context, networkName, target string) (net.Conn, error) {
		if !c.fallback.Load() {
			if stream, e := wgDial(ctx, networkName, target); e == nil {
				return stream, nil
			}
		}
		if len(config.RelayID) != 64 || len(config.RelayToken) != 64 {
			return nil, errors.New("protected connection is unavailable")
		}
		dialer := websocket.Dialer{HandshakeTimeout: 12 * time.Second, ReadBufferSize: 32768, WriteBufferSize: 32768, TLSClientConfig: &tls.Config{RootCAs: roots, MinVersion: tls.VersionTLS12, ServerName: "chat.parano1d.org"}, NetDialContext: func(ctx context.Context, network, address string) (net.Conn, error) {
			return (&net.Dialer{Timeout: 10 * time.Second, Control: func(_, _ string, raw syscall.RawConn) error {
				var bound error
				e := raw.Control(func(fd uintptr) { bound = bindNetwork(config.Network, int(fd)) })
				if e != nil {
					return e
				}
				return bound
			}}).DialContext(ctx, "tcp", net.JoinHostPort(endpoint.Addr().String(), "443"))
		}}
		headers := http.Header{}
		headers.Set("Authorization", "Bearer "+config.RelayID+":"+config.RelayToken)
		socket, response, e := dialer.DialContext(ctx, "wss://chat.parano1d.org/v1/tunnel/connect?target="+url.QueryEscape(target), headers)
		if e != nil {
			if response != nil && response.Body != nil {
				response.Body.Close()
			}
			return nil, fmt.Errorf("protected HTTPS connection is unavailable: %w", e)
		}
		c.fallback.Store(true)
		c.dev.Down()
		return wsstream.New(socket), nil
	}
	if config.PreferHTTPS {
		c.fallback.Store(true)
		c.dev.Down()
	}
	c.transport = &http.Transport{DialContext: dial, ForceAttemptHTTP2: true, MaxIdleConns: 6, MaxIdleConnsPerHost: 2, IdleConnTimeout: 45 * time.Second, TLSClientConfig: &tls.Config{RootCAs: roots, MinVersion: tls.VersionTLS12}, TLSHandshakeTimeout: 15 * time.Second, ResponseHeaderTimeout: 20 * time.Second}
	c.server = &http.Server{Handler: http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		expected := "Basic " + base64.StdEncoding.EncodeToString([]byte("paramo1d:"+c.token))
		if subtle.ConstantTimeCompare([]byte(r.Header.Get("Proxy-Authorization")), []byte(expected)) != 1 {
			http.Error(w, "Authentication required", 407)
			return
		}
		if r.Method != http.MethodConnect {
			http.Error(w, "CONNECT required", 405)
			return
		}
		select {
		case c.slots <- struct{}{}:
			defer func() { <-c.slots }()
		default:
			http.Error(w, "Connection limit", 503)
			return
		}
		remote, e := dial(r.Context(), "tcp", r.Host)
		if e != nil {
			http.Error(w, "Protected connection unavailable", 502)
			return
		}
		remote = idleconn.New(remote, 8*time.Minute)
		defer remote.Close()
		local, buffer, e := w.(http.Hijacker).Hijack()
		if e != nil {
			return
		}
		defer local.Close()
		c.mu.Lock()
		c.connections[local] = true
		c.mu.Unlock()
		defer func() { c.mu.Lock(); delete(c.connections, local); c.mu.Unlock() }()
		fmt.Fprint(buffer, "HTTP/1.1 200 Connection Established\r\n\r\n")
		buffer.Flush()
		done := make(chan struct{})
		go func() { io.Copy(remote, buffer); remote.Close(); close(done) }()
		io.Copy(local, remote)
		local.Close()
		<-done
	}), ReadHeaderTimeout: 8 * time.Second, IdleTimeout: 20 * time.Second, MaxHeaderBytes: 8192}
	go c.server.Serve(listener)
	return c, nil
}

type bufferedConn struct {
	net.Conn
	reader *bufio.Reader
}

func (c *bufferedConn) Read(b []byte) (int, error) { return c.reader.Read(b) }
func (c *Client) Port() int                        { return c.port }
func (c *Client) Close() {
	c.cancel()
	c.server.Close()
	c.transport.CloseIdleConnections()
	c.dev.Close()
	c.mu.Lock()
	defer c.mu.Unlock()
	for conn := range c.connections {
		conn.Close()
	}
}
func (c *Client) Request(method, target string, body []byte, headers map[string]string) (json.RawMessage, error) {
	u, e := url.Parse(target)
	if e != nil || u.Scheme != "https" || u.User != nil || u.Hostname() == "" || u.Fragment != "" {
		return nil, errors.New("protected requests require HTTPS")
	}
	if method != "GET" && method != "POST" {
		return nil, errors.New("unsupported request method")
	}
	if len(body) > 1024*1024 {
		return nil, errors.New("request exceeds limit")
	}
	request, e := http.NewRequestWithContext(c.ctx, method, target, bytes.NewReader(body))
	if e != nil {
		return nil, e
	}
	for k, v := range headers {
		switch strings.ToLower(k) {
		case "accept", "content-type", "x-paramo1d-time", "x-paramo1d-signature":
			request.Header.Set(k, v)
		default:
			return nil, errors.New("unsupported request header")
		}
	}
	client := &http.Client{Transport: c.transport, Timeout: 40 * time.Second, CheckRedirect: func(*http.Request, []*http.Request) error { return http.ErrUseLastResponse }}
	response, e := client.Do(request)
	if e != nil {
		return nil, errors.New("protected connection is unavailable")
	}
	defer response.Body.Close()
	if response.StatusCode < 200 || response.StatusCode >= 300 {
		return nil, fmt.Errorf("Service returned %d", response.StatusCode)
	}
	payload, e := io.ReadAll(io.LimitReader(response.Body, 4*1024*1024+1))
	if e != nil || len(payload) > 4*1024*1024 {
		return nil, errors.New("response exceeds limit")
	}
	if !json.Valid(payload) {
		return nil, errors.New("invalid service response")
	}
	return payload, nil
}
func (c *Client) Status() map[string]any {
	handshakes := 0
	if value, e := c.dev.IpcGet(); e == nil {
		for _, line := range strings.Split(value, "\n") {
			if strings.HasPrefix(line, "last_handshake_time_sec=") {
				n, _ := strconv.ParseInt(strings.TrimPrefix(line, "last_handshake_time_sec="), 10, 64)
				if n > 0 {
					handshakes++
				}
			}
		}
	}
	return map[string]any{"enabled": true, "handshake": handshakes > 0, "transport": func() string {
		if c.fallback.Load() {
			return "https"
		}
		return "amneziawg"
	}(), "proxy_port": c.port}
}

// Bind only the tunnel's own sockets to the chosen Android network.
type networkBind struct {
	conn.Bind
	network uint64
}

func (b *networkBind) Open(port uint16) ([]conn.ReceiveFunc, uint16, error) {
	functions, actual, e := b.Bind.Open(port)
	if e != nil || b.network == 0 {
		return functions, actual, e
	}
	peek, ok := b.Bind.(conn.PeekLookAtSocketFd)
	if !ok {
		b.Close()
		return nil, 0, errors.New("tunnel socket binding unavailable")
	}
	for _, get := range []func() (int, error){peek.PeekLookAtSocketFd4, peek.PeekLookAtSocketFd6} {
		fd, e := get()
		if e != nil {
			continue
		}
		if e = bindNetwork(b.network, fd); e != nil {
			b.Close()
			return nil, 0, e
		}
	}
	return functions, actual, nil
}
