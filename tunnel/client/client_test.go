package client

import (
	"bufio"
	"context"
	"crypto/ecdh"
	"crypto/tls"
	"crypto/x509"
	"encoding/hex"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/http/httptest"
	"sync/atomic"
	"testing"
	"time"
)

func TestHTTPSWinsWhenUDPConnectsButItsTLSStalls(t *testing.T) {
	server := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) { io.WriteString(w, `{"ok":true}`) }))
	defer server.Close()
	trust := x509.NewCertPool()
	trust.AddCert(server.Certificate())
	config := &tls.Config{RootCAs: trust, MinVersion: tls.VersionTLS12}
	local, remote := net.Pipe()
	defer remote.Close()
	primary := tlsRoute(func(context.Context, string, string) (net.Conn, error) { return local, nil }, config)
	secondary := tlsRoute((&net.Dialer{}).DialContext, config)
	started := time.Now()
	conn, https, err := raceRoute(context.Background(), primary, secondary, "tcp", server.Listener.Addr().String(), 10*time.Millisecond)
	if err != nil || !https || time.Since(started) > time.Second {
		t.Fatal("stalled TLS prevented HTTPS recovery", err)
	}
	defer conn.Close()
	if !conn.(*tls.Conn).ConnectionState().HandshakeComplete {
		t.Fatal("route selected before TLS verification")
	}
	fmt.Fprint(conn, "GET / HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n")
	response, err := http.ReadResponse(bufio.NewReader(conn), nil)
	if err != nil || response.StatusCode != http.StatusOK {
		t.Fatal("selected TLS connection is unusable", err)
	}
	response.Body.Close()
}

func TestHTTPSStartsWhileUDPIsWaiting(t *testing.T) {
	primaryStopped := make(chan struct{})
	local, remote := net.Pipe()
	defer remote.Close()
	started := time.Now()
	conn, https, err := raceRoute(context.Background(), func(ctx context.Context, _, _ string) (net.Conn, error) {
		<-ctx.Done()
		close(primaryStopped)
		return nil, ctx.Err()
	}, func(context.Context, string, string) (net.Conn, error) { return local, nil }, "tcp", "service:443", 10*time.Millisecond)
	if err != nil || !https || time.Since(started) > time.Second {
		t.Fatal("HTTPS waited for UDP", err)
	}
	conn.Close()
	select {
	case <-primaryStopped:
	case <-time.After(time.Second):
		t.Fatal("losing UDP attempt remained active")
	}
}

func TestFastUDPDoesNotOpenHTTPS(t *testing.T) {
	local, remote := net.Pipe()
	defer remote.Close()
	var backup atomic.Int32
	conn, https, err := raceRoute(context.Background(), func(context.Context, string, string) (net.Conn, error) { return local, nil }, func(context.Context, string, string) (net.Conn, error) { backup.Add(1); return nil, io.EOF }, "tcp", "service:443", time.Second)
	if err != nil || https || backup.Load() != 0 {
		t.Fatal("fast UDP changed transport")
	}
	conn.Close()
}

func TestCancelledRaceClosesLateConnection(t *testing.T) {
	ctx, cancel := context.WithCancel(context.Background())
	started, finish := make(chan struct{}), make(chan struct{})
	local, remote := net.Pipe()
	defer remote.Close()
	done := make(chan error, 1)
	go func() {
		_, _, err := raceRoute(ctx, func(context.Context, string, string) (net.Conn, error) { close(started); <-finish; return local, nil }, func(context.Context, string, string) (net.Conn, error) { return nil, io.EOF }, "tcp", "service:443", time.Second)
		done <- err
	}()
	<-started
	cancel()
	if err := <-done; err != context.Canceled {
		t.Fatal(err)
	}
	close(finish)
	remote.SetReadDeadline(time.Now().Add(time.Second))
	if _, err := remote.Read(make([]byte, 1)); err != io.EOF {
		t.Fatal("losing connection was not closed", err)
	}
}

func TestDestinationRejectionDoesNotChangeRoute(t *testing.T) {
	var backup atomic.Int32
	_, _, err := raceRoute(context.Background(), func(context.Context, string, string) (net.Conn, error) { return nil, &destinationError{503} }, func(context.Context, string, string) (net.Conn, error) { backup.Add(1); return nil, io.EOF }, "tcp", "service:443", time.Second)
	if err == nil || backup.Load() != 0 {
		t.Fatal("destination failure changed route")
	}
}

func TestReadRecoversWhenTLSStallsAfterTCPConnect(t *testing.T) {
	server := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) { io.WriteString(w, `{"ok":true}`) }))
	defer server.Close()
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	c := &Client{ctx: ctx, cancel: cancel}
	transport := server.Client().Transport.(*http.Transport).Clone()
	transport.TLSHandshakeTimeout = 20 * time.Millisecond
	local, remote := net.Pipe()
	defer remote.Close()
	transport.DialContext = func(ctx context.Context, network, address string) (net.Conn, error) {
		if !c.fallback.Load() {
			return local, nil
		}
		return (&net.Dialer{}).DialContext(ctx, network, address)
	}
	c.transport = transport
	defer transport.CloseIdleConnections()
	if _, err := c.Request("GET", server.URL, nil, nil); err != nil || !c.fallback.Load() {
		t.Fatal("TLS failure did not recover", err)
	}
}

func TestPostIsNotReplayedAfterServiceAcceptsIt(t *testing.T) {
	var accepted atomic.Int32
	server := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		accepted.Add(1)
		conn, _, _ := w.(http.Hijacker).Hijack()
		conn.Close()
	}))
	defer server.Close()
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	c := &Client{ctx: ctx, cancel: cancel, transport: server.Client().Transport.(*http.Transport)}
	if _, err := c.Request("POST", server.URL, []byte(`{"message":"once"}`), nil); err == nil {
		t.Fatal("closed response succeeded")
	}
	if accepted.Load() != 1 || c.fallback.Load() {
		t.Fatal("POST was replayed or changed route", accepted.Load())
	}
}

func TestStoppingTransportCancelsWaitingRequest(t *testing.T) {
	started := make(chan struct{})
	server := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		close(started)
		<-r.Context().Done()
	}))
	defer server.Close()
	ctx, cancel := context.WithCancel(context.Background())
	defer cancel()
	c := &Client{ctx: ctx, cancel: cancel, transport: server.Client().Transport.(*http.Transport)}
	done := make(chan error, 1)
	go func() { _, err := c.Request("GET", server.URL, nil, nil); done <- err }()
	select {
	case <-started:
	case <-time.After(2 * time.Second):
		t.Fatal("request did not reach the service")
	}
	c.cancel()
	select {
	case err := <-done:
		if err == nil {
			t.Fatal("cancelled request succeeded")
		}
	case <-time.After(time.Second):
		t.Fatal("request remained active after the transport stopped")
	}
}

func TestKeysMatchWireGuardX25519(t *testing.T) {
	pair, e := Keypair()
	if e != nil {
		t.Fatal(e)
	}
	raw, _ := hex.DecodeString(pair["private_key"])
	key, e := ecdh.X25519().NewPrivateKey(raw)
	if e != nil || hex.EncodeToString(key.PublicKey().Bytes()) != pair["public_key"] {
		t.Fatal("keypair mismatch")
	}
}
func TestRejectConfigurationInjection(t *testing.T) {
	for _, p := range []map[string]string{{"private_key": "value"}, {"h1": "123\nprivate_key=abcd"}, {"s4": "1\r\n"}} {
		if _, e := Parameters(p); e == nil {
			t.Fatal("invalid parameters accepted")
		}
	}
}
func TestRejectInvalidClientBeforeOpeningNetwork(t *testing.T) {
	if _, e := Start(Config{PrivateKey: "bad"}); e == nil {
		t.Fatal("invalid key accepted")
	}
}
