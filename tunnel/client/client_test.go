package client

import (
	"context"
	"crypto/ecdh"
	"encoding/hex"
	"net/http"
	"net/http/httptest"
	"testing"
	"time"
)

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
