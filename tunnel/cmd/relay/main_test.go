package main

import (
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
)

func TestExpandedAddressesPreserveLegacyPool(t *testing.T) {
	peers := map[string]Peer{"existing": {Address: "10.80.0.2"}}
	for i := 0; i < 500; i++ {
		address, err := nextAddress(peers, true)
		if err != nil || strings.HasPrefix(address, "10.80.0.") {
			t.Fatal("expanded pool used a legacy address", address, err)
		}
		peers[fmt.Sprint(i)] = Peer{Address: address}
	}
	address, err := nextAddress(peers, false)
	if err != nil || address != "10.80.0.3" {
		t.Fatal("legacy allocation changed", address, err)
	}
	for i := 2; i < 250; i++ {
		peers[fmt.Sprint("legacy", i)] = Peer{Address: fmt.Sprintf("10.80.0.%d", i)}
	}
	if _, err := nextAddress(peers, false); err == nil {
		t.Fatal("full legacy pool reused an address")
	}
}

func TestCapacityIsSharedBetweenBothTransportsAndRecovers(t *testing.T) {
	r := &Relay{slots: make(chan struct{}, 3), perPeer: 2}
	a, ok := r.acquire("10.80.1.1")
	if !ok {
		t.Fatal("first stream rejected")
	}
	b, ok := r.acquire("10.80.1.1")
	if !ok {
		t.Fatal("second stream rejected")
	}
	if _, ok := r.acquire("10.80.1.1"); ok {
		t.Fatal("per-device capacity ignored")
	}
	c, ok := r.acquire("10.80.1.2")
	if !ok {
		t.Fatal("other device blocked")
	}
	if _, ok := r.acquire("10.80.1.3"); ok {
		t.Fatal("global capacity ignored")
	}
	a()
	d, ok := r.acquire("10.80.1.3")
	if !ok {
		t.Fatal("capacity was not released")
	}
	b()
	c()
	d()
	if len(r.active) != 0 || len(r.slots) != 0 {
		t.Fatal("stream reservation leaked")
	}
}

func TestPublicEndpoint(t *testing.T) {
	if endpoint, err := publicEndpoint("1.1.1.1:443"); err != nil || endpoint != "1.1.1.1:443" {
		t.Fatal("public endpoint rejected")
	}
	for _, endpoint := range []string{"127.0.0.1:443", "10.80.0.1:443", "0.0.0.0:443", "1.1.1.1:0"} {
		if _, err := publicEndpoint(endpoint); err == nil {
			t.Fatal("non-public or unusable endpoint accepted")
		}
	}
}

func TestRouteRestrictsHostAndPort(t *testing.T) {
	for _, host := range []string{"127.0.0.1:22", "10.80.0.1:22", "chat.parano1d.org:22", "example.org:443", "mseed1.parano1d.org:443"} {
		if _, e := target(host); e == nil {
			t.Fatal("route accepted", host)
		}
	}
	if value, e := target("chat.parano1d.org:443"); e != nil || value != "127.0.0.1:443" {
		t.Fatal("chat route failed")
	}
}
func TestEnrollmentRejectsUnsignedRequest(t *testing.T) {
	r := &Relay{}
	q := httptest.NewRequest("POST", "/v1/tunnel/enroll", strings.NewReader(`{"id":"`+strings.Repeat("ab", 32)+`","public_key":"`+strings.Repeat("cd", 32)+`","time_ms":1,"signature":""}`))
	w := httptest.NewRecorder()
	r.enroll(w, q)
	if w.Code != http.StatusUnauthorized {
		t.Fatal(w.Code)
	}
}
