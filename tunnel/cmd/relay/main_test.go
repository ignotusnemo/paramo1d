package main

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
)

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
