package main

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
)

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
