// Probe checks the deployed tunnel with a separate, unfunded test identity.
package main

import (
	"bytes"
	"crypto/ed25519"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"github.com/ignotusnemo/paramo1d/tunnel/client"
	"golang.org/x/crypto/hkdf"
	"io"
	"net/http"
	"os"
	"time"
)

func main() {
	start := time.Now()
	seed := bytes.Repeat([]byte{9}, 32)
	auth := make([]byte, 32)
	io.ReadFull(hkdf.New(sha256.New, seed, []byte("Paramo1d/Courier/1"), []byte("message authentication")), auth)
	signing := ed25519.NewKeyFromSeed(auth)
	pair, e := client.Keypair()
	if e != nil {
		panic("key generation failed")
	}
	clock := time.Now().UnixMilli()
	path := "/v1/tunnel/" + pair["public_key"]
	signed := []byte(fmt.Sprintf("Paramo1d/Courier/inbox/1\x00%s\x00%d", path, clock))
	body, _ := json.Marshal(map[string]any{"id": hex.EncodeToString(signing.Public().(ed25519.PublicKey)), "public_key": pair["public_key"], "time_ms": clock, "signature": hex.EncodeToString(ed25519.Sign(signing, signed))})
	httpClient := &http.Client{Timeout: 20 * time.Second}
	response, e := httpClient.Post("https://chat.parano1d.org/v1/tunnel/enroll", "application/json", bytes.NewReader(body))
	if e != nil {
		fmt.Println("Enrollment connection failed")
		os.Exit(1)
	}
	defer response.Body.Close()
	if response.StatusCode != 200 {
		fmt.Println("Enrollment status", response.StatusCode)
		os.Exit(1)
	}
	var config client.Config
	if json.NewDecoder(io.LimitReader(response.Body, 8192)).Decode(&config) != nil {
		panic("enrollment response invalid")
	}
	config.PreferHTTPS = os.Getenv("PARAMO1D_FORCE_HTTPS")=="1"
 config.PrivateKey = pair["private_key"]
	token, _ := client.Keypair()
	config.Token = token["private_key"]
	tunnel, e := client.Start(config)
	if e != nil {
		fmt.Println(e)
		os.Exit(1)
	}
	defer tunnel.Close()
	health, e := tunnel.Request("GET", "https://chat.parano1d.org/healthz", nil, nil)
	if e != nil {
		fmt.Println(e)
		os.Exit(1)
	}
	result := tunnel.Status()
	result["health"] = json.RawMessage(health)
	result["elapsed_ms"] = time.Since(start).Milliseconds()
	_, denied := tunnel.Request("GET", "https://example.org/", nil, nil)
	result["other_destinations_rejected"] = denied != nil
	delete(result, "proxy_port")
	json.NewEncoder(os.Stdout).Encode(result)
}
