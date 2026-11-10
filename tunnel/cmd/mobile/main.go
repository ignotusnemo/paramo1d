package main

/*
#include <stdlib.h>
*/
import "C"
import (
	"encoding/json"
	"errors"
	"github.com/ignotusnemo/paramo1d/tunnel/client"
	"sync"
	"unsafe"
)

var mu sync.Mutex
var current *client.Client

func execute(input []byte) (any, error) {
	if len(input) > 2*1024*1024 {
		return nil, errors.New("tunnel request exceeds limit")
	}
	var request struct {
		Op      string            `json:"op"`
		Config  client.Config     `json:"config"`
		Method  string            `json:"method"`
		URL     string            `json:"url"`
		Body    string            `json:"body"`
		Headers map[string]string `json:"headers"`
	}
	if e := json.Unmarshal(input, &request); e != nil {
		return nil, errors.New("invalid tunnel request")
	}
	mu.Lock()
	defer mu.Unlock()
	switch request.Op {
	case "keypair":
		return client.Keypair()
	case "start":
		if current != nil {
			current.Close()
			current = nil
		}
		c, e := client.Start(request.Config)
		if e != nil {
			return nil, e
		}
		current = c
		return c.Status(), nil
	case "stop":
		if current != nil {
			current.Close()
			current = nil
		}
		return map[string]any{"enabled": false}, nil
	case "status":
		if current == nil {
			return map[string]any{"enabled": false}, nil
		}
		return current.Status(), nil
	case "request":
		if current == nil {
			return nil, errors.New("turn on the protected connection first")
		}
		c := current
		mu.Unlock()
		result, e := c.Request(request.Method, request.URL, []byte(request.Body), request.Headers)
		mu.Lock()
		return result, e
	default:
		return nil, errors.New("unknown tunnel operation")
	}
}

//export Paramo1dTunnelCall
func Paramo1dTunnelCall(input *C.char) *C.char {
	result, e := execute([]byte(C.GoString(input)))
	var response map[string]any
	if e != nil {
		response = map[string]any{"ok": false, "error": e.Error()}
	} else {
		response = map[string]any{"ok": true, "result": result}
	}
	out, _ := json.Marshal(response)
	return C.CString(string(out))
}

//export Paramo1dTunnelFree
func Paramo1dTunnelFree(value *C.char) { C.free(unsafe.Pointer(value)) }
func main()                            {}
