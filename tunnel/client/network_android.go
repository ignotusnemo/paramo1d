//go:build android

package client

/*
#cgo LDFLAGS: -landroid
#include <android/multinetwork.h>
*/
import "C"
import "errors"

func bindNetwork(network uint64, fd int) error {
	if network == 0 {
		return nil
	}
	if C.android_setsocknetwork(C.net_handle_t(network), C.int(fd)) != 0 {
		return errors.New("physical network is unavailable")
	}
	return nil
}
