//go:build !android

package client

import "errors"

func bindNetwork(network uint64, fd int) error {
	if network != 0 {
		return errors.New("physical network handles require Android")
	}
	return nil
}
