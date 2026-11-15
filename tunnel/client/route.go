package client

import (
	"context"
	"crypto/tls"
	"errors"
	"net"
	"time"
)

type dialFunc func(context.Context, string, string) (net.Conn, error)

func tlsRoute(dial dialFunc, config *tls.Config) dialFunc {
	return func(ctx context.Context, network, target string) (net.Conn, error) {
		ctx, cancel := context.WithTimeout(ctx, 12*time.Second)
		defer cancel()
		stream, err := dial(ctx, network, target)
		if err != nil {
			return nil, err
		}
		host, _, err := net.SplitHostPort(target)
		if err != nil {
			stream.Close()
			return nil, err
		}
		trust := config.Clone()
		trust.ServerName = host
		secured := tls.Client(stream, trust)
		if err := secured.HandshakeContext(ctx); err != nil {
			secured.Close()
			return nil, err
		}
		return secured, nil
	}
}

// destinationError is a reply from a reachable proxy about the target service.
type destinationError struct{ status int }

func (e *destinationError) Error() string { return "protected route cannot reach this service" }

// raceRoute gives UDP a head start and starts HTTPS while UDP is still waiting.
// Only connection establishment is raced. Application data uses the winner.
func raceRoute(ctx context.Context, primary, secondary dialFunc, network, target string, delay time.Duration) (net.Conn, bool, error) {
	ctx, cancel := context.WithCancel(ctx)
	defer cancel()
	type result struct {
		conn  net.Conn
		https bool
		err   error
	}
	results := make(chan result)
	start := func(dial dialFunc, https bool) {
		go func() {
			conn, err := dial(ctx, network, target)
			select {
			case results <- result{conn, https, err}:
			case <-ctx.Done():
				if conn != nil {
					conn.Close()
				}
			}
		}()
	}
	start(primary, false)
	timer := time.NewTimer(delay)
	defer timer.Stop()
	started, finished := 1, 0
	var last error
	for {
		select {
		case <-ctx.Done():
			return nil, false, ctx.Err()
		case <-timer.C:
			if started == 1 {
				start(secondary, true)
				started++
			}
		case r := <-results:
			if r.err == nil {
				return r.conn, r.https, nil
			}
			var destination *destinationError
			if errors.As(r.err, &destination) {
				return nil, false, r.err
			}
			last = r.err
			finished++
			if started == 1 {
				start(secondary, true)
				started++
			}
			if finished == 2 {
				return nil, false, last
			}
		}
	}
}
