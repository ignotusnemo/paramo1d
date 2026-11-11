package idleconn

import (
	"io"
	"net"
	"testing"
	"time"
)

func TestActiveStreamOutlivesIdleTimeout(t *testing.T) {
	for _, direction := range []string{"read", "write"} {
		t.Run(direction, func(t *testing.T) {
			local, peer := net.Pipe()
			stream := New(local, 200*time.Millisecond)
			defer stream.Close()
			defer peer.Close()
			peer.SetDeadline(time.Now().Add(3 * time.Second))
			var reader io.Reader = stream
			var writer io.Writer = peer
			if direction == "write" {
				reader, writer = peer, stream
			}
			done := make(chan error, 1)
			go func() {
				for i := 0; i < 12; i++ {
					if _, err := writer.Write([]byte{byte(i)}); err != nil {
						done <- err
						return
					}
					time.Sleep(30 * time.Millisecond)
				}
				done <- nil
			}()
			for i := 0; i < 12; i++ {
				var value [1]byte
				if _, err := io.ReadFull(reader, value[:]); err != nil {
					t.Fatalf("active %s stream closed at byte %d: %v", direction, i, err)
				}
				if value[0] != byte(i) {
					t.Fatal("stream payload changed")
				}
			}
			if err := <-done; err != nil {
				t.Fatal(err)
			}
		})
	}
}

func TestIdleStreamClosesBlockedRead(t *testing.T) {
	local, peer := net.Pipe()
	stream := New(local, 30*time.Millisecond)
	defer stream.Close()
	defer peer.Close()
	done := make(chan error, 1)
	go func() { _, err := stream.Read(make([]byte, 1)); done <- err }()
	select {
	case err := <-done:
		if err == nil {
			t.Fatal("idle stream remained open")
		}
	case <-time.After(time.Second):
		t.Fatal("idle timeout did not cancel the blocked read")
	}
}

func TestPendingExpiryRespectsRecentActivity(t *testing.T) {
	local, peer := net.Pipe()
	stream := New(local, time.Second)
	defer stream.Close()
	defer peer.Close()
	stream.touch()
	stream.expire()
	peer.SetDeadline(time.Now().Add(time.Second))
	done := make(chan error, 1)
	go func() { _, err := stream.Write([]byte{42}); done <- err }()
	var value [1]byte
	if _, err := io.ReadFull(peer, value[:]); err != nil || value[0] != 42 {
		t.Fatalf("pending expiry closed a recently active stream: %v", err)
	}
	if err := <-done; err != nil {
		t.Fatal(err)
	}
}
