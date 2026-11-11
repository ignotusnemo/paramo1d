// Package idleconn closes streams after a period without successful I/O.
package idleconn

import (
	"net"
	"sync"
	"time"
)

type Conn struct {
	net.Conn
	mu       sync.Mutex
	timer    *time.Timer
	timeout  time.Duration
	deadline time.Time
	closed   bool
}

func New(conn net.Conn, timeout time.Duration) *Conn {
	c := &Conn{Conn: conn, timeout: timeout, deadline: time.Now().Add(timeout)}
	c.timer = time.AfterFunc(timeout, c.expire)
	return c
}

func (c *Conn) expire() {
	c.mu.Lock()
	if c.closed {
		c.mu.Unlock()
		return
	}
	if remaining := time.Until(c.deadline); remaining > 0 {
		c.timer.Reset(remaining)
		c.mu.Unlock()
		return
	}
	c.closed = true
	c.mu.Unlock()
	c.Conn.Close()
}

func (c *Conn) touch() {
	c.mu.Lock()
	defer c.mu.Unlock()
	if !c.closed {
		c.deadline = time.Now().Add(c.timeout)
		c.timer.Reset(c.timeout)
	}
}

func (c *Conn) Read(p []byte) (int, error) {
	n, err := c.Conn.Read(p)
	if n > 0 {
		c.touch()
	}
	return n, err
}

func (c *Conn) Write(p []byte) (int, error) {
	n, err := c.Conn.Write(p)
	if n > 0 {
		c.touch()
	}
	return n, err
}

func (c *Conn) Close() error {
	c.mu.Lock()
	if c.closed {
		c.mu.Unlock()
		return nil
	}
	c.closed = true
	c.timer.Stop()
	c.mu.Unlock()
	return c.Conn.Close()
}
