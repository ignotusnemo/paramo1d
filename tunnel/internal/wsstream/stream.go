// Package wsstream carries a TCP byte stream in bounded WebSocket binary frames.
package wsstream

import (
	"errors"
	"github.com/gorilla/websocket"
	"io"
	"net"
	"sync"
	"time"
)

type Conn struct {
	Socket *websocket.Conn
	reader io.Reader
	write  sync.Mutex
}

func New(socket *websocket.Conn) *Conn { socket.SetReadLimit(65536); return &Conn{Socket: socket} }
func (c *Conn) Read(p []byte) (int, error) {
	for {
		if c.reader == nil {
			kind, r, e := c.Socket.NextReader()
			if e != nil {
				return 0, e
			}
			if kind != websocket.BinaryMessage {
				return 0, errors.New("binary frames required")
			}
			c.reader = r
		}
		n, e := c.reader.Read(p)
		if e == io.EOF {
			c.reader = nil
			if n > 0 {
				return n, nil
			}
			continue
		}
		return n, e
	}
}
func (c *Conn) Write(p []byte) (int, error) {
	c.write.Lock()
	defer c.write.Unlock()
	n := 0
	for len(p) > 0 {
		count := len(p)
		if count > 32768 {
			count = 32768
		}
		if e := c.Socket.WriteMessage(websocket.BinaryMessage, p[:count]); e != nil {
			return n, e
		}
		n += count
		p = p[count:]
	}
	return n, nil
}
func (c *Conn) Close() error         { return c.Socket.Close() }
func (c *Conn) LocalAddr() net.Addr  { return c.Socket.LocalAddr() }
func (c *Conn) RemoteAddr() net.Addr { return c.Socket.RemoteAddr() }
func (c *Conn) SetDeadline(t time.Time) error {
	if e := c.Socket.SetReadDeadline(t); e != nil {
		return e
	}
	return c.Socket.SetWriteDeadline(t)
}
func (c *Conn) SetReadDeadline(t time.Time) error  { return c.Socket.SetReadDeadline(t) }
func (c *Conn) SetWriteDeadline(t time.Time) error { return c.Socket.SetWriteDeadline(t) }
