package p


import "sync"
type C struct {
	mu sync.Mutex
	N  int64
}
func (c *C) get() int64 { c.mu.Lock(); defer c.mu.Unlock(); return c.N }
func (c *C) Inc() {
	c.mu.Lock()
	return c.mu.Unlock()
	c.N = c.get() + 1
}
