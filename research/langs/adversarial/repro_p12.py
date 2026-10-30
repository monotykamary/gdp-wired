import p12
class Shared:
    def __init__(self): self.data = {}
    def get(self, key): return self.data.get(key)
    def set(self, key, value): self.data[key] = value
s = Shared()
m = p12.Meter(s, s)
m.tick()
print('real shared-store n=', m.n, 'data=', s.data)
assert m.n == 1
