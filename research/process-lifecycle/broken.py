"""Pure negative control: deliberately reaps before an admitted operation drains."""


class BrokenDrain:
    # gdp: law reaped has no in-flight signal: phase != 2 or inflight == 0
    def __init__(self):
        self.phase = 0
        self.inflight = 0

    def step(self, action: int):
        if action == 0:
            if self.phase == 0:
                self.inflight += 1
        elif action == 1:
            if self.phase == 0:
                self.phase = 1
        elif action == 2:
            if self.phase == 1:
                self.phase = 2  # BUG: no inflight == 0 guard
