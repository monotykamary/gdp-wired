"""Pure serialized lifecycle model; no PID, process, signal, filesystem or network API.

Premise: a sole surviving parent retains each direct child's PID until reap.
phase: 0 owned, 1 retiring, 2 reaped, 3 invalid.
action: 0 admit signal, 1 finish in-flight operation, 2 retire, 3 reap, 4 lose owner.
Admission models entry into the one owned signaling critical section, not enqueueing
an unchecked callback. Completion may also mean cancellation/draining, not delivery.
"""


class Lifecycle:
    # gdp: law reaped has no in-flight signal: phase != 2 or inflight == 0
    # gdp: law lost owner invalidates authority: owner or phase == 3
    # gdp: law lifecycle stays in domain: phase <= 3
    def __init__(self):
        self.phase = 0
        self.owner = True
        self.inflight = 0
        self.admissions = 0

    # gdp: law no admission after retirement: old(phase) != 1 or admissions == old(admissions)
    # gdp: law no admission after reap: old(phase) != 2 or admissions == old(admissions)
    # gdp: law no admission after owner loss: old(owner) or admissions == old(admissions)
    # gdp: law reap requires prior drain: phase != 2 or old(phase) == 2 or old(inflight) == 0
    # gdp: law closed lifecycle cannot reopen: old(phase) == 0 or phase != 0
    # gdp: law authority cannot resurrect: old(owner) or not owner
    def step(self, action: int):
        if action == 0:
            if self.owner and self.phase == 0:
                self.inflight += 1
                self.admissions += 1
        elif action == 1:
            if self.inflight > 0:
                self.inflight -= 1
        elif action == 2:
            if self.phase == 0:
                self.phase = 1
        elif action == 3:
            if self.owner and self.phase == 1 and self.inflight == 0:
                self.phase = 2
        elif action == 4:
            self.owner = False
            self.phase = 3
