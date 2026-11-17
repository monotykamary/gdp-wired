#!/usr/bin/env python3
"""Python arbitrary-precision arithmetic with explicit machine-width adapters.

No Python width/overflow mode, division-pair trap, or fixed-width primitive is
claimed native. Python's // and % natively implement FLOOR for nonzero divisors.
"""
import sys

def bound(n, w, signed, policy):
    lo = -(1 << (w - 1)) if signed else 0
    hi = (1 << (w - 1)) - 1 if signed else (1 << w) - 1
    if lo <= n <= hi:
        return n, None
    if policy == 'TRAP':
        return None, 'overflow'
    if policy == 'SATURATE':
        return min(hi, max(lo, n)), None
    if policy != 'WRAP':
        raise ValueError('invalid policy')
    v = n % (1 << w)
    if signed and v >= (1 << (w - 1)):
        v -= 1 << w
    return v, None

def evaluate(width, signed, op, policy, mode, a, b):
    if op in ('div', 'rem'):
        if b == 0:
            return None, 'division_by_zero'
        if signed and a == -(1 << (width - 1)) and b == -1 and policy == 'TRAP':
            return None, 'overflow' # explicit machine division-pair adapter
        if mode == 'FLOOR':
            q, r = a // b, a % b
        elif mode == 'TRUNCATING':
            q = abs(a) // abs(b) * (-1 if (a < 0) != (b < 0) else 1)
            r = a - b * q
        elif mode == 'EUCLIDEAN':
            r = a % abs(b)
            q = (a - r) // b
        else:
            raise ValueError('invalid mode')
        n = q if op == 'div' else r
    elif op == 'cast': n = a
    elif op == 'add': n = a + b
    elif op == 'sub': n = a - b
    elif op == 'mul': n = a * b
    elif op == 'neg': n = -a
    else: raise ValueError('invalid operation')
    return bound(n, width, signed, policy)

for line in sys.stdin:
    width, signed, op, policy, mode, a, b = line.split()
    width, signed, a, b = int(width), signed == '1', int(a), int(b)
    assert width in (8, 16, 32, 64)
    value, error = evaluate(width, signed, op, policy, mode, a, b)
    print('ERR ' + error if error else 'OK ' + str(value), flush=True)
