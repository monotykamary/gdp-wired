import sys, time, z3
for f in [a for a in sys.argv[1:] if not a.startswith("--")]:
    s = z3.Solver(); s.set("timeout", 60000)
    t = time.time(); s.from_file(f); r = s.check(); print(f.split('/')[-1], r, round(time.time() - t, 3), "s", flush=True)
    if r == z3.sat and "--model" in sys.argv:
        m = s.model()
        print('  ', ' '.join(f"{d.name()}={m[d]}" for d in m.decls() if d.arity() == 0 and str(m[d]) != '0'))
        for d in m.decls():
            if d.arity() > 0:
                fl = m[d].as_list(); print('  ', d.name(), [(str(e[0]), str(e[1])) for e in fl[:-1] if str(e[1]) != '0'], 'else', fl[-1])
