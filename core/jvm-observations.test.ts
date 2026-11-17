// Native runtime-hook controls. This file is also in the mandatory JDK job.
import {expect, test} from 'bun:test'
import {execFileSync} from 'node:child_process'
import {mkdtempSync, rmSync, writeFileSync} from 'node:fs'
import {tmpdir} from 'node:os'
import {join} from 'node:path'

const hasJdk = (() => { try { execFileSync('javac', ['-version'], {stdio: 'ignore'}); return true } catch { return false } })()
;(hasJdk ? test : test.skip)('JVM observes actual immutable values, isolates invocations, and refuses conflicting reads', () => {
  const root = mkdtempSync(join(tmpdir(), 'gdp-observation-'))
  try {
    writeFileSync(join(root, 'Observed.java'), `
import gdp.Rt;
import java.util.Set;
public class Observed {
  static void check(boolean ok, String what) { if (!ok) throw new AssertionError(what); }
  public static void main(String[] args) {
    Rt.ANSWER = (key, kind) -> 7L;
    Rt.NOW = 11L;
    Rt.Observations first = Rt.beginObservations(Set.of("Quota.ttl"));
    check(Rt.now() == 11L, "actual clock");
    check(Rt.answer("Quota.ttl", Long.class).equals(7L), "actual return");
    Rt.answer("Quota.ttl", Long.class); Rt.now();
    Rt.endObservations(first);
    check(first.error == null && first.clock == 11L && first.calls.get("Quota.ttl").value.equals(7L), "actual values retained");
    Rt.Observations second = Rt.beginObservations(Set.of("Quota.ttl"));
    Rt.endObservations(second);
    check(second.invocation > first.invocation && second.calls.isEmpty() && second.clock == null, "no stale reads");
    Rt.Observations changed = Rt.beginObservations(Set.of("Quota.ttl"));
    Rt.answer("Quota.ttl", Long.class); Rt.ANSWER = (key, kind) -> 8L; Rt.answer("Quota.ttl", Long.class);
    Rt.endObservations(changed); check(changed.error != null, "different repeated answers");
    Rt.Observations clock = Rt.beginObservations(Set.of());
    Rt.NOW = 1L; Rt.now(); Rt.NOW = 2L; Rt.now(); Rt.endObservations(clock);
    check(clock.error != null, "different repeated clocks");
    for (Object value : new Object[]{0.5d, Double.NaN, -0.0d, 9007199254740992L, new java.math.BigInteger("1")}) {
      Rt.ANSWER = (key, kind) -> value;
      Rt.Observations unsupported = Rt.beginObservations(Set.of("Quota.ttl"));
      Rt.answer("Quota.ttl", Object.class); Rt.endObservations(unsupported);
      check(unsupported.error != null, "unsupported or inexact return");
    }
    Rt.Observations huge = Rt.beginObservations(Set.of());
    Rt.NOW = Long.MAX_VALUE; Rt.now(); Rt.endObservations(huge); check(huge.error != null, "unsafe clock");
    Rt.Observations wrong = Rt.beginObservations(Set.of("Quota.ttl"));
    Rt.ANSWER = (key, kind) -> 7L; Rt.answer("Wrong.ttl", Long.class); Rt.endObservations(wrong);
    check(wrong.error != null, "unbound call identity");
    Rt.ANSWER = (key, kind) -> { throw new IllegalStateException("actual raised outcome"); };
    Rt.Observations raised = Rt.beginObservations(Set.of("Quota.ttl"));
    try { Rt.answer("Quota.ttl", Long.class); throw new AssertionError("must throw"); } catch (IllegalStateException expected) {}
    Rt.endObservations(raised);
    check(raised.error == null && raised.calls.get("Quota.ttl").raised.equals("java.lang.IllegalStateException"), "actual raised class");
    System.out.println("ACTUAL_OBSERVATION_CONTROLS_PASS");
  }
}
`)
    execFileSync('javac', ['-d', root, join(import.meta.dir, 'jvm/Rt.java'), join(root, 'Observed.java')], {timeout: 30000, stdio: 'pipe'})
    const output = execFileSync('java', ['-cp', root, 'Observed'], {encoding: 'utf8', timeout: 15000})
    expect(output.trim()).toBe('ACTUAL_OBSERVATION_CONTROLS_PASS')
  } finally { rmSync(root, {recursive: true, force: true}) }
}, 60000)
