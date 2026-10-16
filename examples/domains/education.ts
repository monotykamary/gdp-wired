// Education, HR and elections: section enrollment, exam attempts, letter grades, leave, payroll, ballot tallies,
// committee votes, timesheet approval and a grading queue.
import {type Bool, type Choice, type Maybe, type Term, any, bool, count, forall, loop, max, maybe, min, nat, oneOf, relation, rule, upTo, when, yes} from '../../core/dsl.ts'
import {type Domain, decisionCase, loopCase, machineCase} from '../harness.ts'

// Sections with a capacity each: a student enrolls while there's a seat, drops, and the registrar resizes a section,
// never below its enrollment.
const sections = (bug?: 'resize shrinks' | 'off by one') => rule('section enrollment')
  .inputs({op: oneOf('enroll', 'drop', 'resize'), section: nat, seats: nat})
  .maps({Enrolled: 0, Cap: 0})
  .flags(({op, section, Enrolled, Cap}) => ({enrolls: op.is('enroll').and(bug === 'off by one' ? Enrolled.at(section).atMost(Cap.at(section)) : Enrolled.at(section).lt(Cap.at(section)))}))
  .step(({op, section, seats, enrolls, Enrolled, Cap}) => ({
    Enrolled: Enrolled.set(section, when(enrolls, Enrolled.at(section).plus(1), when(op.is('drop'), Enrolled.at(section).minus(1), Enrolled.at(section)))),
    Cap: Cap.set(section, when(op.is('resize'), bug === 'resize shrinks' ? seats : max(seats, Enrolled.at(section)), Cap.at(section))),
  }))
const sectionLaw = (r: ReturnType<typeof sections>) => r.law('every section: enrolled <= capacity', ({Enrolled, Cap}) => forall(s => Enrolled.at(s).atMost(Cap.at(s))))

// Exam attempts: a student may sit an exam at most `limit` times within any `window` days. The log keeps every admitted
// attempt (student, day); `taken` counts the student's attempts in the window before a request, `attempts` the
// attempts of any one student `who` in the window ending at `now` (a param, so the law is about every student).
const attempts = (opts: {pruned?: boolean, bug?: 'off by one' | 'counts only today' | 'prunes early'} = {}) => {
  const base = rule(opts.pruned ? 'exam attempts per student, pruned' : 'exam attempts per student')
    .params({window: nat, limit: nat, who: nat, now: nat})
    .inputs({student: nat, t: nat})
    .log('student', 't')
    .sums({attempts: (r, {who, now, window}) => count(r.student.eq(who).and(r.t.atMost(now), now.lt(r.t.plus(window))))})
    .queries({taken: (r, {student, t, window}) => count(r.student.eq(student).and(opts.bug === 'counts only today' ? r.t.eq(t) : t.lt(r.t.plus(window))))})
    .flags(({taken, limit}) => ({admitted: opts.bug === 'off by one' ? taken.atMost(limit) : taken.lt(limit)}))
    .keep(({admitted}) => admitted)
    .relations(({student, who, t, now, attempts: a, taken}) => [relation(a.atMost(taken), student.eq(who).and(t.atMost(now)))])
  return !opts.pruned ? base : base.prune('t', ({window}) => (opts.bug === 'prunes early' ? window.minus(1) : window))
}
const attemptLaw = (r: ReturnType<typeof attempts>) => r.law('any student\'s attempts in the window ending at now <= limit', ({attempts: a, limit}) => a.atMost(limit))

// Letter grades: the total is the points plus any extra credit (at most 10), capped at 100; A from 90, B from 80, C
// from 70, D from 60, F below. `letter` is the grade's index (A = 0 … F = 4), `earns` whether a recorded grade fits.
const grades = rule('letter grades').inputs({points: upTo(100), extra: maybe(upTo(10)), grade: oneOf('A', 'B', 'C', 'D', 'F')})
type Letter = 'A' | 'B' | 'C' | 'D' | 'F'
type GradeEnv = {points: Term, extra: Maybe<Term>, grade: Choice<Letter>}
const total = ({points, extra}: GradeEnv) => min(100, points.plus(extra.match({none: () => 0, some: e => e})))
const letter = (t: Term) => when(t.atLeast(90), 0, when(t.atLeast(80), 1, when(t.atLeast(70), 2, when(t.atLeast(60), 3, 4))))
// `strictB`: the bug where B is written as "above 80" rather than "80 and up".
const fits = (g: Letter, t: Term, strictB = false) => ({
  A: () => t.atLeast(90),
  B: () => (strictB ? t.gt(80) : t.atLeast(80)).and(t.lt(90)),
  C: () => t.atLeast(70).and(t.lt(80)),
  D: () => t.atLeast(60).and(t.lt(70)),
  F: () => t.lt(60),
})[g]()
const earns = (env: GradeEnv) => env.grade.match({A: () => fits('A', total(env)), B: () => fits('B', total(env)), C: () => fits('C', total(env)), D: () => fits('D', total(env)), F: () => fits('F', total(env))})
const someGrade = (t: Term, strictB = false) => any(...(['A', 'B', 'C', 'D', 'F'] as const).map(g => fits(g, t, strictB)))
const gradeDecisions = [
  grades.decide('a recorded A needs at least 80 raw points', env => [earns(env), env.grade.is('A')], ({points}) => points.atLeast(80)),
  grades.decide('extra credit never lowers a grade', () => yes, env => letter(total(env)).atMost(letter(env.points))),
  grades.decide('extra credit lifts a grade by at most one letter', () => yes, env => letter(env.points).atMost(letter(total(env)).plus(1))),
  grades.decide('without extra credit the grade is the raw score\'s', env => [env.extra.isNone, earns(env)], env => letter(env.points).eq(env.grade.n)),
  grades.decide('every total earns some grade', () => yes, env => someGrade(total(env))),
]
const gradeBroken = [
  {name: 'an A needs 90 raw points', why: 'the claim forgets that extra credit counts toward the total', decision: grades.decide('a recorded A needs 90 raw points', env => [earns(env), env.grade.is('A')], ({points}) => points.atLeast(90))},
  {name: 'B starts above 80', why: 'an off-by-one boundary leaves a total of exactly 80 with no grade', decision: grades.decide('every total earns some grade', () => yes, env => someGrade(total(env), true))},
]

// Leave: each accrual adds `rate` days, but the unused balance never passes `cap`; a request is granted only within the
// balance.
const leave = (bug?: 'accrual uncapped' | 'checks the cap') => rule('leave balance')
  .params({rate: nat, cap: nat})
  .inputs({op: oneOf('accrue', 'take'), days: nat})
  .state({accrued: 0, taken: 0})
  .flags(({op, days, accrued, taken, cap}) => ({granted: op.is('take').and(bug === 'checks the cap' ? days.atMost(cap) : taken.plus(days).atMost(accrued))}))
  .step(({op, days, rate, cap, accrued, taken, granted}) => ({
    accrued: when(op.is('accrue'), bug === 'accrual uncapped' ? accrued.plus(rate) : min(taken.plus(cap), accrued.plus(rate)), accrued),
    taken: when(granted, taken.plus(days), taken),
  }))
const leaveLaws = (r: ReturnType<typeof leave>) => [
  r.law('taken <= accrued', ({taken, accrued}) => taken.atMost(accrued)),
  r.law('balance <= cap', ({taken, accrued, cap}) => accrued.atMost(taken.plus(cap))),
]

// Payroll in half-wage units: a shift's first 8 hours pay 2 units each, overtime 3 (1.5×). Advances are paid within
// what's earned; a settlement pays out the rest. Shifts run to 20 hours in the runs (bound 20), so overtime shows up.
const payroll = (bug?: 'overtime paid twice' | 'settles the gross') => rule('payroll with overtime')
  .inputs({op: oneOf('work', 'advance', 'settle'), hours: nat, amount: nat})
  .state({worked: 0, earned: 0, paid: 0})
  .flags(({op, amount, earned, paid}) => ({advances: op.is('advance').and(paid.plus(amount).atMost(earned))}))
  .step(({op, hours, amount, worked, earned, paid, advances}) => ({
    worked: when(op.is('work'), worked.plus(hours), worked),
    earned: when(op.is('work'), earned.plus((bug === 'overtime paid twice' ? hours.times(2) : min(hours, 8).times(2)).plus(hours.minus(8).times(3))), earned),
    paid: when(advances, paid.plus(amount), when(op.is('settle'), bug === 'settles the gross' ? paid.plus(earned) : earned, paid)),
  }))
const payrollLaws = (r: ReturnType<typeof payroll>) => [
  r.law('paid <= earned', ({paid, earned}) => paid.atMost(earned)),
  r.law('earned <= 1.5 × base for the hours worked', ({earned, worked}) => earned.atMost(worked.times(3))),
  r.law('earned >= base for the hours worked', ({earned, worked}) => worked.times(2).atMost(earned)),
]

// A ballot tally (first preferences): a ballot is cast once, counted once, and only if cast; each count adds one vote
// to its candidate. The tally also reconciles against the cast total.
const tally = (bug?: 'recounts' | 'counts uncast') => rule('ballot tally')
  .inputs({op: oneOf('cast', 'count'), ballot: nat, candidate: nat})
  .state({cast: 0, counted: 0})
  .maps({Cast: 0, Counted: 0, Votes: 0})
  .flags(({op, ballot, Cast, Counted, cast, counted}) => ({
    casts: op.is('cast').and(Cast.at(ballot).eq(0)),
    counts: op.is('count').and(bug === 'counts uncast' ? yes : Cast.at(ballot).eq(1), bug === 'recounts' ? yes : Counted.at(ballot).eq(0), counted.lt(cast)),
  }))
  .step(({ballot, candidate, casts, counts, cast, counted, Cast, Counted, Votes}) => ({
    Cast: Cast.set(ballot, when(casts, 1, Cast.at(ballot))),
    cast: when(casts, cast.plus(1), cast),
    Counted: Counted.bump(ballot, counts),
    counted: when(counts, counted.plus(1), counted),
    Votes: Votes.bump(candidate, counts),
  }))
const tallyLaws = (r: ReturnType<typeof tally>) => [
  r.law('counted <= cast', ({counted, cast}) => counted.atMost(cast)),
  r.law('every ballot: counted <= cast, so at most once', ({Counted, Cast}) => forall(b => Counted.at(b).atMost(Cast.at(b)))),
  r.law('every ballot is cast at most once', ({Cast}) => forall(b => Cast.at(b).atMost(1))),
  r.law('every candidate: votes <= ballots counted', ({Votes, counted}) => forall(c => Votes.at(c).atMost(counted))),
]

// Committee votes: quorum is more than half the members present; a motion passes with more yes than no, an amendment
// with two thirds of the votes cast (and at least one yes), a procedural question also on a tie the chair breaks.
const committee = rule('committee votes')
  .inputs({kind: oneOf('motion', 'amendment', 'procedural'), members: upTo(15), present: upTo(15), yes: upTo(15), no: upTo(15), chairYes: bool})
  .assume(({members, present, yes: y, no: n}) => present.atMost(members).and(y.plus(n).atMost(present)))
type CommitteeEnv = {kind: Choice<'motion' | 'amendment' | 'procedural'>, members: Term, present: Term, yes: Term, no: Term, chairYes: Bool}
const quorum = ({members, present}: CommitteeEnv) => present.times(2).gt(members)
const passes = (env: CommitteeEnv) => {
  const {kind, yes: y, no: n, chairYes} = env
  return quorum(env).and(kind.match({
    motion: () => y.gt(n),
    amendment: () => y.times(3).atLeast(y.plus(n).times(2)).and(y.atLeast(1)),
    procedural: () => y.gt(n).or(y.eq(n).and(chairYes)),
  }))
}
const committeeDecisions = [
  committee.decide('nothing passes without quorum', env => passes(env), env => quorum(env)),
  committee.decide('a passed amendment has a majority of the votes cast', env => [passes(env), env.kind.is('amendment')], ({yes: y, no: n}) => y.gt(n)),
  committee.decide('a pass has more yes than no, but for a chair-broken procedural tie', env => passes(env), ({kind, yes: y, no: n, chairYes}) => y.gt(n).or(kind.is('procedural').and(chairYes, y.eq(n)))),
  committee.decide('a unanimous full committee passes a motion', ({kind, members, present, yes: y}) => [kind.is('motion'), members.atLeast(1), present.eq(members), y.eq(present)], env => passes(env)),
]
const committeeBroken = [
  {name: 'a majority present is enough', why: 'the claim forgets quorum: two members present out of fifteen are not a meeting', decision: committee.decide('a majority of those present passes a motion', ({kind, yes: y, present}) => [kind.is('motion'), y.times(2).gt(present)], env => passes(env))},
  {name: 'a tie always fails', why: 'a procedural tie passes when the chair votes yes', decision: committee.decide('a tie always fails', ({yes: y, no: n}) => y.eq(n), env => passes(env).not())},
]

// Timesheets: draft (0) → submitted (1) → approved (2) → paid (3); a reviewer can reject a submitted sheet back to draft
// and reopen an approved one. Submitted and Approved count the events per sheet.
const DRAFT = 0, SUBMITTED = 1, APPROVED = 2, PAID = 3
const timesheets = (bug?: 'approves drafts' | 'pays unapproved') => rule('timesheet approval')
  .inputs({op: oneOf('submit', 'approve', 'reject', 'reopen', 'pay'), sheet: nat})
  .maps({Status: 0, Submitted: 0, Approved: 0})
  .flags(({op, sheet, Status}) => {
    const s = Status.at(sheet)
    return {
      submits: op.is('submit').and(s.eq(DRAFT)),
      approves: op.is('approve').and(bug === 'approves drafts' ? s.lt(APPROVED) : s.eq(SUBMITTED)),
      rejects: op.is('reject').and(s.eq(SUBMITTED)),
      reopens: op.is('reopen').and(s.eq(APPROVED)),
      pays: op.is('pay').and(bug === 'pays unapproved' ? s.ne(PAID) : s.eq(APPROVED)),
    }
  })
  .step(({sheet, Status, Submitted, Approved, submits, approves, rejects, reopens, pays}) => ({
    Status: Status.set(sheet, when(submits, SUBMITTED, when(approves, APPROVED, when(rejects.or(reopens), DRAFT, when(pays, PAID, Status.at(sheet)))))),
    Submitted: Submitted.bump(sheet, submits),
    Approved: Approved.bump(sheet, approves),
  }))
const sheetLaws = (r: ReturnType<typeof timesheets>) => [
  r.law('every sheet is in one of the four states', ({Status}) => forall(s => Status.at(s).atMost(PAID))),
  r.law('every approval follows its own submission', ({Status, Submitted, Approved}) => forall(s => Approved.at(s).plus(when(Status.at(s).eq(SUBMITTED), 1, 0)).atMost(Submitted.at(s)))),
  r.law('approved or paid only after an approval', ({Status, Approved}) => forall(s => Status.at(s).lt(APPROVED).or(Approved.at(s).atLeast(1)))),
]

// A grading queue: each turn grades the next submission, unless a student appeals a graded one and the appeal budget
// allows it, which sends it back to the queue. The rank is (appeals left, pending): an appeal drops the first while the
// queue grows, a grading drops the second.
const queue = (bug?: 'appeals unbudgeted' | 'ranks the queue alone') => loop('grading queue with appeals')
  .params({submissions: nat, appeals: nat})
  .inputs({appeal: bool, score: upTo(100)})
  .state({pending: ({submissions}) => submissions, graded: 0, left: ({appeals}) => appeals, gradings: 0, points: 0})
  .while(({pending}) => pending.gt(0))
  .body(({pending, graded, left, gradings, points, appeal, score}) => {
    const back = bug === 'appeals unbudgeted' ? appeal.and(graded.gt(0)) : appeal.and(left.gt(0), graded.gt(0))
    return {
      pending: when(back, pending.plus(1), pending.minus(1)),
      graded: when(back, graded.minus(1), graded.plus(1)),
      left: when(back, left.minus(1), left),
      gradings: when(back, gradings, gradings.plus(1)),
      points: when(back, points, points.plus(score)),
    }
  })
  .rank(({left, pending}) => (bug === 'ranks the queue alone' ? pending : [left, pending]))
const queueLaws = (l: ReturnType<typeof queue>) => [
  l.law('pending + graded = submissions', ({pending, graded, submissions}) => pending.plus(graded).eq(submissions)),
  l.law('appeals left <= budget', ({left, appeals}) => left.atMost(appeals)),
  l.law('points <= 100 per grading', ({points, gradings}) => points.atMost(gradings.times(100))),
]

const sectionsShrink = sections('resize shrinks'), sectionsOff = sections('off by one')
const attemptsOff = attempts({bug: 'off by one'}), attemptsToday = attempts({bug: 'counts only today'}), attemptsEarly = attempts({pruned: true, bug: 'prunes early'})
const leaveUncapped = leave('accrual uncapped'), leaveCap = leave('checks the cap')
const payrollTwice = payroll('overtime paid twice'), payrollGross = payroll('settles the gross')
const tallyRecount = tally('recounts'), tallyUncast = tally('counts uncast')
const sheetsDraft = timesheets('approves drafts'), sheetsUnapproved = timesheets('pays unapproved')
const queueUnbudgeted = queue('appeals unbudgeted'), queueAlone = queue('ranks the queue alone')

export const domain: Domain = {
  domain: 'education',
  about: 'enrollment, exam attempts, letter grades, leave, payroll, ballot tallies, committee votes, timesheets, a grading queue',
  cases: [
    machineCase('section enrollment', 'no section ever holds more students than its capacity', sections(), [sectionLaw(sections())], [
      {name: 'resize shrinks', why: 'a resize sets the capacity below the students already enrolled', rule: sectionsShrink, laws: [sectionLaw(sectionsShrink)]},
      {name: 'off by one', why: 'an enrollment is admitted at enrolled = capacity', rule: sectionsOff, laws: [sectionLaw(sectionsOff)]},
    ]),
    machineCase('exam attempts per student', 'every student sits at most `limit` attempts in any window, read from the log', attempts(), [attemptLaw(attempts())], [
      {name: 'off by one', why: 'an attempt is admitted when the window already holds `limit`', rule: attemptsOff, laws: [attemptLaw(attemptsOff)]},
      {name: 'counts only today', why: 'the check counts the student\'s attempts on the same day, not in the window', rule: attemptsToday, laws: [attemptLaw(attemptsToday)]},
    ]),
    machineCase('exam attempts per student, pruned', 'the same, the log dropping attempts older than the window', attempts({pruned: true}), [attemptLaw(attempts({pruned: true}))], [
      {name: 'prunes a day early', why: 'an attempt still inside the window is dropped, so the next request sees one fewer', rule: attemptsEarly, laws: [attemptLaw(attemptsEarly)]},
    ]),
    decisionCase('letter grades', 'grades fit the total, extra credit helps by at most a letter, every total earns a grade', gradeDecisions, gradeBroken),
    machineCase('leave balance', 'leave taken never passes leave accrued, and the balance never passes the cap', leave(), leaveLaws(leave()), [
      {name: 'accrual uncapped', why: 'accrual adds the rate without the cap on the balance', rule: leaveUncapped, laws: leaveLaws(leaveUncapped)},
      {name: 'checks the cap', why: 'a request is checked against the policy cap, not the balance', rule: leaveCap, laws: leaveLaws(leaveCap)},
    ]),
    machineCase('payroll with overtime', 'pay never passes earnings, and earnings sit between base and 1.5× base for the hours worked', payroll(), payrollLaws(payroll()), [
      {name: 'overtime paid twice', why: 'overtime hours are paid at base and again at the overtime rate', rule: payrollTwice, laws: payrollLaws(payrollTwice)},
      {name: 'settles the gross', why: 'a settlement pays the gross earnings again instead of setting pay to them', rule: payrollGross, laws: payrollLaws(payrollGross)},
    ], {bound: 20}),
    machineCase('ballot tally', 'each ballot is counted once and only if cast, and no candidate has more votes than ballots counted', tally(), tallyLaws(tally()), [
      {name: 'recounts a ballot', why: 'the count forgets whether the ballot was already counted', rule: tallyRecount, laws: tallyLaws(tallyRecount)},
      {name: 'counts an uncast ballot', why: 'the count forgets whether the ballot was cast', rule: tallyUncast, laws: tallyLaws(tallyUncast)},
    ]),
    decisionCase('committee votes', 'passes need quorum and the kind\'s majority', committeeDecisions, committeeBroken),
    machineCase('timesheet approval', 'a sheet is approved only after it was submitted, and paid only after approval', timesheets(), sheetLaws(timesheets()), [
      {name: 'approves drafts', why: 'approval checks the sheet isn\'t approved yet, not that it was submitted', rule: sheetsDraft, laws: sheetLaws(sheetsDraft)},
      {name: 'pays unapproved', why: 'payment checks the sheet isn\'t paid yet, not that it was approved', rule: sheetsUnapproved, laws: sheetLaws(sheetsUnapproved)},
    ]),
    loopCase('grading queue with appeals', 'every queue is graded to the end despite appeals, and nothing is lost', queue(), queueLaws(queue()), [
      {name: 'appeals unbudgeted', why: 'appeals are not counted against the budget, so they can return work forever', loop: queueUnbudgeted, laws: queueLaws(queueUnbudgeted)},
      {name: 'ranks the queue alone', why: 'an appeal grows the queue, so the queue alone is no rank; the appeal budget must come first', loop: queueAlone, laws: queueLaws(queueAlone)},
    ]),
  ],
}
