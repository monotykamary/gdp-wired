// node-oidc-provider v9.13.0 (panva/node-oidc-provider), the refresh_token grant: rotation, and reuse detection that
// revokes the whole grant (lib/actions/grants/refresh_token.js), with the grant check (lib/helpers/grant_source.js),
// the revocation by grant (lib/helpers/revoke.js) and the token expiry (lib/models/base_model.js). MIT, (c) Filip Skokan.
// https://github.com/panva/node-oidc-provider/tree/dc5832bc89a908710443dd4fb8dcc877ba2e82aa/lib
//
// Mapping:
// - The adapter is the store: refresh tokens by value (`Tok`: none, live, or consumed, with grantId, clientId and exp)
//   and grants by id (`Grant`). A token value or grant id is random; the n-th issued gets id n (`nextTok`, `nextGrant`),
//   so a new one never names an old one. A presented `token` is any number.
// - Time: epochTime() (base_model.js:84, :151) is `now: nat`, in seconds, sent in with each request.
// - `issue`: what creates a grant and its first refresh token (the authorization_code grant's issueTokens, outside this
//   file), with the TTLs its config gives (`ttl`, `grantTtl`).
// - The checks between finding the token and reuse detection that read what the rule doesn't hold (mTLS certificate,
//   DPoP proof and replay, requested scope within the token's, attestation binding, the account still there:
//   refresh_token.js:66-104; the session binding in RefreshToken.find, refresh_token.js:50) are one yes/no, `checksOk`;
//   each throws InvalidGrant when it fails, a request where every part keeps its value.
// - rotateRefreshToken (refresh_token.js:115-119) is config: `true`, or a function of the request, so its value is the
//   input `rotates`; the new token's TTL (ttl.RefreshToken) is the input `ttl`. revokeGrantPolicy (revoke.js:19) is
//   the param `revokeGrant` (the default, defaults.js:554-559, is true on this route).
import {bool, forall, nat, no, oneOf, record, rule, when, yes} from '../../../core/dsl.ts'
import {type RealItem, invariant, stepLaw} from '../lib.ts'

const src = {repo: 'panva/node-oidc-provider', commit: 'dc5832bc89a908710443dd4fb8dcc877ba2e82aa', licence: 'MIT', author: 'Filip Skokan (panva)', language: 'JavaScript'}

export const Token = record({st: oneOf('none', 'live', 'consumed'), grant: nat, client: nat, exp: nat})
export const GrantRow = record({live: bool, client: nat, exp: nat})
export const refreshGrant = () => rule('node-oidc-provider refresh_token grant')
  .params({revokeGrant: bool})
  .inputs({op: oneOf('issue', 'refresh'), token: nat, client: nat, now: nat, rotates: bool, ttl: nat, grantTtl: nat, checksOk: bool})
  // Ghosts: `served`, whether the last refresh answered with tokens; `Reused`, per grant, whether a consumed refresh
  // token of it was presented (the reuse the code detects at refresh_token.js:106-112).
  .state({nextTok: 0, nextGrant: 0, served: bool.from(false)})
  .maps({Tok: Token.from({st: 'none', grant: 0, client: 0, exp: 0}), Grant: GrantRow.from({live: false, client: 0, exp: 0}), Reused: bool.from(false)})
  .flags(({op, token, client, now, checksOk, Tok, Grant}) => {
    const t = Tok.at(token), g = Grant.at(t.grant)
    // refresh_token.js:50-62 found (with ignoreExpiration), the client's, not expired (base_model.js:151 `exp <= now`).
    const found = op.is('refresh').and(t.st.is('none').not(), t.client.eq(client), now.lt(t.exp))
    // grant_source.js:34-54 validateGrant: found, not expired, the client's.
    const grantOk = g.live.and(now.lt(g.exp), g.client.eq(client))
    const passes = found.and(grantOk, checksOk)
    return {
      // refresh_token.js:106-112 a consumed token: destroy it and revoke the grant, then InvalidGrant.
      reuse: passes.and(t.st.is('consumed')),
      serve: passes.and(t.st.is('live')),
    }
  })
  .flags(({serve, rotates}) => ({rotate: serve.and(rotates)}))
  .step(({op, token, client, now, ttl, grantTtl, revokeGrant, nextTok, nextGrant, Tok, Grant, Reused, reuse, serve, rotate}) => {
    const issues = op.is('issue'), g = Tok.at(token).grant
    return {
      nextTok: when(issues.or(rotate), nextTok.plus(1), nextTok),
      nextGrant: when(issues, nextGrant.plus(1), nextGrant),
      served: when(op.is('refresh'), serve, no),
      Tok: Tok.each(k => {
        const t = Tok.at(k)
        const fresh = issues.and(k.eq(nextTok)).or(rotate.and(k.eq(nextTok)))
        // refresh_token.js:121-145 rotation: consume the old token, save a new one for the same grant and client.
        const consumed = rotate.and(k.eq(token))
        // :108-109 destroy the token; revoke.js:21-31 revokeByGrantId: every token of the grant goes.
        const gone = reuse.and(k.eq(token).or(t.grant.eq(g)))
        return {
          st: when(fresh, 'live', when(consumed, 'consumed', when(gone, 'none', t.st))),
          grant: when(issues.and(k.eq(nextTok)), nextGrant, when(rotate.and(k.eq(nextTok)), g, t.grant)),
          client: when(fresh, client, t.client),
          exp: when(fresh, now.plus(ttl), t.exp),
        }
      }),
      // revoke.js:30 the grant itself is destroyed when revokeGrantPolicy says so.
      Grant: Grant.each(k => {
        const made = issues.and(k.eq(nextGrant))
        return {live: when(made, yes, when(reuse.and(revokeGrant, k.eq(g)), no, Grant.at(k).live)), client: when(made, client, Grant.at(k).client), exp: when(made, now.plus(grantTtl), Grant.at(k).exp)}
      }),
      Reused: Reused.each(k => Reused.at(k).or(reuse.and(k.eq(g)))),
    }
  })

const r = refreshGrant()
export const items: RealItem[] = [{
  id: 'auth/node-oidc-provider/refreshTokenRotation',
  domain: 'auth',
  source: {...src, path: 'lib/actions/grants/refresh_token.js', lines: '24-212', export: 'handler'},
  also: [{...src, path: 'lib/helpers/grant_source.js', lines: '34-54', export: 'validateGrant'}, {...src, path: 'lib/helpers/revoke.js', lines: '4-35', export: 'revoke'},
    {...src, path: 'lib/models/base_model.js', lines: '149-158', export: 'isExpired'}, {...src, path: 'lib/models/refresh_token.js', lines: '44-56', export: 'RefreshToken'}],
  summary: 'A refresh token is exchanged for new tokens if it is found, the client\'s, unexpired and its grant valid; with rotation the old token is consumed and a new one issued; presenting a consumed token revokes every token of its grant.',
  expressible: 'partial',
  gaps: [
    {gap: 'external', blocks: 'part', detail: 'the sender-constraint, scope, attestation, account and session-binding checks (refresh_token.js:50, :66-104) read state the rule does not hold (certificates, DPoP proofs, the account store); they are one yes/no the request carries'},
    {gap: 'async', blocks: 'part', detail: 'the handler awaits the adapter between find (:51) and consume (:120): two concurrent refreshes with one token can both pass the consumed check and both rotate; the rule takes requests one at a time'},
  ],
  laws: [
    stepLaw(r, r.stepsLaw('a rotated token\'s old value is rejected', 2, (_, after, [first, second]) => second!.token.eq(first!.token).implies(after.served.not()), ({rotate}, j) => (j === 0 ? rotate : undefined)),
      'step', 'docs', 'OAuth 2.0 Security BCP 4.14.2 (refresh token rotation), which rotateRefreshToken implements: "the old refresh token is invalidated"'),
    invariant(r, r.law('once reuse is detected, no token of that grant is live', ({Tok, Reused}) => forall(k => Tok.at(k).st.is('live').implies(Reused.at(Tok.at(k).grant).not()))),
      'safety', 'docs', 'refresh_token.js:106-112 reuse of a consumed token destroys it and revokes the grant (revoke.js: every token of the grant)'),
    stepLaw(r, r.stepLaw('a refresh token past its expiry is never served', ({now, token, Tok}) => now.lt(Tok.at(token).exp), ({serve}) => serve),
      'safety', 'docs', 'refresh_token.js:60-62 "refresh token is expired"'),
    stepLaw(r, r.stepLaw('only the client the token was issued to can use it', ({client, token, Tok}) => client.eq(Tok.at(token).client), ({serve}) => serve),
      'access', 'docs', 'refresh_token.js:56-58 "client mismatch"'),
    stepLaw(r, r.stepLaw('presenting a consumed token revokes its whole grant', ({token, Tok}, after) => forall(k => after.Tok.at(k).grant.eq(Tok.at(token).grant).implies(after.Tok.at(k).st.is('none'))), ({reuse}) => reuse),
      'step', 'docs', 'refresh_token.js:106-112 `revoke(ctx, refreshToken.grantId)`'),
    invariant(r, r.law('at most one live refresh token per grant', ({Tok}) => forall((i, j) => Tok.at(i).st.is('live').and(Tok.at(j).st.is('live'), Tok.at(i).grant.eq(Tok.at(j).grant)).implies(i.eq(j)))),
      'safety', 'inferred', 'rotation (refresh_token.js:115-146) consumes the old token as it saves the new one; each issue makes a new grant'),
  ],
}]
