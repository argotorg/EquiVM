# `Reach` — a reusable symbolic straight-line execution abstraction

## Goal

Factor out the **straight-line stepping boilerplate** that dominates the EVM-equivalence
proofs. Across the Pow routines there are ~150–200 single-opcode steps, each ~8–10 nearly
identical lines (`set sN := st<op> …`, `have hcN/hpN/hgN/hkN/hXN …`, the `by_cases` OOG split),
duplicated between Truth and Pow. Target: a common library (`TruthClaude/Reach.lean`, generic over
the contract `code`) so a straight-line block becomes a short fold over per-opcode combinators, with
the OOG case and the per-step bookkeeping handled inside the combinators.

**Scope:** straight-line segments only. Control flow stays ordinary Lean and composes by
transitivity — branches (`JUMPI`) by `by_cases` / value-lemmas, loops by induction (`powLoopCore`
is the template), internal solc subroutines by sub-lemmas glued with the reach equation.
**`CALL`/`CREATE` are explicitly out of scope** (a single `Xstep` there hides a recursive
sub-execution + depth reset).

## Verified semantics (checked against the trusted base — do not re-trust, re-read if unsure)

- `X (fuel : ℕ) vj s` (`.lake/packages/evmlean/Ethereum/Semantics.lean`, `X@~797`,
  `Xstep@~749`, `Ξ@~824`): a **fuel**-bounded iterator; `fuel = 0 → .error .OutOfFuel`. `Ξ` runs
  `X (g.toNat + 1) (D_J I.code ⟨0⟩)`. **Fuel ≠ gas.** Gas is `s.machineState.gasAvailable`,
  subtracted per opcode by a variable cost. `.OutOfFuel` is a model artifact and must **never** be
  produced — only `.OutOfGass` (note spelling).
- `X` returns **only the final outcome** `Except _ (ExecutionResult State)` (`.success finalState o`
  / `.revert g' o`), *not* an intermediate state. The state is threaded internally by `Xstep`. The
  cursor state `s` in proofs is tracked **by us** (via the `st_op` functions), not handed back by `X`.
- `Xstep vj s : Except _ (State × Option (Bool × ByteArray))`: `none` = continue, `some (false,o)` =
  revert (halt), `some (true,o)` = success (halt). On continue, `X` recurses on
  `{s' with executionEnv.depth := s.depth}`; for the in-scope opcodes the depth reset is a no-op and
  is already absorbed by `stepContinue`/the `_xstep` lemmas — **the abstraction never touches depth.**
- Proven base layer to build on:
  - `TruthClaude/Theory.lean`: `stepContinue` ⟹ `X (g+1-k) vj s = X (g+1-(k+1)) vj s'`;
    `stepOOG` ⟹ `X (g+1-k) vj s = .error .OutOfGass`; `stepHaltSuccess`/`stepHaltRevert` ⟹ the
    `.ok (.success/.revert …)` results; `X_mono` (fuel monotonicity) — reserved for the **single**
    fuel→result conversion at the top, *not* used per step.
  - `TruthClaude/Stepping.lean`: the `st_op` state-update functions (`stPush0`, `stSwap`, `stPop`,
    `stJump`, `stBinop`, `stMul`, `stMLoad`, `stMStore`, `stReturn`, …) and the matching `<op>_xstep`
    lemmas, each producing `Xstep vj s = if gas < cost then .error .OutOfGass else .ok (st_op …, ctrl)`.
- Segment-conclusion shape (from `powRoutine_9c` in `PowSegments.lean`):
  `… = .error .OutOfGass ∨ ∃ k' C' s', X(g+1) s0 = X(g+1-k') s' ∧ code ∧ pc ∧ stack ∧ gas = g-C'
  ∧ k'≤C' ∧ C'≤g ∧ <opt. memory/activeWords/accounts preservation>`. The equivalence statement
  (`Act/Equiv.lean`) supplies `I.calldata.size < UInt256.size`.

## Settled design decisions

1. **Counters, not gas-pinned.** Track `k` (steps) and `C` (gas burned) explicitly with
   `k ≤ C ≤ g.toNat`. `stepContinue`/`stepOOG` are written in this `X(g+1-k) = X(g+1-(k+1))` style
   and hold unconditionally on termination (no `≠ .OutOfFuel` side-goal). The gas-pinned invariant
   (`hX : X(g+1) s0 = X(s.gas+1) s`) would need `X_mono` at **every** step to absorb the per-op
   `C−k` slack — rejected. `X_mono` is used once, at the final fuel→result boundary. (Loops also need
   counters threaded through the induction, cf. `powLoopCore`.)

2. **Carry, at minimum, everything the conclusion asserts** — see Risk A. The cursor (`pc`, `stk`),
   the gas counter (`C`), and any preservation/value the segment concludes (`memory`,
   `activeWords`, accounts) must be **pinned data/equations carried by every combinator**, because
   modularizing across the OOG boundary makes the final state opaque to `conclude`. Pure-stack ops
   carry the invariants unchanged (~1 trivial line/field); `MSTORE`/`RETURN` update `mem`/`aw`.
   Carrying `mem` as a value initialized at `start` to the input's memory makes the relative clause
   `s'.memory = s.memory` fall out for free at `conclude`.

3. **`conclude` shape is the make-or-break — spike it FIRST** (Risk A). Two candidate shapes:
   - **(preferred to try first) Prop-predicate `Reach`**: `RD pc stk mem aw … : Prop :=
     OOG ∨ ∃ k C s, X(g+1) s0 = X(g+1-k) s ∧ s.code=code ∧ s.pc=pc ∧ s.stk=stk ∧ s.gas=g-C ∧
     s.mem=mem ∧ … ∧ k≤C ∧ C≤g`. Combinators are forward **implications**
     `RD pc (a::b::t) … → <decode/cost/…> → RD (pc+1) (b::a::t) …`; chaining is modus ponens; OOG
     threads inside the Prop; `conclude` is trivial because `RD ret finalstk …` *is* the goal. This
     sidesteps the Type/`cases` problem and matches how `powX_success` already composes.
   - **(fallback) indexed `Reach`/`Step`**: a `Type`-level `Reach code g s0 (pc) (stk) (mem) …`
     indexed on the cursor, with a bespoke `Step` inductive (`oog : OOG → Step | reach : Reach →
     Step`) since `OOG : Prop` can't sit in an `Or` with a state-carrying `Reach`. Indices pin
     `pc = ret` etc. through elimination.

## Known risks / corrections to earlier framing

- **Risk A (primary): a plain (non-indexed) `Reach` + `cases`-based `conclude` does NOT close a
  fixed-target conclusion.** `cases st` abstracts the fields, so `r.pc` is opaque and you can't prove
  `s'.pc = ret` for the fixed `ret`; and the OOG `dite`s block `st` from reducing to a concrete
  `.reach (mk …)`. **Mitigation:** Prop-predicate shape, or index the type on the cursor. *Validate
  on a 2-step fold before building any combinator set.*
- **Correction: preservation CANNOT be "derived on demand at `conclude` via `simp only [st*]`."**
  At `conclude` the final state is opaque (post-elimination / behind OOG `dite`s); there is no
  `hs9…hs1` tower in scope (unlike hand-written 9c, where the `by_cases` are inline). Preservation
  must be carried (Decision 2).
- The pretty `|>.swap1` dot-sugar and an `evm_run`-style macro (decode each opcode, auto-fill
  `decode`/overflow/`hnpc`/`hstk`) are a **follow-up**, only after the algebra concludes on 9c.
  First-cut retrofit of 9c is ~30–40 lines (explicit per-step proofs), not ~12 — the ~12 figure is
  post-macro. Still a large win vs ~100.
- `binop` yields the **symbolic** result (`UInt256.lt a b`); resolving it to `⟨0⟩`/`⟨1⟩` for a branch
  stays a manual value-lemma step (e.g. `slt32_zero`/`ult_zero`) at the call site. The library
  shortens stack/gas/pc mechanics, not branch reasoning.
- `MUL` goes through `stMul` (cost 5), not `stBinop` — give it a thin wrapper.
- Build combinator output with a fresh `Reach.mk`, **not** `{ r with … }` (proof fields depend on
  data fields).
- `start` must accept a **nonzero incoming `k`/`C`** (9c is called mid-run by `a5`).
- `decode code ⟨literal⟩` by `decide` is **already known-feasible** (hand-written segments do it
  under `set_option maxRecDepth 10000`); the combinators take the decode proof as a *parameter* so it
  fires at concrete call sites, keeping the library generic over `code`. A `pc : ℕ` field is a
  fallback if `decide` on `UInt256` pc arithmetic is slow.

## Spike plan (do ONLY this first, keep `lake build` green at each step, no `sorry`)

1. **`conclude` spike.** New `TruthClaude/Reach.lean` (`namespace TruthClaude.Reach`, import
   `TruthClaude.Stepping` + `TruthClaude.Theory`, `set_option maxRecDepth 10000`). Build `Reach`
   (Prop-predicate shape first), `start`, two combinators (`jumpdest`, `swap1`), and `conclude`;
   prove a **2-step fold closes a fixed-pc, fixed-stack conclusion**. If Prop-predicate doesn't
   conclude cleanly, switch to indexed `Reach`/`Step`.
2. **Preservation-as-field** on the same spike: carry `mem` through both combinators; confirm
   `conclude` states `s'.memory = startMem`.
3. **Retrofit `powRoutine_9c`** (in `PowSegments.lean`) via the combinators as the acceptance test.
   Report the line-count delta and whether `conclude` is clean. **Stop and report before building
   the rest of the combinators.**

Only after the spike concludes on 9c: fill the combinator set (`push0/1/2/4`, `dup1–6`,
`swap1–3`, `pop`, `iszero`, `callvalue`, `calldatasize`, `calldataload`, parametric `binop` for
add/sub/mul/lt/slt/shr/eq, internal `jump`, and halting `ret`/`stop`/`revert`), then retrofit the
remaining segments, then the dot-sugar + `evm_run` macro (separate task).

## Verification

- `lake build` green after each spike step; never introduce `.OutOfFuel` or `sorry`.
- Acceptance: `powRoutine_9c` builds via the combinators and is materially shorter, and its caller
  `powRoutine_a5` still typechecks unchanged (the retrofit must reproduce 9c's exact conclusion,
  including the three preservation clauses).
- `#print axioms powCorrect` / `truthCorrect` unchanged: standard Lean axioms + the two opaque
  trusted axioms each (`powSelectorBytes`/`powValidJumps`, `truthSelectorBytes`/`truthValidJumps`).
- Spot-check `maxHeartbeats` on a long segment to confirm no elaboration blow-up.
