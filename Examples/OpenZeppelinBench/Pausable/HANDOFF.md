# OZ Pausable (bench) — proof handoff

Read **`prompt.md`**, **`Reasoning/GUIDE.md`**, **`Examples/ERC20/PROOF_GUIDE.md`**, and the canonical
**`Examples/SimpleAuction/HANDOFF.md`** first — it holds the **full global rules, the 4-phase plan, the
per-function prompt template, and the Concurrency model**, all of which apply here verbatim. This is the
**simplest** OZ bench: a single `bool` slot, no mappings/loops/calls. Optimizer-ON exemplar: `Ballot`;
the closest body shape is `Truth`/`Pow` (trivial).

**Goal**
```
runtimeEquivalence!?! OpenZeppelinBench.Pausable.config …pausableBenchBytecode …contract   -- Correct.lean
```
no `sorry`/`admit`; axioms only `propext`/`Classical.choice`/`Quot.sound`/`ofReduceBool`. Optimizer-ON.

## Global rules (full text in `Examples/SimpleAuction/HANDOFF.md`)
1. Never duplicate — search `Reasoning/*` + `Common.lean`, **apply**; reuse → flag as refactor.
2. Respect/extend the library — missing general lemma → `Common.lean` (`-- LIBRARY CANDIDATE …`) or
   additively into `Reasoning/` if genuinely library-general.
3. One file per ABI function, parallel agents; each writes **only its own `<Fn>.lean`**.
4. Sandbox: only under `Examples/OpenZeppelinBench/Pausable/`; never edit `Spec.lean`/`Bytecode.lean`/
   another file (shared helpers → report for Phase 1.5).
5. Spec/Bytecode trusted — spec wrong ⇒ **stop and report to the user**. No new axiom; no `sorry`/`admit`.

## Dispatcher — **linear**, lands at pc 18; arms ascending by selector

| selector | function | body PC | notes |
|---|---|---|---|
| `0x3f4ba83a` | `unpause()`               | **89**  | `whenPaused`: `require(_paused)` (else `ExpectedPause`); `_paused = false`. |
| `0x5c975abb` | `paused()`                | **99**  | getter `_paused` (bool). |
| `0x8456cb59` | `pause()`                 | **125** | `whenNotPaused`: `require(!_paused)` (else `EnforcedPause`); `_paused = true`. |
| `0x9bb8bcec` | `guardedWhenNotPaused()`  | **133** | `whenNotPaused` modifier then empty body (a no-op probe of the modifier). |
| `0xddf70309` | `guardedWhenPaused()`     | **141** | `whenPaused` modifier then empty body. |

The two modifiers `whenNotPaused`/`whenPaused` (`require(!_paused)` / `require(_paused)`) are shared by
≥2 functions — prove each once in `Common.lean`. Phase-0 pins the `firstArmPc` and the `D_J` / selector
facts in a new `Trusted.lean`.

## Storage
Hand-written in `Spec.lean`: `_paused` @ slot 0, offset 0, **1 byte** (bool, packed). `Storage.lean`
needs the single packed-bool slot load/store facts (offset 0 / size 1) — no mappings.

## Per-function files (parallel): `Unpause`, `Paused`, `Pause`, `GuardedWhenNotPaused`,
`GuardedWhenPaused`. All five are tiny: each is one modifier-`require` (revert branch) plus a bool
store or return. Split success/revert early; the two `guarded*` probes have *only* the modifier +
return.

## Phases & per-function template: **see `Examples/SimpleAuction/HANDOFF.md`** (one linear no-match
revert tail). Finish:
```
lake build Examples.OpenZeppelinBench.Pausable.Correct
rg -n '\b(sorry|admit)\b' Examples/OpenZeppelinBench/Pausable
printf '%s\n' 'import Examples.OpenZeppelinBench.Pausable.Correct' \
  '#print axioms OpenZeppelinBench.Pausable.…Correct' | lake env lean --stdin
```
then add the import to `Examples.lean`. **Recommended first target** — smallest end-to-end loop to
validate the OZ-bench dispatcher/storage plumbing before the bigger contracts.
