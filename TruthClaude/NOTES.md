# NOTES — reusable lemma index & open gaps

`lake build TruthClaude` succeeds. `truthCorrect` is stated exactly as given and is proved
**except** for the `callvalue == 0` branch (one isolated `sorry`, see *Open gaps*).
The `callvalue ≠ 0` behaviour and the whole out-of-gas regime are fully proved.

## Files
- `Theory.lean`   — contract-agnostic core: `Ξ`/`X` glue, the stepping drivers, gas/UInt256
  arithmetic, fuel monotonicity, and `runtimeEquivalenceFor` coverage builders.
- `Stepping.lean` — contract-agnostic per-opcode `Xstep` wrappers (the `st<Op>` successor
  `def`s + `<op>_xstep` lemmas).
- `TruthCorrect.lean` — the Truth-specific data, two trusted axioms, the Act-side facts, the
  concrete `callvalue ≠ 0` trace, and the assembled `truthCorrect`.
- `MISSPEC.md` — the two trusted-base computability blockers and how they are handled.

## Reusable library (THEORY) — all contract-agnostic

### `Ξ` ⟶ `X` glue (reduce a goal about code execution to the fuelled iterator)
- `initState` — the fresh EVM state `Ξ` builds (shared, definitionally, with `actExec`).
- `Xi_error_of_X` / `Xi_revert_of_X` / `Xi_success_of_X` — lift an `X` outcome to `Ξ`.

### Stepping drivers (run a trace for a *universally quantified* gas `g`)
- `X_peel` — peel one `Xstep` in `if P then OutOfGass else .ok (s',none)` shape off `X (f+1)`.
- `X_continue` — non-branching specialisation of `X_peel`.
- `X_mono` — **more fuel never changes a terminating run** (swap `g.toNat+1` for a concrete bound).
- `stepContinue` — advance a trace one step (step-count `k`, cumulative cost `C`) when gas suffices.
- `stepOOG` — conclude `X = OutOfGass` when the next instruction's gas is short.
- `stepHaltSuccess` / `stepHaltRevert` — conclude `X = .ok (.success/.revert …)` at a halt.

### Gas / `UInt256` arithmetic
- `toNat_sub_ofNat` — `(g - ofNat c).toNat = g.toNat - c` (no wrap) — the core gas-tracking lemma.
- `collapse_two_stage` — fuse a memory opcode's two gas guards into one `gas < c1 + c2`.
- `uint256_toNat_eq_zero` — `a.toNat = 0 → a = ⟨0⟩`.

### Coverage builders (assemble a `runtimeEquivalenceFor` case)
- `reEquiv_outOfGas` / `reEquiv_noDispatch` / `reEquiv_decodingFailed` / `reEquiv_execution`
  — one per constructor; `reEquiv_execution` bundles dispatch + decode + `ExecContractBody`.

### Per-opcode `Xstep` wrappers (STEPPING)
`push1_xstep`, `push0_xstep`, `callvalue_xstep`, `dup1_xstep`, `iszero_xstep`,
`mstore_xstep` (two-stage), `jumpi_nt_xstep` (not-taken ⇒ no `D_J`), `revert_xstep` (halt),
each with a named successor `def` (`stPush1`, …, `stRevert`).  Plus `isZero_eq_zero_of_ne`
and a `LawfulBEq UInt256` instance.

> To verify a *different* contract: feed these the contract's `decode` facts (by `decide`)
> and chain `stepContinue`/`stepOOG`/`stepHalt*` as in `truthX_callvalue_ne`.  Add an
> `<op>_xstep` only for opcodes not yet covered.

## Truth-specific (MAIN)
- `truthBodyReverts` — `callvalue ≠ 0 ⇒` the Act body `require`-reverts.
- `truthDispatch_unique` — a successful dispatch yields `truthTransition` (single transition).
- `truthX_callvalue_ne` / `truthXi_callvalue_ne` — the proved 11-instruction `callvalue ≠ 0`
  trace: `Ξ = OutOfGass ∨ Ξ = revert`.  **No axioms beyond the evmlean base.**
- `truthCorrect` — thin: `by_cases` on `callvalue`, then on `dispatchMsg`/`decodeCalldata`,
  delegating to the library.

## Trusted axioms (see MISSPEC.md) — only for the pending `callvalue == 0` path
- `truthSelectorBytes` — `keccak("truth()")[0:4] = 0x9e9f51d2` (`ffi.keccak256` is opaque).
- `truthValidJumps`   — the `JUMPDEST` set of `truthBytecode` (`D_J_aux` is `partial`).
These are admitted per the project owner's instruction; the real fix (making the base
definitions computable) is in MISSPEC.md.  **`truthCorrect` does not yet depend on them** —
they will be consumed only when the `callvalue == 0` trace is filled in.

## Open gaps
- **`truthReEquiv_callvalueZero` (`sorry`)** — the `callvalue == 0` dispatch path.  This is the
  large remaining piece: the dispatcher's *taken* jumps (discharge `(D_J truthBytecode 0).contains _`
  via `truthValidJumps`; a `jumpi_taken_xstep` wrapper is still needed), the selector match
  (relate the EVM's `0x9e9f51d2` to Act dispatch via `truthSelectorBytes`), the ~30-step
  `truth()` body that returns `true`, and the `returnEquiv` for the ABI encoding of `bool true`
  (`encodeReturnValue? (.elem .bool) (.bool true)`).  All infrastructure to do this exists in
  THEORY/STEPPING; it is a matter of writing the (long) concrete trace + a handful of new
  wrappers (`jumpi_taken`, `jumpdest`, `pop`, `calldatasize`, `lt`, `calldataload`, `shr`, `eq`,
  `swap1/2`, `sub`, `mload`, `return`) and the Act-side success execution.

## Axiom audit
`#print axioms truthXi_callvalue_ne` ⇒ `[ByteArray_zeroes_size, propext, Classical.choice,
Quot.sound]` — i.e. only the standard three plus one **pre-existing evmlean base axiom**
(`ByteArray_zeroes_size`, from the `@[extern]` zero-memory primitive); nothing introduced here.
`#print axioms truthCorrect` additionally lists `sorryAx` (the `callvalue == 0` gap).
