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

### Per-opcode `Xstep` wrappers (STEPPING) — ~20 opcodes
`push1`, `push0`, `push4`, `callvalue`, `dup1`, `iszero`, `mstore` (two-stage), `pop`,
`calldatasize`, `calldataload`, `jumpdest`, the binops `eq`/`lt`/`shr`/`sub`/`add`,
`jump`/`jumpi_t` (taken — take `(D_J code 0).contains target = true`), `jumpi_nt` (not-taken
⇒ no `D_J`), `revert` (halt) — each with a named successor `def` (`stPush1`, …).  Plus
`isZero_eq_zero_of_ne`, `isZero_zero`, `lt_four_ne_zero_of_lt`/`lt_four_eq_zero_of_ge`,
`ofNat_lt_ofNat`, `byteArray_size_eq_of_beq`, and a `LawfulBEq UInt256` instance.

> To verify a *different* contract: feed these the contract's `decode` facts (by `decide`)
> and chain `stepContinue`/`stepOOG`/`stepHalt*` as in `truthX_callvalue_ne`/`truthX_cvz_short`.
> Taken jumps discharge `(D_J code 0).contains target` from the contract's `D_J` fact
> (`Array.contains_eq_true_of_mem (by simp)`).  Add an `<op>_xstep` only for new opcodes.

## Truth-specific (MAIN)
- `truthBodyReverts` — `callvalue ≠ 0 ⇒` the Act body `require`-reverts.
- `truthDispatch_unique` — a successful dispatch yields `truthTransition` (single transition).
- `truthDispatch_eq` — dispatch reduces (via `truthSelectorBytes`) to a 4-byte prefix compare.
- `truthDispatch_none_short` — `calldata < 4 bytes ⇒` dispatch fails.
- `truthX_callvalue_ne` / `truthXi_callvalue_ne` — proved 11-instruction `callvalue ≠ 0`
  trace: `Ξ = OutOfGass ∨ Ξ = revert`.  **No axioms beyond the evmlean base.**
- `truthContains14`/`truthContains38`, `truthX_cvz_short` — proved 19-instruction
  `callvalue = 0 ∧ calldatasize < 4` trace: **two taken jumps** (`0x0a→0x0e`, `0x16→0x26`,
  via `truthValidJumps`) then `REVERT`; `Ξ = OutOfGass ∨ Ξ = revert`.
- `truthReEquiv_callvalueZero` — `by_cases` on `calldatasize < 4`: the short branch is proved
  (`outOfGas`/`noDispatch`); the `≥ 4` branch is the remaining `sorry`.
- `truthCorrect` — thin: `by_cases` on `callvalue`, then on `dispatchMsg`/`decodeCalldata`,
  delegating to the library.

## Trusted axioms (see MISSPEC.md) — only for the pending `callvalue == 0` path
- `truthSelectorBytes` — `keccak("truth()")[0:4] = 0x9e9f51d2` (`ffi.keccak256` is opaque).
- `truthValidJumps`   — the `JUMPDEST` set of `truthBytecode` (`D_J_aux` is `partial`).
These are admitted per the project owner's instruction; the real fix (making the base
definitions computable) is in MISSPEC.md.  **`truthCorrect` does not yet depend on them** —
they will be consumed only when the `callvalue == 0` trace is filled in.

## Open gaps
- **`truthReEquiv_callvalueZero`, `calldatasize ≥ 4` branch (one `sorry`)** — the rest of the
  dispatcher (now with the JUMPI at `0x16` *not* taken) runs the selector compare
  `PUSH0 CALLDATALOAD PUSH 0xe0 SHR DUP1 PUSH4 0x9e9f51d2 EQ … JUMPI` and then:
  - **wrong selector** ⇒ revert at `0x26` (Act `noDispatch`); and
  - **matching selector** ⇒ jump into `truth()`, which returns `true` (Act `execution` +
    `returnEquiv`).
  What remains:
  1. the **selector correspondence** — relate the EVM value
     `(uInt256OfByteArray (calldata.readBytes 0 32)) >> 224 == 0x9e9f51d2` to the Act condition
     `calldata.extract 0 4 == ⟨#[0x9e,0x9f,0x51,0xd2]⟩` (pure `ByteArray`/`UInt256` arithmetic —
     **provable**, not opaque, but tedious);
  2. the **success trace** (~30 instructions through solc's ABI-return helpers, incl.
     `MLOAD`/`MSTORE` memory tracking) ending in `RETURN`, plus `RETURN output =
     encodeReturnValue? (.elem .bool) (.bool true)` and the Act `return true` execution.
  New wrappers still needed: `swap1/2/3`, `dup2/3/4/5`, `mload`, `return`, `eq` (have it).
  The dispatcher prefix (through both JUMPIs) and all simpler opcodes are already proved; the
  proved `truthX_cvz_short` is the template.

## Axiom audit
`#print axioms truthXi_callvalue_ne` ⇒ `[ByteArray_zeroes_size, propext, Classical.choice,
Quot.sound]` — i.e. only the standard three plus one **pre-existing evmlean base axiom**
(`ByteArray_zeroes_size`, from the `@[extern]` zero-memory primitive); nothing introduced here.
`#print axioms truthCorrect` additionally lists `sorryAx` (the `callvalue == 0` gap).
