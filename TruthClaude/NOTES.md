# NOTES — reusable lemma index

`lake build TruthClaude` succeeds. `truthCorrect` is stated exactly as given and is **fully
proved — no `sorry`**.  Every call is covered: `callvalue ≠ 0`, low-gas (out-of-gas),
`callvalue == 0` with short calldata, with a non-matching selector, and the `truth()` **success
path** (the 93-instruction EVM trace that dispatches `truth()`, stores `1` in memory, and
ABI-encodes / `RETURN`s `true`).

`#print axioms truthCorrect` ⇒ `[propext, Classical.choice, Quot.sound, ByteArray_zeroes_size,
byteArray_zeroes_toList, truthSelectorBytes, truthValidJumps]` — Lean's three, one pre-existing
evmlean base axiom (`ByteArray_zeroes_size`), the one `ffi.zeroes`-content extern spec
(`byteArray_zeroes_toList`), and the **two** genuinely-opaque trusted axioms (`MISSPEC.md`).
**No `sorryAx`.**  (The selector-decode fact is no longer an axiom — see `truthEvmSelector`.)

## Files
- `Theory.lean`   — contract-agnostic core: `Ξ`/`X` glue, the stepping drivers, gas/UInt256
  arithmetic, fuel monotonicity, and `runtimeEquivalenceFor` coverage builders.
- `Stepping.lean` — contract-agnostic per-opcode `Xstep` wrappers (the `st<Op>` successor
  `def`s + `<op>_xstep` lemmas).
- `Memory.lean`   — contract-agnostic byte/memory/ABI lemmas: the big-endian byte round-trip,
  `fromByteArrayBigEndian ∘ toByteArray = toNat` (MLOAD), the `MSTORE`-write characterization
  `toByteArray_write_eq`, `readWithPadding`-as-extract, and `toByteArray = toBytesBE`.  Built on
  the single extern-spec axiom `byteArray_zeroes_toList`.
- `TruthCorrect.lean` — the Truth-specific data, two trusted axioms (+ the proved selector
  decode `truthEvmSelector`), the Act-side facts, the
  concrete memory states (`truthMem1`/`truthMem2`), the per-scenario `Ξ`/`X` traces (incl. the
  generated 93-step success trace `truthX_cvz_success`), and the assembled `truthCorrect`.
- `gen_trace.py` — the generator that emitted the success trace's step-by-step tactic block
  (documents the trace's provenance; not part of the Lean build).
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

### Byte / memory / ABI (MEMORY) — all contract-agnostic
- `fromBytes'_toBytes'`, `fromBytesBigEndian_toBytesBigEndian` — little-/big-endian round-trips.
- `fromBytes'_append`, `fromBytesBigEndian_append_div` — byte concat / big-endian division.
- `byteArray_toList_eq`, `fromByteArrayBigEndian_toByteArray` — the **MLOAD** decode round-trip.
- `readBytes32_toList`/`_len`, `selector_toNat` — `CALLDATALOAD`+`SHR(·,224)` = big-endian of the
  first 4 calldata bytes (the proof backing the `truthEvmSelector` selector decode).
- `toByteArray_write_eq` — **MSTORE** write: `v` at `off ≥ mem.size` is `mem ++ zeroes ++ v`.
- `readWithoutPadding_eq_extract` / `readWithPadding_eq_extract` — **MLOAD/RETURN** read = slice.
- `extract_append_right`/`_left`/`_right'`, `empty_append`, `zeroes_zero`, `zeroes_ofNat_size`,
  `lt_usize`, `toByteArray_size` — supporting `ByteArray`/`USize` lemmas.
- `toByteArray_eq_toBytesBE` — the opaque-memory ↔ pure-ABI bridge (`ffi.zeroes` pad cancels).

### Per-opcode `Xstep` wrappers (STEPPING) — ~28 opcodes
`push0`/`push1`/`push4`, `pop`, `callvalue`, `calldatasize`, `calldataload`, `dup1`–`dup5`,
`swap1`–`swap3`, `iszero`, the binops `eq`/`lt`/`shr`/`sub`/`add`, `mstore`/`mload` (two-stage),
`jumpdest`, `jump`/`jumpi_t` (taken — take `(D_J code 0).contains target = true`), `jumpi_nt`
(not-taken), `revert`/`return` (halt) — each with a named successor `def` (`stPush1`, …).  Plus
`isZero_zero`, `lt_four_eq_zero_of_ge`, `byteArray_size_eq_of_beq`, a `LawfulBEq UInt256` instance.

> To verify a *different* contract: feed these the contract's `decode` facts (by `decide`) and
> chain `stepContinue`/`stepOOG`/`stepHalt*`.  Taken jumps discharge `(D_J code 0).contains
> target` from the contract's `D_J` fact (`Array.contains_eq_true_of_mem (by simp)`).  Memory
> reads/writes use the `Memory.lean` lemmas at the contract's offsets.  Add an `<op>_xstep` only
> for new opcodes.

## Truth-specific (MAIN)
- `truthBodyReverts` / `truthBodyReturns` — the Act body for `callvalue ≠ 0` (`require`-revert)
  resp. `callvalue == 0` (`return true`).
- `truthDispatch_unique` / `truthDispatch_eq` / `truthDispatch_none_short`/`_nomatch`,
  `truthDecode_empty` — the Act dispatch/decode facts (`truthSelectorBytes` drives the selector).
- `truthReturnEncoding` — `encodeReturnValue? (.elem .bool) (.bool true) = some (toByteArray ⟨1⟩)`.
- `truthMem1`/`truthMem2` + `truthMem*_size`/`_read64`/`_read128` — the concrete memory states of
  the `truth()` epilogue (free pointer `0x80` at `0x40`, bool `1` at `0x80`) and their reads.
- `truthX_callvalue_ne`/`truthXi_callvalue_ne` — `callvalue ≠ 0`: `Ξ = OOG ∨ revert`.
- `truthX_cvz_prefix` — the shared 14-instruction dispatcher prefix (callvalue-zero check).
- `truthX_cvz_short`, `truthX_cvz_revertB` — the short-calldata and wrong-selector revert traces.
- `truthX_cvz_success` — **the 93-instruction success trace** (generated): `Ξ`/`X` either OOGs or
  succeeds returning `toByteArray ⟨1⟩` with `σ`/`createdAccounts`/substate unchanged.
- `truthXi_cvz_success` — lifts it to `Ξ`.
- `truthReEquiv_callvalueZero` — `by_cases` on `calldatasize < 4`, then on the selector match:
  short → `noDispatch`; wrong selector → `noDispatch`; matching → `execution` (dispatch + decode
  + `truthBodyReturns` + `execResultsEquiv.success` + `returnEquiv.returned`).
- `truthCorrect` — thin: `by_cases` on `callvalue`, delegating to the library.

## Trusted axioms (see MISSPEC.md) — the **two** genuinely-opaque ones
- `truthSelectorBytes` — `keccak("truth()")[0:4] = 0x9e9f51d2` (`ffi.keccak256` is opaque).
- `truthValidJumps`   — the `JUMPDEST` set of `truthBytecode` (`D_J_aux` is `partial`).
Admitted per the project owner's instruction; the real fix (making the base definitions
computable) is in `MISSPEC.md`, after which both become `decide`-provable and deletable.

Plus one extern-spec axiom (not Truth-specific):
- `byteArray_zeroes_toList` (in `Memory.lean`) — the `ffi.zeroes` (`@[extern "memset_zero"]`)
  content is `0`; the minimal companion to evmlean's pre-existing `ByteArray_zeroes_size`.

> **`truthEvmSelector` is no longer an axiom — it is proved** (`TruthCorrect.lean`, on the
> contract-agnostic `selector_toNat`).  It was the one *non-opaque* admitted fact; per the
> "don't admit what isn't opaque" rule it became a theorem.

## Axiom audit
`#print axioms truthCorrect` ⇒ `[propext, Classical.choice, Quot.sound, ByteArray_zeroes_size,
byteArray_zeroes_toList, truthSelectorBytes, truthValidJumps]`.  No `sorryAx`; no
`native_decide`/`ofReduceBool`.  The `callvalue ≠ 0` sub-result `truthXi_callvalue_ne` needs
**none** of the Truth-specific axioms — only `[ByteArray_zeroes_size, propext, Classical.choice,
Quot.sound]`.
