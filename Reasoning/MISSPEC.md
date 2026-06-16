# Misspecification / proof-blocker report

This file reports **trusted-base defects** that make `truthCorrect` **unprovable as
stated** without either modifying the trusted base or introducing extra axioms.

Neither is a *semantic* error: the EVM model computes the right answers (verified by
`#eval`). They are **computability / proof-engineering** defects — definitions that are
logically *opaque* to the kernel, so no nontrivial fact about their *value* can be
proven without `native_decide` (which adds the `Lean.ofReduceBool`-style
`…native_decide.ax` axiom — forbidden by this task's "no new axiom" rule).

Both block the *main* behaviour of `Truth` (a `callvalue == 0` call that dispatches
`truth()` and returns `true`). The `callvalue ≠ 0` path and the low-gas
(out-of-gas) regime are *unaffected* and are proved cleanly — see `Examples/Truth/Correct.lean`.

> **Status / project-owner directive.** The owner instructed: "you can add specific keccak
> hashes as trusted axioms for now." Accordingly `Examples/Truth/Correct.lean` declares **two** trusted
> axioms (`truthSelectorBytes`, `truthValidJumps`) for the genuinely-opaque base computations
> (Blockers 1 and 2 below), plus one extern-spec axiom (`byteArray_zeroes_toList`, in
> `Memory.lean`) for the *content* of the `@[extern "memset_zero"]` `ffi.zeroes` primitive
> (evmlean already axiomatizes only its **size**, `ByteArray_zeroes_size`).
>
> A third fact — the EVM selector decode `SHR(calldata,224)` vs `calldata.extract 0 4` — was once
> admitted but is **not** opaque, so per the "don't admit what isn't opaque" rule it is now
> **proved** as `truthEvmSelector` (on the contract-agnostic `selector_toNat`); it is no longer
> an axiom.
>
> **`truthCorrect` is fully proved — no `sorry`.** Every call is covered, including the
> `callvalue == 0` **success path**: the 93-instruction EVM trace (`truthX_cvz_success`) that
> dispatches `truth()`, stores the free pointer `0x80` and the bool `1` in memory, and ABI-encodes
> / `RETURN`s the 32-byte word `1`. `truthCorrect` genuinely depends on the two trusted axioms
> (`truthValidJumps` discharges the many taken jumps; `truthSelectorBytes` drives the dispatch
> selector) and `byteArray_zeroes_toList` (the only opacity in the otherwise-computable
> memory/ABI/selector reasoning — the `ffi.zeroes` pad cancels in the round-trips). `#print axioms
> truthCorrect` ⇒ `[propext, Classical.choice, Quot.sound, ByteArray_zeroes_size,
> byteArray_zeroes_toList, truthSelectorBytes, truthValidJumps]` — **no `sorryAx`, no
> `native_decide`**. The `callvalue ≠ 0` sub-result `truthX_callvalue_ne` needs **none** of the
> Truth-specific axioms. Once the base defects are fixed both trusted axioms become
> `decide`-provable and can be deleted with no change to the proof.

---

## Blocker 1 — `D_J_aux` is `partial` ⇒ valid-jump set is logically opaque

* **Definition:** `Ethereum.EVM.D_J_aux`
  `.lake/packages/evmlean/Ethereum/Semantics.lean:100`
  ```
  partial def D_J_aux (c : ByteArray) (i : UInt256) (result : Array UInt256) : Array UInt256 := …
  def D_J (c : ByteArray) (i : UInt256) : Array UInt256 := D_J_aux c i #[]
  ```
* `Ethereum.EVM.Ξ` (code execution) calls `X (g.toNat+1) (D_J I.code ⟨0⟩) …`
  (`Semantics.lean:850`). Inside `Xstep`/`Z` (`Semantics.lean:724`), a `JUMP`/`JUMPI`
  whose **branch is taken** raises `.BadJumpDestination` unless
  `(D_J I.code ⟨0⟩).contains target = true`.
* Because `D_J_aux` is `partial`, `D_J` is an **opaque constant**: it has no
  equational lemmas (`D_J_aux.eq_def` does not exist) and does not reduce in the
  kernel.

* **Minimal scenario (empirically confirmed).** For `truthBytecode`, the first
  `JUMPDEST` is at pc `14` and the dispatcher's `JUMPI` at pc `10` jumps there when
  `callvalue == 0`:
  - `#eval (D_J truthBytecode ⟨0⟩)` ⇒ `#[14, 38, 42, 48, 59, 68, 76, 87, 94, 100, 117]`
    (compiled code works);
  - `example : (D_J truthBytecode ⟨0⟩).contains ⟨14⟩ = true := by decide`
    ⇒ **fails**: "reduction got stuck at the `Decidable` instance
    `(D_J truthBytecode {val := 0}).contains {val := 14}`" (opaque, not depth);
  - `example : D_J truthBytecode ⟨0⟩ = #[…] := by rfl` ⇒ **fails** "not
    definitionally equal";
  - `by native_decide` ⇒ succeeds but `#print axioms` lists
    `…native_decide.ax_1_1` (an `ofReduceBool` axiom) ⇒ **disallowed**.
* **Consequence:** No contract that executes a *taken* jump can be verified with a
  clean `#print axioms`. This blocks every `callvalue == 0` execution of `Truth`
  (the dispatcher's first `JUMPI` is taken to pc `14`).

* **Suggested fix:** make `D_J_aux` total so it gains equational lemmas and reduces
  under `decide`. It already recurses via `N i cᵢ` (strictly increasing `i` toward
  `c.size`); replace `partial` with structural recursion on a `Nat` fuel
  `c.size - i.toNat` (or `termination_by`), e.g.
  ```
  def D_J_aux (c : ByteArray) (i : UInt256) (result : Array UInt256) : Array UInt256 :=
    go (c.size) c i result
  where go : Nat → ByteArray → UInt256 → Array UInt256 → Array UInt256
    | 0, _, _, r => r
    | fuel+1, c, i, r => match c.get? i.toNat >>= parseInstr with
        | none => r
        | some cᵢ => go fuel c (N i cᵢ) (if cᵢ = .JUMPDEST then r.push i else r)
  ```
  Then `(D_J truthBytecode ⟨0⟩).contains ⟨14⟩ = true` is provable by `decide`.
  Alternatively, expose a proven membership lemma for `D_J`.

## Blocker 2 — `ffi.keccak256` is `@[extern] opaque` ⇒ `dispatchMsg` selector is opaque

* **Definition:** `ffi.keccak256` / `ffi.KEC`
  `.lake/packages/evmlean/Ethereum/FFI/ffi.lean:20`
  ```
  @[extern "keccak256"] opaque keccak256 (input : @& ByteArray) (len : USize) : ByteArray
  def KEC (data : ByteArray) : ByteArray := (KECCAK256 data).toOption.getD .empty
  ```
* `Solm.dispatchMsg` (`Solm/Dispatch.lean:20`) selects a transition by comparing
  `calldata.extract 0 4` to `(ffi.KEC (toByteArray (printSignature …))).extract 0 4`.
  Because `keccak256` is `opaque`, `dispatchMsg truthContract calldata` cannot be
  reduced for concrete `calldata`.
* **Consequence:** for the `callvalue == 0` dispatch path one must relate the EVM's
  *hard-coded* selector check (`PUSH4 0x9e9f51d2` in `truthBytecode`) to the Solm
  selector `KEC("truth()")[0:4]`; that requires `KEC("truth()")[0:4] = 0x9e9f51d2`,
  a fact about the opaque `keccak256` that is unprovable without `native_decide`.
* **Note:** the `callvalue ≠ 0` path proved in `Examples/Truth/Correct.lean` *avoids* this by
  case-splitting on `dispatchMsg`'s result **abstractly** (`none` / `some`) instead of
  computing it — the EVM reverts before the selector check regardless of calldata.
* **Suggested fix:** for verification, provide a model-level keccak (or a proven
  `KEC("truth()")[0:4] = 0x9e9f51d2` lemma / a `@[simp]` characterization of the
  finitely-many selectors a contract uses), so `dispatchMsg` reduces under `decide`.

---

### What is proved cleanly despite the blockers
* `callvalue ≠ 0` (any gas): EVM reverts via the compiler's non-payable guard with no
  taken jump and no keccak; Solm either fails `require(callvalue == 0)` (→ `reverted`),
  fails to dispatch, or fails to decode — covered by `execution` / `noDispatch` /
  `decodingFailed`.
* low gas (any calldata): `Ξ = .error .OutOfGass` before any jump — covered by
  `outOfGas`.

The `callvalue == 0 ∧ enough-gas` success path is also fully proved; it genuinely depends on the
two trusted axioms (`truthValidJumps` discharges the taken jumps, `truthSelectorBytes` the dispatch
selector). Once the base defects are fixed, both become `decide`-provable and can be deleted.

---

# `Pow.powCorrect` (the `pow2(uint256 n)` contract)

`powCorrect : runtimeEquivalence!?! powConfig powBytecode Pow.powContract` is **fully proved —
no `sorry`**. `#print axioms Pow.powCorrect` ⇒
`[propext, Classical.choice, Quot.sound, ByteArray_zeroes_size, byteArray_zeroes_toList,
powSelectorBytes, powValidJumps]`.

This is **exactly the Truth axiom set** — the standard logical axioms, the two `ffi.zeroes`
base-axioms, and the two opaque Blocker-1/2 axioms (here `powValidJumps` / `powSelectorBytes`).
`pow2` adds **no** further axioms, even though (unlike `truth()`) it takes an argument and so
exercises the ABI **decoder** and a `while` loop. The two assumptions that earlier stood in for
proofs — `powRealisticCalldata` and `powSuccessAcct` — have both been **discharged**:

## (former Axiom A) — `powRealisticCalldata`: **discharged by fixing the model** (no longer an axiom)

* **The gap it papered over.** solc's ABI decoder checks the argument is present with a **signed**
  `SLT(calldatasize − 4, 32)` (pc 214 of `powBytecode`). For `calldatasize ≥ 2^255 + 4` the word
  `calldatasize − 4 ≥ 2^255` is *negative* in two's-complement, so `SLT … = 1` and the EVM
  **reverts**. The trusted-base `Solm.decodeCalldata` originally did **no** signed length check — it
  read 32 bytes and **succeeded** — so for such calldata (with `n < 256`) the spec *returned `2^n`*
  while the EVM *reverted*: a genuine divergence. (The complementary case `size ≥ 2^256`, where the
  EVM's `CALLDATASIZE` wraps mod `2^256` but the spec does not, is excluded by the equivalence
  statement's own hypothesis `I.calldata.size < UInt256.size`.)
* **The fix (model change in `ABI/Decode.lean`).** `decodeCalldata` now returns `none` exactly when
  there are arguments to decode **and** the args region is `≥ 2^255` bytes
  (`types.isEmpty = false ∧ 2^255 ≤ (calldata.drop 4).length`) — precisely the overflow case of
  solc's signed guard. This is sound for **any** contract (it never rejects calldata the EVM
  accepts, since `headSize < 2^255` always makes the signed check revert there too); a
  zero-parameter selector like `truth()` does no such check and is unaffected, so `truthCorrect`'s
  axiom set is unchanged.
* **Consequence in the proof.** Sizes `≥ 2^255 + 4` now route to **`decodingFailed`** — Solm decode
  fails (`powDecode_none_huge`) and the EVM reverts at the decoder's signed `SLT` (`powX_hugearg`,
  which reuses the short-argument revert trace via the new `slt32_one_high`). The success/`n ≥ 256`
  paths carry the exact realizable bound `size < 2^255 + 4` (the EVM still *succeeds* for
  `size ∈ [2^255, 2^255 + 3]`, where `SLT` is non-negative), threaded as a real hypothesis instead
  of an axiom.

## (former Axiom B) — `powSuccessAcct`: **discharged by threading a preservation clause** (no longer an axiom)

A successful `pow2` run leaves the EVM account state untouched —
`s.createdAccounts = cA ∧ s.accountMap = σ` — which `execResultsEquiv.success` requires. This was
previously asserted as `axiom powSuccessAcct`; it has now been **proved** and the axiom deleted.

* **Why it holds.** `pow2`'s bytecode executes **only** pure stack/memory opcodes — `PUSH*`, `POP`,
  `DUP*`, `SWAP*`, `ADD`/`MUL`/`SUB`/`LT`/`SLT`/`EQ`/`ISZERO`/`SHR`, `MLOAD`, `MSTORE`, `JUMP*`,
  `CALLVALUE`/`CALLDATASIZE`/`CALLDATALOAD`, `RETURN` — **none** of `CREATE`/`CALL`/`SSTORE`/
  `SELFDESTRUCT`/`LOG`, the only opcodes that mutate `createdAccounts` / `accountMap` (see
  `Semantics.lean:209/273/337/595`).
* **How it was discharged.** Accounts are carried as the `acc` field of every `RD` combinator
  (alongside `mem`/`aw`), initialized at `start` to `initState`'s `(cA, σ)` and preserved by each
  opcode (none of the in-scope opcodes touch accounts). At the success terminal, `RDret` exposes
  `(s'.createdAccounts, s'.accountMap) = (cA, σ)`, which `RDret.reEquivElim` feeds straight into
  `execResultsEquiv.success`. The same mechanism is generic, so `truthCorrect`'s axiom set is
  unchanged.

The **revert** scenarios (`callvalue ≠ 0`, short calldata `< 4`, wrong selector, short argument
`4 ≤ size < 36`, huge calldata `size ≥ 2^255 + 4`, `n ≥ 256`) and the **out-of-gas** regime need
**no** axiom — they couple via `noDispatch` / `decodingFailed` / `execution`-with-`revert` /
`outOfGas`, none of which constrains the EVM's account state.
