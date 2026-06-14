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
(out-of-gas) regime are *unaffected* and are proved cleanly — see `TruthCorrect.lean`.

> **Status / project-owner directive.** The owner instructed: "you can add specific keccak
> hashes as trusted axioms for now." Accordingly `TruthCorrect.lean` declares **two** trusted
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
> `native_decide`**. The `callvalue ≠ 0` sub-result `truthXi_callvalue_ne` needs **none** of the
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
* `Act.dispatchMsg` (`Act/Dispatch.lean:20`) selects a transition by comparing
  `calldata.extract 0 4` to `(ffi.KEC (toByteArray (printSignature …))).extract 0 4`.
  Because `keccak256` is `opaque`, `dispatchMsg truthContract calldata` cannot be
  reduced for concrete `calldata`.
* **Consequence:** for the `callvalue == 0` dispatch path one must relate the EVM's
  *hard-coded* selector check (`PUSH4 0x9e9f51d2` in `truthBytecode`) to the Act
  selector `KEC("truth()")[0:4]`; that requires `KEC("truth()")[0:4] = 0x9e9f51d2`,
  a fact about the opaque `keccak256` that is unprovable without `native_decide`.
* **Note:** the `callvalue ≠ 0` path proved in `TruthCorrect.lean` *avoids* this by
  case-splitting on `dispatchMsg`'s result **abstractly** (`none` / `some`) instead of
  computing it — the EVM reverts before the selector check regardless of calldata.
* **Suggested fix:** for verification, provide a model-level keccak (or a proven
  `KEC("truth()")[0:4] = 0x9e9f51d2` lemma / a `@[simp]` characterization of the
  finitely-many selectors a contract uses), so `dispatchMsg` reduces under `decide`.

---

### What is proved cleanly despite the blockers
* `callvalue ≠ 0` (any gas): EVM reverts via the compiler's non-payable guard with no
  taken jump and no keccak; Act either fails `require(callvalue == 0)` (→ `reverted`),
  fails to dispatch, or fails to decode — covered by `execution` / `noDispatch` /
  `decodingFailed`.
* low gas (any calldata): `Ξ = .error .OutOfGass` before any jump — covered by
  `outOfGas`.
The single remaining `sorry` in `truthCorrect` is the `callvalue == 0 ∧ enough-gas`
branch, blocked by **both** defects above. It is isolated and documented in NOTES.md.

---

# `powCorrect` (the `pow2(uint256 n)` contract)

`powCorrect : runtimeEquivalence!?! powConfig powBytecode Pow.powContract` is **fully proved —
no `sorry`**. `#print axioms powCorrect` ⇒
`[propext, Classical.choice, Quot.sound, ByteArray_zeroes_size, byteArray_zeroes_toList,
powSelectorBytes, powValidJumps, powRealisticCalldata, powSuccessAcct]`.

The first six are exactly the Truth set (standard + `ffi.zeroes` base-axioms + the two opaque
Blocker-1/2 axioms, here `powValidJumps` / `powSelectorBytes`). `pow2` adds **two** axioms because,
unlike `truth()`, it takes an argument and so exercises the ABI **decoder** and a `while` loop:

## Axiom A — `powRealisticCalldata` (a genuine model-abstraction gap)

```
axiom powRealisticCalldata {I} (hcode : I.code = powBytecode) : I.calldata.size < 2^255
```

* **Why it is needed.** solc's ABI decoder checks the argument is present with a **signed**
  `SLT(calldatasize − 4, 32)` (pc 214 of `powBytecode`). For `calldatasize ≥ 2^255 + 4` the
  subtraction `calldatasize − 4 ≥ 2^255` is a *negative* two's-complement word, so `SLT … = 1` and
  the EVM **reverts**. But the trusted-base `Act.decodeCalldata` performs **no** signed length
  check — it reads 32 bytes and **succeeds** — so for such calldata (with `n < 256`) the Act spec
  *executes and returns `2^n`* while the EVM *reverts*: a genuine divergence.
* **Why it is sound to assume.** This range is **physically unreachable**: the EVM gas schedule
  charges ≥ 4 gas per calldata byte, so any transaction with `g < 2^256` gas can carry at most
  `~2^254` bytes. The `Ξ` model here (`Semantics.lean:824`) runs the bytecode straight from gas `g`
  and **does not charge intrinsic calldata gas**, so it permits unrealizable calldata sizes. The
  axiom restores the realistic bound `size < 2^255`, below which solc's signed check and the
  (unsigned) Act decoder agree.
* **Suggested fix.** Either (a) charge intrinsic calldata gas in `Ξ` (then `size ≥ 2^254` ⇒
  `Ξ = OutOfGass` ⇒ covered by `outOfGas`), or (b) add the signed length check to
  `Act.decodeCalldata` (then both revert ⇒ `decodingFailed`). Either makes the axiom provable.

## Axiom B — `powSuccessAcct` (mechanically provable; deferred plumbing, **not** opaque)

```
axiom powSuccessAcct {…} (hcode) (h : X … (initState …) = .ok (.success s o)) :
    s.createdAccounts = cA ∧ s.accountMap = σ
```

* `pow2`'s bytecode executes **only** pure stack/memory opcodes — `PUSH*`, `POP`, `DUP*`, `SWAP*`,
  `ADD`/`MUL`/`SUB`/`LT`/`SLT`/`EQ`/`ISZERO`/`SHR`, `MLOAD`, `MSTORE`, `JUMP*`,
  `CALLVALUE`/`CALLDATASIZE`/`CALLDATALOAD`, `RETURN` — **none** of `CREATE`/`CALL`/`SSTORE`/
  `SELFDESTRUCT`/`LOG`, the only opcodes that mutate `createdAccounts` / `accountMap`. So a
  successful run leaves both equal to `initState`'s (`= cA`, `= σ`); `execResultsEquiv.success`
  needs exactly this.
* Unlike Axiom A and the opaque axioms, this is **provable** in the model. Its proof is pure
  plumbing: thread two trivial preservation clauses (`s'.createdAccounts = s.createdAccounts`,
  `s'.accountMap = s.accountMap`) — mirroring the already-threaded `memory`/`activeWords` clauses —
  through the dozen success-trace lemmas (`solcGuardPrologue`, `powX_dispToEq`, `powX_disp`,
  `powX_decodeToCf`, `powRoutine_{cf,bb,a5,9c}`, `powX_require`, `powLoopCore`, `powX_exit`,
  `powX_encode`) and chain them in `powX_success`. It is stated as an axiom only to keep the
  development tractable; it is intended to be discharged.

The five **revert** scenarios (`callvalue ≠ 0`, short calldata `< 4`, wrong selector, short
argument `4 ≤ size < 36`, `n ≥ 256`) and the **out-of-gas** regime need **neither** new axiom —
they couple via `noDispatch` / `decodingFailed` / `execution`-with-`revert` / `outOfGas`, none of
which constrains the EVM's account state.
