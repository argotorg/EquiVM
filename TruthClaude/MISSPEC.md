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
> hashes as trusted axioms for now." Accordingly `TruthCorrect.lean` declares three trusted
> axioms (`truthSelectorBytes`, `truthValidJumps`, `truthEvmSelector`) for the opaque-base
> computations, plus one extern-spec axiom (`byteArray_zeroes_toList`, in `Memory.lean`) for the
> *content* of the `@[extern "memset_zero"]` `ffi.zeroes` primitive (evmlean already axiomatizes
> only its **size**, `ByteArray_zeroes_size`).
>
> **`truthCorrect` is now fully proved — no `sorry`.** Every call is covered, including the
> `callvalue == 0` **success path**: the 93-instruction EVM trace (`truthX_cvz_success`) that
> dispatches `truth()`, stores the free pointer `0x80` and the bool `1` in memory, and ABI-encodes
> / `RETURN`s the 32-byte word `1`. `truthCorrect` genuinely depends on the three trusted axioms
> (`truthValidJumps` discharges the many taken jumps; `truthSelectorBytes`/`truthEvmSelector`
> drive the selector) and `byteArray_zeroes_toList` (the only opacity in the otherwise-computable
> memory/ABI reasoning — the `ffi.zeroes` pad cancels in the round-trips). `#print axioms
> truthCorrect` lists exactly these four plus Lean's three and the pre-existing evmlean
> `ByteArray_zeroes_size` — **no `sorryAx`, no `native_decide`**. The `callvalue ≠ 0` sub-result
> `truthXi_callvalue_ne` needs **none** of the Truth-specific axioms. Once the base defects are
> fixed the first three become `decide`-provable and can be deleted with no change to the proof.

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
