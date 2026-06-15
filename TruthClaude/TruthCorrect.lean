import TruthClaude.Theory
import TruthClaude.Stepping
import TruthClaude.Memory
import TruthClaude.Solc
import TruthClaude.Reach

/-!
# Truth — a worked runtime-equivalence example

The contract (Solidity):

```solidity
contract Truth {
  function truth() public pure returns (bool) { return true; }
}
```

This file pins down the three ingredients of a runtime-equivalence claim:
* `truthBytecode` — the deployed EVM runtime bytecode (solc output);
* `truthContract` — the Act specification;
* `truthCorrect`  — the correctness statement.  **Fully proved** (no `sorry`): every call —
  `callvalue ≠ 0`, low-gas, short-calldata, wrong-selector, and the `truth()` success path
  (a 93-instruction EVM trace that ABI-encodes and `RETURN`s `true`) — is shown equivalent to
  the Act spec, via the contract-agnostic `TruthClaude.Theory`/`Stepping`/`Memory` libraries.
  `#print axioms truthCorrect` lists only Lean's three, the evmlean `ByteArray_zeroes_size`
  base axiom, the `ffi.zeroes`-content extern spec, and the three documented trusted
  selector/jump axioms (see `MISSPEC.md`) — no `sorryAx`.
-/

open Act ABI

/-! ## 1. The contract's runtime bytecode -/

/-- Deployed runtime bytecode of the `Truth` contract. -/
def truthBytecode : ByteArray :=
  ⟨#[
    0x60, 0x80, 0x60, 0x40, 0x52, 0x34, 0x80, 0x15, 0x60, 0x0e, 0x57, 0x5f,
    0x5f, 0xfd, 0x5b, 0x50, 0x60, 0x04, 0x36, 0x10, 0x60, 0x26, 0x57, 0x5f,
    0x35, 0x60, 0xe0, 0x1c, 0x80, 0x63, 0x9e, 0x9f, 0x51, 0xd2, 0x14, 0x60,
    0x2a, 0x57, 0x5b, 0x5f, 0x5f, 0xfd, 0x5b, 0x60, 0x30, 0x60, 0x44, 0x56,
    0x5b, 0x60, 0x40, 0x51, 0x60, 0x3b, 0x91, 0x90, 0x60, 0x64, 0x56, 0x5b,
    0x60, 0x40, 0x51, 0x80, 0x91, 0x03, 0x90, 0xf3, 0x5b, 0x5f, 0x60, 0x01,
    0x90, 0x50, 0x90, 0x56, 0x5b, 0x5f, 0x81, 0x15, 0x15, 0x90, 0x50, 0x91,
    0x90, 0x50, 0x56, 0x5b, 0x60, 0x5e, 0x81, 0x60, 0x4c, 0x56, 0x5b, 0x82,
    0x52, 0x50, 0x50, 0x56, 0x5b, 0x5f, 0x60, 0x20, 0x82, 0x01, 0x90, 0x50,
    0x60, 0x75, 0x5f, 0x83, 0x01, 0x84, 0x60, 0x57, 0x56, 0x5b, 0x92, 0x91,
    0x50, 0x50, 0x56
  ]⟩

/-! ## 2. The Act specification -/

/-- The single transition: `truth()` requires zero callvalue and returns `true`.
    (The `require(callvalue == 0)` mirrors the compiler-inserted non-payable guard.) -/
def truthTransition : TransitionDecl :=
  { name := "truth"
    params := []
    returnType := some (.elem .bool)
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0))
      , .return (.boolLit true) ] }

/-- Act specification of the `Truth` contract: no storage, no constructor body,
    a single transition. -/
def truthContract : ContractDecl :=
  { name := "Truth"
    storage := []
    ctor := { params := [], body := [] }
    transitions := [truthTransition] }

/-- Configuration: empty storage layout and the default external-call ABI. -/
def truthConfig : Config :=
  { storage := { layout := fun _ => none }
    externalABI := defaultExternalCallABI }

open Ethereum Ethereum.EVM TruthClaude.Theory TruthClaude.Reach

set_option maxRecDepth 10000

/-! ## 3. Trusted axioms for opaque trusted-base computations

`truthCorrect` needs exactly **two** facts about definitions in the (read-only) trusted base
that are **logically opaque** (see `MISSPEC.md`): the keccak selector of `truth()` (because
`ffi.keccak256` is `@[extern] opaque`) and the valid-jump-destination set of `truthBytecode`
(because `Ethereum.EVM.D_J_aux` is `partial`).  Both values are confirmed by `#eval` but cannot
be reduced in the kernel.  Per the project owner's instruction we admit them as **trusted
axioms** here; the real fix is to make those base definitions computable (`MISSPEC.md`), after
which both become provable by `decide` and can be deleted.

The EVM selector-decode fact (`SHR(calldata,224)` vs `calldata.extract 0 4`) was *also* once
admitted, but it is **not** opaque — it is now **proved** as `truthEvmSelector` (below), built
on the contract-agnostic `selector_toNat` in `Memory.lean`.  Beyond these two trusted axioms and
Lean's standard three, `truthCorrect` depends only on the pre-existing evmlean base axiom
`ByteArray_zeroes_size` and its companion extern-spec `byteArray_zeroes_toList`
(`ffi.ByteArray.zeroes` yields zero bytes). -/

/-- The 4-byte function selector of `truth()` is `0x9e9f51d2` (keccak of `"truth()"`). -/
axiom truthSelectorBytes :
    (ffi.KEC (String.toByteArray (Act.transitionSigStr truthTransition))).extract 0 4
      = ⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩

/-- The `JUMPDEST` positions of `truthBytecode` (the valid jump targets). -/
axiom truthValidJumps :
    Ethereum.EVM.D_J truthBytecode ⟨0⟩
      = #[⟨14⟩, ⟨38⟩, ⟨42⟩, ⟨48⟩, ⟨59⟩, ⟨68⟩, ⟨76⟩, ⟨87⟩, ⟨94⟩, ⟨100⟩, ⟨117⟩]

/-! ## 4. Truth-specific Act-side facts -/

/-- Dispatch reduces (via `truthSelectorBytes`) to a 4-byte calldata-prefix comparison. -/
theorem truthDispatch_eq (cd : ByteArray) :
    dispatchMsg truthContract cd
      = if ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4)
        then some truthTransition else none := by
  simp only [dispatchMsg, truthContract, List.map_cons, List.map_nil, List.find?_cons,
    List.find?_nil, Prod.map, id_eq, Function.comp_apply]
  rw [truthSelectorBytes]
  by_cases hb : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) = true
  · simp [hb]
  · simp only [Bool.not_eq_true] at hb; simp [hb]

/-- `truthContract` has exactly one transition, so any successful dispatch yields it. -/
theorem truthDispatch_unique {cd : ByteArray} {t : TransitionDecl}
    (h : dispatchMsg truthContract cd = some t) : t = truthTransition := by
  simp only [dispatchMsg, truthContract, List.map_cons, List.map_nil] at h
  -- `find?` over the single-transition list: the only candidate is `truthTransition`.
  split at h
  · rename_i pair heq
    have hmem := List.mem_of_find?_eq_some heq
    simp only [List.mem_singleton, Prod.map, id_eq, Prod.mk.injEq] at hmem
    rw [Option.some.injEq] at h
    rw [← h, hmem.1]
  · exact absurd h (by simp)

/-- With non-zero call value, the Act body reverts: `require(callvalue == 0)` fails. -/
theorem truthBodyReverts (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecContractBody truthConfig truthContract evm locals truthTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse ?_))
  have hval : (Value.int (Int.ofNat ↑evm.executionEnv.weiValue.val) == Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro hh
    rw [Value.int.injEq] at hh
    exact h (TruthClaude.Theory.uint256_toNat_eq_zero (Int.ofNat.inj hh))
  show evalExpr? truthConfig _ evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool false)
  simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]

/-- With zero call value, the Act body returns `true`: `require(callvalue == 0)` passes and
    `return true` yields `(.bool true)` with the frame/EVM-state unchanged. -/
theorem truthBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecContractBody truthConfig truthContract evm locals truthTransition.body
      (.returned { contract := truthContract, locals := locals } evm (some (.bool true))) := by
  refine ExecFuncBody.execBlockRet (ExecBlock.consNormal (ExecStmt.requireTrue ?_)
            (ExecBlock.consReturn (ExecStmt.return ?_)))
  · have hval : (Value.int (Int.ofNat ↑evm.executionEnv.weiValue.val) == Value.int 0) = true := by
      rw [h]; rfl
    show evalExpr? truthConfig _ evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true)
    simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]
  · show evalExpr? truthConfig _ evm (.boolLit true) = .ok (.bool true)
    simp only [evalExpr?]; rfl

/-- **ABI encoding of the `truth()` return.**  `encodeReturnValue?` of `(.bool true)` is the
    32-byte big-endian word `1` — definitionally the EVM `RETURN`/`MSTORE` value
    `UInt256.toByteArray ⟨1⟩` (the opaque `ffi.zeroes` pad cancels; see
    `TruthClaude.Theory.toByteArray_eq_toBytesBE`). -/
theorem truthReturnEncoding :
    encodeReturnValue? (.elem .bool) (.bool true) = some (UInt256.toByteArray ⟨1⟩) := by
  rw [TruthClaude.Theory.toByteArray_eq_toBytesBE]
  simp [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?,
    staticABIEncodedSize?, isDynamicABIType, encodeABIValuesFrom?, encodeABIValue?,
    encodeABIWord?, Bool.toUInt256_true]
  rfl

/-! ## 5. The Ξ traces (per scenario) -/

/-- The EVM trace for `callvalue ≠ 0`: the non-payable guard reverts (11 instructions ending
    in `REVERT`), with no taken jump.  Built compositionally as one `RDrev`. -/
theorem truthX_callvalue_ne
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev truthBytecode g (initState cA gh bl σ σ₀ g A I) := by
  -- prologue → PUSH1 0x0e · JUMPI (not taken: callvalue ≠ 0 ⇒ iszero = 0) → revert stub, one `RD`
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push1 ⟨14⟩,
      jumpiNT (isZero_eq_zero_of_ne hwv),
      push0, push0,
      raw rev 0 (by decide) (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov) ]

/-! ### callvalue = 0 dispatcher -/

theorem truthContains14 : (D_J truthBytecode ⟨0⟩).contains ⟨14⟩ = true := by
  rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)
theorem truthContains38 : (D_J truthBytecode ⟨0⟩).contains ⟨38⟩ = true := by
  rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)
theorem truthContains42 : (D_J truthBytecode ⟨0⟩).contains ⟨42⟩ = true := by
  rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)

/-! ### Selector decode — **proved** (was a trusted axiom; not opaque)

Relating the EVM's `CALLDATALOAD; PUSH 0xe0; SHR` selector to `calldata.extract 0 4` is pure
byte arithmetic.  `Memory.selector_toNat` does the 256-bit-shift ↔ byte-extraction core; below is
the `0x9e9f51d2`-specific bijection and the final equivalence (needs `4 ≤ calldata.size`, which
the dispatch path always has).  No new axioms — only `byteArray_zeroes_toList`. -/

private theorem u256_eq_self : UInt256.eq ⟨2661241298⟩ ⟨2661241298⟩ = ⟨1⟩ := by decide
private theorem u256_eq_ne {b : UInt256} (h : (⟨2661241298⟩ : UInt256) ≠ b) :
    UInt256.eq ⟨2661241298⟩ b = ⟨0⟩ := by
  simp only [UInt256.eq, Bool.toUInt256, decide_eq_false h]; rfl

/-- Big-endian decode of four bytes equals `0x9e9f51d2` iff the bytes are `[9e,9f,51,d2]`. -/
private theorem be4 (l : List UInt8) (hl : l.length = 4) :
    fromBytesBigEndian l = 2661241298 ↔ l = [0x9e, 0x9f, 0x51, 0xd2] := by
  match l, hl with
  | [b0, b1, b2, b3], _ =>
    unfold fromBytesBigEndian Function.comp
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, fromBytes',
      List.cons.injEq, and_true]
    have h0 := b0.toFin.isLt; have h1 := b1.toFin.isLt
    have h2 := b2.toFin.isLt; have h3 := b3.toFin.isLt
    simp only [UInt8.size] at h0 h1 h2 h3
    have e0 : b0.toFin.val = b0.toNat := rfl; have e1 : b1.toFin.val = b1.toNat := rfl
    have e2 : b2.toFin.val = b2.toNat := rfl; have e3 : b3.toFin.val = b3.toNat := rfl
    rw [e0, e1, e2, e3]
    have l0 : (0x9e : UInt8).toNat = 158 := rfl; have l1 : (0x9f : UInt8).toNat = 159 := rfl
    have l2 : (0x51 : UInt8).toNat = 81 := rfl; have l3 : (0xd2 : UInt8).toNat = 210 := rfl
    constructor
    · intro he
      exact ⟨UInt8.toNat_inj.mp (by omega), UInt8.toNat_inj.mp (by omega),
             UInt8.toNat_inj.mp (by omega), UInt8.toNat_inj.mp (by omega)⟩
    · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

/-- The `ByteArray` `==` selector test equals the first-four-bytes list condition. -/
private theorem extract_eq_iff (cd : ByteArray) (hsz : 4 ≤ cd.size) :
    ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) = true
      ↔ cd.data.toList.take 4 = [0x9e, 0x9f, 0x51, 0xd2] := by
  rw [show ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4)
        = ((#[0x9e, 0x9f, 0x51, 0xd2] : Array UInt8) == (cd.extract 0 4).data) from rfl,
      beq_iff_eq, ByteArray.data_extract, ← Array.toList_inj, Array.toList_extract]
  show ([0x9e, 0x9f, 0x51, 0xd2] : List UInt8) = (cd.data.toList.drop 0).take (0 + 4 - 0) ↔ _
  rw [List.drop_zero]
  constructor
  · intro he; rw [← he]
  · intro he; rw [he]

/-- **Selector decode** (proved): the EVM selector check `eq(0x9e9f51d2, SHR(calldata,224))`
    agrees with the dispatcher's 4-byte compare `0x9e9f51d2 == calldata.extract 0 4`. -/
theorem truthEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨2661241298⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  have hlen4 : (cd.data.toList.take 4).length = 4 := by
    rw [List.length_take]
    have : 4 ≤ cd.data.toList.length := by rw [Array.length_toList]; exact hsz
    omega
  have hsv : (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩).toNat
             = fromBytesBigEndian (cd.data.toList.take 4) := selector_toNat cd hsz
  by_cases hc : cd.data.toList.take 4 = [0x9e, 0x9f, 0x51, 0xd2]
  · have h1 : UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩ = ⟨2661241298⟩ :=
      u256_inj (by rw [hsv]; exact (be4 _ hlen4).mpr hc)
    rw [if_pos ((extract_eq_iff cd hsz).mpr hc), h1, u256_eq_self]
  · rw [if_neg (fun he => hc ((extract_eq_iff cd hsz).mp he))]
    exact u256_eq_ne (fun he => hc ((be4 _ hlen4).mp (by rw [← hsv, ← he]; rfl)))

/-- The shared dispatcher prefix for `callvalue = 0`: through the non-payable guard's taken jump
    (`0x08 → 0x0e`) and on to the `0x16` `JUMPI`, reaching pc 22 with stack `[0x26, (size < 4)]`,
    the free-pointer memory in place.  Built compositionally as one `RD`. -/
theorem truthX_cvz_prefix
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RD truthBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨22⟩
        [⟨38⟩, UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩]
        solcFreePtrMem (UInt256.ofNat 3) (cA, σ) 14 53 := by
  -- prologue → PUSH1 0x0e · JUMPI(taken, cv=0) · JUMPDEST · POP · PUSH1 4 · CALLDATASIZE · LT · PUSH1 0x26
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push1 ⟨14⟩,
      jumpiT (by rw [hwv]; decide) truthContains14,
      jumpdest, pop, push1 ⟨4⟩, calldatasize, lt, push1 ⟨38⟩ ]

/-- Dispatcher trace for `callvalue = 0 ∧ calldatasize < 4`: the prefix reaches the `0x16`
    `JUMPI` with `(size < 4) = 1`, so it jumps to the `0x26` revert stub.  One `RDrev`. -/
theorem truthX_cvz_short
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev truthBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (truthX_cvz_prefix hcode hwv) with [
    jumpiT (lt_four_ne_zero_of_lt hsz) truthContains38,
    jumpdest, push0, push0,
    raw rev 0 (by decide) (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov) ]
/-- Short calldata (`< 4` bytes) cannot match the 4-byte selector ⇒ dispatch fails. -/
theorem truthDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg truthContract cd = none := by
  rw [truthDispatch_eq]
  have hfalse : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) = false := by
    by_contra hc
    rw [Bool.not_eq_false] at hc
    have hsz := TruthClaude.Theory.byteArray_size_eq_of_beq hc
    rw [ByteArray.size_extract] at hsz
    simp only [show (⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray).size = 4 from rfl] at hsz
    omega
  simp [hfalse]

/-- Selector mismatch ⇒ dispatch fails. -/
theorem truthDispatch_none_nomatch {cd : ByteArray}
    (h : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) = false) :
    dispatchMsg truthContract cd = none := by
  rw [truthDispatch_eq]; simp [h]

/-- **calldatasize ≥ 4, wrong selector**: the dispatcher continues past the `0x16` JUMPI
    (not taken), decodes & compares the selector (`EQ = 0` via `truthEvmSelector`), and reverts
    at `0x26`.  Built compositionally off the prefix as one `RDrev`. -/
theorem truthX_cvz_revertB
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hmatch : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == I.calldata.extract 0 4) = false) :
    RDrev truthBytecode g (initState cA gh bl σ σ₀ g A I) := by
  -- prefix falls through the size JUMPI (size ≥ 4 ⇒ LT = 0), decodes the selector, mismatch ⇒ revert
  exact evm_run (truthX_cvz_prefix hcode hwv) with [
    jumpiNT (lt_four_eq_zero_of_ge hsz hsize),
    push0, calldataload, push1 ⟨224⟩, shr, dup1, push4 ⟨2661241298⟩, eq, push1 ⟨42⟩,
    jumpiNT (by rw [show ((⟨0⟩ : UInt256).toNat) = 0 from by decide, truthEvmSelector hsz];
                simp [hmatch]),
    jumpdest, push0, push0,
    raw rev 0 (by decide) (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov) ]

/-! ## Concrete memory states of the `truth()` epilogue -/

/-- Memory after solc stores the free pointer `0x80` at `0x40`. -/
noncomputable def truthMem1 : ByteArray :=
  (UInt256.toByteArray ⟨128⟩).write 0 ByteArray.empty 64 32
/-- Memory after solc additionally stores the return word `1` at `0x80`. -/
noncomputable def truthMem2 : ByteArray :=
  (UInt256.toByteArray ⟨1⟩).write 0 truthMem1 128 32

theorem truthMem1_eq :
    truthMem1 = (ByteArray.empty ++ ffi.ByteArray.zeroes (USize.ofNat 64)) ++ UInt256.toByteArray ⟨128⟩ := by
  rw [truthMem1, toByteArray_write_eq _ _ _ (by decide) (by exact lt_usize _ (by norm_num))]; rfl
theorem truthMem1_size : truthMem1.size = 96 := by
  rw [truthMem1_eq, ByteArray.size_append, ByteArray.size_append, zeroes_ofNat_size _ (by norm_num),
      toByteArray_size]; decide
theorem truthMem1_read64 : truthMem1.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := truthMem1_size; omega), truthMem1_eq,
      extract_append_right' _ _ _ _
        (by rw [ByteArray.size_append, zeroes_ofNat_size _ (by norm_num)]; rfl)
        (by rw [ByteArray.size_append, zeroes_ofNat_size _ (by norm_num), toByteArray_size]; rfl)]
theorem truthMem2_eq :
    truthMem2 = (truthMem1 ++ ffi.ByteArray.zeroes (USize.ofNat 32)) ++ UInt256.toByteArray ⟨1⟩ := by
  rw [truthMem2, toByteArray_write_eq _ _ _ (by rw [truthMem1_size]; omega)
        (by rw [truthMem1_size]; exact lt_usize _ (by norm_num))]
  norm_num [truthMem1_size]
theorem truthMem2_size : truthMem2.size = 160 := by
  rw [truthMem2_eq, ByteArray.size_append, ByteArray.size_append, truthMem1_size,
      zeroes_ofNat_size _ (by norm_num), toByteArray_size]
theorem truthMem1pad_size : (truthMem1 ++ ffi.ByteArray.zeroes (USize.ofNat 32)).size = 128 := by
  rw [ByteArray.size_append, truthMem1_size, zeroes_ofNat_size _ (by norm_num)]
theorem truthMem2_read64 : truthMem2.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := truthMem2_size; omega), truthMem2_eq,
      extract_append_left _ _ _ _ (by have := truthMem1pad_size; omega),
      extract_append_left _ _ _ _ (by have := truthMem1_size; omega),
      ← readWithPadding_eq_extract _ _ (by have := truthMem1_size; omega), truthMem1_read64]
theorem truthMem2_read128 : truthMem2.readWithPadding 128 32 = UInt256.toByteArray ⟨1⟩ := by
  rw [readWithPadding_eq_extract _ _ (by have := truthMem2_size; omega), truthMem2_eq,
      extract_append_right' _ _ _ _ (by have := truthMem1pad_size; omega)
        (by have := truthMem1pad_size; have := toByteArray_size (⟨1⟩ : UInt256); omega)]

/-- Decoding `truth()`'s (empty) argument list always succeeds with the empty store. -/
theorem truthDecode_empty {I : Ethereum.ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (truthTransition.params.map Param.name)
      (transitionSignature truthTransition).paramTypes I.calldata = some ∅ := by
  have hlen : ¬ (I.calldata.toList.length < 4) := by
    rw [TruthClaude.Theory.byteArray_toList_eq, Array.length_toList]
    have : I.calldata.size = I.calldata.data.size := rfl
    omega
  show decodeCalldata [] [] I.calldata = some ∅
  unfold decodeCalldata
  rw [if_neg hlen]
  rfl

set_option maxHeartbeats 800000 in
/-- **The `truth()` success trace**.  With zero call value, ≥4-byte calldata and the matching
    selector, the dispatcher jumps into `truth()`, which stores the free pointer and the bool `1`
    in memory and `RETURN`s the 32-byte word `1`.  Accounts `(cA, σ)` are preserved (no `SSTORE`);
    the substate is dropped by `RDret` (the Act equivalence ignores it).  Built compositionally off
    the dispatcher prefix as one `RDret`. -/
theorem truthX_cvz_success {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hmatch : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    RDret truthBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ) (UInt256.toByteArray ⟨1⟩) := by
  -- prefix → size JUMPI(nt) → selector decode/compare (match) → JUMPI(t) into `truth()` →
  --   abi-encode bool 1 (PUSH/JUMP plumbing through the solc helpers) → MSTORE 1 @128 → RETURN 1
  exact evm_run (truthX_cvz_prefix hcode hwv) with [
    jumpiNT (lt_four_eq_zero_of_ge hsz hsize),
    push0, calldataload, push1 ⟨224⟩, shr, dup1, push4 ⟨2661241298⟩, eq, push1 ⟨42⟩,
    jumpiT (by rw [show ((⟨0⟩ : UInt256).toNat) = 0 from by decide,
                show UInt256.eq ⟨2661241298⟩
                  (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩) = ⟨1⟩
              from by rw [truthEvmSelector hsz]; simp [hmatch]]; decide) (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)),
    jumpdest, push1 ⟨48⟩, push1 ⟨68⟩, jump (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)),
    jumpdest, push0, push1 ⟨1⟩, swap1, pop, swap1, jump (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, Fin.isValue,
          List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
          Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      (by rw [if_neg (by rw [solcFreePtrMem_size]; decide),
          show (⟨64⟩ : UInt256).toNat = 64 from (by decide), solcFreePtrMem_read64,
          fromByteArrayBigEndian_toByteArray,
          show UInt256.ofNat ((⟨128⟩ : UInt256).toNat) = ⟨128⟩ from (by decide)])
      (by decide) (by evm_ov),
    push1 ⟨59⟩, swap2, swap1, push1 ⟨100⟩, jump (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)),
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop,
    push1 ⟨117⟩, push0, dup4, add, dup5, push1 ⟨87⟩, jump (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)),
    jumpdest, push1 ⟨94⟩, dup2, push1 ⟨76⟩, jump (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)),
    jumpdest, push0, dup2, iszero, iszero, swap1, pop, swap2, swap1, pop, jump (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)),
    jumpdest, dup3,
    raw mstore 6 truthMem2 (UInt256.ofNat 5) (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, Fin.isValue,
          List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
          Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      (by rw [show ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 from by decide,
          show UInt256.isZero (UInt256.isZero ⟨1⟩) = ⟨1⟩ from by decide]; rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)),
    jumpdest, swap3, swap2, pop, pop, jump (by rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, Fin.isValue,
          List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
          Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      (by rw [if_neg (by rw [truthMem2_size]; decide),
          show (⟨64⟩ : UInt256).toNat = 64 from (by decide), truthMem2_read64,
          fromByteArrayBigEndian_toByteArray,
          show UInt256.ofNat ((⟨128⟩ : UInt256).toNat) = ⟨128⟩ from (by decide)])
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨1⟩) (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, Fin.isValue,
          List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
          Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      (by rw [show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide,
          show ((⟨128⟩ : UInt256).toNat) = 128 from by decide, truthMem2_read128])
      (by evm_ov) ]

theorem truthReEquiv_callvalueZero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) :
    runtimeEquivalenceFor truthConfig truthContract cA gh bl σ σ₀ g A I := by
  by_cases hsz : I.calldata.size < 4
  · -- short calldata ⇒ EVM reverts, Act fails to dispatch
    exact (truthX_cvz_short hcode hwv hsz).reEquivNoDispatch hcode (truthDispatch_none_short hsz)
  · rw [not_lt] at hsz
    by_cases hmatch : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · -- matching selector → `truth()` runs and returns `true`
      have hd : dispatchMsg truthContract I.calldata = some truthTransition := by
        rw [truthDispatch_eq, if_pos hmatch]
      exact (truthX_cvz_success hcode hwv hsz hsize hmatch).reEquivElim hcode fun _ _ hsucc => by
        refine reEquiv_execution hd (truthDecode_empty hsz)
          (truthBodyReturns (initState cA gh bl σ σ₀ g A I) ∅ ?_) ?_
        · show (initState cA gh bl σ σ₀ g A I).executionEnv.weiValue = ⟨0⟩
          simp only [initState]; exact hwv
        · rw [hsucc]
          exact execResultsEquiv.success rfl rfl rfl rfl
            (returnEquiv.returned rfl rfl truthReturnEncoding)
    · -- wrong selector → EVM reverts at `0x26`, Act fails to dispatch
      rw [Bool.not_eq_true] at hmatch
      exact (truthX_cvz_revertB hcode hwv hsz hsize hmatch).reEquivNoDispatch hcode
        (truthDispatch_none_nomatch hmatch)

/-! ## 6. The correctness statement -/

/-- The runtime bytecode refines the Act specification, for every initial state. -/
theorem truthCorrect :
    runtimeEquivalence!?! truthConfig truthBytecode truthContract := by
  refine ⟨fun cA gh bl σ σ₀ g A I hcode hsize => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact truthReEquiv_callvalueZero hcode hsize hwv
  · -- callvalue ≠ 0: the non-payable guard reverts; match it against Act's dispatch/decode cases
    exact (truthX_callvalue_ne hcode hwv).reEquivElim hcode fun _ _ hrev => by
      by_cases hdisp : dispatchMsg truthContract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        cases truthDispatch_unique ht
        by_cases hdec : decodeCalldata (truthTransition.params.map Param.name)
            (transitionSignature truthTransition).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          refine reEquiv_execution ht hca (truthBodyReverts _ _ ?_) ?_
          · show I.weiValue ≠ ⟨0⟩; exact hwv
          · rw [hrev]; exact .revert rfl rfl

