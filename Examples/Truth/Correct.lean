import Examples.Truth.Bytecode
import Examples.Truth.Spec
import Reasoning.Theory
import Reasoning.Dispatch
import Reasoning.SolmBody
import Reasoning.Stepping
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Reach

/-!
# Truth — runtime-equivalence proof for `truth()`

Every call (`callvalue ≠ 0`, short calldata, wrong selector, and the `truth()` success path)
is shown equivalent to the Solm spec, via the generic `Reasoning` library.  `#print axioms
truthCorrect` lists only Lean's three, the evmlean base axioms, and the two documented trusted
selector/jump axioms (`Examples/Truth/Bytecode.lean`) — no `sorryAx`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 10000

/-! ## 4. Truth-specific Solm-side facts -/

/-- Dispatch reduces (via `truthSelectorBytes`) to a 4-byte calldata-prefix comparison. -/
theorem truthDispatch_eq (cd : ByteArray) :
    dispatchMsg truthContract cd
      = if ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4)
        then some truthTransition else none :=
  dispatch_eq rfl truthSelectorBytes cd

/-- `truthContract` has exactly one transition, so any successful dispatch yields it. -/
theorem truthDispatch_unique {cd : ByteArray} {t : TransitionDecl}
    (h : dispatchMsg truthContract cd = some t) : t = truthTransition :=
  dispatch_unique rfl h

/-- With non-zero call value, the Solm body reverts: `require(callvalue == 0)` fails. -/
theorem truthBodyReverts (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecContractBody truthConfig truthContract evm locals truthTransition.body .reverted :=
  bodyReverts_nonPayable h

/-- With zero call value, the Solm body returns `true`: `require(callvalue == 0)` passes and
    `return true` yields `(.bool true)` with the frame/EVM-state unchanged. -/
theorem truthBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecContractBody truthConfig truthContract evm locals truthTransition.body
      (.returned { contract := truthContract, locals := locals } evm (some (.bool true))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by simp only [evalExpr?]; rfl)

/-- **ABI encoding of the `truth()` return.**  `encodeReturnValue?` of `(.bool true)` is the
    32-byte big-endian word `1` — definitionally the EVM `RETURN`/`MSTORE` value
    `UInt256.toByteArray ⟨1⟩` (the opaque `ffi.zeroes` pad cancels; see
    `Reasoning.Theory.toByteArray_eq_toBytesBE`). -/
theorem truthReturnEncoding :
    encodeReturnValue? (.elem .bool) (.bool true) = some (UInt256.toByteArray ⟨1⟩) := by
  rw [Reasoning.Theory.toByteArray_eq_toBytesBE]
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
      raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-! ### callvalue = 0 dispatcher -/

theorem truthContains14 : (D_J truthBytecode ⟨0⟩).contains ⟨14⟩ = true := by
  rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)
theorem truthContains38 : (D_J truthBytecode ⟨0⟩).contains ⟨38⟩ = true := by
  rw [truthValidJumps]; exact Array.contains_eq_true_of_mem (by simp)

/-! ### Selector decode (proved, not an axiom): the EVM `CALLDATALOAD; PUSH 0xe0; SHR` selector
    vs `calldata.extract 0 4` — a generic instance of `evmSelectorDecode`. -/

/-- The EVM selector check `eq(0x9e9f51d2, SHR(calldata,224))` agrees with the dispatcher's
    4-byte compare `0x9e9f51d2 == calldata.extract 0 4`. -/
theorem truthEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨2661241298⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x9e 0x9f 0x51 0xd2 ⟨2661241298⟩ (by decide)

/-- The shared dispatcher prefix for `callvalue = 0`: through the non-payable guard's taken jump
    (`0x08 → 0x0e`) and on to the `0x16` `JUMPI`, reaching pc 22 with stack `[0x26, (size < 4)]`,
    the free-pointer memory in place.  Built compositionally as one `RD`. -/
theorem truthX_cvz_prefix
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RD truthBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨22⟩
        [⟨38⟩, UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 14 53 := by
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
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

/-- Short calldata (`< 4` bytes) cannot match the 4-byte selector ⇒ dispatch fails. -/
theorem truthDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg truthContract cd = none :=
  dispatch_none_short rfl truthSelectorBytes rfl h

/-- Selector mismatch ⇒ dispatch fails. -/
theorem truthDispatch_none_nomatch {cd : ByteArray}
    (h : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == cd.extract 0 4) = false) :
    dispatchMsg truthContract cd = none :=
  dispatch_none_nomatch rfl truthSelectorBytes h

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
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]


/-- Decoding `truth()`'s (empty) argument list always succeeds with the empty store. -/
theorem truthDecode_empty {I : Ethereum.ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (truthTransition.params.map Param.name)
      (transitionSignature truthTransition).paramTypes I.calldata = some ∅ := by
  have hlen : ¬ (I.calldata.toList.length < 4) := by
    rw [Reasoning.Theory.byteArray_toList_eq, Array.length_toList]
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
    the substate is dropped by `RDret` (the Solm equivalence ignores it).  Built compositionally off
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
    raw mstore 6 (solcReturnMem ⟨1⟩) (UInt256.ofNat 5) (by decide)
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
      (by rw [if_neg (by rw [solcReturnMem_size]; decide),
          show (⟨64⟩ : UInt256).toNat = 64 from (by decide), solcReturnMem_read64,
          fromByteArrayBigEndian_toByteArray,
          show UInt256.ofNat ((⟨128⟩ : UInt256).toNat) = ⟨128⟩ from (by decide)])
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨1⟩) (by decide)
      (fun s haws hstks => by simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, Fin.isValue,
          List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos,
          Nat.one_lt_ofNat, getElem!_pos, List.getElem_cons_zero, List.getElem_cons_succ]; decide)
      (by rw [show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide,
          show ((⟨128⟩ : UInt256).toNat) = 128 from by decide, solcReturnMem_read128])
      (by evm_ov) ]

theorem truthReEquiv_callvalueZero
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = truthBytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) :
    runtimeEquivalenceFor truthConfig truthContract cA gh bl σ σ₀ g A I := by
  by_cases hsz : I.calldata.size < 4
  · -- short calldata ⇒ EVM reverts, Solm fails to dispatch
    exact (truthX_cvz_short hcode hwv hsz).reEquivNoDispatch hcode (truthDispatch_none_short hsz)
  · rw [not_lt] at hsz
    by_cases hmatch : ((⟨#[0x9e, 0x9f, 0x51, 0xd2]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · -- matching selector → `truth()` runs and returns `true`
      have hd : dispatchMsg truthContract I.calldata = some truthTransition := by
        rw [truthDispatch_eq, if_pos hmatch]
      exact (truthX_cvz_success hcode hwv hsz hsize hmatch).reEquivExecution hcode hd
        (truthDecode_empty hsz)
        (truthBodyReturns (initState cA gh bl σ σ₀ g A I) ∅ (by simp only [initState]; exact hwv))
        (returnEquiv_of_encode truthReturnEncoding)
    · -- wrong selector → EVM reverts at `0x26`, Solm fails to dispatch
      rw [Bool.not_eq_true] at hmatch
      exact (truthX_cvz_revertB hcode hwv hsz hsize hmatch).reEquivNoDispatch hcode
        (truthDispatch_none_nomatch hmatch)

/-! ## 6. The correctness statement -/

/-- The runtime bytecode refines the Solm specification, for every initial state. -/
theorem truthCorrect :
    runtimeEquivalence!?! truthConfig truthBytecode truthContract := by
  refine ⟨fun cA gh bl σ σ₀ g A I hcode hsize _hperm => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact truthReEquiv_callvalueZero hcode hsize hwv
  · -- callvalue ≠ 0: the non-payable guard reverts; the generic helper handles the Solm coupling
    exact (truthX_callvalue_ne hcode hwv).reEquivNonPayable hcode rfl
      fun ca => truthBodyReverts _ ca (by simp only [initState]; exact hwv)

