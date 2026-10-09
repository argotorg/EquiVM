import Benchmarks.Morpho.MorphoBlue.Common

/-! Shared source guards and refinement bridges for contracts with fallback entries. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MorphoBlue

def calldataGuard : Expr := .binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩)
  (.binary .add (.binary .exp (.intLit 2) (.intLit 255)) (.intLit 4))

theorem calldataGuard_eval {cfg : Config} {solm : Frame} {evm : EVM.State}
    (hget : solm.locals.get? "__calldata" = some (.bytes evm.executionEnv.calldata)) :
    evalExpr? cfg solm evm calldataGuard =
      .ok (.bool (decide (evm.executionEnv.calldata.size < 2 ^ 255 + 4))) := by
  simp only [calldataGuard, evalExpr?, hget, readLocalPath?, evalBinaryOp?,
    bind, pure, EvalResult.bind]
  norm_num [Int.toNat]

def calldataPrelude (rest : List Stmt) : List Stmt :=
  .require (.binary .eq (.env .callvalue) (.intLit 0)) ::
  .letDecl "__calldata" (some .bytes) (.env .msgData) ::
  .require calldataGuard :: rest

-- LIBRARY CANDIDATE: the nonpayable calldata-size prelude, over arbitrary frames and tails.
theorem calldataPrelude_ok {cfg : Config} {solm : Frame} {evm : EVM.State}
    {rest : List Stmt} (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock cfg evm solm (calldataPrelude rest)
      { solm with locals := solm.locals.insert "__calldata" (.bytes evm.executionEnv.calldata) }
      rest := by
  apply ABlock.requireStep
    ((ABlock.start.requireStep (evalCallvalueEq_true hcv)).letStep
      (value := .bytes evm.executionEnv.calldata) (by simp only [evalExpr?, envValue, pure]))
  simpa only [hsize, decide_true] using calldataGuard_eval
    (cfg := cfg) (evm := evm)
    (solm := { solm with
      locals := solm.locals.insert "__calldata" (.bytes evm.executionEnv.calldata) }) (store_get_self _ _ _)

-- LIBRARY CANDIDATE: a failing calldata-size prelude rejects any remaining body.
theorem calldataPrelude_reverts {cfg : Config} {C : ContractDecl} {evm : EVM.State}
    {locals imms : Store} {rest : List Stmt}
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : ¬ evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody cfg C evm locals (calldataPrelude rest) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply ABlock.requireRevert
    ((ABlock.start.requireStep (evalCallvalueEq_true hcv)).letStep
      (value := .bytes evm.executionEnv.calldata) (by simp only [evalExpr?, envValue, pure]))
  simpa only [hsize, decide_false] using calldataGuard_eval
    (cfg := cfg) (evm := evm)
    (solm := { contract := C
               locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata)
               immutables := imms }) (store_get_self _ _ _)

-- LIBRARY CANDIDATE: word addition of a modular negation is subtraction.
theorem word_add_sub_zero (a b : UInt256) :
    a + UInt256.sub ⟨0⟩ b = UInt256.sub a b := by
  apply u256_inj
  change (a.val + (0 - b.val)).val = (a.val - b.val).val
  rw [← add_sub_assoc, add_zero]

theorem wordAddNegFour (w : UInt256) :
    w + UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932 =
      UInt256.sub w ⟨4⟩ := by
  rw [show UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932 =
    UInt256.sub ⟨0⟩ ⟨4⟩ by native_decide]
  exact word_add_sub_zero _ _

-- GENERALIZES Reasoning.Reach.RDret.reEquivExecutionGen — accept selector dispatch
-- directly so a mutating transition can coexist with a fallback or receive entry.
theorem reEquivSelectorExecutionGen {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {immutables : Store} {σ σ₀ A I} {g : UInt256}
    {code o : ByteArray} {callargs cs retVal} {acc : AccountMap} {evm' : EVM.State}
    (hcode : I.code = code)
    (h : RDret code (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) acc o)
    (hd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract (initState σ σ₀ (.ofUInt256 g) A I)
      callargs t.body (.returned cs evm' retVal) immutables)
    (hAccounts : acc = evm'.accountMap)
    (henc : returnEquiv o retVal t.returnType) :
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
  · have hxi := Xi_success_of_X (g := g) (by rw [← hcode] at hX; exact hX)
    rw [hacc] at hxi
    refine .execution rfl (.intro hd rfl hdec rfl hbody) ?_
    rw [hxi]
    exact .success rfl rfl hAccounts (.abi henc)

-- GENERALIZES Reasoning.Reach.RDstatic.reEquivStaticHalt — accept selector dispatch
-- when the contract also declares a fallback or receive entry.
theorem reEquivSelectorStatic {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {immutables : Store} {σ σ₀ A I} {g : UInt256} {code : ByteArray} {callargs}
    (hcode : I.code = code)
    (h : RDstatic code (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I))
    (hd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract (initState σ σ₀ (.ofUInt256 g) A I)
      callargs t.body .staticViolation immutables) :
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables := by
  apply RDstatic.reEquivElim hcode h
  intro hxi
  refine .execution rfl (.intro hd rfl hdec rfl hbody) ?_
  rw [hxi]
  exact .staticHalt rfl rfl

-- GENERALIZES Reasoning.Reach.RDret.reEquivExecution — accept selector dispatch
-- directly so the contract may also declare a fallback or receive transition.
theorem reEquivSelectorExecution {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {immutables : Store} {σ σ₀ A I} {g : UInt256}
    {code o : ByteArray} {callargs cs retVal}
    (hcode : I.code = code)
    (h : RDret code (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) σ o)
    (hd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract (initState σ σ₀ (.ofUInt256 g) A I)
      callargs t.body (.returned cs (initState σ σ₀ (.ofUInt256 g) A I) retVal) immutables)
    (henc : returnEquiv o retVal t.returnType) :
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables :=
  reEquivSelectorExecutionGen hcode h hd hdec hbody rfl henc

-- GENERALIZES Reasoning.Reach.RDrev.reEquivExecutionRevert — accept selector dispatch
-- directly so the contract may also declare a fallback or receive transition.
theorem reEquivSelectorRevert {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {immutables : Store} {σ σ₀ A I} {g : UInt256} {code : ByteArray} {callargs}
    (hcode : I.code = code)
    (h : RDrev code (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I))
    (hd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract (initState σ σ₀ (.ofUInt256 g) A I)
      callargs t.body .reverted immutables) :
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables := by
  apply RDrev.reEquivElim hcode h
  intro g' o hxi
  refine .execution rfl (.intro hd rfl hdec rfl hbody) ?_
  rw [hxi]
  exact .revert rfl rfl

-- LIBRARY CANDIDATE: relate Solm list lookup to Lean list indexing.
theorem lookupNth_eq_getElem? {α : Type} (xs : List α) (i : Nat) :
    lookupNth? xs i = xs[i]? := by
  induction xs generalizing i with
  | nil => rfl
  | cons a xs ih =>
    cases i <;> simp only [lookupNth?, List.getElem?_cons_zero, List.getElem?_cons_succ, ih]

-- LIBRARY CANDIDATE: identify a four-byte ABI selector by its bytes.
theorem selectorPrefix_eq {cd : ByteArray} {b0 b1 b2 b3 : UInt8} (hsize : 4 ≤ cd.size)
    (h0 : cd[0] = b0) (h1 : cd[1] = b1) (h2 : cd[2] = b2) (h3 : cd[3] = b3) :
    cd.extract 0 4 = ⟨#[b0, b1, b2, b3]⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.data_extract, Array.size_extract]
    simp [Nat.min_eq_left hsize]
  · intro i hi hj
    have hi4 : i < 4 := by simpa using hj
    interval_cases i <;> simp_all [ByteArray.data_extract, Array.getElem_extract]
    all_goals first | exact h0 | exact h1 | exact h2 | exact h3

-- GENERALIZES Reasoning.Theory.solcReturnMem_read128: normalize the free pointer
-- loaded by generated RETURN summaries.
theorem wordReturn_freePtr (w : UInt256) :
    ((w.toByteArray.write 0 solcFreePtrMem
      (memLoad (UInt256.ofNat 64) solcFreePtrMem).toNat 32).readWithPadding
      (memLoad (UInt256.ofNat 64) solcFreePtrMem).toNat (UInt256.ofNat 32).toNat) =
      w.toByteArray := by
  have hload : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ :=
    solcFreePtrMem_mload64
  rw [hload]
  exact solcReturnMem_read128 _

-- LIBRARY CANDIDATE: a one-word return after hashing a mapping slot.
theorem wordReturn_twoWordHash (key slot w : UInt256) :
    let mem := twoWordHashMem key slot solcFreePtrMem
    ((w.toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding
      (memLoad (UInt256.ofNat 64) mem).toNat (UInt256.ofNat 32).toNat) = w.toByteArray := by
  dsimp only
  have hmem : (twoWordHashMem key slot solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 key slot solcFreePtrMem_size
  have hload : memLoad (UInt256.ofNat 64) (twoWordHashMem key slot solcFreePtrMem) = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide)
      (twoWordHashMem_read64 key slot solcFreePtrMem_size solcFreePtrMem_read64)
  rw [hload]
  apply toByteArray_write_read_back_of_gap
  rw [hmem]
  exact lt_usize _ (by decide)

-- GENERALIZES Reasoning.Reach.RDrev.reEquivDecodingFailed: permit a fallback.
theorem reEquivSelectorDecodingFailed {cfg : Config} {contract : ContractDecl}
    {t : TransitionDecl} {immutables : Store} {σ σ₀ A I} {g : UInt256} {code : ByteArray}
    (hcode : I.code = code)
    (h : RDrev code (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I))
    (hd : selectorDispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = none) :
    runtimeRefinementFor cfg contract σ σ₀ g A I immutables := by
  apply RDrev.reEquivElim hcode h
  intro g' o hxi
  exact .decodingFailed hd rfl hdec hxi

-- LIBRARY CANDIDATE: the SUB guard used by solc's canonical-address decoders.
theorem addressMaskSub_nonzero {w : UInt256} (hnc : ¬ w.toNat < EVM.addressModulus) :
    UInt256.sub w (UInt256.land w solcAddrMask) ≠ ⟨0⟩ := by
  apply u256_sub_ne_zero_of_ne
  intro heq
  apply hnc
  have hcan := solcAddrMask_result_canonical w
  rw [← heq] at hcan
  exact hcan

-- LIBRARY CANDIDATE: canonical word-byte view of any full calldata word.
theorem calldataWord_toBytesBE (cd : ByteArray) (off : Nat)
    (hlen : off + 32 ≤ cd.size) :
    EVM.Word.toBytesBE (calldataWord cd off) = (cd.toList.drop off).take 32 := by
  unfold calldataWord
  rw [← decode_word_at_eq_any cd off hlen]
  apply toBytesBE_bytesToWord_of_length
  simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
  change min 32 (cd.size - off) = 32
  omega

end Benchmarks.Morpho.MorphoBlue
