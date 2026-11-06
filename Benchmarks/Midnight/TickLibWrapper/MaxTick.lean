import Benchmarks.Midnight.TickLibWrapper.Dispatch

/-!
# TickLibWrapper `maxTick()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 389; reach lemma `tickLibWrapperReachMaxTickBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight.TickLibWrapper

set_option maxRecDepth 2000000

/-- `maxTick()`'s spec body: nonpayable guard, calldata-size guard, `return 6744`. -/
theorem maxTickBody_eq : maxTickTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .letDecl "__calldata" (some .bytes) (.env .msgData),
     .require (.binary .lt
        (.arrayLength .localVar { base := "__calldata", steps := [] })
        (.intLit 57896044618658097711785492504343953926634992332820282019728792003956564819972)),
     .return [.intLit 6744]] := by
  rfl

/-- `maxTick()`'s calldata decodes to the empty store whenever it is at least a selector. -/
theorem maxTickDecode_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (maxTickTransition.params.map Param.name)
      (transitionSignature maxTickTransition).paramTypes I.calldata = some ∅ := by
  change decodeCalldataWithMode .modern [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- The `__calldata` length require evaluates to `true` under the signed bound. -/
theorem evalCalldataLen_true {evm : EVM.State} {cd : ByteArray}
    {frame : Frame} (hb : frame.locals.get? "__calldata" = some (.bytes cd))
    (hlen : cd.size < 2 ^ 255 + 4) :
    evalExpr? config frame evm
      (.binary .lt (.arrayLength .localVar { base := "__calldata", steps := [] })
        (.intLit 57896044618658097711785492504343953926634992332820282019728792003956564819972)) =
      .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hb]
  simp only [readLocalPath?, evalBinaryOp?, Int.ofNat_eq_natCast]
  rw [decide_eq_true (by omega : (cd.size : Int) <
    57896044618658097711785492504343953926634992332820282019728792003956564819972)]

/-- The `__calldata` length require evaluates to `false` past the signed bound. -/
theorem evalCalldataLen_false {evm : EVM.State} {cd : ByteArray}
    {frame : Frame} (hb : frame.locals.get? "__calldata" = some (.bytes cd))
    (hlen : 2 ^ 255 + 4 ≤ cd.size) :
    evalExpr? config frame evm
      (.binary .lt (.arrayLength .localVar { base := "__calldata", steps := [] })
        (.intLit 57896044618658097711785492504343953926634992332820282019728792003956564819972)) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hb]
  simp only [readLocalPath?, evalBinaryOp?, Int.ofNat_eq_natCast]
  rw [decide_eq_false (by omega : ¬ (cd.size : Int) <
    57896044618658097711785492504343953926634992332820282019728792003956564819972)]

/-- The dispatcher memory's free pointer word: `mem[0x40] = 0x80`. -/
theorem dispatchMemLoad64 :
    memLoad (UInt256.ofNat 64)
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty 64 32) = ⟨128⟩ := by
  unfold memLoad
  rw [ulit_toNat' 64 (by decide),
    if_neg (by rw [toByteArray_write32_size_of_ge _ _ 64 0 96 (by decide) (by omega)
        (lt_usize _ (by decide)) (by decide)]; omega),
    toByteArray_write_read_back_of_gap _ _ 64 (lt_usize _ (by decide)),
    fromByteArrayBigEndian_toByteArray]
  exact u256_ofNat_toNat ⟨128⟩

/-- The Stele `maxTick()` body returns `6744` (callvalue `0`, calldata under the signed bound). -/
theorem maxTickBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm ∅ maxTickTransition.body
      (.returned
        { contract := contract,
          locals := (∅ : Store).insert "__calldata" (.bytes evm.executionEnv.calldata) }
        evm (some [.int 6744])) := by
  rw [maxTickBody_eq]
  refine ExecFuncBody.execBlockRet
    ((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep ?_ |>.requireStep ?_
      |>.returns ?_)
  · simp only [evalExpr?, envValue, pure]
  · exact evalCalldataLen_true
      (store_get_self (∅ : Store) "__calldata" (.bytes evm.executionEnv.calldata)) hlen
  · simp only [evalExpr?, pure]

/-- The success EVM trace: arm → callvalue guard → length guard → `PUSH2 6744; …; RETURN`. -/
theorem maxTickX_ok {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsel : selIs I (tickLibWrapperSelBytes 1)) :
    RDret tickLibWrapperBytecode g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray ⟨6744⟩) := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨0⟩ = ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 0) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachMaxTickBody (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_389_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_395_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_406 (by simp) rd2
  have hmemsize : ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty 64 32).size = 96 :=
    toByteArray_write32_size_of_ge _ _ 64 0 96 (by decide) (by omega)
      (lt_usize _ (by decide)) (by decide)
  rw [show (UInt256.ofNat 64).toNat = 64 from by decide, dispatchMemLoad64] at rd3
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    show (UInt256.ofNat 32).toNat = 32 from by decide] at rd3
  rw [toByteArray_write_read_back_of_gap _ _ 128
    (by rw [hmemsize]; exact lt_usize _ (by decide))] at rd3
  exact rd3

/-- `maxTick()`: the theorem `Correct.lean` routes selector 1 to. -/
theorem tickLibWrapperMaxTickBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = tickLibWrapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tickLibWrapperSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (tickLibWrapperSelBytes 1) rfl hsel
  have h0 : ¬ selIs I (tickLibWrapperSelBytes 0) := by
    intro h
    have h0e : tickLibWrapperSelBytes 0 = I.calldata.extract 0 4 :=
      byteArray_eq_of_beq h
    have h1e : tickLibWrapperSelBytes 1 = I.calldata.extract 0 4 :=
      byteArray_eq_of_beq hsel
    have heq : tickLibWrapperSelBytes 0 = tickLibWrapperSelBytes 1 := h0e.trans h1e.symm
    exact absurd heq (by decide)
  have hd : dispatchMsg contract I.calldata = some maxTickTransition :=
    tickLibWrapperDispatch_maxTick h0 hsel
  have hdec := maxTickDecode_ok hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · have hbody : ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ maxTickTransition.body
          (.returned
            { contract := contract,
              locals := (∅ : Store).insert "__calldata" (.bytes I.calldata) }
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [.int 6744])) := by
        have hb := maxTickBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (by simp only [initState]; exact hwv)
          (by simp only [initState]; exact hbig)
        simpa using hb
      exact (maxTickX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig hsel)
        |>.reEquivExecution hcode hd hdec hbody
          (returnEquiv_of_encode (uint256ReturnEncoding ⟨6744⟩))
    · rw [not_lt] at hbig
      have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩ := by
        rw [lnot3_add_returnSize hsz hsize]
        show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 0) ≠ ⟨0⟩
        have h1 : UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 0) = ⟨1⟩ :=
          slt_lit_one_high (a := UInt256.ofNat (I.calldata.size - 4)) (m := 0) (by norm_num)
            (by rw [ulit_toNat' _ (by omega)]; omega)
        rw [h1]; decide
      obtain ⟨_, _, rd⟩ := tickLibWrapperReachMaxTickBody (σ := σ) (σ₀ := σ₀) (A := A)
        (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
      have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_389_fallthrough (by simp) hwv rd
      have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_395_taken (by simp) hslt
        (by jump_dest) rd1
      have hrev := tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd2
      have hbody : ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ maxTickTransition.body .reverted := by
        rw [maxTickBody_eq]
        exact ExecFuncBody.execBlockRevert
          ((ABlock.start.requireStep
            (evalCallvalueEq_true (by simp only [initState]; exact hwv))).letStep
            (by simp only [evalExpr?, envValue, pure, initState])
            |>.requireRevert
              (evalCalldataLen_false
                (store_get_self (∅ : Store) "__calldata" (.bytes I.calldata)) hbig))
      exact hrev.reEquivExecutionRevert hcode hd hdec hbody
  · obtain ⟨_, _, rd⟩ := tickLibWrapperReachMaxTickBody (σ := σ) (σ₀ := σ₀) (A := A)
      (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_389_taken (by simp) hwv
      (by jump_dest) rd
    have hrev := tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd1
    have hbody : ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ maxTickTransition.body .reverted := by
      rw [maxTickBody_eq]
      exact bodyReverts_nonPayable (by simp only [initState]; exact hwv)
    exact hrev.reEquivExecutionRevert hcode hd hdec hbody

end Benchmarks.Midnight.TickLibWrapper
