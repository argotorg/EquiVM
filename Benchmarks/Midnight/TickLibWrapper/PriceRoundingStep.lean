import Benchmarks.Midnight.TickLibWrapper.Dispatch
import Benchmarks.Midnight.TickLibWrapper.MaxTick

/-!
# TickLibWrapper `priceRoundingStep()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 417 — the first-compared selector (`0x00b6da9b`) takes
`tickLibWrapper_block_18_taken`; the skeleton did not emit a reach lemma for it, so one is
proved here (`tickLibWrapperReachPriceRoundingStepBody`).
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight.TickLibWrapper

set_option maxRecDepth 2000000

/-- `priceRoundingStep()`'s spec body: nonpayable guard, calldata-size guard, `return 1e11`. -/
theorem priceRoundingStepBody_eq : priceRoundingStepTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .letDecl "__calldata" (some .bytes) (.env .msgData),
     .require (.binary .lt
        (.arrayLength .localVar { base := "__calldata", steps := [] })
        (.intLit 57896044618658097711785492504343953926634992332820282019728792003956564819972)),
     .return [.intLit 100000000000]] := by
  rfl

/-- `priceRoundingStep()`'s calldata decodes to the empty store whenever it is at least a
    selector. -/
theorem priceRoundingStepDecode_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (priceRoundingStepTransition.params.map Param.name)
      (transitionSignature priceRoundingStepTransition).paramTypes I.calldata = some ∅ := by
  change decodeCalldataWithMode .modern [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- Dispatcher path to `priceRoundingStep()` (arm entry pc 417): prologue → first selector
    compare taken.  The skeleton left this arm without a reach lemma (see `Dispatch.lean`). -/
theorem tickLibWrapperReachPriceRoundingStepBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tickLibWrapperSelBytes 0)) :
    ∃ k C, RD (tickLibWrapperBytecode) I g (initState σ σ₀ g A I) (UInt256.ofNat 417)
      [(UInt256.ofNat 128),
       (UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes (⟨0⟩ : UInt256).toNat 32))
         (UInt256.ofNat 224))]
      ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty (UInt256.ofNat 64).toNat 32)
      (M (UInt256.ofNat 0) (UInt256.ofNat 64) (⟨32⟩ : UInt256)) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨11983515⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x00 0xb6 0xda 0x9b ⟨11983515⟩ (by native_decide)
      (by simpa [tickLibWrapperSelBytes] using hsel)
  have rd0 := RD.initState (g := g) (σ := σ) (σ₀ := σ₀) (A := A) hcode
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_0_taken (by simp)
    (by rw [lt_four_eq_zero_of_ge hsz hsize]; decide) (by jump_dest) rd0
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_18_taken
    (by simp)
    (by simpa [solcSelectorWord] using
      (show (UInt256.eq ⟨11983515⟩ (solcSelectorWord I)) ≠ ⟨0⟩ by
        rw [hword]; native_decide))
    (by jump_dest) rd1
  exact ⟨_, _, by simpa [tickLibWrapperBlocks.tickLibWrapper_block_0_taken_stack,
    tickLibWrapperBlocks.tickLibWrapper_block_0_taken_memory,
    tickLibWrapperBlocks.tickLibWrapper_block_18_taken_stack] using rd2⟩

/-- The Stele `priceRoundingStep()` body returns `1e11` (callvalue `0`, calldata under bound). -/
theorem priceRoundingStepBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm ∅ priceRoundingStepTransition.body
      (.returned
        { contract := contract,
          locals := (∅ : Store).insert "__calldata" (.bytes evm.executionEnv.calldata) }
        evm (some [.int 100000000000])) := by
  rw [priceRoundingStepBody_eq]
  refine ExecFuncBody.execBlockRet
    ((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep ?_ |>.requireStep ?_
      |>.returns ?_)
  · simp only [evalExpr?, envValue, pure]
  · exact evalCalldataLen_true
      (store_get_self (∅ : Store) "__calldata" (.bytes evm.executionEnv.calldata)) hlen
  · simp only [evalExpr?, pure]

/-- The success EVM trace: arm → callvalue guard → length guard → `PUSH5 1e11; …; RETURN`. -/
theorem priceRoundingStepX_ok {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsel : selIs I (tickLibWrapperSelBytes 0)) :
    RDret tickLibWrapperBytecode g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray ⟨100000000000⟩) := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨0⟩ = ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 0) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachPriceRoundingStepBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_417_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_423_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_434 (by simp) rd2
  have hmemsize : ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty 64 32).size = 96 :=
    toByteArray_write32_size_of_ge _ _ 64 0 96 (by decide) (by omega)
      (lt_usize _ (by decide)) (by decide)
  rw [show (UInt256.ofNat 64).toNat = 64 from by decide,
    show (UInt256.ofNat 128).toNat = 128 from by decide,
    show (UInt256.ofNat 32).toNat = 32 from by decide] at rd3
  rw [toByteArray_write_read_back_of_gap _ _ 128
    (by rw [hmemsize]; exact lt_usize _ (by decide))] at rd3
  exact rd3

/-- `priceRoundingStep()`: the theorem `Correct.lean` routes selector 0 to. -/
theorem tickLibWrapperPriceRoundingStepBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = tickLibWrapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tickLibWrapperSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (tickLibWrapperSelBytes 0) rfl hsel
  have hd : dispatchMsg contract I.calldata = some priceRoundingStepTransition :=
    tickLibWrapperDispatch_priceRoundingStep hsel
  have hdec := priceRoundingStepDecode_ok hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · have hbody : ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ priceRoundingStepTransition.body
          (.returned
            { contract := contract,
              locals := (∅ : Store).insert "__calldata" (.bytes I.calldata) }
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (some [.int 100000000000])) := by
        have hb := priceRoundingStepBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (by simp only [initState]; exact hwv)
          (by simp only [initState]; exact hbig)
        simpa using hb
      exact (priceRoundingStepX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig hsel)
        |>.reEquivExecution hcode hd hdec hbody
          (returnEquiv_of_encode (uint256ReturnEncoding ⟨100000000000⟩))
    · rw [not_lt] at hbig
      have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩ := by
        rw [lnot3_add_returnSize hsz hsize]
        show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 0) ≠ ⟨0⟩
        have h1 : UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 0) = ⟨1⟩ :=
          slt_lit_one_high (a := UInt256.ofNat (I.calldata.size - 4)) (m := 0) (by norm_num)
            (by rw [ulit_toNat' _ (by omega)]; omega)
        rw [h1]; decide
      obtain ⟨_, _, rd⟩ := tickLibWrapperReachPriceRoundingStepBody (σ := σ) (σ₀ := σ₀) (A := A)
        (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
      have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_417_fallthrough (by simp) hwv rd
      have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_423_taken (by simp) hslt
        (by jump_dest) rd1
      have hrev := tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd2
      have hbody : ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ priceRoundingStepTransition.body
            .reverted := by
        rw [priceRoundingStepBody_eq]
        exact ExecFuncBody.execBlockRevert
          ((ABlock.start.requireStep
            (evalCallvalueEq_true (by simp only [initState]; exact hwv))).letStep
            (by simp only [evalExpr?, envValue, pure, initState])
            |>.requireRevert
              (evalCalldataLen_false
                (store_get_self (∅ : Store) "__calldata" (.bytes I.calldata)) hbig))
      exact hrev.reEquivExecutionRevert hcode hd hdec hbody
  · obtain ⟨_, _, rd⟩ := tickLibWrapperReachPriceRoundingStepBody (σ := σ) (σ₀ := σ₀) (A := A)
      (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_417_taken (by simp) hwv
      (by jump_dest) rd
    have hrev := tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd1
    have hbody : ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ priceRoundingStepTransition.body
          .reverted := by
      rw [priceRoundingStepBody_eq]
      exact bodyReverts_nonPayable (by simp only [initState]; exact hwv)
    exact hrev.reEquivExecutionRevert hcode hd hdec hbody

end Benchmarks.Midnight.TickLibWrapper
