import Benchmarks.Midnight.TickLibWrapper.Dispatch
import Benchmarks.Midnight.TickLibWrapper.MaxTick

/-!
# TickLibWrapper `lnOnePlusDelta()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 135; reach lemma `tickLibWrapperReachLnOnePlusDeltaBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight.TickLibWrapper

set_option maxRecDepth 2000000

/-- `lnOnePlusDelta()`'s spec body: nonpayable guard, calldata-size guard, `return LN`. -/
theorem lnOnePlusDeltaBody_eq : lnOnePlusDeltaTransition.body =
    [.require (.binary .eq (.env .callvalue) (.intLit 0)),
     .letDecl "__calldata" (some .bytes) (.env .msgData),
     .require (.binary .lt
        (.arrayLength .localVar { base := "__calldata", steps := [] })
        (.intLit 57896044618658097711785492504343953926634992332820282019728792003956564819972)),
     .return [.intLit 4987541511039073]] := by
  rfl

/-- `lnOnePlusDelta()`'s calldata decodes to the empty store whenever it is at least a selector. -/
theorem lnOnePlusDeltaDecode_ok {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size) :
    config.externalABI.decodeCalldata? (lnOnePlusDeltaTransition.params.map Param.name)
      (transitionSignature lnOnePlusDeltaTransition).paramTypes I.calldata = some ∅ := by
  change decodeCalldataWithMode .modern [] [] I.calldata = some (∅ : Store)
  exact decodeCalldataWithMode_empty_ok hsz4

/-- The `int256` return encoding of `4987541511039073` is its word's 32 big-endian bytes. -/
theorem lnOnePlusDeltaReturnEncoding :
    encodeReturnValue? (.elem (.int (.sint ⟨256, by decide⟩))) (.int 4987541511039073)
      = some (UInt256.toByteArray ⟨4987541511039073⟩) := by
  native_decide

/-- The Stele `lnOnePlusDelta()` body returns `LN` (callvalue `0`, calldata under the bound). -/
theorem lnOnePlusDeltaBodyReturns (evm : EVM.State)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm ∅ lnOnePlusDeltaTransition.body
      (.returned
        { contract := contract,
          locals := (∅ : Store).insert "__calldata" (.bytes evm.executionEnv.calldata) }
        evm (some [.int 4987541511039073])) := by
  rw [lnOnePlusDeltaBody_eq]
  refine ExecFuncBody.execBlockRet
    ((ABlock.start.requireStep (evalCallvalueEq_true hwv)).letStep ?_ |>.requireStep ?_
      |>.returns ?_)
  · simp only [evalExpr?, envValue, pure]
  · exact evalCalldataLen_true
      (store_get_self (∅ : Store) "__calldata" (.bytes evm.executionEnv.calldata)) hlen
  · simp only [evalExpr?, pure]

/-- The success EVM trace: arm → callvalue guard → length guard → `PUSH7 LN; …; RETURN`. -/
theorem lnOnePlusDeltaX_ok {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = tickLibWrapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsel : selIs I (tickLibWrapperSelBytes 4)) :
    RDret tickLibWrapperBytecode g (initState σ σ₀ g A I) σ
      (UInt256.toByteArray ⟨4987541511039073⟩) := by
  have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨0⟩ = ⟨0⟩ := by
    rw [lnot3_add_returnSize hsz4 hsize]
    show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 0) = ⟨0⟩
    exact slt_ofNat_lit_zero (by norm_num) (by omega) (by omega)
  obtain ⟨_, _, rd⟩ := tickLibWrapperReachLnOnePlusDeltaBody (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsz4 hsize hsel
  have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_135_fallthrough (by simp) hwv rd
  have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_141_fallthrough (by simp) hslt rd1
  have rd3 := tickLibWrapperBlocks.tickLibWrapper_block_152 (by simp) rd2
  have hmemsize : ((UInt256.ofNat 128).toByteArray.write 0 ByteArray.empty 64 32).size = 96 :=
    toByteArray_write32_size_of_ge _ _ 64 0 96 (by decide) (by omega)
      (lt_usize _ (by decide)) (by decide)
  rw [show (UInt256.ofNat 64).toNat = 64 from by decide, dispatchMemLoad64] at rd3
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
    show (UInt256.ofNat 32).toNat = 32 from by decide] at rd3
  rw [toByteArray_write_read_back_of_gap _ _ 128
    (by rw [hmemsize]; exact lt_usize _ (by decide))] at rd3
  exact rd3

/-- `lnOnePlusDelta()`: the theorem `Correct.lean` routes selector 4 to. -/
theorem tickLibWrapperLnOnePlusDeltaBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = tickLibWrapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tickLibWrapperSelBytes 4)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (tickLibWrapperSelBytes 4) rfl hsel
  have hdist (i : ℕ) (hi : i < 4) : ¬ selIs I (tickLibWrapperSelBytes i) := by
    intro h
    have h0e : tickLibWrapperSelBytes i = I.calldata.extract 0 4 := byteArray_eq_of_beq h
    have h1e : tickLibWrapperSelBytes 4 = I.calldata.extract 0 4 := byteArray_eq_of_beq hsel
    have heq : tickLibWrapperSelBytes i = tickLibWrapperSelBytes 4 := h0e.trans h1e.symm
    interval_cases i <;> exact absurd heq (by decide)
  have hd : dispatchMsg contract I.calldata = some lnOnePlusDeltaTransition :=
    tickLibWrapperDispatch_lnOnePlusDelta (hdist 0 (by omega)) (hdist 1 (by omega))
      (hdist 2 (by omega)) (hdist 3 (by omega)) hsel
  have hdec := lnOnePlusDeltaDecode_ok hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · have hbody : ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ lnOnePlusDeltaTransition.body
          (.returned
            { contract := contract,
              locals := (∅ : Store).insert "__calldata" (.bytes I.calldata) }
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (some [.int 4987541511039073])) := by
        have hb := lnOnePlusDeltaBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (by simp only [initState]; exact hwv)
          (by simp only [initState]; exact hbig)
        simpa using hb
      exact (lnOnePlusDeltaX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hbig hsel)
        |>.reEquivExecution hcode hd hdec hbody
          (returnEquiv_of_encode lnOnePlusDeltaReturnEncoding)
    · rw [not_lt] at hbig
      have hslt : UInt256.slt ((UInt256.lnot ⟨3⟩) + UInt256.ofNat I.calldata.size) ⟨0⟩ ≠ ⟨0⟩ := by
        rw [lnot3_add_returnSize hsz hsize]
        show UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 0) ≠ ⟨0⟩
        have h1 : UInt256.slt (UInt256.ofNat (I.calldata.size - 4)) (UInt256.ofNat 0) = ⟨1⟩ :=
          slt_lit_one_high (a := UInt256.ofNat (I.calldata.size - 4)) (m := 0) (by norm_num)
            (by rw [ulit_toNat' _ (by omega)]; omega)
        rw [h1]; decide
      obtain ⟨_, _, rd⟩ := tickLibWrapperReachLnOnePlusDeltaBody (σ := σ) (σ₀ := σ₀) (A := A)
        (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
      have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_135_fallthrough (by simp) hwv rd
      have rd2 := tickLibWrapperBlocks.tickLibWrapper_block_141_taken (by simp) hslt
        (by jump_dest) rd1
      have hrev := tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd2
      have hbody : ExecTransitionBody config contract
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ lnOnePlusDeltaTransition.body .reverted := by
        rw [lnOnePlusDeltaBody_eq]
        exact ExecFuncBody.execBlockRevert
          ((ABlock.start.requireStep
            (evalCallvalueEq_true (by simp only [initState]; exact hwv))).letStep
            (by simp only [evalExpr?, envValue, pure, initState])
            |>.requireRevert
              (evalCalldataLen_false
                (store_get_self (∅ : Store) "__calldata" (.bytes I.calldata)) hbig))
      exact hrev.reEquivExecutionRevert hcode hd hdec hbody
  · obtain ⟨_, _, rd⟩ := tickLibWrapperReachLnOnePlusDeltaBody (σ := σ) (σ₀ := σ₀) (A := A)
      (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have rd1 := tickLibWrapperBlocks.tickLibWrapper_block_135_taken (by simp) hwv
      (by jump_dest) rd
    have hrev := tickLibWrapperBlocks.tickLibWrapper_block_131 (by simp) rd1
    have hbody : ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ lnOnePlusDeltaTransition.body .reverted := by
      rw [lnOnePlusDeltaBody_eq]
      exact bodyReverts_nonPayable (by simp only [initState]; exact hwv)
    exact hrev.reEquivExecutionRevert hcode hd hdec hbody

end Benchmarks.Midnight.TickLibWrapper
