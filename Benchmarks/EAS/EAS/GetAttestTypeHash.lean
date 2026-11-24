import Benchmarks.EAS.EAS.Entry

variable {fork : Ethereum.Fork}
/-! # EAS `getAttestTypeHash()` refinement -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

private def attestTypeHashWord : UInt256 :=
  UInt256.ofNat 0xdbfdf8dc2b135c26253e00d5b6cbe6f20457e003fd526d97cea183883570de61

private def attestTypeHashExpr : Expr :=
  .fixedBytesLit ⟨31, by decide⟩ (EVM.Word.toBytesBE attestTypeHashWord)

private def attestTypeHashValue : Value :=
  .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE attestTypeHashWord)

private theorem getAttestTypeHash_body :
    getAttestTypeHashTransition.body = easEntryPrefix ++ [.return [attestTypeHashExpr]] := by
  native_decide

theorem easGetAttestTypeHashBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 0)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 0) rfl hsel
  have hdec : config.externalABI.decodeCalldata?
      (getAttestTypeHashTransition.params.map Param.name)
      (transitionSignature getAttestTypeHashTransition).paramTypes I.calldata = some (∅ : Store) :=
    by
      change decodeCalldataWithMode Syntax.abiDecodeMode [] [] I.calldata = some (∅ : Store)
      exact decodeCalldataWithMode_empty_ok hsz
  obtain ⟨k, C, rd⟩ := easReachGetAttestTypeHashBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_4138_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases hs : I.calldata.size - 4 < 2^255
    · have rd2 := easBlocks.eas_block_4144_fallthrough (immWords := wordsOf (immStore v)) (by simp)
        (easCalldataSizeCheck_ok hsz hsize hs) rd1
      have hr := easBlocks.eas_block_4186 (immWords := wordsOf (immStore v)) (by simp) rd2
      have hout : RDret fork (deployedRuntime v) (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ attestTypeHashWord.toByteArray := by
        rw [show (UInt256.ofNat 32).toNat = 32 from rfl,
          ← Reasoning.Theory.writeWord, writeWord_sparse_read_back] at hr
        exact hr
      refine RDret.reEquivExecution
        (retVal := some [attestTypeHashValue])
        (cs := { contract := contract, locals := easEntryLocals ∅ I.calldata, immutables := immStore v })
        hcode hout (easDispatch_getAttestTypeHash hsel) hdec ?_ ?_
      · rw [getAttestTypeHash_body]
        apply easEntryBody_returns (value := attestTypeHashValue) hv hsz hsize hs
        simp only [attestTypeHashExpr, attestTypeHashValue, evalExpr?, pure]
      · exact returnEquiv_of_encode (bytes32ReturnEncoding attestTypeHashWord)
    · have rd2 := easBlocks.eas_block_4144_taken (immWords := wordsOf (immStore v)) (by simp)
        (easCalldataSizeCheck_revert hsz hsize hs)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      refine RDrev.reEquivExecutionRevert hcode hr (easDispatch_getAttestTypeHash hsel) hdec ?_
      rw [getAttestTypeHash_body]
      exact easEntryBody_size_revert hv hsz hsize hs
  · have rd1 := easBlocks.eas_block_4138_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    refine RDrev.reEquivExecutionRevert hcode hr (easDispatch_getAttestTypeHash hsel) hdec ?_
    rw [getAttestTypeHash_body]
    exact easEntryBody_value_revert hv

end Benchmarks.EAS.EAS
