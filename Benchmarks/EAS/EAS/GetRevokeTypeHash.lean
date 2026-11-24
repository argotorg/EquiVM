import Benchmarks.EAS.EAS.Entry

variable {fork : Ethereum.Fork}
/-! # EAS `getRevokeTypeHash()` refinement -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

private def revokeTypeHashWord : UInt256 :=
  UInt256.ofNat 0xa98d02348410c9c76735e0d0bb1396f4015ac2bb9615f9c2611d19d7a8a99650

private def revokeTypeHashExpr : Expr :=
  .fixedBytesLit ⟨31, by decide⟩ (EVM.Word.toBytesBE revokeTypeHashWord)

private def revokeTypeHashValue : Value :=
  .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE revokeTypeHashWord)

private theorem getRevokeTypeHash_body :
    getRevokeTypeHashTransition.body = easEntryPrefix ++ [.return [revokeTypeHashExpr]] := by
  native_decide

theorem easGetRevokeTypeHashBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 10)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 10) rfl hsel
  have hd : dispatchMsg contract I.calldata = some getRevokeTypeHashTransition := by
    apply easDispatch_getRevokeTypeHash (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  have hdec : config.externalABI.decodeCalldata?
      (getRevokeTypeHashTransition.params.map Param.name)
      (transitionSignature getRevokeTypeHashTransition).paramTypes I.calldata = some (∅ : Store) :=
    by
      change decodeCalldataWithMode Syntax.abiDecodeMode [] [] I.calldata = some (∅ : Store)
      exact decodeCalldataWithMode_empty_ok hsz
  obtain ⟨k, C, rd⟩ := easReachGetRevokeTypeHashBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_2331_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases hs : I.calldata.size - 4 < 2^255
    · have rd2 := easBlocks.eas_block_2337_fallthrough (immWords := wordsOf (immStore v)) (by simp)
        (easCalldataSizeCheck_ok hsz hsize hs) rd1
      have hr := easBlocks.eas_block_2379 (immWords := wordsOf (immStore v)) (by simp) rd2
      have hout : RDret fork (deployedRuntime v) (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ revokeTypeHashWord.toByteArray := by
        rw [show (UInt256.ofNat 32).toNat = 32 from rfl,
          ← Reasoning.Theory.writeWord, writeWord_sparse_read_back] at hr
        exact hr
      refine RDret.reEquivExecution
        (retVal := some [revokeTypeHashValue])
        (cs := { contract := contract, locals := easEntryLocals ∅ I.calldata, immutables := immStore v })
        hcode hout hd hdec ?_ ?_
      · rw [getRevokeTypeHash_body]
        apply easEntryBody_returns (value := revokeTypeHashValue) hv hsz hsize hs
        simp only [revokeTypeHashExpr, revokeTypeHashValue, evalExpr?, pure]
      · exact returnEquiv_of_encode (bytes32ReturnEncoding revokeTypeHashWord)
    · have rd2 := easBlocks.eas_block_2337_taken (immWords := wordsOf (immStore v)) (by simp)
        (easCalldataSizeCheck_revert hsz hsize hs)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
      rw [getRevokeTypeHash_body]
      exact easEntryBody_size_revert hv hsz hsize hs
  · have rd1 := easBlocks.eas_block_2331_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
    rw [getRevokeTypeHash_body]
    exact easEntryBody_value_revert hv

end Benchmarks.EAS.EAS
