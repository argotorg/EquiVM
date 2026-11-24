import Benchmarks.EAS.EAS.Entry

variable {fork : Ethereum.Fork}
/-! # EAS `getSchemaRegistry()` refinement -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

private theorem getSchemaRegistry_body :
    getSchemaRegistryTransition.body = easEntryPrefix ++ [.return [.immutable "_schemaRegistry"]] := by
  native_decide

theorem easGetSchemaRegistryBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 19)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 19) rfl hsel
  have hd : dispatchMsg contract I.calldata = some getSchemaRegistryTransition := by
    apply easDispatch_getSchemaRegistry (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  have hdec : config.externalABI.decodeCalldata?
      (getSchemaRegistryTransition.params.map Param.name)
      (transitionSignature getSchemaRegistryTransition).paramTypes I.calldata = some (∅ : Store) :=
    by
      change decodeCalldataWithMode Syntax.abiDecodeMode [] [] I.calldata = some (∅ : Store)
      exact decodeCalldataWithMode_empty_ok hsz
  obtain ⟨k, C, rd⟩ := easReachGetSchemaRegistryBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_603_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases hs : I.calldata.size - 4 < 2^255
    · have rd2 := easBlocks.eas_block_609_fallthrough (immWords := wordsOf (immStore v)) (by simp)
        (easCalldataSizeCheck_ok hsz hsize hs) rd1
      have hr := easBlocks.eas_block_651 (immWords := wordsOf (immStore v)) (by simp) rd2
      have hout : RDret fork (deployedRuntime v) (Sat256.ofUInt256 g)
          (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ (UInt256.ofNat v._schemaRegistry.toNat).toByteArray := by
        rw [show (UInt256.ofNat 32).toNat = 32 from rfl,
          ← Reasoning.Theory.writeWord, writeWord_sparse_read_back] at hr
        rw [wordsOf_immStore__schemaRegistry] at hr
        change RDret fork _ _ _ _ (UInt256.land (EVM.word v._schemaRegistry.val) solcAddrMask).toByteArray at hr
        rw [addressWord_val_clean] at hr
        exact hr
      refine RDret.reEquivExecution
        (retVal := some [.address v._schemaRegistry])
        (cs := { contract := contract, locals := easEntryLocals ∅ I.calldata, immutables := immStore v })
        hcode hout hd hdec ?_ ?_
      · rw [getSchemaRegistry_body]
        exact easEntryBody_returns hv hsz hsize hs (evalImmutable__schemaRegistry _ _ _ _ v)
      · apply returnEquiv.returned rfl
        exact scalarReturnEncoding (t := .address) rfl
          (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]; decide)
          (by simp only [encodeABIValue?, encodeABIWord?]; rfl)
    · have rd2 := easBlocks.eas_block_609_taken (immWords := wordsOf (immStore v)) (by simp)
        (easCalldataSizeCheck_revert hsz hsize hs)
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
      rw [getSchemaRegistry_body]
      exact easEntryBody_size_revert hv hsz hsize hs
  · have rd1 := easBlocks.eas_block_603_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
    rw [getSchemaRegistry_body]
    exact easEntryBody_value_revert hv

end Benchmarks.EAS.EAS
