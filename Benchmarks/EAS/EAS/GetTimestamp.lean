import Benchmarks.EAS.EAS.ScalarDecode
import Benchmarks.EAS.EAS.Storage

variable {fork : Ethereum.Fork}

/-! # EAS `getTimestamp(bytes32)` refinement -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem getTimestamp_body : getTimestampTransition.body = easEntryPrefix ++ [.return [.storage timestampRef]] := by
  native_decide

theorem getTimestampEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2222⟩ R mem aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ
      (UInt256.land (solcSlotWord σ ee (timestampSlot (calldataWord ee.calldata 4))) easUint64Mask).toByteArray := by
  have hr := easBlocks.eas_block_2222 (immWords := wordsOf (immStore v)) hstack rd
  rw [show (UInt256.ofNat 32).toNat = 32 from rfl,
    ← Reasoning.Theory.writeWord, writeWord_sparse_read_back] at hr
  change RDret fork _ _ _ _
    (UInt256.land (solcSlotWord σ ee (UInt256.ofNat (fromByteArrayBigEndian
      (KEC ((twoWordHashMem (calldataWord ee.calldata 4) ⟨2⟩ mem).readWithPadding 0 64))))) easUint64Mask).toByteArray at hr
  rw [twoWordHashMem_solcMappingSlot_any] at hr
  exact hr

theorem easGetTimestampBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 12)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 12) rfl hsel
  have hd : dispatchMsg contract I.calldata = some getTimestampTransition := by
    apply easDispatch_getTimestamp (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  obtain ⟨k, C, rd⟩ := easReachGetTimestampBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_2174_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases h36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2^255 + 4
      · have rd2 := easBlocks.eas_block_2180_fallthrough (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]; exact solcDecodeLenCheckOk_4_32 h36 hbig hsize) rd1
        have hout := getTimestampEVM v (by simp) rd2
        have hdec : config.externalABI.decodeCalldata?
            (getTimestampTransition.params.map Param.name)
            (transitionSignature getTimestampTransition).paramTypes I.calldata =
            some ((∅ : Store).insert "data"
              (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE (calldataWord I.calldata 4)))) :=
          easDecodeBytes32_ok "data" h36 hbig hsize
        let word := calldataWord I.calldata 4
        let value := UInt256.land (solcSlotWord σ I (timestampSlot word)) easUint64Mask
        refine RDret.reEquivExecution
          (retVal := some [.int (Int.ofNat value.toNat)])
          (cs := { contract := contract
                   locals := easEntryLocals ((∅ : Store).insert "data"
                     (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) I.calldata
                   immutables := immStore v }) hcode hout hd hdec ?_ ?_
        · rw [getTimestamp_body]
          apply easEntryBody_returns hv hsz hsize (by change I.calldata.size - 4 < 2^255; omega)
          have hread := timestamp_read (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (locals := easEntryLocals ((∅ : Store).insert "data"
              (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) I.calldata)
            (imms := immStore v) (word := word)
            (by simp only [easEntryLocals,
                  store_get_ne _ _ (by decide : ("__calldata" == "_timestamps") = false),
                  store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "_timestamps") = false),
                  store_get_ne _ _ (by decide : ("data" == "_timestamps") = false), store_get_empty])
            (by simp only [easEntryLocals,
                  store_get_ne _ _ (by decide : ("__calldata" == "data") = false),
                  store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "data") = false), store_get_self])
          exact hread
        · exact returnEquiv_of_encode (uintReturnEncoding ⟨64, by decide⟩ value
            (u256LandMaskToNatLtOfToNat _ _ (by decide)))
      · have rd2 := easBlocks.eas_block_2180_taken (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]
              exact ne_of_eq_of_ne (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by decide))
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
        exact RDrev.reEquivDecodingFailed hcode hr hd
          (easDecodeScalar_none_huge "data" (.bytes abiBytes32Width) (by omega) hsize)
    · have rd2 := easBlocks.eas_block_2180_taken (immWords := wordsOf (immStore v)) (by simp)
        (by rw [easCalldataSub4 hsz hsize]
            exact ne_of_eq_of_ne (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by decide))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      exact RDrev.reEquivDecodingFailed hcode hr hd
        (easDecodeScalar_none_short "data" (.bytes abiBytes32Width) hsz (by omega) hsize)
  · have rd1 := easBlocks.eas_block_2174_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata?
        (getTimestampTransition.params.map Param.name)
        (transitionSignature getTimestampTransition).paramTypes I.calldata with
    | none => exact RDrev.reEquivDecodingFailed hcode hr hd hdec
    | some args =>
      refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
      rw [getTimestamp_body]
      exact easEntryBody_value_revert hv

end Benchmarks.EAS.EAS
