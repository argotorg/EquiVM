import Benchmarks.EAS.EAS.GetAttestationEVM
import Benchmarks.EAS.EAS.ScalarDecode

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easGetAttestationBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 8)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 8) rfl hsel
  have hd : dispatchMsg contract I.calldata = some getAttestationTransition := by
    apply easDispatch_getAttestation (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  obtain ⟨k, C, rd⟩ := easReachGetAttestationBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_2545_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases h36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2^255 + 4
      · have rd2 := easBlocks.eas_block_2551_fallthrough (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]; exact solcDecodeLenCheckOk_4_32 h36 hbig hsize) rd1
        let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
        let word := calldataWord I.calldata 4
        let args := (∅ : Store).insert "uid" (wordBytes32Value word)
        have hdec : config.externalABI.decodeCalldata?
            (getAttestationTransition.params.map Param.name)
            (transitionSignature getAttestationTransition).paramTypes I.calldata = some args :=
          easDecodeBytes32_ok "uid" h36 hbig hsize
        have hr := getAttestationEVM (evm := evm) v (by simp) (by native_decide) rd2
        have henv : evm.executionEnv = I := rfl
        rw [henv] at hr
        by_cases hcopy : copyStoredValid evm word 544
        · rw [if_pos hcopy] at hr
          refine RDret.reEquivExecution
            (retVal := some [getAttestationTuple evm word])
            (cs := {
              contract := contract
              locals := getAttestationFinalLocals (getAttestationPrefixLocals args evm) evm word
              immutables := immStore v }) hcode hr hd hdec ?_ ?_
          · exact getAttestationSource_ok (store_get_self _ _ _) hv hsz hsize (by change I.calldata.size-4 < 2^255; omega) hcopy
          · exact returnEquiv_of_encode (attestationReturnEncoding evm word)
        · rw [if_neg hcopy] at hr
          exact RDrev.reEquivExecutionRevert hcode hr hd hdec
            (getAttestationSource_revert (store_get_self _ _ _) hv hsz hsize (by change I.calldata.size-4 < 2^255; omega) hcopy)
      · have rd2 := easBlocks.eas_block_2551_taken (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]
              exact ne_of_eq_of_ne (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by decide))
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
        exact RDrev.reEquivDecodingFailed hcode hr hd
          (easDecodeScalar_none_huge "uid" (.bytes abiBytes32Width) (by omega) hsize)
    · have rd2 := easBlocks.eas_block_2551_taken (immWords := wordsOf (immStore v)) (by simp)
        (by rw [easCalldataSub4 hsz hsize]
            exact ne_of_eq_of_ne (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by decide))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      exact RDrev.reEquivDecodingFailed hcode hr hd
        (easDecodeScalar_none_short "uid" (.bytes abiBytes32Width) hsz (by omega) hsize)
  · have rd1 := easBlocks.eas_block_2545_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata?
        (getAttestationTransition.params.map Param.name)
        (transitionSignature getAttestationTransition).paramTypes I.calldata with
    | none => exact RDrev.reEquivDecodingFailed hcode hr hd hdec
    | some args =>
      refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
      rw [getAttestation_body]
      exact easEntryBody_value_revert hv

end Benchmarks.EAS.EAS
