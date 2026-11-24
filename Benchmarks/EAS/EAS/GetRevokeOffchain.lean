import Benchmarks.EAS.EAS.ScalarDecode
import Benchmarks.EAS.EAS.Storage

variable {fork : Ethereum.Fork}

/-! # EAS `getRevokeOffchain(address,bytes32)` refinement -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem getRevokeOffchain_body : getRevokeOffchainTransition.body =
    easEntryPrefix ++ [.return [.storage offchainRef]] := by
  native_decide

theorem getRevokeOffchainEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 4 ≤ 1024) (hcanon : word.toNat < EVM.addressModulus)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨2496⟩ (word :: solcAddrMask :: R) mem aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ
      (UInt256.land (solcSlotWord σ ee (offchainSlot word (calldataWord ee.calldata 36))) easUint64Mask).toByteArray := by
  have hr := easBlocks.eas_block_2496 (immWords := wordsOf (immStore v)) hstack rd
  rw [solcAddrMask_clean hcanon] at hr
  rw [show (UInt256.ofNat 32).toNat = 32 from rfl,
    ← Reasoning.Theory.writeWord, writeWord_sparse_read_back] at hr
  change RDret fork _ _ _ _
    (UInt256.land (solcSlotWord σ ee (UInt256.ofNat (fromByteArrayBigEndian
      (KEC ((twoWordHashMem (calldataWord ee.calldata 36)
        (UInt256.ofNat (fromByteArrayBigEndian (KEC ((twoWordHashMem word ⟨3⟩ mem).readWithPadding 0 64))))
        (twoWordHashMem word ⟨3⟩ mem)).readWithPadding 0 64))))) easUint64Mask).toByteArray at hr
  rw [twoWordHashMem_solcMappingSlot_any, twoWordHashMem_solcMappingSlot_any] at hr
  exact hr

theorem easGetRevokeOffchainBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 9)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 9) rfl hsel
  have hd : dispatchMsg contract I.calldata = some getRevokeOffchainTransition := by
    apply easDispatch_getRevokeOffchain (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  obtain ⟨k, C, rd⟩ := easReachGetRevokeOffchainBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_2420_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases h68 : 68 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2^255 + 4
      · have rd2 := easBlocks.eas_block_2426_fallthrough (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]; exact solcDecodeLenCheckOk_4_64 h68 hbig hsize) rd1
        have rd3 := easBlocks.eas_block_2468 (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · let a := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
          let word := calldataWord I.calldata 36
          let args := ((∅ : Store).insert "revoker" (.address a)).insert "data"
            (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))
          let value := UInt256.land (solcSlotWord σ I
            (offchainSlot (calldataWord I.calldata 4) word)) easUint64Mask
          have hdec : config.externalABI.decodeCalldata?
              (getRevokeOffchainTransition.params.map Param.name)
              (transitionSignature getRevokeOffchainTransition).paramTypes I.calldata = some args :=
            easDecodeAddressBytes32_ok "revoker" "data" h68 hbig hsize hc
          obtain ⟨k4, C4, rd4⟩ := easDecodeAddressEVM_ok v (by simp) hc
            (by rw [easPatchedValidJumps v]; jump_dest) rd3
          have hout := getRevokeOffchainEVM v (by simp) hc rd4
          have hworda : keyValueToWord (.address a) = calldataWord I.calldata 4 :=
            keyValueToWord_address_of_canonical _ hc
          refine RDret.reEquivExecution
            (retVal := some [.int (Int.ofNat value.toNat)])
            (cs := { contract := contract
                     locals := easEntryLocals args I.calldata
                     immutables := immStore v }) hcode hout hd hdec ?_ ?_
          · rw [getRevokeOffchain_body]
            apply easEntryBody_returns hv hsz hsize (by change I.calldata.size - 4 < 2^255; omega)
            have hread := offchain_read (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (locals := easEntryLocals args I.calldata) (imms := immStore v) (revoker := a) (word := word)
              (by simp only [args, easEntryLocals,
                    store_get_ne _ _ (by decide : ("__calldata" == "_revocationsOffchain") = false),
                    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "_revocationsOffchain") = false),
                    store_get_ne _ _ (by decide : ("data" == "_revocationsOffchain") = false),
                    store_get_ne _ _ (by decide : ("revoker" == "_revocationsOffchain") = false), store_get_empty])
              (by simp only [args, easEntryLocals,
                    store_get_ne _ _ (by decide : ("__calldata" == "revoker") = false),
                    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "revoker") = false),
                    store_get_ne _ _ (by decide : ("data" == "revoker") = false), store_get_self])
              (by simp only [args, easEntryLocals,
                    store_get_ne _ _ (by decide : ("__calldata" == "data") = false),
                    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "data") = false), store_get_self])
            simpa only [offchainWord, hworda] using hread
          · exact returnEquiv_of_encode (uintReturnEncoding ⟨64, by decide⟩ value
              (u256LandMaskToNatLtOfToNat _ _ (by decide)))
        · have hr := easDecodeAddressEVM_revert v (by simp) hc rd3
          exact RDrev.reEquivDecodingFailed hcode hr hd
            (easDecodeAddressBytes32_none_noncanon "revoker" "data" h68 hbig hsize hc)
      · have rd2 := easBlocks.eas_block_2426_taken (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]
              exact ne_of_eq_of_ne (solcDecodeLenCheckHuge_4_64 (by omega) hsize) (by decide))
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
        exact RDrev.reEquivDecodingFailed hcode hr hd
          (easDecodePair_none_huge "revoker" "data" .address (.bytes abiBytes32Width) (by omega) hsize)
    · have rd2 := easBlocks.eas_block_2426_taken (immWords := wordsOf (immStore v)) (by simp)
        (by rw [easCalldataSub4 hsz hsize]
            exact ne_of_eq_of_ne (solcDecodeLenCheckShort_4_64 hsz (by omega) hsize) (by decide))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      exact RDrev.reEquivDecodingFailed hcode hr hd
        (easDecodePair_none_short "revoker" "data" .address (.bytes abiBytes32Width) hsz (by omega) hsize)
  · have rd1 := easBlocks.eas_block_2420_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata?
        (getRevokeOffchainTransition.params.map Param.name)
        (transitionSignature getRevokeOffchainTransition).paramTypes I.calldata with
    | none => exact RDrev.reEquivDecodingFailed hcode hr hd hdec
    | some args =>
      refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
      rw [getRevokeOffchain_body]
      exact easEntryBody_value_revert hv

end Benchmarks.EAS.EAS
