import Benchmarks.EAS.EAS.ScalarDecode
import Benchmarks.EAS.EAS.Storage

variable {fork : Ethereum.Fork}

/-! # EAS `getNonce(address)` refinement -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem getNonce_body : getNonceTransition.body = easEntryPrefix ++ [.return [.storage nonceRef]] := by
  native_decide

theorem getNonceEVM {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {word : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 4 ≤ 1024) (hcanon : word.toNat < EVM.addressModulus)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨3969⟩ (word :: solcAddrMask :: R) mem aw rdata σ k C) :
    RDret fork (deployedRuntime v) g s0 σ (solcSlotWord σ ee (solcMappingSlot ⟨0⟩ word)).toByteArray := by
  have hr := easBlocks.eas_block_3969 (immWords := wordsOf (immStore v)) hstack rd
  rw [solcAddrMask_clean hcanon] at hr
  rw [show (UInt256.ofNat 32).toNat = 32 from rfl,
    ← Reasoning.Theory.writeWord, writeWord_sparse_read_back] at hr
  change RDret fork _ _ _ _
    (solcSlotWord σ ee (UInt256.ofNat (fromByteArrayBigEndian
      (KEC ((twoWordHashMem word ⟨0⟩ mem).readWithPadding 0 64))))).toByteArray at hr
  rw [twoWordHashMem_solcMappingSlot_any] at hr
  exact hr

theorem easGetNonceBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 2)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 2) rfl hsel
  have hd : dispatchMsg contract I.calldata = some getNonceTransition := by
    apply easDispatch_getNonce (hsel := hsel)
    all_goals
      change ¬ (_ == I.calldata.extract 0 4) = true
      rw [← byteArray_eq_of_beq hsel]
      decide +kernel
  obtain ⟨k, C, rd⟩ := easReachGetNonceBody (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) v hcode hsz hsize hsel
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd1 := easBlocks.eas_block_3893_fallthrough (immWords := wordsOf (immStore v)) (by simp) hv rd
    by_cases h36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2^255 + 4
      · have rd2 := easBlocks.eas_block_3899_fallthrough (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]; exact solcDecodeLenCheckOk_4_32 h36 hbig hsize) rd1
        have rd3 := easBlocks.eas_block_3941 (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd2
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · have hdec : config.externalABI.decodeCalldata?
              (getNonceTransition.params.map Param.name)
              (transitionSignature getNonceTransition).paramTypes I.calldata =
              some ((∅ : Store).insert "account"
                (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))) :=
            easDecodeAddress_ok "account" h36 hbig hsize hc
          obtain ⟨k4, C4, rd4⟩ := easDecodeAddressEVM_ok v (by simp) hc
            (by rw [easPatchedValidJumps v]; jump_dest) rd3
          have hout := getNonceEVM v (by simp) hc rd4
          let a := AccountAddress.ofNat (calldataWord I.calldata 4).toNat
          have hslot : nonceSlot a = solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4) := by
            unfold nonceSlot a
            rw [keyValueToWord_address_of_canonical _ hc]
          refine RDret.reEquivExecution
            (retVal := some [.int (Int.ofNat (solcSlotWord σ I (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))).toNat)])
            (cs := { contract := contract
                     locals := easEntryLocals ((∅ : Store).insert "account" (.address a)) I.calldata
                     immutables := immStore v }) hcode hout hd hdec ?_ ?_
          · rw [getNonce_body]
            apply easEntryBody_returns hv hsz hsize (by change I.calldata.size - 4 < 2^255; omega)
            have hread := nonce_read (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (locals := easEntryLocals ((∅ : Store).insert "account" (.address a)) I.calldata)
              (imms := immStore v) (a := a)
              (by simp only [easEntryLocals,
                    store_get_ne _ _ (by decide : ("__calldata" == "_nonces") = false),
                    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "_nonces") = false),
                    store_get_ne _ _ (by decide : ("account" == "_nonces") = false), store_get_empty])
              (by simp only [easEntryLocals,
                    store_get_ne _ _ (by decide : ("__calldata" == "account") = false),
                    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "account") = false), store_get_self])
            simpa only [nonceWord, hslot] using hread
          · exact returnEquiv_of_encode (uint256ReturnEncoding _)
        · have hr := easDecodeAddressEVM_revert v (by simp) hc rd3
          exact RDrev.reEquivDecodingFailed hcode hr hd
            (easDecodeAddress_none_noncanon "account" h36 hbig hsize hc)
      · have rd2 := easBlocks.eas_block_3899_taken (immWords := wordsOf (immStore v)) (by simp)
          (by rw [easCalldataSub4 hsz hsize]
              exact ne_of_eq_of_ne (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by decide))
          (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
        have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
        exact RDrev.reEquivDecodingFailed hcode hr hd
          (easDecodeScalar_none_huge "account" .address (by omega) hsize)
    · have rd2 := easBlocks.eas_block_3899_taken (immWords := wordsOf (immStore v)) (by simp)
        (by rw [easCalldataSub4 hsz hsize]
            exact ne_of_eq_of_ne (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by decide))
        (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
      have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd2
      exact RDrev.reEquivDecodingFailed hcode hr hd
        (easDecodeScalar_none_short "account" .address hsz (by omega) hsize)
  · have rd1 := easBlocks.eas_block_3893_taken (immWords := wordsOf (immStore v)) (by simp) hv
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    have hr := easBlocks.eas_block_402 (immWords := wordsOf (immStore v)) (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata?
        (getNonceTransition.params.map Param.name)
        (transitionSignature getNonceTransition).paramTypes I.calldata with
    | none => exact RDrev.reEquivDecodingFailed hcode hr hd hdec
    | some args =>
      refine RDrev.reEquivExecutionRevert hcode hr hd hdec ?_
      rw [getNonce_body]
      exact easEntryBody_value_revert hv

end Benchmarks.EAS.EAS
