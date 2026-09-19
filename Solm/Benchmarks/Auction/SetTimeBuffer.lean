import Solm.Benchmarks.Auction.SetterSource
import Solm.Benchmarks.Auction.Uint256Setter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem setTimeBufferBody (evm : EVM.State) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm
      ((∅ : Store).insert "_timeBuffer" (.int (Int.ofNat value.toNat)))
      setTimeBufferTransition.body
      (.returned
        { contract := auctionContract
          locals := (∅ : Store).insert "_timeBuffer" (.int (Int.ofNat value.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨203⟩ value) none) := by
  exact ownerSetUint256 evm _ "timeBuffer" "_timeBuffer" ⟨203⟩ value hwv ho
    (by simp) (by simp) (by simp) (by native_decide) rfl

theorem setTimeBufferBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (entryBytes 7))
    (hreach : EntryReached 7 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 7 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 7) (entryBytes_size 7) hsel
    obtain ⟨_, _, rd519⟩ := hreach
    obtain ⟨_, _, rd532⟩ := entryGuardZero 7 (by decide) rd519 hwv
    obtain ⟨_, _, rd5357⟩ := setterToDecoder 0 rd532 (by evm_ov)
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
            (setTimeBufferTransition.params.map Param.name)
            (transitionSignature setTimeBufferTransition).paramTypes I.calldata =
              some ((∅ : Store).insert "_timeBuffer"
                (.int (Int.ofNat (calldataWord I.calldata 4).toNat))) :=
          decodeCalldata_uint256_ok hlen hhi
        obtain ⟨_, _, rd545⟩ := decodeUint256Ok rd5357 hlen hhi hsize
          (by native_decide) (by evm_ov)
        obtain ⟨_, _, rd1934⟩ := setterFromDecoder 0 rd545 (by evm_ov)
        by_cases ho : solcSourceWord I = ownerWord σ_evm I
        · obtain ⟨_, _, rd1976⟩ := ownerAllowed 2 rd1934 ho (by evm_ov)
          obtain ⟨_, _, rd413⟩ := setterStoreEvent 0 rd1976 hperm
            (by jump_dest) (by evm_ov)
          have hbody := setTimeBufferBody
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (calldataWord I.calldata 4) hwv (by
              change solcSourceWord I = ownerWord σ_solm I
              rw [← ownerWord_equiv hAccounts I]
              exact ho)
          exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGenAccountMapEquiv
            hcode hd hdec hbody (by rw [storageStore_createdAccounts]; rfl) (by
              rw [storageStore_accountMap]
              exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨203⟩ _ hAccounts)
            (.fallthrough rfl rfl (by native_decide))
        · have hbody : ExecTransitionBody auctionConfig auctionContract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              ((∅ : Store).insert "_timeBuffer"
                (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
              setTimeBufferTransition.body .reverted := by
            apply ownerBodyReverts _ _ _ hwv
            · change solcSourceWord I ≠ ownerWord σ_solm I
              rw [← ownerWord_equiv hAccounts I]
              exact ho
            · simp
          exact (ownerDenied 2 rd1934 ho (by evm_ov)).reEquivExecutionRevert
            hcode hd hdec hbody
      · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
            (setTimeBufferTransition.params.map Param.name)
            (transitionSignature setTimeBufferTransition).paramTypes I.calldata = none :=
          decodeCalldata_uint256_none_huge (by omega)
        exact (decodeUint256Fail rd5357
          (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by evm_ov)).reEquivDecodingFailed
          hcode hd hdec
    · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
          (setTimeBufferTransition.params.map Param.name)
          (transitionSignature setTimeBufferTransition).paramTypes I.calldata = none :=
        decodeCalldata_uint256_none_short (by omega)
      exact (decodeUint256Fail rd5357
        (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by evm_ov)).reEquivDecodingFailed
        hcode hd hdec
  · exact entryNonpayableRevert 7 (by decide) hcode hsel hreach hwv

end Auction
