import Solm.Benchmarks.Auction.SetterSource
import Solm.Benchmarks.Auction.Uint256Setter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem setReservePriceBody (evm : EVM.State) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv) :
    ExecTransitionBody auctionConfig auctionContract evm
      ((∅ : Store).insert "_reservePrice" (.int (Int.ofNat value.toNat)))
      setReservePriceTransition.body
      (.returned
        { contract := auctionContract
          locals := (∅ : Store).insert "_reservePrice" (.int (Int.ofNat value.toNat)) }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨204⟩ value) none) := by
  exact ownerSetUint256 evm _ "reservePrice" "_reservePrice" ⟨204⟩ value hwv ho
    (by simp) (by simp) (by simp) (by native_decide) rfl

theorem setReservePriceBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (entryBytes 15))
    (hreach : EntryReached 15 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 15 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 15) (entryBytes_size 7) hsel
    obtain ⟨_, _, rd828⟩ := hreach
    obtain ⟨_, _, rd841⟩ := entryGuardZero 15 (by decide) rd828 hwv
    obtain ⟨_, _, rd5357⟩ := setterToDecoder 1 rd841 (by evm_ov)
    by_cases hlen : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
            (setReservePriceTransition.params.map Param.name)
            (transitionSignature setReservePriceTransition).paramTypes I.calldata =
              some ((∅ : Store).insert "_reservePrice"
                (.int (Int.ofNat (calldataWord I.calldata 4).toNat))) :=
          decodeCalldata_uint256_ok hlen hhi
        obtain ⟨_, _, rd854⟩ := decodeUint256Ok rd5357 hlen hhi hsize
          (by native_decide) (by evm_ov)
        obtain ⟨_, _, rd2478⟩ := setterFromDecoder 1 rd854 (by evm_ov)
        by_cases ho : solcSourceWord I = ownerWord σ_evm I
        · obtain ⟨_, _, rd2520⟩ := ownerAllowed 5 rd2478 ho (by evm_ov)
          obtain ⟨_, _, rd413⟩ := setterStoreEvent 1 rd2520 hperm
            (by jump_dest) (by evm_ov)
          have hbody := setReservePriceBody
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (calldataWord I.calldata 4) hwv (by
              change solcSourceWord I = ownerWord σ_solm I
              rw [← ownerWord_equiv hAccounts I]
              exact ho)
          exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGenAccountMapEquiv
            hcode hd hdec hbody (by rw [storageStore_createdAccounts]; rfl) (by
              rw [storageStore_accountMap]
              exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨204⟩ _ hAccounts)
            (.fallthrough rfl rfl (by native_decide))
        · have hbody : ExecTransitionBody auctionConfig auctionContract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              ((∅ : Store).insert "_reservePrice"
                (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
              setReservePriceTransition.body .reverted := by
            apply ownerBodyReverts _ _ _ hwv
            · change solcSourceWord I ≠ ownerWord σ_solm I
              rw [← ownerWord_equiv hAccounts I]
              exact ho
            · simp
          exact (ownerDenied 5 rd2478 ho (by evm_ov)).reEquivExecutionRevert
            hcode hd hdec hbody
      · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
            (setReservePriceTransition.params.map Param.name)
            (transitionSignature setReservePriceTransition).paramTypes I.calldata = none :=
          decodeCalldata_uint256_none_huge (by omega)
        exact (decodeUint256Fail rd5357
          (solcDecodeLenCheckHuge_4_32 (by omega) hsize) (by evm_ov)).reEquivDecodingFailed
          hcode hd hdec
    · have hdec : decodeCalldataWithMode auctionConfig.abiDecodeMode
          (setReservePriceTransition.params.map Param.name)
          (transitionSignature setReservePriceTransition).paramTypes I.calldata = none :=
        decodeCalldata_uint256_none_short (by omega)
      exact (decodeUint256Fail rd5357
        (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize) (by evm_ov)).reEquivDecodingFailed
        hcode hd hdec
  · exact entryNonpayableRevert 15 (by decide) hcode hsel hreach hwv

end Auction
