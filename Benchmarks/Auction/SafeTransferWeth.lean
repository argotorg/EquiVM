import Benchmarks.Auction.SafeTransferWethAfterDeposit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethFallbackExecution {cA gh bl σ σ₀ A I} {g : Sat256}
    {cACall : Batteries.RBSet AccountAddress compare} {σCall : AccountMap}
    {mem out : ByteArray} {aw amount owner finish ret : UInt256}
    {R : List UInt256} {k C : Nat}
    (evmCall : EVM.State) (recipient : AccountAddress)
    (henv : evmCall.executionEnv = I) (hcreated : evmCall.createdAccounts = cACall)
    (hσ₀ : evmCall.σ₀ = σ₀) (hgenesis : evmCall.genesisBlockHeader = gh)
    (hblocks : evmCall.blocks = bl) (haccounts : accountMapEquiv σCall evmCall.accountMap)
    (hR : R.length ≤ 970) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hm : AuctionWethMemory mem aw amount owner finish)
    (hrecipient : recipient = AccountAddress.ofUInt256 owner)
    (hcode : uniswapExtCodeSizeWord σCall
      (UInt256.land (auctionSlotWord ⟨202⟩ σCall I) solcAddrMask) ≠ ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      (⟨0⟩ :: amount :: owner :: ret :: R) mem aw out (cACall, σCall) k C) :
    auctionWethCodePresent evmCall ∧
      AuctionWethExecution (initState cA gh bl σ σ₀ g A I) I g
        evmCall recipient amount owner mem aw ret R := by
  have hword := transferBranchWethWordAt haccounts rfl (congrArg (·.codeOwner) henv)
  have htarget := auctionWethTarget_accountMapEquiv haccounts henv
  have hcodeS : auctionWethCodePresent evmCall :=
    transferBranchWethLookupCodePos haccounts rfl hword hcode
  refine ⟨hcodeS, ?_⟩
  obtain ⟨gasArg, _, _, h3431⟩ := auctionSafeTransferFallbackToDepositCallAnyMem
    (by evm_ov) hcode hm.depositFree hm.depositLen rd
  by_cases hbalance : amount ≤ (σCall.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
  · obtain ⟨cAD, σD, τD, AD, z, outDeposit, kD, CD, hdepositRaw, hpost, hsize, h3432⟩ :=
      auctionCoupledValueCall evmCall henv hcreated hσ₀ hgenesis hblocks haccounts hperm hdepth
        hbalance (by native_decide) (by evm_ov) h3431
    have hdeposit : typedCallViaEVM auctionConfig evmCall (auctionWethTarget evmCall)
        "deposit" (Int.ofNat amount.toNat) []
        (z, { evmCall with accountMap := τD, substate := AD, createdAccounts := cAD }, outDeposit)
        true := by
      rw [htarget]
      exact ⟨_, hm.depositEncode, hdepositRaw⟩
    cases z
    · exact .depositFailure _ outDeposit hdeposit
        (auctionSafeTransferWethCallFailure (Or.inl rfl) (by evm_ov)
          (Nat.lt_trans hsize (by native_decide)) h3432)
    · have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat outDeposit.size)).toNat = 0 := by
        have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat outDeposit.size := Nat.zero_le _
        simp only [min, hle, ↓reduceIte]
        rfl
      rw [hmin, byteArray_write_len_zero] at h3432
      exact auctionSafeTransferWethAfterDepositExecution evmCall recipient
        henv hσ₀ hgenesis hblocks hR hret hperm hdepth hm hrecipient hdeposit hpost h3432
  · obtain ⟨_, _, _, _, h3432⟩ := auctionCallNotMade h3431 (by native_decide) hperm
      (by intro hh; exact hbalance hh.1) (by evm_ov)
    have hnotS : ¬ (EVM.wordOfInt (Int.ofNat amount.toNat) ≤
        (evmCall.accountMap.find? evmCall.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) ∧
        evmCall.executionEnv.depth ≠ 1024) := by
      rw [wordOfInt_ofNat_toNat, henv]
      have hbal : (σCall.find? I.codeOwner |>.elim (⟨0⟩ : UInt256) (·.balance)) =
          (evmCall.accountMap.find? I.codeOwner |>.elim (⟨0⟩ : UInt256) (·.balance)) := by
        have hh := haccounts I.codeOwner
        cases hs : σCall.find? I.codeOwner <;>
          cases ht : evmCall.accountMap.find? I.codeOwner <;> simp [hs, ht] at hh ⊢
        exact hh.2.1
      rw [← hbal]
      exact fun hh ↦ hbalance hh.1
    have hdeposit : typedCallViaEVM auctionConfig evmCall (auctionWethTarget evmCall)
        "deposit" (Int.ofNat amount.toNat) []
        (false, { evmCall with substate :=
          (evmCall.addAccessedAccount (auctionWethTarget evmCall)).substate }, ByteArray.empty)
        true := ⟨depositSelector, rfl, callViaEVM.callNotMade rfl rfl hnotS⟩
    exact .depositFailure _ ByteArray.empty hdeposit
      (auctionSafeTransferWethCallFailure (Or.inl rfl) (by evm_ov) (by native_decide) h3432)

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethFallbackCorrect {cA gh bl σ σ₀ A I} {g : Sat256}
    {cACall : Batteries.RBSet AccountAddress compare} {σCall : AccountMap}
    {mem out : ByteArray} {aw amount owner finish ret : UInt256}
    {R : List UInt256} {k C : Nat}
    (evm evmCall : EVM.State) (recipient : AccountAddress)
    (henv : evmCall.executionEnv = I) (hcreated : evmCall.createdAccounts = cACall)
    (hσ₀ : evmCall.σ₀ = σ₀) (hgenesis : evmCall.genesisBlockHeader = gh)
    (hblocks : evmCall.blocks = bl) (haccounts : accountMapEquiv σCall evmCall.accountMap)
    (hR : R.length ≤ 970) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hm : AuctionWethMemory mem aw amount owner finish)
    (hrecipient : recipient = AccountAddress.ofUInt256 owner)
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hcode : uniswapExtCodeSizeWord σCall
      (UInt256.land (auctionSlotWord ⟨202⟩ σCall I) solcAddrMask) ≠ ⟨0⟩)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3347⟩
      (⟨0⟩ :: amount :: owner :: ret :: R) mem aw out (cACall, σCall) k C) :
    AuctionSafeTransferOutcome (initState cA gh bl σ σ₀ g A I) I g
      evm evmCall recipient amount finish ret R := by
  obtain ⟨hcodeS, hresult⟩ := auctionSafeTransferWethFallbackExecution evmCall recipient
    henv hcreated hσ₀ hgenesis hblocks haccounts hR hret hperm hdepth hm hrecipient hcode rd
  exact hresult.toOutcome hm hcall hcodeS

end Auction
