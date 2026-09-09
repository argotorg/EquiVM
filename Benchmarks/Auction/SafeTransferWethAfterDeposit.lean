import Benchmarks.Auction.SafeTransferWethCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethAfterDepositExecution {cA gh bl σ σ₀ A I} {g : Sat256}
    {cAD : Batteries.RBSet AccountAddress compare} {σD τD : AccountMap} {AD : Substate}
    {mem outDeposit : ByteArray} {aw amount owner finish ret weth : UInt256}
    {R : List UInt256} {k C : Nat}
    (evmCall : EVM.State) (recipient : AccountAddress)
    (henv : evmCall.executionEnv = I) (hσ₀ : evmCall.σ₀ = σ₀)
    (hgenesis : evmCall.genesisBlockHeader = gh) (hblocks : evmCall.blocks = bl)
    (hR : R.length ≤ 970) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hm : AuctionWethMemory mem aw amount owner finish)
    (hrecipient : recipient = AccountAddress.ofUInt256 owner)
    (hdeposit : typedCallViaEVM auctionConfig evmCall (auctionWethTarget evmCall)
      "deposit" (Int.ofNat amount.toNat) []
      (true, { evmCall with accountMap := τD, substate := AD, createdAccounts := cAD },
        outDeposit) true)
    (haccounts : accountMapEquiv σD τD)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3432⟩
      (⟨1⟩ :: (⟨4⟩ + auctionSettleAuctionDynMload64 mem aw) :: amount ::
        ⟨3504541104⟩ :: weth :: amount :: owner :: ret :: R)
      (auctionSettleAuctionDynDepositMem mem aw) (auctionSettleAuctionDynDepositCallAw mem aw)
      outDeposit (cAD, σD) k C) :
    AuctionWethExecution (initState cA gh bl σ σ₀ g A I) I g
      evmCall recipient amount owner mem aw ret R := by
  let evmDeposit := { evmCall with accountMap := τD, substate := AD, createdAccounts := cAD }
  obtain ⟨_, _, h3452⟩ := auctionSafeTransferDepositSuccessToTransferLoadWethAnyMem
    (by evm_ov) rd
  obtain ⟨_, _, h3455⟩ := auctionSafeTransferAfterDepositLoadFreePtrAnyMem
    (by evm_ov) hm.depositCallFree h3452
  obtain ⟨_, _, h3466⟩ := auctionSafeTransferAfterDepositStoreTransferSelectorAnyMem
    (by evm_ov) h3455
  obtain ⟨_, _, h3481⟩ := auctionSafeTransferAfterDepositStoreTransferOwnerAnyMem
    (by evm_ov) h3466
  obtain ⟨_, _, h3488⟩ := auctionSafeTransferAfterDepositStoreTransferAmountAnyMem
    (by evm_ov) h3481
  obtain ⟨_, _, _, h3517⟩ := auctionSafeTransferAfterDepositPrepTransferCallAnyMem
    (by evm_ov) hm.transferFree hm.transferLen h3488
  obtain ⟨cAT, σT, τT, AT, z, outTransfer, kT, CT, htransferRaw, hpost, hsize, h3518⟩ :=
    auctionCoupledValueCall evmDeposit henv rfl hσ₀ hgenesis hblocks haccounts hperm hdepth
      (by exact Nat.zero_le _) (by native_decide) (by evm_ov) h3517
  have htarget := auctionWethTarget_accountMapEquiv haccounts (show evmDeposit.executionEnv = I
    from henv)
  have htransfer : typedCallViaEVM auctionConfig evmDeposit (auctionWethTarget evmDeposit)
      "transfer" 0 [.address recipient, .int (Int.ofNat amount.toNat)]
      (z, { evmCall with accountMap := τT, substate := AT, createdAccounts := cAT }, outTransfer)
      true := by
    rw [htarget, hrecipient]
    exact ⟨_, hm.transferEncode, htransferRaw⟩
  have houtSize : outTransfer.size < UInt256.size := Nat.lt_trans hsize (by native_decide)
  cases z
  · exact .transferFailure evmDeposit _ outDeposit outTransfer hdeposit htransfer
      (auctionSafeTransferWethCallFailure (Or.inr rfl) (by evm_ov) houtSize h3518)
  · exact auctionSafeTransferWethReturnExecution evmCall evmDeposit recipient
      (by omega) hret hm hdeposit htransfer hpost
      (Nat.lt_trans hsize (by native_decide)) h3518

set_option maxHeartbeats 1000000 in
theorem auctionSafeTransferWethAfterDeposit {cA gh bl σ σ₀ A I} {g : Sat256}
    {cAD : Batteries.RBSet AccountAddress compare} {σD τD : AccountMap} {AD : Substate}
    {mem out outDeposit : ByteArray} {aw amount owner finish ret weth : UInt256}
    {R : List UInt256} {k C : Nat}
    (evm evmCall : EVM.State) (recipient : AccountAddress)
    (henv : evmCall.executionEnv = I) (hσ₀ : evmCall.σ₀ = σ₀)
    (hgenesis : evmCall.genesisBlockHeader = gh) (hblocks : evmCall.blocks = bl)
    (hR : R.length ≤ 970) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hm : AuctionWethMemory mem aw amount owner finish)
    (hrecipient : recipient = AccountAddress.ofUInt256 owner)
    (hcall : callViaEVM evm (EVM.address recipient) (Int.ofNat amount.toNat) ByteArray.empty
      (false, evmCall, out) true)
    (hcode : auctionWethCodePresent evmCall)
    (hdeposit : typedCallViaEVM auctionConfig evmCall (auctionWethTarget evmCall)
      "deposit" (Int.ofNat amount.toNat) []
      (true, { evmCall with accountMap := τD, substate := AD, createdAccounts := cAD },
        outDeposit) true)
    (haccounts : accountMapEquiv σD τD)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3432⟩
      (⟨1⟩ :: (⟨4⟩ + auctionSettleAuctionDynMload64 mem aw) :: amount ::
        ⟨3504541104⟩ :: weth :: amount :: owner :: ret :: R)
      (auctionSettleAuctionDynDepositMem mem aw) (auctionSettleAuctionDynDepositCallAw mem aw)
      outDeposit (cAD, σD) k C) :
    AuctionSafeTransferOutcome (initState cA gh bl σ σ₀ g A I) I g
      evm evmCall recipient amount finish ret R := by
  exact (auctionSafeTransferWethAfterDepositExecution evmCall recipient henv hσ₀ hgenesis hblocks
    hR hret hperm hdepth hm hrecipient hdeposit haccounts rd).toOutcome hm hcall hcode

end Auction
