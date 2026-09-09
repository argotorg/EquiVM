import Benchmarks.Auction.CreateBidRefundRuntime
import Benchmarks.Auction.SafeTransferWeth
import Benchmarks.Auction.CreateBidWethMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

set_option maxHeartbeats 1000000 in
theorem auctionCreateBidWethRuntime
    {cA cA' gh bl σ_evm σ_solm σCall σ₀ A I} {g : UInt256}
    {marker owner aw : UInt256} {mem rdata : ByteArray}
    (evm evmRefund : EVM.State)
    (hinit : evm = initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
    (henv : evmRefund.executionEnv = I) (hcreated : evmRefund.createdAccounts = cA')
    (haccounts : accountMapEquiv σCall evmRefund.accountMap)
    (hσ₀ : evmRefund.σ₀ = σ₀) (hgenesis : evmRefund.genesisBlockHeader = gh)
    (hblocks : evmRefund.blocks = bl) (hdepth : I.depth.val < 1024)
    (hcode : I.code = auctionBytecode) (hperm : I.perm = true)
    (hsel : selIs I (auctionSelBytes 6))
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hstatus : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩)
    (hnoun :
      Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨207⟩ =
        auctionCreateBidArgWord I)
    (htime : (UInt256.ofNat
        (auctionCreateBidEnterState evm).executionEnv.header.timestamp).toNat <
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩).toNat)
    (hreserve : (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨204⟩).toNat ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hmulFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
        (UInt256.land
          (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
          ⟨255⟩).toNat < UInt256.size)
    (haddFit :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 < UInt256.size)
    (hbid :
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat +
        ((Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
            (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat *
          (UInt256.land
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨205⟩)
            ⟨255⟩).toNat) / 100 ≤
      (auctionCreateBidEnterState evm).executionEnv.weiValue.toNat)
    (hbidder :
      AccountAddress.ofNat
          (auctionPackedBidderWord
            (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
              (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat ≠
        AccountAddress.ofNat 0)
    (howner : AccountAddress.ofNat
      (auctionPackedBidderWord (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat =
      AccountAddress.ofUInt256 owner)
    (hcall : callViaEVM (auctionCreateBidEnterState evm)
      (EVM.address (AccountAddress.ofNat
        (auctionPackedBidderWord (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
          (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨211⟩)).toNat))
      (Int.ofNat (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩).toNat)
      ByteArray.empty (false, evmRefund, rdata) true)
    (hm : AuctionWethMemory mem aw
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩) owner
      (Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨210⟩))
    (hweth : uniswapExtCodeSizeWord σCall
      (UInt256.land (auctionSlotWord ⟨202⟩ σCall I) solcAddrMask) ≠ ⟨0⟩)
    (hreach : ∃ k C, RD auctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3347⟩
      [⟨0⟩, Solm.EVM.storageLoad (auctionCreateBidEnterState evm)
        (auctionCreateBidEnterState evm).executionEnv.codeOwner ⟨208⟩,
        owner, ⟨1715⟩, marker, ⟨128⟩, auctionCreateBidArgWord I, ⟨413⟩, auctionSelWord I]
      mem aw rdata (cA', σCall) k C) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  obtain ⟨_, _, hreach⟩ := hreach
  have hresult := auctionSafeTransferWethFallbackCorrect (auctionCreateBidEnterState evm)
    evmRefund _ henv hcreated hσ₀ hgenesis hblocks haccounts (by evm_ov) (by jump_dest)
    hperm hdepth hm howner hcall hweth hreach
  rcases hresult with ⟨hrev, hsafe⟩ | ⟨cAF, σF, τF, AF, memF, awF, outF, csF,
      hpost, hfinish, hsafe, hjoin⟩
  · have hbody := auctionCreateBidTransitionReverts_refundReverted evm I
      hstatus hnoun htime hreserve hmulFit haddFit hbid hbidder hsafe
    rw [hinit] at hbody
    exact hrev.reEquivExecutionRevert hcode (auctionDispatch_createBid hsel)
      (auctionDecode_createBid hsz36 hbig) hbody
  · exact auctionCreateBidRefundReturnedRuntime evm
      { evmRefund with accountMap := τF, substate := AF, createdAccounts := cAF }
      hinit henv rfl hpost
      hcode hperm hsel hsz36 hbig hstatus hnoun htime hreserve hmulFit haddFit hbid hbidder
      hsafe hfinish hjoin

end Auction
