import Benchmarks.Auction.CreateAuctionWithMemory
import Benchmarks.Auction.SettleCurrentAndCreateNewAuctionCallFailure

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

theorem auctionSettleAndCreateFromSettleReturn {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {σ : AccountMap} {evmSettle : EVM.State} {settleFrame : Frame}
    {mem out : ByteArray} {aw free : UInt256} {k C : Nat}
    (hcode : I.code = auctionBytecode) (hperm : I.perm = true)
    (hdispatch : dispatchMsg auctionContract I.calldata = some settleAndCreateTransition)
    (hdecode : decodeCalldataWithMode auctionConfig.abiDecodeMode
      (settleAndCreateTransition.params.map Param.name)
      (transitionSignature settleAndCreateTransition).paramTypes I.calldata = some ∅)
    (hwv : I.weiValue = ⟨0⟩)
    (hstatus : auctionSlotWord ⟨101⟩ σ_solm I ≠ ⟨2⟩)
    (hpaused : auctionPausedWord σ_solm I = ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hsettle : ExecFuncBody auctionConfig { contract := auctionContract, locals := ∅ }
      (auctionSettleAuctionEnterState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      settleAuctionWithMemoryFn.body (.returned settleFrame evmSettle
        (some [.int (Int.ofNat free.toNat)])))
    (henv : evmSettle.executionEnv = I) (ha : accountMapEquiv σ evmSettle.accountMap)
    (horig : evmSettle.σ₀ = σ₀) (hgen : evmSettle.genesisBlockHeader = gh)
    (hblocks : evmSettle.blocks = bl)
    (hm : AuctionCreateMemoryValid mem aw free) (hfree : free.toNat < 2 ^ 68)
    (rd : RD auctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2690⟩
      [⟨413⟩, auctionSelWord I] mem aw out (evmSettle.createdAccounts, σ) k C) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  let evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hs : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨101⟩ ≠ ⟨2⟩ := hstatus
  have hp : UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨51⟩)
      ⟨255⟩ = ⟨0⟩ := hpaused
  obtain ⟨_, _, rd3000⟩ := auctionSettleAndCreateAfterSettleReturn_toCreateAuction rd
  have hcreate := auctionCreateAuctionWithMemoryRuntime hm hfree hperm hdepth (by simp)
    (by native_decide) henv ha horig hgen hblocks rd3000
  rcases hcreate with ⟨hr, hc⟩ | ⟨ep, fp, sp, he, hmap, hc, kr, Cr, mr, ar, outr, hr⟩
  · have hbody := auctionSettleAndCreateTransitionReverts_afterSettleCreate evm evmSettle
      hwv hs hp hsettle hc
    exact hr.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hbody := auctionSettleAndCreateTransitionReturns_afterSettleCreate evm evmSettle ep
      hwv hs hp hsettle hc
    have hreturn := auctionSettleAndCreateStatusResetReturn hperm hr
    have hpost : accountMapEquiv (auctionSettleAuctionExitMap sp I)
        (auctionSettleAuctionExitState ep).accountMap := by
      simpa only [auctionSettleAuctionExitMap, auctionSettleAuctionExitState,
        storageStore_accountMap, he] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨101⟩ ⟨1⟩ hmap
    exact hreturn.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
      (by simp only [auctionSettleAuctionExitState, storageStore_createdAccounts]) hpost
      (returnEquiv.fallthrough rfl rfl (by native_decide))

theorem auctionSettleEvent_createMemory {mem : ByteArray} {aw free : UInt256}
    (hmem : 96 ≤ mem.size) (hread : mem.readWithPadding 64 32 = free.toByteArray)
    (haw : 10 ≤ aw.toNat) (hawSize : aw.toNat * 32 < UInt256.size)
    (hfree : 96 ≤ free.toNat) (hfreeBound : free.toNat + 95 < UInt256.size)
    (hgap : free.toNat - mem.size < USize.size) :
    AuctionCreateMemoryValid (auctionSettleEventState ⟨128⟩ mem aw).1
      (auctionSettleEventState ⟨128⟩ mem aw).2 free := by
  obtain ⟨hr, hm, ha, hs, hc⟩ := auctionSettleEventState_preservesFree hmem hread haw hawSize
    hfree hfreeBound hgap
  exact ⟨hfree, hfreeBound, hm, ha, hs, hc, hr⟩

theorem auctionSettleAndCreateEventReturn {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw free : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hmem : 96 ≤ mem.size) (hread : mem.readWithPadding 64 32 = free.toByteArray)
    (haw : 10 ≤ aw.toNat) (hawSize : aw.toNat * 32 < UInt256.size)
    (hfree : 96 ≤ free.toNat) (hfreeBound : free.toNat + 95 < UInt256.size)
    (hgap : free.toNat - mem.size < USize.size)
    (rd : RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4688⟩
      [⟨128⟩, ⟨2690⟩, ⟨413⟩, auctionSelWord I] mem aw out acc k C) :
    ∃ mem' aw' k' C', AuctionCreateMemoryValid mem' aw' free ∧
      RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2690⟩
        [⟨413⟩, auctionSelWord I] mem' aw' out acc k' C' := by
  obtain ⟨kr, Cr, hr⟩ := auctionSettleAuctionEventToRetExact (by simp) hperm (by native_decide) rd
  exact ⟨_, _, kr, Cr,
    auctionSettleEvent_createMemory hmem hread haw hawSize hfree hfreeBound hgap, hr⟩

end Auction
