import Benchmarks.Auction.CreateAuctionWithMemoryCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

namespace Auction

-- LIBRARY CANDIDATE: a made zero-value call does not observe the stored input substate.
theorem typedZeroCall_substate {cfg : Config} {evm evm' : EVM.State}
    {target : EVM.Address} {name : Ident} {args : List Value} {z : Bool} {out : ByteArray}
    {perm : Bool} (hdepth : evm.executionEnv.depth ≠ 1024)
    (hcall : typedCallViaEVM cfg evm target name 0 args (z, evm', out) perm)
    (a : Substate) :
    typedCallViaEVM cfg { evm with substate := a } target name 0 args (z, evm', out) perm := by
  obtain ⟨calldata, hencode, hraw⟩ := hcall
  refine ⟨calldata, hencode, ?_⟩
  cases hraw with
  | callMade hv htheta he hb hd => exact callViaEVM.callMade hv htheta he hb hd
  | callNotMade _ _ hbad =>
    exact False.elim (hbad ⟨by rw [wordOfInt_zero]; exact Fin.zero_le _, hdepth⟩)

theorem auctionCreateAuctionMintCall_transport {cA gh bl σInit σ σ₀ A I} {g : Sat256}
    {evm : EVM.State} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {z : Bool} {out : ByteArray} {A' : Substate}
    (henv : evm.executionEnv = I) (ha : accountMapEquiv σ evm.accountMap)
    (hdepth : I.depth.val < 1024) (horig : evm.σ₀ = σ₀)
    (hgen : evm.genesisBlockHeader = gh) (hblocks : evm.blocks = bl)
    (hcall : typedCallViaEVM auctionConfig
      { initState cA gh bl σInit σ₀ g A I with accountMap := σ, createdAccounts := evm.createdAccounts }
      (EVM.address (AccountAddress.ofNat
        ((UInt256.land (auctionSlotWord ⟨201⟩ σ I) solcAddrMask).toNat))) "mint" 0 []
      (z, { initState cA gh bl σInit σ₀ g A I with
        accountMap := σ', substate := A', createdAccounts := cA' }, out) true) :
    ∃ (σS' : AccountMap) (AS' : Substate),
      typedCallViaEVM auctionConfig evm
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩)
            solcAddrMask).toNat))) "mint" 0 []
        (z, { evm with accountMap := σS', substate := AS', createdAccounts := cA' }, out) true ∧
      accountMapEquiv σ' σS' := by
  have hd : I.depth ≠ 1024 := by intro he; have := congrArg Fin.val he; omega
  have ht : auctionSlotWord ⟨201⟩ σ I =
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨201⟩ := by
    rw [henv]
    exact accountMapEquiv_storage_findD ha I.codeOwner ⟨201⟩ ⟨0⟩
  rw [ht] at hcall
  have hc := typedZeroCall_substate hd hcall evm.substate
  exact typedCallViaEVM_accountMapEquiv hc ha horig.symm rfl hgen hblocks rfl henv

end Auction
