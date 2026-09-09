import Benchmarks.Auction.CreateAuctionMemory
import Benchmarks.Auction.CallReturnDataBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem auctionCreateAuctionWithMemoryPostMintCall {cA cACur gh bl σInit σ σ₀ A I}
    {g : Sat256} {mem rdata : ByteArray} {aw free ret : UInt256}
    {R : List UInt256} {k C : Nat}
    (hm : AuctionCreateMemoryValid mem aw free)
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024) (hR : R.length + 20 ≤ 1024)
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3000⟩
      (ret :: R) mem aw rdata (cACur, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : Nat),
      RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: (⟨4⟩ + free) :: ⟨0x1249c58b⟩ ::
          auctionMintTargetWord σ I :: ret :: R)
        (out.write 0 (auctionCreateAuctionMintSelMemAt mem free) free.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat) aw out (cA', σ') k' C'
      ∧ typedCallViaEVM auctionConfig
        { initState cA gh bl σInit σ₀ g A I with accountMap := σ, createdAccounts := cACur }
        (EVM.address (AccountAddress.ofNat
          ((UInt256.land (auctionSlotWord ⟨201⟩ σ I) solcAddrMask).toNat))) "mint" 0 []
        (z, { initState cA gh bl σInit σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' }, out) true
      ∧ out.size < 2 ^ 64 := by
  have hload := hm.load64
  have hloadSel := hm.selector.load64
  have hg64 := hm.grow64
  have hg32 := hm.growFree (len := 32) (by decide)
  dsimp only [auctionLoadWord] at hload hloadSel
  dsimp only [auctionGrowWords] at hg64 hg32
  have hspan : UInt256.sub ((⟨4⟩ : UInt256) + free) free = ⟨4⟩ := by
    rw [u256_add_comm]
    exact auctionMintDecodeLengthCheck free (len := 4) (by decide)
  have hM4 : MachineState.M aw.toNat free.toNat 4 = aw.toNat :=
    auctionMachineState_M_inBounds (by have := hm.wordsCover; omega)
  have hM32 : MachineState.M aw.toNat free.toNat 32 = aw.toNat :=
    auctionMachineState_M_inBounds (by have := hm.wordsCover; omega)
  have hpost := auctionCreateAuction_postMintCallAt hperm hdepth hR (by
    dsimp only
    rw [hload, hg64, hg32, hloadSel, hspan]
    exact auctionCreateAuctionMintSelMemAt_encode mem free (by have := hm.memCover; omega)) rd
  have haw : UInt256.ofNat
      (MachineState.M (MachineState.M aw.toNat free.toNat (⟨4⟩ : UInt256).toNat)
        free.toNat (⟨32⟩ : UInt256).toNat) = aw := by
    change UInt256.ofNat (MachineState.M (MachineState.M aw.toNat free.toNat 4) free.toNat 32) = aw
    rw [hM4, hM32, u256_ofNat_toNat]
  simp only [hload, hg64, hg32, hloadSel, hspan, haw] at hpost
  obtain ⟨cA', σ', z, out, A', k', C', hout, hcall, _⟩ := hpost
  exact ⟨cA', σ', z, out, A', k', C', hout, hcall, auctionMintReturnData_size_lt_2pow64 hcall⟩

end Auction
