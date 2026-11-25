import Benchmarks.Midnight.TakeTickGuard
import Benchmarks.Midnight.RuntimeBlocks_043

variable {fork : Ethereum.Fork}

/-! The offer time window and self-take restriction. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def TakeTimeValid (I : ExecutionEnv) (offer : OfferData) : Prop :=
  offer.start.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat ∧
    (UInt256.ofNat I.header.timestamp).toNat ≤ offer.expiry.toNat

theorem midnightTakeTimeGuard {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 2 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11108⟩ R mem aw rdata σ k C) :
    (¬ TakeTimeValid I offer ∧ RDrev fork midnightBytecode g s0) ∨
    (TakeTimeValid I offer ∧ ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨11136⟩ R mem aw' rdata σ k' C') := by
  have hstart : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 96) mem = offer.start :=
    ho.words.load_offset ⟨3, by change 3 < 15; decide⟩ rfl
  have hexpiry : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 128) mem = offer.expiry :=
    ho.words.load_offset ⟨4, by change 4 < 15; decide⟩ rfl
  by_cases hs : offer.start.toNat ≤ (UInt256.ofNat I.header.timestamp).toNat
  · have rd1 := midnightBlocks.midnight_block_11108_fallthrough hstack (by
      rw [hroot, hstart]; exact ult_zero hs) rd
    by_cases he : (UInt256.ofNat I.header.timestamp).toNat ≤ offer.expiry.toNat
    · have rd2 := midnightBlocks.midnight_block_11122_fallthrough hstack (by
        rw [hroot, hexpiry]; exact ugt_zero he) rd1
      exact Or.inr ⟨⟨hs, he⟩, _, _, _, by memory_fund ha, rd2⟩
    · have rr := midnightBlocks.midnight_block_11122_taken hstack (by
        rw [hroot, hexpiry, ugt_one (by omega)]; decide) (by jump_dest) rd1
      exact Or.inl ⟨fun h ↦ he h.2, midnightBlocks.midnight_block_14923 hstack rr⟩
  · have rr := midnightBlocks.midnight_block_11108_taken hstack (by
      rw [hroot, hstart, ult_one (by omega)]; decide) (by jump_dest) rd
    exact Or.inl ⟨fun h ↦ hs h.1, midnightBlocks.midnight_block_14938 hstack rr⟩

theorem midnightTakeSelfGuard {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr root taker : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} {offer : OfferData}
    (hstack : R.length + 4 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ marketPtr arrayPtr callbackPtr root offer)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 544) mem = taker)
    (hcanon : taker.toNat < EVM.addressModulus) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨11136⟩ R mem aw rdata σ k C) :
    (UInt256.ofNat offer.maker.val = taker ∧ RDrev fork midnightBytecode g s0) ∨
    (UInt256.ofNat offer.maker.val ≠ taker ∧ ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨11171⟩ R mem aw' rdata σ k' C') := by
  have hm : memLoad ((⟨832⟩ : UInt256) + UInt256.ofNat 64) mem = UInt256.ofNat offer.maker.val :=
    ho.words.load_offset ⟨2, by change 2 < 15; decide⟩ rfl
  have hclean : UInt256.land (UInt256.ofNat offer.maker.val) solcAddrMask =
      UInt256.ofNat offer.maker.val := solcAddrMask_clean (addressWord_canonical offer.maker)
  by_cases he : UInt256.ofNat offer.maker.val = taker
  · have rr := midnightBlocks.midnight_block_11136_taken hstack (by
      rw [hroot, hm, htaker, addressMask_computed, solcAddrMask_clean hcanon,
        hclean, he, uInt256_eq_self]
      decide) (by jump_dest) rd
    exact Or.inl ⟨he, midnightBlocks.midnight_block_14908 (by omega) rr⟩
  · have rd1 := midnightBlocks.midnight_block_11136_fallthrough hstack (by
      rw [hroot, hm, htaker, addressMask_computed, solcAddrMask_clean hcanon, hclean]
      exact u256_eq_of_ne (Ne.symm he)) rd
    exact Or.inr ⟨he, _, _, _, by memory_fund ha, rd1⟩

end Benchmarks.Midnight
