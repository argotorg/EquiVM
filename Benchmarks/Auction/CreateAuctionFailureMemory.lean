import Benchmarks.Auction.CreateAuctionMemory
import Benchmarks.Auction.UnpauseErrorStringDecoder

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem AuctionCreateMemoryValid.growZero {mem : ByteArray} {aw free : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) {len : Nat} (hlen : len ≤ 64) :
    auctionGrowWords aw ⟨0⟩ len = aw := by
  apply auctionGrowWords_inBounds
  have := hm.wordsLow; change 0 + len ≤ 32 * aw.toNat; omega

theorem AuctionCreateMemoryValid.scratch {mem out : ByteArray} {aw free : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) (hlen : 4 ≤ out.size) :
    AuctionCreateMemoryValid (out.write 0 mem 0 4) aw free := by
  have hcover : 0 + 4 ≤ mem.size := by have := hm.memCover; omega
  refine ⟨hm.freeLow, hm.freeBound, ?_, hm.wordsLow, hm.wordsBound, hm.wordsCover, ?_⟩
  · rw [write_eq_gen out mem 0 4 (by decide) hlen hcover]
    simp only [ByteArray.size_append, ByteArray.size_extract]
    have := hm.memCover; omega
  · exact (write_read_above_gen out mem 0 4 64 (by decide) hlen hcover (by decide)
      (by have := hm.freeLow; have := hm.memCover; omega)).trans hm.read64

theorem AuctionCreateMemoryValid.loadZero_eq_five {mem mem' : ByteArray} {aw free : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) :
    auctionLoadWord mem' aw ⟨0⟩ = auctionLoadWord mem' (UInt256.ofNat 5) ⟨0⟩ := by
  have hn : ¬ (⟨0⟩ : UInt256) ≥ aw * ⟨32⟩ :=
    u256_not_ge_mul32_of_cover hm.wordsBound (by
      have := hm.wordsLow; change 0 + 32 ≤ 32 * aw.toNat; omega)
  simp only [auctionLoadWord, hn,
    show ¬ (⟨0⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ by decide, or_false]

theorem AuctionCreateMemoryValid.errorSelector {mem out : ByteArray} {aw free : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) (hlen : 4 ≤ out.size)
    (hsel : out.extract 0 4 = errorStringSelector) :
    ∃ preSel : UInt256, auctionLoadWord (out.write 0 mem 0 4) aw ⟨0⟩ = preSel ∧
      UInt256.shiftRight preSel ⟨224⟩ = (⟨0x08c379a0⟩ : UInt256) := by
  rw [hm.loadZero_eq_five]
  exact auctionMintFailureErrorSelector_bridge hlen hsel

theorem AuctionCreateMemoryValid.otherSelector {mem out : ByteArray} {aw free : UInt256}
    (hm : AuctionCreateMemoryValid mem aw free) (hlen : 4 ≤ out.size)
    (hsel : out.extract 0 4 ≠ errorStringSelector) :
    ∃ preSel : UInt256, auctionLoadWord (out.write 0 mem 0 4) aw ⟨0⟩ = preSel ∧
      UInt256.sub (UInt256.shiftRight preSel ⟨224⟩) ⟨0x08c379a0⟩ ≠ ⟨0⟩ := by
  rw [hm.loadZero_eq_five]
  obtain ⟨preSel, hword, hne⟩ := auctionMintFailureSelector_bridge (mem := mem) hlen hsel
  exact ⟨preSel, hword, u256_sub_ne_zero_of_ne hne⟩

end Auction
