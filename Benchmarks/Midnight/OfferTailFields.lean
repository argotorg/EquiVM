import Benchmarks.Midnight.OfferTailBlocks
import Benchmarks.Midnight.OfferDecodeFacts

variable {fork : Ethereum.Fork}

/-! The offer tail's addresses, Boolean flag, and uint128 caps. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def offerTailPrefixWords (bytes : ByteArray) (base : Nat) (data : UInt256) : List UInt256 :=
  [data, calldataWord bytes (base + 288), calldataWord bytes (base + 320),
    calldataWord bytes (base + 352), calldataWord bytes (base + 384)]

def offerTailPrefixMemory (mem bytes : ByteArray) (base : Nat) (data : UInt256) : ByteArray :=
  writeWordArray mem 1088 (offerTailPrefixWords bytes base data)

theorem midnightOfferTailFields {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw data rel : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hrel : rel.toNat < 2^64) (hm : 416 ≤ mem.size)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10687⟩ (data :: rel :: R) mem aw rdata σ k C) :
    (decodeOfferData I.calldata (rel.toNat + 4) = none ∧ RDrev fork midnightBytecode g s0) ∨
    (OfferData.tailCanonicalAt I.calldata (rel.toNat + 4) ∧
      ∃ aw' k' C',
        MemoryFunding credit (offerTailPrefixMemory mem I.calldata (rel.toNat + 4) data) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨10795⟩
          (calldataWord I.calldata (rel.toNat + 420) :: rel :: R)
          (offerTailPrefixMemory mem I.calldata (rel.toNat + 4) data) aw' rdata σ k' C') := by
  have hadd (off : Nat) (ho : off ≤ 420) :
      (rel + UInt256.ofNat off).toNat = rel.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  let words := [data, calldataWord I.calldata (rel.toNat + 292),
    calldataWord I.calldata (rel.toNat + 324), calldataWord I.calldata (rel.toNat + 356),
    calldataWord I.calldata (rel.toNat + 388)]
  have hr (n : Nat) :
      memLoad (UInt256.ofNat 384) (writeWordArray mem 1088 (words.take n)) = ⟨832⟩ := by
    rw [memLoad_writeWordArray_below mem 1088 (UInt256.ofNat 384) _ hm (by decide), hroot]
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightOfferStoreCallbackData (by omega)
    (by simpa only [words, List.take, writeWordArray, Nat.reduceAdd] using hr 0) ha rd
  by_cases h0 : (calldataWord I.calldata (rel.toNat + 292)).toNat < EVM.addressModulus
  · obtain ⟨k2, C2, _, ha2, rd2⟩ := midnightCalldataAddress_funded
      (by simp only [List.length_cons]; omega) (by rw [hadd 292 (by decide)]; exact h0)
      (by jump_dest) ha1 rd1
    rw [hadd 292 (by decide)] at rd2
    obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightOfferStoreReceiver (by omega)
      (by simpa only [words, List.take, writeWordArray, Nat.reduceAdd] using hr 1) ha2 rd2
    by_cases h1 : (calldataWord I.calldata (rel.toNat + 324)).toNat < EVM.addressModulus
    · obtain ⟨k4, C4, _, ha4, rd4⟩ := midnightCalldataAddress_funded
        (by simp only [List.length_cons]; omega) (by rw [hadd 324 (by decide)]; exact h1)
        (by jump_dest) ha3 rd3
      rw [hadd 324 (by decide)] at rd4
      obtain ⟨aw5, k5, C5, ha5, rd5⟩ := midnightOfferStoreRatifier (by omega)
        (by simpa only [words, List.take, writeWordArray, Nat.reduceAdd] using hr 2) ha4 rd4
      by_cases h2 : calldataWord I.calldata (rel.toNat + 356) = ⟨0⟩ ∨
              calldataWord I.calldata (rel.toNat + 356) = ⟨1⟩
      · obtain ⟨k6, C6, _, ha6, rd6⟩ := midnightCalldataBool_funded
          (by simp only [List.length_cons]; omega) (by rw [hadd 356 (by decide)]; exact h2)
          (by jump_dest) ha5 rd5
        rw [hadd 356 (by decide)] at rd6
        obtain ⟨aw7, k7, C7, ha7, rd7⟩ := midnightOfferStoreReduceOnly (by omega)
          (by simpa only [words, List.take, writeWordArray, Nat.reduceAdd] using hr 3) ha6 rd6
        by_cases h3 : (calldataWord I.calldata (rel.toNat + 388)).toNat < 2^128
        · obtain ⟨k8, C8, _, ha8, rd8⟩ := midnightCalldataUint128_funded
            (by simp only [List.length_cons]; omega) (by rw [hadd 388 (by decide)]; exact h3)
            (by jump_dest) ha7 rd7
          rw [hadd 388 (by decide)] at rd8
          obtain ⟨aw9, k9, C9, ha9, rd9⟩ := midnightOfferStoreMaxUnits (by omega)
            (by simpa only [words, List.take, writeWordArray, Nat.reduceAdd] using hr 4) ha8 rd8
          by_cases h4 : (calldataWord I.calldata (rel.toNat + 420)).toNat < 2^128
          · obtain ⟨k10, C10, _, ha10, rd10⟩ := midnightCalldataUint128_funded
              (by simp only [List.length_cons]; omega) (by rw [hadd 420 (by decide)]; exact h4)
              (by jump_dest) ha9 rd9
            rw [hadd 420 (by decide)] at rd10
            right
            refine ⟨?_, ?_⟩
            · simpa only [OfferData.tailCanonicalAt, Nat.add_assoc, Nat.reduceAdd] using
                And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3 h4)))
            · simp only [offerTailPrefixMemory, offerTailPrefixWords, writeWordArray,
                Nat.add_assoc, Nat.reduceAdd]
              exact ⟨_, _, _, ha10, rd10⟩
          · left
            refine ⟨decodeOfferData_none_noncanon (by
              intro hc
              exact h4 (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hc.2.2.2.2.2.2.2)), ?_⟩
            exact midnightCalldataUint128_bad (by simp only [List.length_cons]; omega)
              (by rw [hadd 420 (by decide)]; exact h4) rd9
        · left
          refine ⟨decodeOfferData_none_noncanon (by
            intro hc
            exact h3 (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hc.2.2.2.2.2.2.1)), ?_⟩
          exact midnightCalldataUint128_bad (by simp only [List.length_cons]; omega)
            (by rw [hadd 388 (by decide)]; exact h3) rd7
      · left
        refine ⟨decodeOfferData_none_noncanon (by
          intro hc
          exact h2 (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hc.2.2.2.2.2.1)), ?_⟩
        exact midnightCalldataBool_bad (by simp only [List.length_cons]; omega)
          (by rw [hadd 356 (by decide)]; exact h2) rd5
    · left
      refine ⟨decodeOfferData_none_noncanon (by
        intro hc
        exact h1 (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hc.2.2.2.2.1)), ?_⟩
      exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega)
        (by rw [hadd 324 (by decide)]; exact h1) rd3
  · left
    refine ⟨decodeOfferData_none_noncanon (by
      intro hc
      exact h0 (by simpa only [Nat.add_assoc, Nat.reduceAdd] using hc.2.2.2.1)), ?_⟩
    exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega)
      (by rw [hadd 292 (by decide)]; exact h0) rd1

end Benchmarks.Midnight
