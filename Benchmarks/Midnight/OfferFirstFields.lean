import Benchmarks.Midnight.OfferFirstBlocks
import Benchmarks.Midnight.OfferDecodeFacts

variable {fork : Ethereum.Fork}

/-! The offer's market pointer and first seven scalar fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def offerFirstWords (bytes : ByteArray) (base : Nat) (market : UInt256) : List UInt256 :=
  [market, calldataWord bytes (base + 32), calldataWord bytes (base + 64),
    calldataWord bytes (base + 96), calldataWord bytes (base + 128),
    calldataWord bytes (base + 160), calldataWord bytes (base + 192),
    calldataWord bytes (base + 224)]

def offerFirstMemory (mem bytes : ByteArray) (base : Nat) (market : UInt256) : ByteArray :=
  writeWordArray mem 832 (offerFirstWords bytes base market)

set_option maxHeartbeats 800000 in
theorem midnightOfferFirstFields {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw market rel : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hrel : rel.toNat < 2^64) (hm : 416 ≤ mem.size)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10530⟩ (market :: rel :: R) mem aw rdata σ k C) :
    (decodeOfferData I.calldata (rel.toNat + 4) = none ∧ RDrev fork midnightBytecode g s0) ∨
    ((calldataWord I.calldata (rel.toNat + 36) = ⟨0⟩ ∨
        calldataWord I.calldata (rel.toNat + 36) = ⟨1⟩) ∧
      (calldataWord I.calldata (rel.toNat + 68)).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata (rel.toNat + 228)).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata (rel.toNat + 260)).toNat < 2^64 ∧
      ∃ aw' k' C',
        MemoryFunding credit (offerFirstMemory mem I.calldata (rel.toNat + 4) market) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨10669⟩
          (rel :: calldataWord I.calldata (rel.toNat + 260) :: R)
          (offerFirstMemory mem I.calldata (rel.toNat + 4) market) aw' rdata σ k' C') := by
  have hadd (off : Nat) (ho : off ≤ 260) :
      (rel + UInt256.ofNat off).toNat = rel.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightOfferStoreMarket (by omega) hroot ha rd
  by_cases hb : calldataWord I.calldata (rel.toNat + 36) = ⟨0⟩ ∨
      calldataWord I.calldata (rel.toNat + 36) = ⟨1⟩
  · obtain ⟨k2, C2, _, ha2, rd2⟩ := midnightCalldataBool_funded
      (by simp only [List.length_cons]; omega) (by rw [hadd 36 (by decide)]; exact hb)
      (by jump_dest) ha1 rd1
    rw [hadd 36 (by decide)] at rd2
    have hr1 : memLoad (UInt256.ofNat 384) (writeWord mem 832 market) = ⟨832⟩ := by
      rw [offerRoot_writeWord _ _ _ hm (by decide), hroot]
    obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightOfferStoreBuy (by omega) hr1 ha2 rd2
    by_cases hmaker : (calldataWord I.calldata (rel.toNat + 68)).toNat < EVM.addressModulus
    · obtain ⟨k4, C4, _, ha4, rd4⟩ := midnightCalldataAddress_funded
        (by simp only [List.length_cons]; omega) (by rw [hadd 68 (by decide)]; exact hmaker)
        (by jump_dest) ha3 rd3
      rw [hadd 68 (by decide)] at rd4
      let m2 := writeWord (writeWord mem 832 market) 864
        (calldataWord I.calldata (rel.toNat + 36))
      have hm2 : 416 ≤ m2.size := by simp only [m2, writeWord_sparse_size]; omega
      have hr2 : memLoad (UInt256.ofNat 384) m2 = ⟨832⟩ := by
        dsimp only [m2]
        rw [offerRoot_writeWord _ _ _ (by rw [writeWord_sparse_size]; omega)
          (by decide), hr1]
      obtain ⟨aw5, k5, C5, ha5, rd5⟩ := midnightOfferStoreMiddle
        (by omega) hrel hm2 hr2 ha4 rd4
      by_cases hcallback : (calldataWord I.calldata (rel.toNat + 228)).toNat < EVM.addressModulus
      · obtain ⟨k6, C6, _, ha6, rd6⟩ := midnightCalldataAddress_funded
          (by simp only [List.length_cons]; omega) (by rw [hadd 228 (by decide)]; exact hcallback)
          (by jump_dest) ha5 rd5
        rw [hadd 228 (by decide)] at rd6
        let m3 := offerMiddleMemory m2 I.calldata (rel.toNat + 4)
          (calldataWord I.calldata (rel.toNat + 68))
        have hr3 : memLoad (UInt256.ofNat 384) m3 = ⟨832⟩ := by
          dsimp only [m3]
          rw [offerMiddleMemory, memLoad_writeWordArray_below m2 896 (UInt256.ofNat 384)
            _ hm2 (by decide), hr2]
        dsimp only [m3] at hr3
        by_cases hoff : (calldataWord I.calldata (rel.toNat + 260)).toNat < 2^64
        · have hg : UInt256.gt (calldataWord I.calldata (rel + UInt256.ofNat 260).toNat)
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
                (UInt256.ofNat 1)) = ⟨0⟩ := by
            rw [hadd 260 (by decide)]
            apply ugt_zero
            change _ ≤ 2^64 - 1
            omega
          have rd7 := midnightBlocks.midnight_block_10639_fallthrough (by omega) hg rd6
          have ha7 := memoryFundingAt (credit := credit) rd7 (by
            unfold midnightBlocks.midnight_block_10639_fallthrough_memory
            memory_fund ha6)
          simp only [midnightBlocks.midnight_block_10639_fallthrough_stack,
            midnightBlocks.midnight_block_10639_fallthrough_memory, hr3,
            hadd 260 (by decide)] at ha7 rd7
          right
          refine ⟨hb, hmaker, hcallback, hoff, ?_⟩
          have he : writeWord m3 1056 (calldataWord I.calldata (rel.toNat + 228)) =
              offerFirstMemory mem I.calldata (rel.toNat + 4) market := by
            simp only [m3, m2, offerMiddleMemory, offerMiddleWords, offerFirstMemory,
              offerFirstWords, writeWordArray, Nat.add_assoc, Nat.reduceAdd]
          change MemoryFunding credit
            (writeWord m3 1056 (calldataWord I.calldata (rel.toNat + 228))) _ _ at ha7
          change RD fork midnightBytecode I g s0 ⟨10669⟩
            (rel :: calldataWord I.calldata (rel.toNat + 260) :: R)
            (writeWord m3 1056 (calldataWord I.calldata (rel.toNat + 228))) _ rdata σ _ _ at rd7
          rw [he] at ha7 rd7
          exact ⟨_, _, _, ha7, rd7⟩
        · left
          refine ⟨decodeOfferData_none_callbackOffset (by
            simpa only [Nat.add_assoc, Nat.reduceAdd] using hoff), ?_⟩
          have hg : UInt256.gt (calldataWord I.calldata (rel + UInt256.ofNat 260).toNat)
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
                (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
            rw [hadd 260 (by decide), ugt_one (by change 2^64 - 1 < _; omega)]
            decide
          have rr := midnightBlocks.midnight_block_10639_taken (by omega) hg (by jump_dest) rd6
          exact midnightBlocks.midnight_block_6350 (by
            simp only [midnightBlocks.midnight_block_10639_taken_stack, List.length_cons]; omega) rr
      · left
        refine ⟨decodeOfferData_none_noncanon (by
          intro h
          exact hcallback (by simpa only [Nat.add_assoc, Nat.reduceAdd] using h.2.2.1)), ?_⟩
        exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega)
          (by rw [hadd 228 (by decide)]; exact hcallback) rd5
    · left
      refine ⟨decodeOfferData_none_noncanon (by
        intro h
        exact hmaker (by simpa only [Nat.add_assoc, Nat.reduceAdd] using h.2.1)), ?_⟩
      exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega)
        (by rw [hadd 68 (by decide)]; exact hmaker) rd3
  · left
    refine ⟨decodeOfferData_none_noncanon (by
      intro h
      exact hb (by simpa only [Nat.add_assoc, Nat.reduceAdd] using h.1)), ?_⟩
    exact midnightCalldataBool_bad (by simp only [List.length_cons]; omega)
      (by rw [hadd 36 (by decide)]; exact hb) rd1

end Benchmarks.Midnight
