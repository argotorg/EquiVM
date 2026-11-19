import Benchmarks.Midnight.MarketInitcodeTrace
import Benchmarks.Midnight.AllocationAccounting

/-! Initialization-code concatenation with allocation limits justified by gas payment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

theorem midnightMarketInitcodeConcat_accounted {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root prefixPtr encoded ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 11 ≤ 1024) (hb : root.toNat + m.encodingSize + 64 < UInt256.size)
    (hp : prefixPtr.toNat + 43 ≤ mem.size) (hpb : prefixPtr.toNat + 32 ≤ root.toNat)
    (he : encoded.toNat + 32 ≤ mem.size) (heb : encoded.toNat + 32 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hprefix : memLoad prefixPtr mem = UInt256.ofNat 11)
    (hencoded : memLoad encoded mem = UInt256.ofNat m.encodingSize)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hgas : midnightGasBound g.toUInt256) (ha0 : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨20604⟩
      (encoded :: ret :: (encoded + UInt256.ofNat 32) :: prefixPtr :: R) mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (root.toNat + m.encodingSize + 64 < 2^64 ∧
      ∃ aw' k' C', MemoryAccounting (marketInitcodeMemory mem root prefixPtr encoded m) aw' C' ∧
      RD midnightBytecode I g s0 ret (root :: (root + UInt256.ofNat 32) :: R)
      (marketInitcodeMemory mem root prefixPtr encoded m) aw' rdata σ k' C') := by
  have hword : UInt256.size = 2^256 := rfl
  have ha (n : Nat) (hn : n ≤ m.encodingSize + 64) :
      (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hp32 : (prefixPtr + UInt256.ofNat 32).toNat = prefixPtr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have he32 : (encoded + UInt256.ofNat 32).toNat = encoded.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hn : (UInt256.ofNat m.encodingSize).toNat = m.encodingSize :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hfirst : memLoad encoded (marketInitcodeFirstMemory mem root prefixPtr) =
      UInt256.ofNat m.encodingSize := by
    rw [marketInitcodeFirstMemory, copyZeroMemory_load_before _ _ _ _ _ _
      (by decide) (by omega) he (by omega), hencoded]
  dsimp only [marketInitcodeFirstMemory, copyZeroMemory, Reasoning.Theory.writeWord] at hfirst
  simp only [Nat.add_assoc, Nat.reduceAdd] at hfirst
  have hlen : UInt256.ofNat (11 + m.encodingSize + 32) + UInt256.lnot (UInt256.ofNat 31) =
      UInt256.ofNat (11 + m.encodingSize) := by
    rw [addNot31_ofNat (by omega) (by change _ < 2^256; omega)]
    congr 1
  have rd1 := midnightBlocks.midnight_block_20604 hstack (by jump_dest) rd
  have ha1 := memoryAccountingAt rd1 (by
    unfold midnightBlocks.midnight_block_20604_memory
    memory_account ha0)
  simp only [midnightBlocks.midnight_block_20604_stack,
    midnightBlocks.midnight_block_20604_memory, hfree, hprefix, hp32,
    wordAddNat_add, ha 32 (by omega), ha 43 (by omega),
    show (UInt256.ofNat 11).toNat = 11 from rfl] at rd1 ha1
  simp only [hfirst, hn, he32] at rd1 ha1
  simp only [wordAddNat_add, word_add_sub_left, hlen,
    ha (11 + m.encodingSize + 32) (by omega)] at rd1 ha1
  let scratch := writeWord (marketInitcodeCopyMemory mem root prefixPtr encoded m)
    root.toNat (UInt256.ofNat (11 + m.encodingSize))
  have hoff : 11 + m.encodingSize + 32 = 43 + m.encodingSize := by omega
  have hs : root.toNat + m.encodingSize + 64 ≤ scratch.size := by
    simp only [scratch, marketInitcodeCopyMemory, copyZeroMemory, writeWord_sparse_size]
    omega
  rcases memoryAccounting_headroom rd1 ha1 hgas with hoog | hroom
  · exact Or.inl hoog
  have hroom' : scratch.size + 2^62 < 2^64 := by
    simpa only [scratch, marketInitcodeCopyMemory, marketInitcodeFirstMemory, copyZeroMemory,
      Reasoning.Theory.writeWord, hoff, Nat.add_assoc, Nat.reduceAdd] using hroom
  have hfit : root.toNat + m.encodingSize + 64 < 2^64 := by omega
  right
  refine ⟨hfit, ?_⟩
  have hend := marketInitcodeAllocationEnd m hfit
  have hc : allocationCheck root (allocationEnd root (UInt256.ofNat (11 + m.encodingSize + 32))) =
      ⟨0⟩ := by
    rw [hend]
    apply allocationCheck_ok
    · rw [ha _ le_rfl]; omega
    · rw [ha _ le_rfl]; omega
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightAllocate_accounted
    (by simp only [List.length_cons]; omega) hc hret ha1 rd1
  rw [hend] at rd2 ha2
  refine ⟨aw2, k2, C2, ?_⟩
  simpa only [marketInitcodeMemory, marketInitcodeCopyMemory, marketInitcodeFirstMemory,
    copyZeroMemory, Reasoning.Theory.writeWord, hoff, Nat.add_assoc, Nat.reduceAdd] using And.intro ha2 rd2

end Benchmarks.Midnight
