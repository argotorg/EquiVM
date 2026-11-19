import Benchmarks.Midnight.MarketInitcodeTrace
import Benchmarks.Midnight.RuntimeBlocks_081

/-! Concatenating the SSTORE2 prefix with the market payload before CREATE2. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000 in
theorem midnightMarketDeploymentConcat {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root prefixPtr encoded : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 11 ≤ 1024) (hb : root.toNat + m.encodingSize + 64 < 2^64)
    (hp : prefixPtr.toNat + 43 ≤ mem.size) (hpb : prefixPtr.toNat + 32 ≤ root.toNat)
    (he : encoded.toNat + 32 ≤ mem.size) (heb : encoded.toNat + 32 ≤ root.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hprefix : memLoad prefixPtr mem = UInt256.ofNat 11)
    (hencoded : memLoad encoded mem = UInt256.ofNat m.encodingSize)
    (rd : RD midnightBytecode I g s0 ⟨21601⟩
      (encoded :: (encoded + UInt256.ofNat 32) :: prefixPtr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ⟨21662⟩ (root :: (root + UInt256.ofNat 32) :: R)
      (marketInitcodeMemory mem root prefixPtr encoded m) aw' rdata σ k' C' := by
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
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_21601_packed (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_21601_stack,
    midnightBlocks.midnight_block_21601_memory, hfree, hprefix, hp32,
    wordAddNat_add, ha 32 (by omega), ha 43 (by omega),
    show (UInt256.ofNat 11).toNat = 11 from rfl] at rd1
  simp only [hfirst, hn, he32] at rd1
  simp only [wordAddNat_add, word_add_sub_left,
    u256_add_comm (UInt256.ofNat 32), wordAddNat_add, word_add_sub_left, hlen,
    ha (11 + m.encodingSize + 32) (by omega)] at rd1
  have hend := marketInitcodeAllocationEnd m hb
  have hc : allocationCheck root (allocationEnd root (UInt256.ofNat (11 + m.encodingSize + 32))) =
      ⟨0⟩ := by
    rw [hend]
    apply allocationCheck_ok
    · rw [ha _ le_rfl]; omega
    · rw [ha _ le_rfl]; omega
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightAllocate
    (by simp only [List.length_cons]; omega) hc (by jump_dest) rd1
  rw [hend] at rd2
  have hoff : 11 + m.encodingSize + 32 = 43 + m.encodingSize := by omega
  refine ⟨aw2, k2, C2, ?_⟩
  simpa only [marketInitcodeMemory, marketInitcodeCopyMemory, marketInitcodeFirstMemory,
    copyZeroMemory, Reasoning.Theory.writeWord, hoff, Nat.add_assoc, Nat.reduceAdd] using rd2


end Benchmarks.Midnight
