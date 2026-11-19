import Benchmarks.Midnight.LiquidateCallbackMarketPrefix
import Benchmarks.Midnight.MarketEncodeMemory

/-! The three disjoint word ranges filled before the callback's remaining scalar fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem liquidateCallbackMarketPrefixMemory_words (mem : ByteArray) (root : Nat)
    (sender : AccountAddress) (id : UInt256) (m : MarketData)
    (hb : root + 612 + 128 * m.collaterals.length < UInt256.size) :
    let output := liquidateCallbackMarketPrefixMemory mem root sender id m
    MemoryWords output (root + 4) [UInt256.ofNat sender.val, id, UInt256.ofNat 320] ∧
    MemoryWords output (root + 324)
      [m.chainId, UInt256.ofNat m.midnight.val, UInt256.ofNat m.loanToken.val, UInt256.ofNat 256] ∧
    MemoryWords output (root + 580)
      (UInt256.ofNat m.collaterals.length :: m.collaterals.flatMap CollateralData.words) := by
  let memPrefix := liquidateCallbackPrefixMemory mem root sender id
  let first := [m.chainId, UInt256.ofNat m.midnight.val,
    UInt256.ofNat m.loanToken.val, UInt256.ofNat 256]
  let head := writeWordArray memPrefix (root + 324) first
  let written := m.collaterals.flatMap CollateralData.words
  have hn : written.length = 4 * m.collaterals.length := collateralWords_length _
  have hm : liquidateCallbackMarketPrefixMemory mem root sender id m =
      writeWordArray (writeWord head (root + 580) (UInt256.ofNat m.collaterals.length))
        (root + 612) written := by
    simp only [liquidateCallbackMarketPrefixMemory, liquidateCallbackArrayHeadMemory,
      liquidateCallbackHeadMemory, head, first, memPrefix, written, writeWordArray,
      Nat.add_assoc, Nat.reduceAdd]
  dsimp only
  rw [hm]
  have hcaller : MemoryWords memPrefix (root + 4)
      [UInt256.ofNat sender.val, id, UInt256.ofNat 320] :=
    MemoryWords.of_writeWordArray _ _ _ (by
      simp only [List.length_cons, List.length_nil]; omega) (by simp)
  have hcaller1 := hcaller.writeWords (off := root + 324) first (Or.inl (by
    simp only [List.length_cons, List.length_nil]; omega))
  have hcaller2 := hcaller1.writeWord (off := root + 580) (UInt256.ofNat m.collaterals.length)
    (Or.inl (by simp only [List.length_cons, List.length_nil]; omega))
  have hcaller3 := hcaller2.writeWords (off := root + 612) written
    (Or.inl (by simp only [List.length_cons, List.length_nil]; omega))
  refine ⟨hcaller3, ?_, ?_⟩
  · have hfirst : MemoryWords head (root + 324) first :=
      MemoryWords.of_writeWordArray _ _ _ (by
        simp only [first, List.length_cons, List.length_nil]; omega) (by simp [first])
    exact (hfirst.writeWord (off := root + 580) (UInt256.ofNat m.collaterals.length)
      (Or.inl (by simp only [first, List.length_cons, List.length_nil]; omega))).writeWords
      (off := root + 612) written
      (Or.inl (by simp only [first, List.length_cons, List.length_nil]; omega))
  · have hcount : MemoryWords (writeWord head (root + 580) (UInt256.ofNat m.collaterals.length))
        (root + 580) [UInt256.ofNat m.collaterals.length] :=
      MemoryWords.of_writeWord _ _ _ (by omega)
    have ht := hcount.append_writeWordArray written (by
      simp only [List.length_append, List.length_cons, List.length_nil, hn]; omega)
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc,
      List.cons_append, List.nil_append] using ht

end Benchmarks.Midnight
