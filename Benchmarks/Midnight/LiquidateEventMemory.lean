import Benchmarks.Midnight.RuntimeBlocks_024
import Benchmarks.Midnight.WordArray
import Benchmarks.Midnight.AddressDecode

/-! The nine-word liquidation event buffer and preservation of lower memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateEventHeadWords (I : ExecutionEnv) (seized repaid mode receiver payer : UInt256) :
    List UInt256 :=
  [UInt256.ofNat I.source.val, seized, repaid, UInt256.isZero (UInt256.isZero mode),
    UInt256.land receiver solcAddrMask, UInt256.land payer solcAddrMask]

def liquidateEventHeadMemory (mem : ByteArray) (root : UInt256) (I : ExecutionEnv)
    (seized repaid mode receiver payer : UInt256) : ByteArray :=
  writeWordArray mem root.toNat (liquidateEventHeadWords I seized repaid mode receiver payer)

def liquidateEventMemory (mem : ByteArray) (root : UInt256) (I : ExecutionEnv)
    (seized repaid mode receiver payer badDebt loss fee : UInt256) : ByteArray :=
  writeWordArray mem root.toNat
    (liquidateEventHeadWords I seized repaid mode receiver payer ++ [badDebt, loss, fee])

theorem liquidateEventHeadMemory_eq {mem : ByteArray} {root seized repaid mode receiver payer : UInt256}
    (I : ExecutionEnv) (hroot : root.toNat < 2^64) (hlo : 832 ≤ root.toNat)
    (hsize : 832 ≤ mem.size) (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid) :
    midnightBlocks.midnight_block_5548_memory (ee := I) (mem := mem)
      (x1 := mode) (x6 := receiver) (x7 := payer) =
      liquidateEventHeadMemory mem root I seized repaid mode receiver payer := by
  have hadd (n : Nat) (hn : n ≤ 256) : (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  let caller := UInt256.ofNat I.source.val
  have hms1 : memLoad (UInt256.ofNat 640) (writeWord mem root.toNat caller) = seized := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by change 640 + 32 ≤ mem.size; omega)
      (Or.inl (by change 640 + 32 ≤ root.toNat; omega)), hseized]
  have hmr1 : memLoad (UInt256.ofNat 608) (writeWord mem root.toNat caller) = repaid := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by change 608 + 32 ≤ mem.size; omega)
      (Or.inl (by change 608 + 32 ≤ root.toNat; omega)), hpaid]
  have hmr2 : memLoad (UInt256.ofNat 608)
      (writeWord (writeWord mem root.toNat caller) (root.toNat + 32) seized) = repaid := by
    rw [memLoad_writeWord_preserved _ _ _ _ (by
      change 608 + 32 ≤ (writeWord mem root.toNat caller).size
      rw [writeWord_sparse_size]; omega)
      (Or.inl (by change 608 + 32 ≤ root.toNat + 32; omega)), hmr1]
  dsimp only [Reasoning.Theory.writeWord, caller] at hms1 hmr2
  simp only [midnightBlocks.midnight_block_5548_memory, hfree,
    hadd 32 (by decide), hadd 64 (by decide), hadd 96 (by decide),
    hadd 128 (by decide), hadd 160 (by decide), hms1, hmr2, addressMask_computed]
  simp only [liquidateEventHeadMemory, liquidateEventHeadWords, writeWordArray,
    Reasoning.Theory.writeWord, Nat.add_assoc, Nat.reduceAdd]

theorem liquidateEventMemory_tail {mem : ByteArray} {root : UInt256} (I : ExecutionEnv)
    (seized repaid mode receiver payer badDebt loss fee : UInt256) (hroot : root.toNat < 2^64) :
    midnightBlocks.midnight_block_5636_memory
      (mem := liquidateEventHeadMemory mem root I seized repaid mode receiver payer)
      (x0 := root) (x1 := UInt256.ofNat 192) (x2 := badDebt) (x3 := loss) (x4 := fee) (x5 := root) =
      liquidateEventMemory mem root I seized repaid mode receiver payer badDebt loss fee := by
  have hadd (n : Nat) (hn : n ≤ 256) : (root + UInt256.ofNat n).toNat = root.toNat + n :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  simp only [midnightBlocks.midnight_block_5636_memory,
    hadd 192 (by decide), hadd 224 (by decide), hadd 256 (by decide),
    liquidateEventMemory, writeWordArray_append]
  simp only [liquidateEventHeadMemory, liquidateEventHeadWords, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul, writeWordArray, Reasoning.Theory.writeWord, Nat.add_assoc]

theorem liquidateEventMemory_size_ge (mem : ByteArray) (root : UInt256) (I : ExecutionEnv)
    (seized repaid mode receiver payer badDebt loss fee : UInt256) :
    mem.size ≤ (liquidateEventMemory mem root I seized repaid mode receiver payer badDebt loss fee).size :=
  writeWordArray_size_ge ..

theorem liquidateEventMemory_load_below (mem : ByteArray) (root read : UInt256) (I : ExecutionEnv)
    (seized repaid mode receiver payer badDebt loss fee : UInt256)
    (hin : read.toNat + 32 ≤ mem.size) (hbelow : read.toNat + 32 ≤ root.toNat) :
    memLoad read (liquidateEventMemory mem root I seized repaid mode receiver payer badDebt loss fee) =
      memLoad read mem := memLoad_writeWordArray_below _ _ _ _ hin hbelow

end Benchmarks.Midnight
