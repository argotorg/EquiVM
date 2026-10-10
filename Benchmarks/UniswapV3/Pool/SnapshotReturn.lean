import Benchmarks.UniswapV3.Pool.SnapshotArithmetic
import Benchmarks.UniswapV3.Pool.WordArrayMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_010

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem writeWordArray_readTriple (mem : ByteArray) (off : Nat) (a b c : UInt256) :
    (writeWordArray mem off [a, b, c]).readWithPadding off 96 = wordBytes [a, b, c] := by
  have hs := writeWordArray_size mem off [a, b, c] (by simp)
  have h0 := writeWordArray_read mem off [a, b, c] 0 (by change 0 < 3; decide)
  have h1 := writeWordArray_read mem off [a, b, c] 1 (by change 1 < 3; decide)
  have h2 := writeWordArray_read mem off [a, b, c] 2 (by change 2 < 3; decide)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at hs h0 h1 h2
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split_unbounded _ _ 32 64 (by decide) (by decide) (by omega),
    byteArray_readWithPadding_split_unbounded _ _ 32 32 (by decide) (by decide) (by omega)]
  rw [show off + 32 + 32 = off + 64 by omega, h0, h1, h2]
  simp only [wordBytes, ByteArray.append_empty]

theorem writeWordArray_load64 {mem : ByteArray} {aw p : UInt256}
    (hm : HeapMemory mem aw p) (ws : List UInt256) :
    memLoad (UInt256.ofNat 64) (writeWordArray mem p.toNat ws) = p := by
  apply mloadWordValue_of_readWithPadding
  · have hs := writeWordArray_size_mono mem p.toNat ws
    have h := hm.size
    change 64 < _
    omega
  · change (writeWordArray mem p.toNat ws).readWithPadding 64 32 = _
    rw [writeWordArray_preserve_below mem p.toNat 64 ws (by have := hm.lower; omega) hm.size]
    exact hm.free

theorem snapshotReturnX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p seconds liquidity tick : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨1952⟩ (seconds :: liquidity :: tick :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 96 ≤ 2 ^ 200) (hov : R.length + 7 ≤ 1024) :
    RDret (deployedRuntime v) g s0 σ (wordBytes (snapshotCleanWords seconds liquidity tick)) := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 160 - 1) := by native_decide
  have h32 := uadd_word_ofNat_toNat p 32 (show p.toNat + 32 < UInt256.size by change _ < 2 ^ 256; omega)
  have h64 : (UInt256.ofNat 64 + p).toNat = p.toNat + 64 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have hfold : (UInt256.land (UInt256.ofNat 4294967295) seconds).toByteArray.write 0
      ((UInt256.land liquidity (UInt256.ofNat (2 ^ 160 - 1))).toByteArray.write 0
        ((UInt256.signextend (UInt256.ofNat 6) tick).toByteArray.write 0 mem p.toNat 32)
        (p.toNat + 32) 32) (p.toNat + 64) 32 =
      writeWordArray mem p.toNat (snapshotCleanWords seconds liquidity tick) := rfl
  have hnew := writeWordArray_load64 hm (snapshotCleanWords seconds liquidity tick)
  have hr := uniswapV3Pool_block_1952 (immWords := wordsOf (immStore v)) hov rd
  simp only [hload, hmask, h32, h64, hfold, hnew, u256_sub_self, u256_add_zero] at hr
  change RDret (deployedRuntime v) g s0 σ
    ((writeWordArray mem p.toNat (snapshotCleanWords seconds liquidity tick)).readWithPadding p.toNat 96) at hr
  rw [snapshotCleanWords, writeWordArray_readTriple] at hr
  exact hr

end Benchmarks.UniswapV3.Pool
