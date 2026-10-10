import Benchmarks.UniswapV3.Pool.BoundedActiveWords
import Benchmarks.UniswapV3.Pool.SwapInitStack

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapInitHeadBoundedX {limit : Nat} {σ σsnap : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw aw0 p snap fee remaining x5 x6 x7 x8 x9 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2822⟩
      ([UInt256.ofNat ee.header.timestamp, UInt256.ofNat 64 + p, p, ⟨0⟩,
        snap, x5, x6, x7, x8, x9, remaining] ++ R)
      (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ ee)
      aw rdata σ k C)
    (hm : HeapMemory mem aw0 p) (ha : BoundedActiveWords aw limit)
    (hs : Slot0Memory mem snap σsnap ee) (hsl : 96 ≤ snap.toNat)
    (hsb : snap.toNat + 224 ≤ p.toNat) (hb : p.toNat + 256 ≤ limit)
    (hov : R.length + 15 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2911⟩
      ([UInt256.ofNat 1, UInt256.ofNat 1, slot0FieldWord 0 20 σsnap ee,
        (p + UInt256.ofNat 192) + UInt256.ofNat 64, p + UInt256.ofNat 192, ⟨0⟩,
        UInt256.sgt remaining (UInt256.ofNat 0), p, snap, x5, x6, x7, x8, x9, remaining] ++ R)
      (swapStateHeadMem (wordArrayAllocMem mem p (swapCacheInitWords fee σ ee))
        (p + UInt256.ofNat 192) remaining) aw' rdata σ k' C' ∧ BoundedActiveWords aw' limit := by
  have hsmall := ha.small
  have hpfit : p.toNat + 256 < UInt256.size := by change _ < 2 ^ 256; omega
  have hpre := swapInitMemory_prefix mem p fee remaining σ ee (by omega)
  have hs' : Slot0Memory
      (swapStateHeadMem (wordArrayAllocMem mem p (swapCacheInitWords fee σ ee))
        (p + UInt256.ofNat 192) remaining) snap σsnap ee :=
    MemoryPrefix.wordArray hpre hs hsl hsb
  have hprice := Slot0Memory.load_price hs' (by omega)
  have r1 := uniswapV3Pool_block_2822 (immWords := wordsOf (immStore v)) hov rd
  rw [swapInitStack_eq fee remaining _ snap p x5 x6 x7 x8 x9 R σ ee hm (by omega) hprice,
    swapInitMemory_eq fee σ ee hm (by omega)] at r1
  refine ⟨_, _, _, r1, ?_⟩
  let cursor := UInt256.ofNat 64 + p
  let q := p + UInt256.ofNat 192
  let tail := swapCacheRawTailMem
    (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ ee)
    cursor (UInt256.ofNat ee.header.timestamp)
  have hload : memLoad (UInt256.ofNat 64) tail = q :=
    swapCacheRawTailMem_load fee σ ee hm (by omega)
  change BoundedActiveWords (M (M (M (M (M (M (M (M (M aw cursor ⟨32⟩)
    (UInt256.ofNat 32 + cursor) ⟨32⟩)
    (UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor)) ⟨32⟩)
    (UInt256.ofNat 32 + (UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor))) ⟨32⟩)
    (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩)
    (memLoad (UInt256.ofNat 64) tail) ⟨32⟩)
    (UInt256.ofNat 32 + memLoad (UInt256.ofNat 64) tail) ⟨32⟩)
    (UInt256.ofNat 0 + snap) ⟨32⟩) limit
  have hzero : UInt256.ofNat 0 + snap = snap := u256_zero_add snap
  rw [hload, hzero]
  have h64 : cursor.toNat = p.toNat + 64 := by
    dsimp only [cursor]
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat p 64 (by omega)
  have h96 : (UInt256.ofNat 32 + cursor).toNat = p.toNat + 96 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 32 (by rw [h64]; omega), h64]
  have h128 : (UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor)).toNat = p.toNat + 128 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 32 (by rw [h96]; omega), h96]
  have h160 : (UInt256.ofNat 32 + (UInt256.ofNat 32 +
      (UInt256.ofNat 32 + cursor))).toNat = p.toNat + 160 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 32 (by rw [h128]; omega), h128]
  have h192 : q.toNat = p.toNat + 192 := uadd_word_ofNat_toNat p 192 (by omega)
  have h224 : (UInt256.ofNat 32 + q).toNat = p.toNat + 224 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat _ 32 (by rw [h192]; omega), h192]
  have ha1 := BoundedActiveWords.expand32 ha (show cursor.toNat + 32 ≤ limit by rw [h64]; omega)
  have ha2 := BoundedActiveWords.expand32 ha1
    (show (UInt256.ofNat 32 + cursor).toNat + 32 ≤ limit by rw [h96]; omega)
  have ha3 := BoundedActiveWords.expand32 ha2
    (show (UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor)).toNat + 32 ≤ limit by
      rw [h128]; omega)
  have ha4 := BoundedActiveWords.expand32 ha3
    (show (UInt256.ofNat 32 + (UInt256.ofNat 32 +
      (UInt256.ofNat 32 + cursor))).toNat + 32 ≤ limit by rw [h160]; omega)
  have ha5 := BoundedActiveWords.expand32 (off := UInt256.ofNat 64) ha4
    (by change 64 + 32 ≤ limit; omega)
  have ha6 := BoundedActiveWords.expand32 (off := UInt256.ofNat 64) ha5
    (by change 64 + 32 ≤ limit; omega)
  have ha7 := BoundedActiveWords.expand32 ha6 (show q.toNat + 32 ≤ limit by rw [h192]; omega)
  have ha8 := BoundedActiveWords.expand32 ha7
    (show (UInt256.ofNat 32 + q).toNat + 32 ≤ limit by rw [h224]; omega)
  exact BoundedActiveWords.expand32 ha8 (by omega)

theorem swapInitHeadX {σ σsnap : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw aw0 p snap fee remaining x5 x6 x7 x8 x9 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2822⟩
      ([UInt256.ofNat ee.header.timestamp, UInt256.ofNat 64 + p, p, ⟨0⟩,
        snap, x5, x6, x7, x8, x9, remaining] ++ R)
      (swapCacheHeadMem (writeWord mem 64 (p + UInt256.ofNat 192)) p fee σ ee)
      aw rdata σ k C)
    (hm : HeapMemory mem aw0 p) (ha : ActiveWords aw)
    (hs : Slot0Memory mem snap σsnap ee) (hsl : 96 ≤ snap.toNat)
    (hsb : snap.toNat + 224 ≤ p.toNat) (hb : p.toNat + 256 ≤ 2 ^ 200)
    (hov : R.length + 15 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2911⟩
      ([UInt256.ofNat 1, UInt256.ofNat 1, slot0FieldWord 0 20 σsnap ee,
        (p + UInt256.ofNat 192) + UInt256.ofNat 64, p + UInt256.ofNat 192, ⟨0⟩,
        UInt256.sgt remaining (UInt256.ofNat 0), p, snap, x5, x6, x7, x8, x9, remaining] ++ R)
      (swapStateHeadMem (wordArrayAllocMem mem p (swapCacheInitWords fee σ ee))
        (p + UInt256.ofNat 192) remaining) aw' rdata σ k' C' ∧ ActiveWords aw' := by
  obtain ⟨aw', k', C', rd', ha'⟩ := swapInitHeadBoundedX (v := v)
    rd hm (BoundedActiveWords.of_active ha) hs hsl hsb hb hov
  exact ⟨aw', k', C', rd', ha'.active⟩

end Benchmarks.UniswapV3.Pool
