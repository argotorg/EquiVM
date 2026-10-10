import Benchmarks.UniswapV3.Pool.BoundedActiveWords
import Benchmarks.UniswapV3.Pool.SwapInitMemory
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace
import Benchmarks.UniswapV3.Pool.FeeGrowthStorage
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_013

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapStateMiddleMem (mem : ByteArray) (cursor price tick : UInt256) : ByteArray :=
  writeWord (writeWord mem cursor.toNat price) (UInt256.ofNat 32 + cursor).toNat tick

theorem swapStateMiddleMemory_eq (mem : ByteArray) (cursor price tick snap : UInt256)
    (hp : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) price = price)
    (ht : memLoad (UInt256.ofNat 32 + snap) (writeWord mem cursor.toNat price) = tick)
    (htc : UInt256.signextend (UInt256.ofNat 2) tick = tick) :
    uniswapV3Pool_block_2911_taken_memory (mem := mem) (x0 := UInt256.ofNat 1)
      (x1 := UInt256.ofNat 1) (x2 := price) (x3 := cursor) (x8 := snap) =
      swapStateMiddleMem mem cursor price tick := by
  simp only [uniswapV3Pool_block_2911_taken_memory, amountDeltaMask160, hp]
  change writeWord (writeWord mem cursor.toNat price) (UInt256.ofNat 32 + cursor).toNat
    (UInt256.signextend (UInt256.ofNat 2)
      (memLoad (UInt256.ofNat 32 + snap) (writeWord mem cursor.toNat price))) = _
  rw [ht, htc]
  rfl

theorem swapStateMiddleBoundedX {limit : Nat} {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw cursor price tick snap x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (zero : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2911⟩
      ([UInt256.ofNat 1, UInt256.ofNat 1, price, cursor, x4, x5, x6, x7,
        snap, x9, x10, x11, x12, x13, x14, zero.toUInt256] ++ R) mem aw rdata σ k C)
    (hp : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) price = price)
    (ht : memLoad (UInt256.ofNat 32 + snap) (writeWord mem cursor.toNat price) = tick)
    (htc : UInt256.signextend (UInt256.ofNat 2) tick = tick)
    (ha : BoundedActiveWords aw limit) (hb : cursor.toNat + 64 ≤ limit)
    (hs : snap.toNat + 64 ≤ limit) (hov : R.length + 17 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2950⟩
      ([feeGrowthWord (!zero) σ ee, UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor),
        x4, x5, x6, x7, snap, x9, x10, x11, x12, x13, x14, zero.toUInt256] ++ R)
      (swapStateMiddleMem mem cursor price tick) aw' rdata σ k' C' ∧
      BoundedActiveWords aw' limit := by
  have hsmall := ha.small
  have hmem := swapStateMiddleMemory_eq mem cursor price tick snap hp ht htc
  have h32 : (UInt256.ofNat 32 + cursor).toNat = cursor.toNat + 32 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat cursor 32 (by change _ < 2 ^ 256; omega)
  have hs32 : (UInt256.ofNat 32 + snap).toNat = snap.toNat + 32 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat snap 32 (by change _ < 2 ^ 256; omega)
  have ha' := BoundedActiveWords.expand32
    (BoundedActiveWords.expand32
      (BoundedActiveWords.expand32 ha (show cursor.toNat + 32 ≤ limit by omega))
      (show (UInt256.ofNat 32 + snap).toNat + 32 ≤ limit by rw [hs32]; omega))
    (show (UInt256.ofNat 32 + cursor).toNat + 32 ≤ limit by rw [h32]; omega)
  cases zero
  · have r1 := uniswapV3Pool_block_2911_fallthrough (immWords := wordsOf (immStore v))
      hov rfl rd
    have hmem' : uniswapV3Pool_block_2911_fallthrough_memory (mem := mem)
        (x0 := UInt256.ofNat 1) (x1 := UInt256.ofNat 1) (x2 := price)
        (x3 := cursor) (x8 := snap) = swapStateMiddleMem mem cursor price tick := hmem
    rw [hmem'] at r1
    obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_2939 (immWords := wordsOf (immStore v))
      (by change R.length + 13 + 2 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    exact ⟨_, kr, Cr, rr, ha'⟩
  · have r1 := uniswapV3Pool_block_2911_taken (immWords := wordsOf (immStore v))
      hov (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    rw [hmem] at r1
    obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_2946 (immWords := wordsOf (immStore v))
      (by change R.length + 13 + 1 ≤ 1024; omega) r1
    exact ⟨_, kr, Cr, rr, ha'⟩

theorem swapStateMiddleX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw cursor price tick snap x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (zero : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2911⟩
      ([UInt256.ofNat 1, UInt256.ofNat 1, price, cursor, x4, x5, x6, x7,
        snap, x9, x10, x11, x12, x13, x14, zero.toUInt256] ++ R) mem aw rdata σ k C)
    (hp : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) price = price)
    (ht : memLoad (UInt256.ofNat 32 + snap) (writeWord mem cursor.toNat price) = tick)
    (htc : UInt256.signextend (UInt256.ofNat 2) tick = tick)
    (ha : ActiveWords aw) (hb : cursor.toNat + 64 ≤ 2 ^ 200)
    (hs : snap.toNat + 64 ≤ 2 ^ 200) (hov : R.length + 17 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨2950⟩
      ([feeGrowthWord (!zero) σ ee, UInt256.ofNat 32 + (UInt256.ofNat 32 + cursor),
        x4, x5, x6, x7, snap, x9, x10, x11, x12, x13, x14, zero.toUInt256] ++ R)
      (swapStateMiddleMem mem cursor price tick) aw' rdata σ k' C' ∧ ActiveWords aw' := by
  obtain ⟨aw', k', C', rd', ha'⟩ := swapStateMiddleBoundedX (v := v)
    zero rd hp ht htc (BoundedActiveWords.of_active ha) hb hs hov
  exact ⟨aw', k', C', rd', ha'.active⟩

end Benchmarks.UniswapV3.Pool
