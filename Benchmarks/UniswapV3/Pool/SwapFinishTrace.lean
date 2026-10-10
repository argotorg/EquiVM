import Benchmarks.UniswapV3.Pool.SwapPayment
import Benchmarks.UniswapV3.Pool.WordArrayHeap
import Benchmarks.UniswapV3.Pool.HeapWordPairReturn
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_020

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
theorem swapFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw free p exactWord cache snap amount0 amount1 len start limit amount zero recipient : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨5137⟩
      ([p, exactWord, cache, snap, amount1, amount0, len, start, limit, amount, zero, recipient,
        ⟨621⟩] ++ R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hm : HeapMemory mem aw free) (hb : free.toNat + 160 ≤ 2 ^ 200)
    (hp : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 22 ≤ 1024) :
    RDret (deployedRuntime v) g s0 (storeSlot0Unlocked evm true).accountMap
      (amount0.toByteArray ++ amount1.toByteArray) := by
  have hoff (n : Nat) (hn : n ≤ 192) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hm1 := hm.expand32 (p + UInt256.ofNat 64) (by rw [hoff 64 (by decide)]; omega)
  have hm2 := hm1.expand32 (p + UInt256.ofNat 192) (by rw [hoff 192 (by decide)]; omega)
  have hm3 := hm2.expand32 (p + UInt256.ofNat 96) (by rw [hoff 96 (by decide)]; omega)
  have hload : memLoad (UInt256.ofNat 64) mem = free := hm.load64
  have hf32 : (free + UInt256.ofNat 32).toNat = free.toNat + 32 :=
    uadd_word_ofNat_toNat free 32 (by change _ < 2 ^ 256; omega)
  have hf64 : (UInt256.ofNat 64 + free).toNat = free.toNat + 64 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat free 64 (by change _ < 2 ^ 256; omega)
  have hf96 : (free + UInt256.ofNat 96).toNat = free.toNat + 96 :=
    uadd_word_ofNat_toNat free 96 (by change _ < 2 ^ 256; omega)
  have hf128 : (free + UInt256.ofNat 128).toNat = free.toNat + 128 :=
    uadd_word_ofNat_toNat free 128 (by change _ < 2 ^ 256; omega)
  let price := UInt256.land
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
    (memLoad (p + UInt256.ofNat 64) mem)
  let liquidity := UInt256.land (memLoad (p + UInt256.ofNat 192) mem)
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))
  let tick := UInt256.signextend (UInt256.ofNat 2) (memLoad (p + UInt256.ofNat 96) mem)
  let payload := [amount0, amount1, price, liquidity, tick]
  let memEvent := writeWordArray mem free.toNat payload
  have hfold : tick.toByteArray.write 0 (liquidity.toByteArray.write 0
      (price.toByteArray.write 0 (amount1.toByteArray.write 0
        (amount0.toByteArray.write 0 mem free.toNat 32) (free.toNat + 32) 32)
          (free.toNat + 64) 32) (free.toNat + 96) 32) (free.toNat + 128) 32 = memEvent := by
    simp only [memEvent, payload, writeWordArray, Reasoning.Theory.writeWord, Nat.add_assoc]
  dsimp only [price, liquidity, tick] at hfold
  let awState := M (M (M aw (p + UInt256.ofNat 64) ⟨32⟩)
    (p + UInt256.ofNat 192) ⟨32⟩) (p + UInt256.ofNat 96) ⟨32⟩
  have hactive : ActiveWords (M (M (M (M (M awState free ⟨32⟩)
      (free + UInt256.ofNat 32) ⟨32⟩) (UInt256.ofNat 64 + free) ⟨32⟩)
        (free + UInt256.ofNat 96) ⟨32⟩) (free + UInt256.ofNat 128) ⟨32⟩) :=
    activeWords_expand32 (activeWords_expand32 (activeWords_expand32
      (activeWords_expand32 (activeWords_expand32 hm3.active (by omega))
        (by rw [hf32]; omega)) (by rw [hf64]; omega)) (by rw [hf96]; omega))
      (by rw [hf128]; omega)
  have hmEvent := wordArrayHeap hm3.cursor payload (by simp [payload])
    (activeWords_expand hactive (off := free) (size := ⟨160⟩) hb)
  have hnewload : memLoad (UInt256.ofNat 64) memEvent = free := hmEvent.load64
  have hfirst : M awState (UInt256.ofNat 64) ⟨32⟩ = awState := expandedWords64_eq hm3.active
  have hsecond := expandedWords64_eq hactive
  change M (M (M (M (M (M awState free ⟨32⟩)
    (free + UInt256.ofNat 32) ⟨32⟩) (UInt256.ofNat 64 + free) ⟨32⟩)
      (free + UInt256.ofNat 96) ⟨32⟩) (free + UInt256.ofNat 128) ⟨32⟩)
        (UInt256.ofNat 64) ⟨32⟩ = _ at hsecond
  obtain ⟨k1, C1, r1⟩ := (uniswapV3Pool_block_5137 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 21 ≤ 1024; omega) rd).pack
  simp only [uniswapV3Pool_block_5137_stack, uniswapV3Pool_block_5137_memory,
    hload, hf32, hf64, hf96, hf128, hfold, hnewload] at r1
  rw [hfirst, hsecond] at r1
  obtain ⟨k2, C2, r2⟩ := uniswapV3Pool_block_5213 (immWords := wordsOf (immStore v))
    (by change R.length + 19 ≤ 1024; omega) hperm
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
  have hmap := storeSlot0Unlocked_accountMap evm true
  rw [slot0UnlockedWord_true, ← hs.accounts, hs.env] at hmap
  change (storeSlot0Unlocked evm true).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
          (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac ↦ ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256))))) at hmap
  simp only [uniswapV3Pool_block_5213_stack, ← hmap, u256_sub_self, u256_add_zero] at r2
  exact RD.poolReturnWordPair_heap (v := v) r2 hmEvent (by omega)
    (by change R.length + 5 ≤ 1024; omega)

end Benchmarks.UniswapV3.Pool
