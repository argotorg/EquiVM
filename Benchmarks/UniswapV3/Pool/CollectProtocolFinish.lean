import Benchmarks.UniswapV3.Pool.CollectProtocolPaymentTrace
import Benchmarks.UniswapV3.Pool.HeapTupleReturn

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem collectProtocolFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p amount0 amount1 x2 x3 recipient : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨9325⟩
      (amount1 :: amount0 :: x2 :: x3 :: recipient :: ⟨690⟩ :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hfit0 : amount0.toNat < 2 ^ 128) (hfit1 : amount1.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 64 ≤ 2 ^ 200) (hov : R.length + 13 ≤ 1024) :
    RDret (deployedRuntime v) g s0 (storeSlot0Unlocked evm true).accountMap
      (amount0.toByteArray ++ amount1.toByteArray) := by
  obtain ⟨_, _, rdEvent⟩ := uniswapV3Pool_block_9325 (immWords := wordsOf (immStore v)) hov hperm rd
  have hca : UInt256.land amount0 (UInt256.ofNat (2 ^ 128 - 1)) = amount0 := by
    rw [u256_land_comm]; exact uint128Word_clean hfit0
  have hcb : UInt256.land amount1 (UInt256.ofNat (2 ^ 128 - 1)) = amount1 := by
    rw [u256_land_comm]; exact uint128Word_clean hfit1
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hp32 : (p + (UInt256.ofNat 32)).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hfold : amount1.toByteArray.write 0 (amount0.toByteArray.write 0 mem p.toNat 32)
      (p.toNat + 32) 32 = pairEventMem mem p amount0 amount1 := rfl
  have hmEvent := pairEventHeap (first := amount0) (second := amount1) hm.cursor hb
  have hnewload : memLoad (UInt256.ofNat 64) (pairEventMem mem p amount0 amount1) = p := hmEvent.load64
  have hfirst : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hactive : ActiveWords (M (M aw p ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩) :=
    activeWords_expand32 (activeWords_expand32 hm.active (by omega)) (by rw [hp32]; omega)
  have hsecond : M (M (M aw p ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩ =
      M (M aw p ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩ := expandedWords64_eq hactive
  have hmap := storeSlot0Unlocked_accountMap evm true
  rw [slot0UnlockedWord_true, ← hs.accounts, hs.env] at hmap
  change (storeSlot0Unlocked evm true).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
          (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256))))) at hmap
  simp only [uniswapV3Pool_block_9325_stack, uniswapV3Pool_block_9325_memory, solcMask128,
    hca, hcb, hload, hp32, hfold, hnewload, u256_sub_self, u256_add_zero, hfirst, hsecond, ← hmap] at rdEvent
  have rdReturn := uniswapV3Pool_block_9434 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEvent
  simp only [uniswapV3Pool_block_9434_stack] at rdReturn
  exact RD.poolReturnUint128Pair_heap (v := v) rdReturn hmEvent hb hfit0 hfit1 (by omega)

end Benchmarks.UniswapV3.Pool
