import Benchmarks.UniswapV3.Pool.CollectFinish
import Benchmarks.UniswapV3.Pool.HeapWordPairReturn
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_031

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem burnFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p key amount a0 a1 x0 x1 lower upper : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨9833⟩
      (x0 :: x1 :: key :: a1 :: a0 :: amount :: upper :: lower :: ⟨621⟩ :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true) (ha : amount.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 96 ≤ 2 ^ 200) (hov : R.length + 16 ≤ 1024) :
    RDret (deployedRuntime v) g s0 (storeSlot0Unlocked evm true).accountMap
      (a0.toByteArray ++ a1.toByteArray) := by
  obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_9833 (immWords := wordsOf (immStore v))
    (by evm_ov) hperm rd
  have hc : UInt256.land amount (UInt256.ofNat (2 ^ 128 - 1)) = amount := by
    rw [u256_land_comm]; exact uint128Word_clean ha
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hp64 : (UInt256.ofNat 64 + p).toNat = p.toNat + 64 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have hfold : a1.toByteArray.write 0
      (a0.toByteArray.write 0 (amount.toByteArray.write 0 mem p.toNat 32) (p.toNat + 32) 32)
      (p.toNat + 64) 32 = tripleEventMem mem p amount a0 a1 := rfl
  have hmEvent := tripleEventHeap (a := amount) (b := a0) (c := a1) hm.cursor hb
  have hnewload : memLoad (UInt256.ofNat 64) (tripleEventMem mem p amount a0 a1) = p := hmEvent.load64
  have hfirst : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hactive : ActiveWords (M (M (M aw p ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩)
      (UInt256.ofNat 64 + p) ⟨32⟩) :=
    activeWords_expand32 (activeWords_expand32 (activeWords_expand32 hm.active (by omega))
      (by rw [hp32]; omega)) (by rw [hp64]; omega)
  have hsecond := expandedWords64_eq hactive
  change M (M (M (M aw p ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩)
    (UInt256.ofNat 64 + p) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩ = _ at hsecond
  simp only [uniswapV3Pool_block_9833_stack, uniswapV3Pool_block_9833_memory, solcMask128,
    hc, hload, hp32, hp64, hfold, hnewload, u256_sub_self, u256_add_zero, hfirst, hsecond] at r1
  obtain ⟨k2, C2, r2⟩ := uniswapV3Pool_block_9941 (immWords := wordsOf (immStore v))
    (by evm_ov) hperm (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  have hmap := storeSlot0Unlocked_accountMap evm true
  rw [slot0UnlockedWord_true, ← hs.accounts, hs.env] at hmap
  change (storeSlot0Unlocked evm true).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
          (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac ↦ ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256))))) at hmap
  simp only [uniswapV3Pool_block_9941_stack, ← hmap] at r2
  exact RD.poolReturnWordPair_heap (v := v) r2 hmEvent (by omega) (by omega)

end Benchmarks.UniswapV3.Pool
