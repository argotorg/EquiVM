import Benchmarks.UniswapV3.Pool.HeapTupleReturn
import Benchmarks.UniswapV3.Pool.CollectPaymentsSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_027

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the memory and cursor after a three-word event payload.
def tripleEventMem (mem : ByteArray) (p a b c : UInt256) : ByteArray :=
  writeWord (pairEventMem mem p a b) (p.toNat + 64) c

def tripleEventWords (aw p : UInt256) : UInt256 :=
  M (M (M (M aw p ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩) (UInt256.ofNat 64 + p) ⟨32⟩) p ⟨96⟩

theorem tripleEventHeap {mem aw p a b c} (hm : MemoryCursor mem aw p) (hb : p.toNat + 96 ≤ 2 ^ 200) :
    HeapMemory (tripleEventMem mem p a b c) (tripleEventWords aw p) p := by
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hp64 : (UInt256.ofNat 64 + p).toNat = p.toNat + 64 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have h1 := hm.writeAbove p a (le_refl _) (by omega)
  have h2 := h1.cursor.writeAbove (p + UInt256.ofNat 32) b (by rw [hp32]; omega) (by rw [hp32]; omega)
  have h3 := h2.cursor.writeAbove (UInt256.ofNat 64 + p) c (by rw [hp64]; omega) (by rw [hp64]; omega)
  rw [hp32, hp64] at h3
  exact ⟨h3.size, h3.free, h3.lower, h3.gap, activeWords_expand h3.active hb⟩

theorem collectFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p position amount0 amount1 x3 x4 x5 x6 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (recipient : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 ⟨7965⟩
      (position :: amount1 :: amount0 :: x3 :: x4 :: x5 :: x6 :: EVM.word recipient.val :: ⟨690⟩ :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hfit0 : amount0.toNat < 2 ^ 128) (hfit1 : amount1.toNat < 2 ^ 128)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 96 ≤ 2 ^ 200) (hov : R.length + 16 ≤ 1024) :
    RDret (deployedRuntime v) g s0 (storeSlot0Unlocked evm true).accountMap
      (amount0.toByteArray ++ amount1.toByteArray) := by
  obtain ⟨_, _, rdEvent⟩ := uniswapV3Pool_block_7965 (immWords := wordsOf (immStore v)) (by evm_ov) hperm rd
  have hca : UInt256.land amount0 (UInt256.ofNat (2 ^ 128 - 1)) = amount0 := by
    rw [u256_land_comm]; exact uint128Word_clean hfit0
  have hcb : UInt256.land amount1 (UInt256.ofNat (2 ^ 128 - 1)) = amount1 := by
    rw [u256_land_comm]; exact uint128Word_clean hfit1
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by native_decide
  have hr : UInt256.land (EVM.word recipient.val) solcAddrMask = EVM.word recipient.val := by
    rw [← word_of_addressOfNat_eq_mask, accountAddress_of_word_val]
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hp64 : (UInt256.ofNat 64 + p).toNat = p.toNat + 64 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have hfold : amount1.toByteArray.write 0
      (amount0.toByteArray.write 0 ((EVM.word recipient.val).toByteArray.write 0 mem p.toNat 32)
        (p.toNat + 32) 32) (p.toNat + 64) 32 =
      tripleEventMem mem p (EVM.word recipient.val) amount0 amount1 := rfl
  have hmEvent := tripleEventHeap (a := EVM.word recipient.val) (b := amount0) (c := amount1) hm.cursor hb
  have hnewload : memLoad (UInt256.ofNat 64)
      (tripleEventMem mem p (EVM.word recipient.val) amount0 amount1) = p := hmEvent.load64
  have hfirst : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hactive : ActiveWords (M (M (M aw p ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩)
      (UInt256.ofNat 64 + p) ⟨32⟩) :=
    activeWords_expand32 (activeWords_expand32 (activeWords_expand32 hm.active (by omega))
      (by rw [hp32]; omega)) (by rw [hp64]; omega)
  have hsecond := expandedWords64_eq hactive
  change M (M (M (M aw p ⟨32⟩) (p + UInt256.ofNat 32) ⟨32⟩)
    (UInt256.ofNat 64 + p) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩ = _ at hsecond
  simp only [uniswapV3Pool_block_7965_stack, uniswapV3Pool_block_7965_memory, solcMask128,
    hca, hcb, hmask, hr, hload, hp32, hp64, hfold, hnewload,
    u256_sub_self, u256_add_zero, hfirst, hsecond] at rdEvent
  obtain ⟨_, _, rdReturn⟩ := uniswapV3Pool_block_8074 (immWords := wordsOf (immStore v))
    (by evm_ov) hperm (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdEvent
  have hmap := storeSlot0Unlocked_accountMap evm true
  rw [slot0UnlockedWord_true, ← hs.accounts, hs.env] at hmap
  change (storeSlot0Unlocked evm true).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
          (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac => ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256))))) at hmap
  simp only [uniswapV3Pool_block_8074_stack, ← hmap] at rdReturn
  exact RD.poolReturnUint128Pair_heap (v := v) rdReturn hmEvent (by omega) hfit0 hfit1 (by omega)

end Benchmarks.UniswapV3.Pool
