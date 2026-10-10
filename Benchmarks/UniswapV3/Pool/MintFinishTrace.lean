import Benchmarks.UniswapV3.Pool.MintFinishSource
import Benchmarks.UniswapV3.Pool.WordArrayHeap
import Benchmarks.UniswapV3.Pool.HeapWordPairReturn
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_022

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw p before0 before1 junk0 junk1 amount0 amount1 len start amount upper lower recipient : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨6283⟩
      (before1 :: before0 :: junk1 :: junk0 :: amount1 :: amount0 :: len :: start ::
        amount :: upper :: lower :: recipient :: ⟨621⟩ :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 27 ≤ 1024) :
    RDret (deployedRuntime v) g s0 (storeSlot0Unlocked evm true).accountMap
      (amount0.toByteArray ++ amount1.toByteArray) := by
  obtain ⟨k1, C1, r1⟩ := (uniswapV3Pool_block_6283 (immWords := wordsOf (immStore v))
    (by evm_ov) rd).pack
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have ha64 : UInt256.ofNat 32 + (UInt256.ofNat 32 + p) = UInt256.ofNat 64 + p := by
    rw [← uadd_assoc]; rfl
  have ha96 : UInt256.ofNat 32 + (UInt256.ofNat 64 + p) = UInt256.ofNat 96 + p := by
    rw [← uadd_assoc]; rfl
  have ha128 : UInt256.ofNat 32 + (UInt256.ofNat 96 + p) = UInt256.ofNat 128 + p := by
    rw [← uadd_assoc]; rfl
  have hp32 : (UInt256.ofNat 32 + p).toNat = p.toNat + 32 := by
    rw [u256_add_comm]; exact uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hp64 : (UInt256.ofNat 64 + p).toNat = p.toNat + 64 := by
    rw [u256_add_comm]; exact uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  have hp96 : (UInt256.ofNat 96 + p).toNat = p.toNat + 96 := by
    rw [u256_add_comm]; exact uadd_word_ofNat_toNat p 96 (by change _ < 2 ^ 256; omega)
  let caller := UInt256.land
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
    (UInt256.ofNat ee.source.val)
  let liquidity := UInt256.land
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1)) amount
  let payload := [caller, liquidity, amount0, amount1]
  let memEvent := writeWordArray mem p.toNat payload
  have hfold : amount1.toByteArray.write 0
      (amount0.toByteArray.write 0 (liquidity.toByteArray.write 0
        (caller.toByteArray.write 0 mem p.toNat 32) (p.toNat + 32) 32)
        (p.toNat + 64) 32) (p.toNat + 96) 32 = memEvent := by
    simp only [memEvent, payload, writeWordArray, Reasoning.Theory.writeWord, Nat.add_assoc]
  dsimp only [caller, liquidity] at hfold
  have hactive : ActiveWords (M (M (M (M aw p ⟨32⟩) (UInt256.ofNat 32 + p) ⟨32⟩)
      (UInt256.ofNat 64 + p) ⟨32⟩) (UInt256.ofNat 96 + p) ⟨32⟩) :=
    activeWords_expand32 (activeWords_expand32 (activeWords_expand32
      (activeWords_expand32 hm.active (by omega)) (by rw [hp32]; omega))
      (by rw [hp64]; omega)) (by rw [hp96]; omega)
  have hmEvent := wordArrayHeap hm.cursor payload (by simp [payload])
    (activeWords_expand hactive (off := p) (size := ⟨128⟩) hb)
  have hnewload : memLoad (UInt256.ofNat 64) memEvent = p := hmEvent.load64
  have hfirst : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hsecond := expandedWords64_eq hactive
  change M (M (M (M (M aw p ⟨32⟩) (UInt256.ofNat 32 + p) ⟨32⟩)
    (UInt256.ofNat 64 + p) ⟨32⟩) (UInt256.ofNat 96 + p) ⟨32⟩) (UInt256.ofNat 64) ⟨32⟩ = _ at hsecond
  simp only [uniswapV3Pool_block_6283_stack, uniswapV3Pool_block_6283_memory,
    hload, ha64, ha96, ha128, hp32, hp64, hp96, hfold, hnewload, hfirst, hsecond] at r1
  obtain ⟨k2, C2, r2⟩ := uniswapV3Pool_block_6396 (immWords := wordsOf (immStore v))
    (by evm_ov) hperm (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  have hmap := storeSlot0Unlocked_accountMap evm true
  rw [slot0UnlockedWord_true, ← hs.accounts, hs.env] at hmap
  change (storeSlot0Unlocked evm true).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))
        (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
          (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
            (fun ac ↦ ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256))))) at hmap
  have hlen : UInt256.sub (UInt256.ofNat 128 + p) p = UInt256.ofNat 128 := by
    rw [u256_add_comm, word_add_sub_left]
  simp only [uniswapV3Pool_block_6396_stack, ← hmap, hlen] at r2
  exact RD.poolReturnWordPair_heap (v := v) r2 hmEvent (by omega) (by omega)

end Benchmarks.UniswapV3.Pool
