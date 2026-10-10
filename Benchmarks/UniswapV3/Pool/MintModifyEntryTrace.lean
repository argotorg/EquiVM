import Benchmarks.UniswapV3.Pool.MintMemory
import Benchmarks.UniswapV3.Pool.MintPrefixSource
import Benchmarks.UniswapV3.Pool.SafeCast128Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintModifyEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p len start : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : MintArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨5837⟩
      (⟨0⟩ :: ⟨0⟩ :: len :: start :: a.amount :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: EVM.word a.recipient.val :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (hov : R.length + 18 ≤ 1024) :
    (ExecStmt config (mintInitFrame v a) evm
        (.internalCall "SafeCast_toInt128" mintCastExprs "__c0") .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (safeCast128Valid (Int.ofNat a.amount.toNat) ∧
      ExecStmt config (mintInitFrame v a) evm
        (.internalCall "SafeCast_toInt128" mintCastExprs "__c0") (.ok (mintCastFrame v a) evm) ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨16233⟩
        (p :: ⟨5915⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: len :: start :: a.amount ::
          EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower :: EVM.word a.recipient.val :: R)
        (wordArrayAllocMem mem p (mintModifyArgs a).words) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p (mintModifyArgs a).words) aw'
        (p + UInt256.ofNat 128) ∧
      ModifyPositionParamsMemory (wordArrayAllocMem mem p (mintModifyArgs a).words)
        p (mintModifyArgs a)) := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hadd (n : Nat) (hn : n ≤ 128) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hclean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1)) a.amount = a.amount := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat a.amount _ (bits := 128) (by native_decide) ha.2.2
  let aw1 := M (M (M (M (M aw ⟨64⟩ ⟨32⟩) ⟨64⟩ ⟨32⟩) p ⟨32⟩)
    (p + UInt256.ofNat 32) ⟨32⟩) (p + UInt256.ofNat 64) ⟨32⟩
  have hactive : ActiveWords aw1 := by
    exact (((((hm.expand32 ⟨64⟩ (by decide)).expand32 ⟨64⟩ (by decide)).expand32 p
      (by omega)).expand32 (p + UInt256.ofNat 32) (by rw [hadd 32 (by decide)]; omega)).expand32
      (p + UInt256.ofNat 64) (by rw [hadd 64 (by decide)]; omega)).active
  have r1 := uniswapV3Pool_block_5837 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  rw [mintCastMemory_eq a ha hm hb, uniswapV3Pool_block_5837_stack, hload, hclean] at r1
  rw [u256_add_comm (UInt256.ofNat 32) p,
    u256_add_comm (UInt256.ofNat 32) (p + UInt256.ofNat 32), u256_add_assoc,
    show UInt256.ofNat 32 + UInt256.ofNat 32 = UInt256.ofNat 64 from by decide,
    u256_add_comm (UInt256.ofNat 32) (p + UInt256.ofNat 64), u256_add_assoc,
    show UInt256.ofNat 64 + UInt256.ofNat 32 = UInt256.ofNat 96 from by decide] at r1
  obtain ⟨k1, C1, r1⟩ := r1.pack
  have r1' : RD (deployedRuntime v) ee g s0 ⟨16216⟩
      (EVM.wordOfInt (Int.ofNat a.amount.toNat) :: ⟨5905⟩ ::
        (p + UInt256.ofNat 96) :: p :: ⟨5915⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        len :: start :: a.amount :: EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower ::
        EVM.word a.recipient.val :: R) (mintCastMemory mem p a) aw1 rdata σ k1 C1 := by
    simpa only [wordOfInt_ofNat_toNat] using r1
  have hi : Int.ofNat a.amount.toNat < (2 ^ 128 : Int) := Int.ofNat_lt.mpr ha.2.2
  have hn : 0 ≤ Int.ofNat a.amount.toNat := Int.natCast_nonneg _
  rcases safeCast128X (v := v) (Int.ofNat a.amount.toNat) r1'
      (by omega) (by omega)
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 13 + 5 ≤ 1024; omega) with ⟨rr, hv⟩ | ⟨hv, k2, C2, r2⟩
  · exact Or.inl ⟨mintCastRevertsCall v a evm ha hv, rr⟩
  · rw [wordOfInt_ofNat_toNat] at r2
    have r3 := uniswapV3Pool_block_5905 (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 3 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
    rw [mintModifyMemory_eq mem p a hv hb] at r3
    refine Or.inr ⟨hv, mintCastSource v a evm ha hv, _, _, _, r3, ?_, ?_⟩
    · exact wordArrayAllocMem_heap mem p _ (mintModifyArgs a).words hm.lower
        (by intro h; cases h) hb
        (activeWords_expand32 hactive (by rw [hadd 96 (by decide)]; omega))
    · exact wordArrayAllocMem_region mem p (mintModifyArgs a).words hm.lower
        (by intro h; cases h)

end Benchmarks.UniswapV3.Pool
