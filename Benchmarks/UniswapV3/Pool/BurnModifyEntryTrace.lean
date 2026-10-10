import Benchmarks.UniswapV3.Pool.BurnMemory
import Benchmarks.UniswapV3.Pool.BurnPrefixSource
import Benchmarks.UniswapV3.Pool.SafeCast128Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem burnModifyEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : BurnArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨9648⟩
      (⟨0⟩ :: ⟨0⟩ :: a.amount :: EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower :: R)
      mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 128 ≤ 2 ^ 200)
    (hperm : ee.perm = true) (hov : R.length + 16 ≤ 1024) :
    (ExecStmt config (burnInitFrame v a) (storeSlot0Unlocked evm false)
        (.internalCall "SafeCast_toInt128" burnCastExprs "__c0") .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecStmt config (burnInitFrame v a) (storeSlot0Unlocked evm false)
        (.internalCall "SafeCast_toInt128" burnCastExprs "__c0")
        (.ok (burnCastFrame v a) (storeSlot0Unlocked evm false)) ∧
      ∃ σ' aw' k' C', SourceState s0 ee σ' (storeSlot0Unlocked evm false) ∧
        RD (deployedRuntime v) ee g s0 ⟨16233⟩
          (p :: ⟨9737⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: a.amount ::
            EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower :: R)
          (wordArrayAllocMem mem p (burnModifyArgs a evm).words) aw' rdata σ' k' C' ∧
        HeapMemory (wordArrayAllocMem mem p (burnModifyArgs a evm).words) aw'
          (p + UInt256.ofNat 128) ∧
        ModifyPositionParamsMemory (wordArrayAllocMem mem p (burnModifyArgs a evm).words)
          p (burnModifyArgs a evm)) := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hadd (n : Nat) (hn : n ≤ 128) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hclean : UInt256.land a.amount
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1)) = a.amount :=
    u256LandMaskCleanOfToNat a.amount _ (bits := 128) (by native_decide) ha.2.2
  have hstore := storeSlot0Unlocked_accountMap evm false
  rw [slot0UnlockedWord_false, ← hs.accounts, hs.env] at hstore
  change (storeSlot0Unlocked evm false).accountMap = sstoreAccountMap ee.codeOwner σ
    (UInt256.ofNat 0) (UInt256.land
      (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
      (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac ↦ ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))) at hstore
  let aw1 := M (M (M (M (M aw ⟨64⟩ ⟨32⟩) ⟨64⟩ ⟨32⟩) p ⟨32⟩)
    (p + UInt256.ofNat 32) ⟨32⟩) (p + UInt256.ofNat 64) ⟨32⟩
  have hactive : ActiveWords aw1 := by
    exact (((((hm.expand32 ⟨64⟩ (by decide)).expand32 ⟨64⟩ (by decide)).expand32 p
      (by omega)).expand32 (p + UInt256.ofNat 32) (by rw [hadd 32 (by decide)]; omega)).expand32
      (p + UInt256.ofNat 64) (by rw [hadd 64 (by decide)]; omega)).active
  obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_9648 (immWords := wordsOf (immStore v))
    (by omega) hperm (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  rw [burnCastMemory_eq a evm ha hm hs.env hb, uniswapV3Pool_block_9648_stack,
    hload, hclean, ← hstore] at r1
  have r1' : RD (deployedRuntime v) ee g s0 ⟨16216⟩
      (EVM.wordOfInt (Int.ofNat a.amount.toNat) :: ⟨9724⟩ ::
        (p + UInt256.ofNat 96) :: p :: ⟨9737⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        a.amount :: EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower :: R)
      (burnCastMemory mem p a evm) aw1 rdata (storeSlot0Unlocked evm false).accountMap k1 C1 := by
    simpa only [wordOfInt_ofNat_toNat] using r1
  have hi : Int.ofNat a.amount.toNat < (2 ^ 128 : Int) := Int.ofNat_lt.mpr ha.2.2
  have hn : 0 ≤ Int.ofNat a.amount.toNat := Int.natCast_nonneg _
  rcases safeCast128X (v := v) (Int.ofNat a.amount.toNat) r1'
      (by omega) (by omega)
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 11 + 5 ≤ 1024; omega) with ⟨rr, hv⟩ | ⟨hv, k2, C2, r2⟩
  · exact Or.inl ⟨burnCastRevertsCall v a _ ha hv, rr⟩
  · rw [wordOfInt_ofNat_toNat] at r2
    have r3 := uniswapV3Pool_block_9724 (immWords := wordsOf (immStore v))
      (by change R.length + 10 + 3 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
    rw [burnModifyMemory_eq mem p a evm hb] at r3
    refine Or.inr ⟨burnCastSource v a _ ha hv, _, _, _, _, ?_, r3, ?_, ?_⟩
    · exact ⟨(storeSlot0Unlocked_originalAccounts evm false).trans hs.world,
        (storeSlot0Unlocked_executionEnv evm false).trans hs.env, rfl⟩
    · exact wordArrayAllocMem_heap mem p _ (burnModifyArgs a evm).words hm.lower
        (by intro h; cases h) hb
        (activeWords_expand32 hactive (by rw [hadd 96 (by decide)]; omega))
    · exact wordArrayAllocMem_region mem p (burnModifyArgs a evm).words hm.lower
        (by intro h; cases h)

end Benchmarks.UniswapV3.Pool
