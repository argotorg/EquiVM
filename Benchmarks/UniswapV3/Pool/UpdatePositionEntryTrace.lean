import Benchmarks.UniswapV3.Pool.UpdatePositionModel
import Benchmarks.UniswapV3.Pool.PositionGet
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_063
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_064

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionEntryWords (a : UpdatePositionArgs) : List UInt256 :=
  [EVM.wordOfInt a.current, EVM.wordOfInt a.delta, EVM.wordOfInt a.upper,
    EVM.wordOfInt a.lower, EVM.word a.owner.val]

def updatePositionPrefixWords (a : UpdatePositionArgs) (σ : AccountMap) (ee : ExecutionEnv) :
    List UInt256 :=
  [⟨0⟩, ⟨0⟩, feeGrowthWord true σ ee, feeGrowthWord false σ ee,
    solcMappingSlot ⟨7⟩ (updatePositionKey a), EVM.wordOfInt a.current, EVM.wordOfInt a.delta,
    EVM.wordOfInt a.upper, EVM.wordOfInt a.lower, EVM.word a.owner.val]

def updatePositionPrefixMemory (a : UpdatePositionArgs) (mem : ByteArray) (free : UInt256) : ByteArray :=
  positionGetMem mem free a.owner (EVM.wordOfInt a.lower) (EVM.wordOfInt a.upper) ⟨7⟩

theorem updatePositionEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19151⟩
      (updatePositionEntryWords a ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hm : HeapMemory mem aw free) (hb : free.toNat + 87 ≤ 2 ^ 200)
    (hov : R.length + 18 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (UInt256.ofNat (if a.delta = 0 then 19492 else 19190))
      (updatePositionPrefixWords a σ ee ++ ret :: R)
      (updatePositionPrefixMemory a mem free) aw' rdata σ k' C' ∧
      HeapMemory (updatePositionPrefixMemory a mem free) aw' (free + ⟨58⟩) := by
  simp only [updatePositionEntryWords, List.cons_append, List.nil_append] at rd
  have r1 := uniswapV3Pool_block_19151 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_19151_stack] at r1
  obtain ⟨aw2, k2, C2, r2, hm2⟩ := positionGetX (v := v) a.owner r1 hm hb
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
  have hsign : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a.delta) =
      EVM.wordOfInt a.delta := by
    rw [signextend_wordOfInt ⟨128, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨128, by decide⟩ _ hfit.2.2.1.1 hfit.2.2.1.2]
  by_cases hz : a.delta = 0
  · have hc : UInt256.isZero (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a.delta)) ≠
        UInt256.ofNat 0 := by rw [hsign, hz]; decide
    obtain ⟨_, _, r3⟩ := uniswapV3Pool_block_19166_taken (immWords := wordsOf (immStore v))
      (by evm_ov) hc (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
    simp only [uniswapV3Pool_block_19166_taken_stack] at r3
    rw [if_pos hz]
    exact ⟨_, _, _, r3, hm2⟩
  · have hword : EVM.wordOfInt a.delta ≠ (⟨0⟩ : UInt256) := by
      intro hzero
      have he := congrArg (fun w ↦ normalizeInt (.sint ⟨128, by decide⟩) (Int.ofNat w.toNat)) hzero
      dsimp only at he
      rw [normalizeInt_wordOfInt, normalizeSint_eq_self ⟨128, by decide⟩ _
        hfit.2.2.1.1 hfit.2.2.1.2] at he
      change a.delta = normalizeInt (.sint ⟨128, by decide⟩) 0 at he
      rw [normalizeSint_eq_self ⟨128, by decide⟩ 0 (by decide) (by decide)] at he
      exact hz he
    have hc : UInt256.isZero (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt a.delta)) =
        UInt256.ofNat 0 := by rw [hsign]; exact isZero_eq_zero_of_ne hword
    obtain ⟨_, _, r3⟩ := uniswapV3Pool_block_19166_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) hc r2
    simp only [uniswapV3Pool_block_19166_fallthrough_stack] at r3
    rw [if_neg hz]
    exact ⟨_, _, _, r3, hm2⟩

end Benchmarks.UniswapV3.Pool
