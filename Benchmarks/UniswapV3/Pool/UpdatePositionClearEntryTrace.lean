import Benchmarks.UniswapV3.Pool.UpdatePositionPositionSource
import Benchmarks.UniswapV3.Pool.LiquidityDeltaWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_065

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def updatePositionClearEntryPC (upper : Bool) : UInt256 := if upper then ⟨19556⟩ else ⟨19540⟩
def updatePositionClearCallPC (upper : Bool) : UInt256 := if upper then ⟨19563⟩ else ⟨19546⟩
def updatePositionClearReturnPC (upper : Bool) : UInt256 := if upper then ⟨19573⟩ else ⟨19556⟩

theorem updatePositionNegativeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19527⟩ (updatePositionPositionWords v a evm ++ R)
      mem aw rdata σ k C) (ha : a.Fits) (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (if a.delta < 0 then ⟨19540⟩ else ⟨19573⟩)
      (updatePositionPositionWords v a evm ++ R) mem aw rdata σ k' C' := by
  have hd := liquidityDeltaRawSign (EVM.wordOfInt a.delta) a.delta
    (by rw [normalizeInt_wordOfInt, normalizeSint_eq_self ⟨128, by decide⟩ _ ha.2.2.1.1 ha.2.2.1.2])
  simp only [updatePositionPositionWords, updatePositionChangedWords_eq,
    List.cons_append, List.nil_append] at rd ⊢
  by_cases hn : a.delta < 0
  · rw [if_pos hn]
    exact ⟨k + 9, C + 34, uniswapV3Pool_block_19527_fallthrough
      (immWords := wordsOf (immStore v)) (by evm_ov) (by rw [hd, if_pos hn]; rfl) rd⟩
  · rw [if_neg hn]
    exact ⟨k + 9, C + 34, uniswapV3Pool_block_19527_taken
      (immWords := wordsOf (immStore v)) (by evm_ov) (by rw [hd, if_neg hn]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩

theorem updatePositionClearGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (updatePositionClearEntryPC upper)
      (updatePositionPositionWords v a evm ++ R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0
      (if updatePositionFlag v a evm upper then updatePositionClearCallPC upper
        else updatePositionClearReturnPC upper)
      (updatePositionPositionWords v a evm ++ R) mem aw rdata σ k' C' := by
  simp only [updatePositionPositionWords, updatePositionChangedWords_eq,
    List.cons_append, List.nil_append] at rd ⊢
  cases upper
  · cases hf : updatePositionFlag v a evm false
    · simp only [hf, Bool.false_eq_true, if_false] at rd ⊢
      exact ⟨k + 4, C + 19, uniswapV3Pool_block_19540_taken
        (immWords := wordsOf (immStore v)) (by evm_ov) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩
    · simp only [hf, if_true] at rd ⊢
      exact ⟨k + 4, C + 19, uniswapV3Pool_block_19540_fallthrough
        (immWords := wordsOf (immStore v)) (by evm_ov) (by rfl) rd⟩
  · cases hf : updatePositionFlag v a evm true
    · simp only [hf, Bool.false_eq_true, if_false] at rd ⊢
      exact ⟨k + 5, C + 20, uniswapV3Pool_block_19556_taken
        (immWords := wordsOf (immStore v)) (by evm_ov) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩
    · simp only [hf, if_true] at rd ⊢
      exact ⟨k + 5, C + 20, uniswapV3Pool_block_19556_fallthrough
        (immWords := wordsOf (immStore v)) (by evm_ov) (by rfl) rd⟩

theorem updatePositionClearCallEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : UpdatePositionArgs) (evm : EVM.State) (upper : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (updatePositionClearCallPC upper)
      (updatePositionPositionWords v a evm ++ R) mem aw rdata σ k C)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨21964⟩
      (EVM.wordOfInt (if upper then a.upper else a.lower) :: ⟨5⟩ ::
        updatePositionClearReturnPC upper :: updatePositionPositionWords v a evm ++ R)
      mem aw rdata σ k' C' := by
  simp only [updatePositionPositionWords, updatePositionChangedWords_eq,
    List.cons_append, List.nil_append] at rd ⊢
  cases upper
  · exact ⟨k + 5, C + 20, uniswapV3Pool_block_19546 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩
  · exact ⟨k + 5, C + 20, uniswapV3Pool_block_19563 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩

theorem updatePositionReturnX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : UpdatePositionArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19573⟩
      (updatePositionPositionWords v a evm ++ ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (solcMappingSlot ⟨7⟩ (updatePositionKey a) :: R)
      mem aw rdata σ k' C' := by
  simp only [updatePositionPositionWords, updatePositionChangedWords_eq,
    List.cons_append, List.nil_append] at rd
  exact ⟨k + 15, C + 37, uniswapV3Pool_block_19573 (immWords := wordsOf (immStore v)) hov hret rd⟩

end Benchmarks.UniswapV3.Pool
