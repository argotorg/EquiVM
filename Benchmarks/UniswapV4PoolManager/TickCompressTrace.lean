import Benchmarks.UniswapV4PoolManager.TickCompressWords
import Benchmarks.UniswapV4PoolManager.SignedModStep
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_054

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

open poolManagerBlocks in
theorem tickCompressTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw tick spacing a b c d : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (lte : Bool) (hstack : R.length+11 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨19221⟩
      ([tick, spacing, ⟨0⟩, spacing, tick, spacing, a, b, c, d, if lte then ⟨0⟩ else ⟨1⟩] ++ R)
      mem aw rdata σ k C) :
    RD (deployedRuntime v) I g s0 (if lte then ⟨19234⟩ else ⟨21109⟩)
      ([tickCompressRaw tick spacing, spacing, a, b, c, d, if lte then ⟨0⟩ else ⟨1⟩] ++ R)
      mem aw rdata σ (k+11) (C+43) := by
  have rd1 := rdSmod h
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨19221⟩ : UInt256), UInt8.ofNat 7,
      .SMOD, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by change R.length+10 ≤ 1024; omega)
  cases lte with
  | false =>
    have rd2 := poolManagerBlocks.poolManager_block_19222_taken (by simp; omega) (by decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simpa only [poolManagerBlocks.poolManager_block_19222_taken_stack, tickCompressRaw,
      Bool.false_eq_true, if_false, Nat.add_assoc] using rd2
  | true =>
    have rd2 := poolManagerBlocks.poolManager_block_19222_fallthrough (by simp; omega) (by rfl) rd1
    simpa only [poolManagerBlocks.poolManager_block_19222_fallthrough_stack, tickCompressRaw,
      if_true, Nat.add_assoc] using rd2

end Benchmarks.UniswapV4PoolManager
