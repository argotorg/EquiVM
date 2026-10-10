import Benchmarks.UniswapV4PoolManager.WordReadTraceLoop
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_009

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 3000

theorem wordReadReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} {n i : Nat} {cursor : Nat → UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 9 ≤ 1024) (hn : 224+32*n < UInt256.size)
    (h : RD (deployedRuntime v) I g s0 ⟨2508⟩ (wordReadTraceExitStack cursor n i R)
      mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ (mem.readWithPadding 160 (64+32*n)) := by
  have hr := poolManagerBlocks.poolManager_block_2508 (by simp; omega) h
  simpa only [show (UInt256.ofNat 160).toNat = 160 from rfl, wordArrayReturnSpan_of_fit n hn] using hr

/-- Complete either word-array loop, including its mandatory read for an empty array. -/
theorem wordReadTraceReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} {n : Nat} {values cursor : Nat → UInt256} {loopPC stride : UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 9 ≤ 1024) (hn : 224+32*n < UInt256.size)
    (step : ∀ i mem aw k C, i < max 1 n →
      RD (deployedRuntime v) I g s0 loopPC (wordReadTraceStack cursor stride n i R) mem aw rdata σ k C →
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 (if i+1 < n then loopPC else ⟨2508⟩)
        (if i+1 < n then wordReadTraceStack cursor stride n (i+1) R else wordReadTraceExitStack cursor n (i+1) R)
        (writeWord mem (224+32*i) (values i)) aw' rdata σ k' C')
    (h : RD (deployedRuntime v) I g s0 loopPC (wordReadTraceStack cursor stride n 0 R)
      (arrayHeaderMemory n) aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ
      (wordBytes ([UInt256.ofNat 32, UInt256.ofNat n] ++ wordArrayWords values 0 n)) := by
  cases n with
  | zero =>
      obtain ⟨aw2, k2, C2, rd2⟩ := step 0 _ aw k C (by omega) h
      simp only [show ¬ (0:Nat)+1 < 0 by omega, if_false] at rd2
      have hr := wordReadReturnTrace v hstack hn rd2
      simpa only [Nat.mul_zero, Nat.add_zero, wordArrayWords, List.append_nil,
        emptyArrayExtraWrite_read] using hr
  | succ n =>
      obtain ⟨aw2, k2, C2, rd2⟩ := wordReadTraceLoop step n 0 _ aw k C (by omega) h
      have hr := wordReadReturnTrace v hstack hn rd2
      simpa only [Nat.mul_zero, Nat.add_zero,
        arrayPayloadMemory_read (n+1) _ (wordArrayWords_length _ _ _)] using hr

end Benchmarks.UniswapV4PoolManager
