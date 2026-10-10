import Benchmarks.UniswapV4PoolManager.BalanceDeltaSource
import Benchmarks.UniswapV4PoolManager.Signed128
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def balanceDeltaOutputStack (a b x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256)
    (R : List UInt256) : List UInt256 :=
  x7 :: x12 :: x2 :: x3 :: x4 :: x5 :: x6 :: balanceDeltaWord a b ::
    x8 :: x9 :: x10 :: x11 :: balanceDeltaWord a b :: R

-- toBalanceDelta is inlined here; the summary also takes the caller's next liquidity-sign branch.
theorem balanceDeltaFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw a b x2 x4 x5 x6 x7 x8 x9 x10 x11 x12 : UInt256} {delta : Int}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024)
    (hlo : -(2^127 : Int) ≤ delta) (hhi : delta < 2^127)
    (h : RD (deployedRuntime v) I g s0 ⟨5999⟩
      (b :: a :: x2 :: EVM.wordOfInt delta :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: x10 :: x11 :: x12 :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (if delta < 0 then ⟨6620⟩ else ⟨6036⟩)
      (balanceDeltaOutputStack a b x2 (EVM.wordOfInt delta) x4 x5 x6 x7 x8 x9 x10 x11 x12 R)
      mem aw rdata σ k' C' := by
  have hs : EVM.signed (EVM.wordOfInt delta) = delta := signed_wordOfInt
    (show int256Fits delta from ⟨by change -(2^255 : Int) ≤ delta; omega, by change delta < (2^255 : Int); omega⟩)
  have hsign : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
    signextend128_wordOfInt hlo hhi
  have hcmp : UInt256.slt (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta)) ⟨0⟩ =
      UInt256.fromBool (decide (delta < 0)) := by
    rw [hsign, slt_signed, hs]
    rfl
  by_cases hn : delta < 0
  · rw [if_pos hn]
    have rd := poolManagerBlocks.poolManager_block_5999_taken hstack
      (by rw [hcmp, decide_eq_true hn]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    exact ⟨_, _, rd⟩
  · rw [if_neg hn]
    have rd := poolManagerBlocks.poolManager_block_5999_fallthrough hstack
      (by rw [hcmp, decide_eq_false hn]; rfl) h
    exact ⟨_, _, rd⟩

end Benchmarks.UniswapV4PoolManager
