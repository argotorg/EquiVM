import Benchmarks.UniswapV4PoolManager.TickSpacingTrace
import Benchmarks.UniswapV4PoolManager.WordSignextend24

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickSpacingCheckExactTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw spacing lowerGross upperGross x0 x1 x2 ptr x4 x5 x6 x7 x8 x9 params : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hc : int24Canonical spacing)
    (hs : memLoad (params+UInt256.ofNat 128) mem = spacing)
    (hl : memLoad (ptr+UInt256.ofNat 32) mem = lowerGross)
    (hu : memLoad (ptr+UInt256.ofNat 96) mem = upperGross)
    (hgl : lowerGross.toNat < 2^128) (hgu : upperGross.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨7329⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R)
      mem aw rdata σ k C) :
    if tickSpacingLimit (EVM.signed spacing) < Int.ofNat lowerGross.toNat ∨
        tickSpacingLimit (EVM.signed spacing) < Int.ofNat upperGross.toNat then RDrev (deployedRuntime v) g s0
    else ∃ k' C', RD (deployedRuntime v) I g s0 ⟨7256⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R)
      mem (M (M (M aw (params+UInt256.ofNat 128) ⟨32⟩) (ptr+UInt256.ofNat 32) ⟨32⟩) (ptr+UInt256.ofNat 96) ⟨32⟩) rdata σ k' C' := by
  have rd1 := poolManagerBlocks.poolManager_block_7329 hstack h
  have hcanon : UInt256.signextend (UInt256.ofNat 2) spacing = spacing := (signextend24_eq_iff spacing).mpr hc
  have hclean : UInt256.land lowerGross (UInt256.ofNat 340282366920938463463374607431768211455) = lowerGross :=
    u256LandMaskCleanOfToNat _ _ rfl hgl
  simp only [poolManagerBlocks.poolManager_block_7329_stack, hs, hl, hcanon, hclean] at rd1
  have hlo := tickSpacingLimitTrace v (by simp only [List.length_cons]; omega) rd1
  by_cases hlow : tickSpacingLimit (EVM.signed spacing) < Int.ofNat lowerGross.toNat
  · rw [if_pos hlow] at hlo
    rw [if_pos (.inl hlow)]
    exact hlo
  · rw [if_neg hlow] at hlo
    obtain ⟨k2, C2, rd2⟩ := hlo
    have hhi := tickSpacingUpperGuardExactTrace v (by simp only [List.length_cons]; omega) hu hgu rd2
    by_cases hhigh : tickSpacingLimit (EVM.signed spacing) < Int.ofNat upperGross.toNat
    · rw [if_pos hhigh] at hhi
      rw [if_pos (.inr hhigh)]
      exact hhi
    · rw [if_neg hhigh] at hhi
      rw [if_neg (by simpa only [hlow, hhigh, or_self, not_false_eq_true])]
      exact hhi

theorem tickSpacingCheckTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw spacing lowerGross upperGross x0 x1 x2 ptr x4 x5 x6 x7 x8 x9 params : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hc : int24Canonical spacing)
    (hs : memLoad (params+UInt256.ofNat 128) mem = spacing)
    (hl : memLoad (ptr+UInt256.ofNat 32) mem = lowerGross)
    (hu : memLoad (ptr+UInt256.ofNat 96) mem = upperGross)
    (hgl : lowerGross.toNat < 2^128) (hgu : upperGross.toNat < 2^128)
    (h : RD (deployedRuntime v) I g s0 ⟨7329⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R)
      mem aw rdata σ k C) :
    if tickSpacingLimit (EVM.signed spacing) < Int.ofNat lowerGross.toNat ∨
        tickSpacingLimit (EVM.signed spacing) < Int.ofNat upperGross.toNat then RDrev (deployedRuntime v) g s0
    else ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨7256⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: x6 :: x7 :: x8 :: x9 :: params :: R)
      mem aw' rdata σ k' C' := by
  have hr := tickSpacingCheckExactTrace v hstack hc hs hl hu hgl hgu h
  split_ifs at hr ⊢
  · exact hr
  · obtain ⟨k', C', rd⟩ := hr
    exact ⟨_, k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
