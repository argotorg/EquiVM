import Benchmarks.UniswapV4PoolManager.PoolModifyBitmap
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyFlipStart (upper : Bool) : UInt256 := if upper then ⟨7263⟩ else ⟨7256⟩
def poolModifyFlipReturn (upper : Bool) : UInt256 := if upper then ⟨7296⟩ else ⟨7324⟩
def poolModifyFlipNext (upper : Bool) : UInt256 := if upper then ⟨5722⟩ else ⟨7263⟩

def poolModifyFlipEnterActiveWords (aw params ptr : UInt256) (upper flipped : Bool) : UInt256 :=
  let flagAW := M aw (if upper then ptr+UInt256.ofNat 64 else ptr) ⟨32⟩
  if flipped then M (M flagAW (params+UInt256.ofNat 128) ⟨32⟩) (UInt256.ofNat 128) ⟨32⟩ else flagAW

theorem poolModifyFlipEnterExactTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 x9 params : UInt256} {p : PoolModifyParams}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (upper flipped : Bool)
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024) (hc : int24Canonical p.spacing)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hs : memLoad (params+UInt256.ofNat 128) mem = p.spacing)
    (hf : memLoad (if upper then ptr+UInt256.ofNat 64 else ptr) mem = UInt256.fromBool flipped)
    (h : RD (deployedRuntime v) I g s0 (poolModifyFlipStart upper)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata σ k C) :
    if flipped then ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16652⟩
      ((poolSlot id+⟨5⟩) :: (if upper then p.upper else p.lower) :: p.spacing :: poolModifyFlipReturn upper ::
        x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem (poolModifyFlipEnterActiveWords aw params ptr upper flipped) rdata σ k' C'
    else ∃ k' C', RD (deployedRuntime v) I g s0 (poolModifyFlipNext upper)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem (poolModifyFlipEnterActiveWords aw params ptr upper flipped) rdata σ k' C' := by
  have hc' : UInt256.signextend (UInt256.ofNat 2) p.spacing = p.spacing := (signextend24_eq_iff _).mpr hc
  cases upper <;> cases flipped
  all_goals simp only [poolModifyFlipStart, poolModifyFlipNext, poolModifyFlipReturn, poolModifyFlipEnterActiveWords,
    Bool.false_eq_true, if_false, if_true] at hf h ⊢
  · exact ⟨_, _, poolManagerBlocks.poolManager_block_7256_fallthrough
      (by simp only [List.length_cons]; omega) hf h⟩
  · have rd1 := poolManagerBlocks.poolManager_block_7256_taken
      (by simp only [List.length_cons]; omega) (by rw [hf]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have rd2 := poolManagerBlocks.poolManager_block_7301 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_7301_stack, hm, hs, hc'] at rd2
    exact ⟨_, _, rd2⟩
  · exact ⟨_, _, poolManagerBlocks.poolManager_block_7263_taken
      (by simp only [List.length_cons]; omega) (by rw [hf]; decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h⟩
  · have rd1 := poolManagerBlocks.poolManager_block_7263_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hf]; decide) h
    have rd2 := poolManagerBlocks.poolManager_block_7274 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_7274_stack, hm, hs, hc'] at rd2
    exact ⟨_, _, rd2⟩

theorem poolModifyFlipReturnExactTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (upper : Bool) (v : PoolManagerImmutables) (hstack : R.length+1 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 (poolModifyFlipReturn upper) R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (poolModifyFlipNext upper) R mem aw rdata σ k' C' := by
  cases upper with
  | false => exact ⟨_, _, poolManagerBlocks.poolManager_block_7324 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h⟩
  | true => exact ⟨_, _, poolManagerBlocks.poolManager_block_7296 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h⟩

theorem poolModifyFlipEnterTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw id ptr x0 x1 x2 x4 x5 x9 params : UInt256} {p : PoolModifyParams}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (upper flipped : Bool)
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024) (hc : int24Canonical p.spacing)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id)
    (hs : memLoad (params+UInt256.ofNat 128) mem = p.spacing)
    (hf : memLoad (if upper then ptr+UInt256.ofNat 64 else ptr) mem = UInt256.fromBool flipped)
    (h : RD (deployedRuntime v) I g s0 (poolModifyFlipStart upper)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw rdata σ k C) :
    if flipped then ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16652⟩
      ((poolSlot id+⟨5⟩) :: (if upper then p.upper else p.lower) :: p.spacing :: poolModifyFlipReturn upper ::
        x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw' rdata σ k' C'
    else ∃ aw' k' C', RD (deployedRuntime v) I g s0 (poolModifyFlipNext upper)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta :: p.lower :: x9 :: params :: R)
      mem aw' rdata σ k' C' := by
  have hr := poolModifyFlipEnterExactTrace upper flipped v hstack hc hm hs hf h
  split_ifs at hr ⊢
  all_goals obtain ⟨k', C', rd⟩ := hr; exact ⟨_, k', C', rd⟩

theorem poolModifyFlipReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (upper : Bool) (v : PoolManagerImmutables) (hstack : R.length+1 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 (poolModifyFlipReturn upper) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 (poolModifyFlipNext upper) R mem aw' rdata σ k' C' := by
  obtain ⟨k', C', rd⟩ := poolModifyFlipReturnExactTrace upper v hstack h
  exact ⟨aw, k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
