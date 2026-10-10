import Benchmarks.UniswapV4PoolManager.PoolModifyOutside
import Benchmarks.UniswapV4PoolManager.TickSqrtCanonicalTrace
import Benchmarks.UniswapV4PoolManager.Signed128Range
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_019
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_020

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyOutsideStartPC (one : Bool) : UInt256 := if one then ⟨6569⟩ else ⟨6344⟩
def poolModifyOutsidePricePC (one : Bool) : UInt256 := if one then ⟨6591⟩ else ⟨6375⟩
def poolModifyOutsideCastPC (one : Bool) : UInt256 := if one then ⟨6597⟩ else ⟨6386⟩
def poolModifyOutsideInputStack (one : Bool) (tick sqrtPrice : UInt256) (p : PoolModifyParams)
    (R : List UInt256) : List UInt256 :=
  if one then p.upper :: p.lower :: sqrtPrice :: EVM.wordOfInt p.delta :: R
  else tick :: sqrtPrice :: p.lower :: p.upper :: EVM.wordOfInt p.delta :: R

theorem poolModifyOutsideEnterTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw tick sqrtPrice : UInt256} {p : PoolModifyParams}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (one : Bool) (v : PoolManagerImmutables) (hstack : R.length+8 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 (poolModifyOutsideStartPC one)
      (poolModifyOutsideInputStack one tick sqrtPrice p R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16728⟩
      (p.lower :: ⟨6365⟩ :: poolModifyOutsidePricePC one :: EVM.wordOfInt p.delta :: p.upper ::
        ⟨6381⟩ :: poolModifyOutsideCastPC one :: R) mem aw rdata σ k' C' := by
  cases one with
  | false => exact ⟨_, _, poolManagerBlocks.poolManager_block_6344 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h⟩
  | true => exact ⟨_, _, poolManagerBlocks.poolManager_block_6569 hstack
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h⟩

theorem poolModifyTwoPricesTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret lower upper : UInt256} {delta : Int}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hl : int24Canonical lower) (hu : int24Canonical upper)
    (hlb : (EVM.signed lower).natAbs ≤ 887272) (hub : (EVM.signed upper).natAbs ≤ 887272)
    (hd : signedFits ⟨128, by decide⟩ delta)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16728⟩
      (lower :: ⟨6365⟩ :: ret :: EVM.wordOfInt delta :: upper :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret
      (tickSqrtPrice (EVM.signed upper) :: tickSqrtPrice (EVM.signed lower) :: EVM.wordOfInt delta :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := tickSqrtCanonicalTrace v (by simp only [List.length_cons]; omega) hl hlb
    (by rw [deployedRuntime_jumps]; jump_dest) h
  have rd2 := poolManagerBlocks.poolManager_block_6365 (by omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
  have hs : UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt delta) = EVM.wordOfInt delta :=
    signextend128_wordOfInt hd.1 hd.2
  simp only [poolManagerBlocks.poolManager_block_6365_stack, hs] at rd2
  exact tickSqrtCanonicalTrace v (by simp only [List.length_cons]; omega) hu hub hret rd2

theorem poolModifyOutsidePricesTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw tick sqrtPrice : UInt256} {p : PoolModifyParams}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (one : Bool) (v : PoolManagerImmutables) (hstack : R.length+12 ≤ 1024)
    (hl : int24Canonical p.lower) (hu : int24Canonical p.upper) (ht : poolTicksValid p.lower p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (h : RD (deployedRuntime v) I g s0 (poolModifyOutsideStartPC one)
      (poolModifyOutsideInputStack one tick sqrtPrice p R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 (if one then ⟨17610⟩ else ⟨17703⟩)
      (tickSqrtPrice (EVM.signed p.lower) :: tickSqrtPrice (EVM.signed p.upper) :: EVM.wordOfInt p.delta ::
        ⟨6381⟩ :: poolModifyOutsideCastPC one :: R) mem aw rdata σ k' C' := by
  obtain ⟨k1, C1, rd1⟩ := poolModifyOutsideEnterTrace one v (by omega) h
  obtain ⟨k2, C2, rd2⟩ := poolModifyTwoPricesTrace v (by simp only [List.length_cons]; omega)
    hl hu (poolTicksValid_bounds ht).1 (poolTicksValid_bounds ht).2 hd
    (by cases one <;> rw [deployedRuntime_jumps] <;> jump_dest) rd1
  cases one with
  | false => exact ⟨_, _, poolManagerBlocks.poolManager_block_6375
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2⟩
  | true => exact ⟨_, _, poolManagerBlocks.poolManager_block_6591
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2⟩

end Benchmarks.UniswapV4PoolManager
