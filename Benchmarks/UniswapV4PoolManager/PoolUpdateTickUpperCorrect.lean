import Benchmarks.UniswapV4PoolManager.PoolUpdateTickCall
import Benchmarks.UniswapV4PoolManager.TickUpperTrace
import Benchmarks.UniswapV4PoolManager.TickUpperStoreTrace
import Benchmarks.UniswapV4PoolManager.FunctionTraceMono

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickUpperReturnTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (tick x0 x1 x2 ptr x4 x5 : UInt256)
    (delta : Int) (R : List UInt256) : State → Option (List Value) → Prop
  | post, some [.bool flipped, .int gross] =>
    post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ unsignedFits ⟨128, by decide⟩ gross ∧
    ∃ aw k C, RD (deployedRuntime v) I g s0 (if 0 ≤ delta then ⟨7329⟩ else ⟨7256⟩)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: tick :: EVM.wordOfInt delta :: R)
      (tickUpperResultMemory mem ptr (EVM.wordOfInt gross) (UInt256.fromBool flipped))
      aw rdata post.accountMap k C
  | _, _ => False

def tickUpperUpdateActiveWords (aw ptr packed : UInt256) : UInt256 :=
  M (M (if Int.ofNat (tickGrossWord packed).toNat = 0 then M aw (UInt256.ofNat 128) ⟨32⟩ else aw)
    (ptr+UInt256.ofNat 96) ⟨32⟩) (ptr+UInt256.ofNat 64) ⟨32⟩

def tickUpperReturnTraceAtAW (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (tick x0 x1 x2 ptr x4 x5 : UInt256)
    (delta : Int) (R : List UInt256) (aw : UInt256) : State → Option (List Value) → Prop
  | post, some [.bool flipped, .int gross] =>
    post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ unsignedFits ⟨128, by decide⟩ gross ∧
    ∃ k C, RD (deployedRuntime v) I g s0 (if 0 ≤ delta then ⟨7329⟩ else ⟨7256⟩)
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: tick :: EVM.wordOfInt delta :: R)
      (tickUpperResultMemory mem ptr (EVM.wordOfInt gross) (UInt256.fromBool flipped))
      aw rdata post.accountMap k C
  | _, _ => False

theorem poolUpdateTickUpperExactResultTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 x2 ptr x4 x5 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨17774⟩
      (tickGrossWord (tickFieldWord evm id (EVM.signed tick) .liquidityPacked) :: EVM.wordOfInt delta :: ⟨7100⟩ ::
        tickUpperLiquidityTail id tick (tickFieldWord evm id (EVM.signed tick) .liquidityPacked)
          x0 x1 x2 ptr x4 x5 delta R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (tickUpperReturnTraceAtAW v I g s0 evm.σ₀ mem rdata tick x0 x1 x2 ptr x4 x5 delta R (tickUpperUpdateActiveWords aw ptr (tickFieldWord evm id (EVM.signed tick) .liquidityPacked)))
      (poolUpdateTickResult f evm id (EVM.signed tick) delta true) := by
  have hr := tickUpperExactTrace v hstack hI hm hd h
  simp only [poolUpdateTickResult, poolUpdateTickFinishResult, poolUpdateTickTailResult,
    tickFeesPost_env, hI]
  dsimp only at hr
  generalize hp : tickFieldWord evm id (EVM.signed tick) .liquidityPacked = packed at hr ⊢
  by_cases hg : liquidityAddFits (tickGrossWord packed) delta
  · rw [if_pos hg] at hr ⊢
    by_cases hs : tickFeesNeeded evm id (EVM.signed tick) (Int.ofNat (tickGrossWord packed).toNat) ∧ I.perm = false
    · rw [if_pos hs] at hr ⊢
      exact hr
    · rw [if_neg hs] at hr ⊢
      by_cases hn : signedFits ⟨128, by decide⟩ (tickNetAfter packed delta true)
      · rw [if_pos hn] at hr ⊢
        obtain ⟨k1, C1, rd1⟩ := hr
        dsimp only [tickUpperStoreInput] at rd1
        have hI' := (tickFeesPost_env evm id packed (EVM.signed tick)).trans hI
        have hstore := tickUpperStoreExactTrace (delta := delta) v (by omega) hI' (tickGrossAfter_bound hg) hd rd1
        by_cases hperm : I.perm = false
        · rw [if_pos hperm] at hstore ⊢
          exact hstore
        · rw [if_neg hperm] at hstore ⊢
          simp only [functionResultTrace, tickUpperReturnTraceAtAW, wordOfInt_ofNat_toNat]
          refine ⟨(tickLiquidityStore_env _ _ _ _ _).trans hI', ?_, ?_, hstore⟩
          · rw [tickLiquidityStore_σ₀, tickFeesPost_σ₀]
          · have hb := tickGrossAfter_bound hg
            change 0 ≤ Int.ofNat _ ∧ Int.ofNat _ < (2^128 : Int)
            simp only [Int.ofNat_eq_natCast] at *
            omega
      · rw [if_neg hn] at hr ⊢
        exact hr
  · rw [if_neg hg] at hr ⊢
    exact hr

theorem poolUpdateTickUpperResultTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 x2 ptr x4 x5 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨17774⟩
      (tickGrossWord (tickFieldWord evm id (EVM.signed tick) .liquidityPacked) :: EVM.wordOfInt delta :: ⟨7100⟩ ::
        tickUpperLiquidityTail id tick (tickFieldWord evm id (EVM.signed tick) .liquidityPacked)
          x0 x1 x2 ptr x4 x5 delta R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (tickUpperReturnTrace v I g s0 evm.σ₀ mem rdata tick x0 x1 x2 ptr x4 x5 delta R)
      (poolUpdateTickResult f evm id (EVM.signed tick) delta true) := by
  have hr := poolUpdateTickUpperExactResultTrace f v hstack hI hm hd h
  apply functionResultTrace_mono hr
  intro post values ht
  unfold tickUpperReturnTraceAtAW at ht
  split at ht
  · exact ⟨ht.1, ht.2.1, ht.2.2.1, _, ht.2.2.2⟩
  · exact False.elim ht

end Benchmarks.UniswapV4PoolManager
