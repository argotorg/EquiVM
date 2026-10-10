import Benchmarks.UniswapV4PoolManager.PoolUpdateTickCall
import Benchmarks.UniswapV4PoolManager.TickLowerTrace
import Benchmarks.UniswapV4PoolManager.TickLowerStoreTrace
import Benchmarks.UniswapV4PoolManager.FunctionTraceMono

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickLowerReturnTrace (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id lower upper x0 x1 x2 ptr x4 x5 : UInt256)
    (delta : Int) (R : List UInt256) : State → Option (List Value) → Prop
  | post, some [.bool flipped, .int gross] =>
    post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ unsignedFits ⟨128, by decide⟩ gross ∧
    ∃ aw k C, RD (deployedRuntime v) I g s0 ⟨17774⟩
      (tickGrossWord (tickFieldWord post id (EVM.signed upper) .liquidityPacked) :: EVM.wordOfInt delta :: ⟨7100⟩ ::
        tickUpperLiquidityTail id upper (tickFieldWord post id (EVM.signed upper) .liquidityPacked)
          x0 x1 x2 ptr x4 x5 delta (lower :: R))
      (twoWordHashMem upper (poolSlot id+⟨4⟩)
        (tickLowerResultMemory (twoWordHashMem lower (poolSlot id+⟨4⟩) mem) ptr
          (EVM.wordOfInt gross) (UInt256.fromBool flipped))) aw rdata post.accountMap k C
  | _, _ => False

def tickLowerUpdateActiveWords (aw ptr : UInt256) : UInt256 :=
  M (M (M (M (M (M aw (UInt256.ofNat 128) ⟨32⟩) (ptr+UInt256.ofNat 32) ⟨32⟩) ptr ⟨32⟩) ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64)

def tickLowerReturnTraceAtAW (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ₀ : AccountMap) (mem rdata : ByteArray) (id lower upper x0 x1 x2 ptr x4 x5 : UInt256)
    (delta : Int) (R : List UInt256) (aw : UInt256) : State → Option (List Value) → Prop
  | post, some [.bool flipped, .int gross] =>
    post.executionEnv = I ∧ post.σ₀ = σ₀ ∧ unsignedFits ⟨128, by decide⟩ gross ∧
    ∃ k C, RD (deployedRuntime v) I g s0 ⟨17774⟩
      (tickGrossWord (tickFieldWord post id (EVM.signed upper) .liquidityPacked) :: EVM.wordOfInt delta :: ⟨7100⟩ ::
        tickUpperLiquidityTail id upper (tickFieldWord post id (EVM.signed upper) .liquidityPacked)
          x0 x1 x2 ptr x4 x5 delta (lower :: R))
      (twoWordHashMem upper (poolSlot id+⟨4⟩)
        (tickLowerResultMemory (twoWordHashMem lower (poolSlot id+⟨4⟩) mem) ptr
          (EVM.wordOfInt gross) (UInt256.fromBool flipped))) aw rdata post.accountMap k C
  | _, _ => False

theorem poolUpdateTickLowerExactResultTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper x0 x1 x2 ptr x4 x5 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical lower) (hu : int24Canonical upper) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6949⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: upper :: EVM.wordOfInt delta :: lower :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (tickLowerReturnTraceAtAW v I g s0 evm.σ₀ mem rdata id lower upper x0 x1 x2 ptr x4 x5 delta R (tickLowerUpdateActiveWords aw ptr))
      (poolUpdateTickResult f evm id (EVM.signed lower) delta false) := by
  have hr := tickLowerExactTrace v hstack hI hm hmem hl hd h
  simp only [poolUpdateTickResult, poolUpdateTickFinishResult, poolUpdateTickTailResult,
    tickFeesPost_env, hI]
  dsimp only at hr
  generalize hp : tickFieldWord evm id (EVM.signed lower) .liquidityPacked = packed at hr ⊢
  by_cases hg : liquidityAddFits (tickGrossWord packed) delta
  · rw [if_pos hg] at hr ⊢
    by_cases hs : tickFeesNeeded evm id (EVM.signed lower) (Int.ofNat (tickGrossWord packed).toNat) ∧ I.perm = false
    · rw [if_pos hs] at hr ⊢
      exact hr
    · rw [if_neg hs] at hr ⊢
      by_cases hn : signedFits ⟨128, by decide⟩ (tickNetAfter packed delta false)
      · rw [if_pos hn] at hr ⊢
        obtain ⟨k1, C1, rd1⟩ := hr
        dsimp only [tickLowerStoreInput] at rd1
        have hI' := (tickFeesPost_env evm id packed (EVM.signed lower)).trans hI
        have hstore := tickLowerStoreExactTrace (delta := delta) v (by simp only [List.length_cons]; omega) hI' hu hd rd1
        by_cases hperm : I.perm = false
        · rw [if_pos hperm] at hstore ⊢
          exact hstore
        · rw [if_neg hperm] at hstore ⊢
          simp only [functionResultTrace, tickLowerReturnTraceAtAW, wordOfInt_ofNat_toNat]
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

theorem poolUpdateTickLowerResultTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper x0 x1 x2 ptr x4 x5 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical lower) (hu : int24Canonical upper) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6949⟩
      (x0 :: x1 :: x2 :: ptr :: x4 :: x5 :: upper :: EVM.wordOfInt delta :: lower :: R)
      mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (tickLowerReturnTrace v I g s0 evm.σ₀ mem rdata id lower upper x0 x1 x2 ptr x4 x5 delta R)
      (poolUpdateTickResult f evm id (EVM.signed lower) delta false) := by
  have hr := poolUpdateTickLowerExactResultTrace f v hstack hI hm hmem hl hu hd h
  apply functionResultTrace_mono hr
  intro post values ht
  unfold tickLowerReturnTraceAtAW at ht
  split at ht
  · exact ⟨ht.1, ht.2.1, ht.2.2.1, _, ht.2.2.2⟩
  · exact False.elim ht

end Benchmarks.UniswapV4PoolManager
