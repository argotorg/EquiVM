import Benchmarks.UniswapV4PoolManager.TickUpperFeeTrace
import Benchmarks.UniswapV4PoolManager.TickUpperNetTrace
import Benchmarks.UniswapV4PoolManager.LiquidityAddTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickUpperStoreInput (id tick packed x5 x6 x7 ptr x9 x10 : UInt256) (delta : Int)
    (R : List UInt256) : List UInt256 :=
  tickSlot id (EVM.signed tick) :: EVM.wordOfInt (tickGrossAfterInt packed delta) ::
    EVM.wordOfInt (tickNetAfter packed delta true) :: UInt256.fromBool (tickFlipped packed delta) ::
    x5 :: x6 :: x7 :: ptr :: x9 :: x10 :: tick :: EVM.wordOfInt delta :: R

theorem tickUpperExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x5 x6 x7 ptr x9 x10 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨17774⟩
      (tickGrossWord (tickFieldWord evm id (EVM.signed tick) .liquidityPacked) :: EVM.wordOfInt delta :: ⟨7100⟩ ::
        tickUpperLiquidityTail id tick (tickFieldWord evm id (EVM.signed tick) .liquidityPacked) x5 x6 x7 ptr x9 x10 delta R)
      mem aw rdata evm.accountMap k C) :
    let packed := tickFieldWord evm id (EVM.signed tick) .liquidityPacked
    if liquidityAddFits (tickGrossWord packed) delta then
      if tickFeesNeeded evm id (EVM.signed tick) (Int.ofNat (tickGrossWord packed).toNat) ∧ I.perm = false then
        RDstatic (deployedRuntime v) g s0 else
      if signedFits ⟨128, by decide⟩ (tickNetAfter packed delta true) then ∃ k' C',
        RD (deployedRuntime v) I g s0 ⟨7205⟩ (tickUpperStoreInput id tick packed x5 x6 x7 ptr x9 x10 delta R)
          mem (if Int.ofNat (tickGrossWord packed).toNat = 0 then M aw (UInt256.ofNat 128) ⟨32⟩ else aw) rdata (tickFeesPost evm id packed (EVM.signed tick)).accountMap k' C'
      else RDrev (deployedRuntime v) g s0
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  generalize hp : tickFieldWord evm id (EVM.signed tick) .liquidityPacked = packed at h ⊢
  have hsum := liquidityAddTrace (x := tickGrossWord packed) (y := delta) (ret := ⟨7100⟩) v
    (by simp only [tickUpperLiquidityTail, List.length_cons]; omega) (tickGrossWord_bound packed) hd.1 hd.2
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) h
  by_cases hf : liquidityAddFits (tickGrossWord packed) delta
  · rw [if_pos hf] at hsum ⊢
    obtain ⟨k1, C1, rd1⟩ := hsum
    have hfees := tickUpperFeeExactTrace (packed := packed) (delta := delta) v (by omega) hI hm hf rd1
    by_cases hs : tickFeesNeeded evm id (EVM.signed tick) (Int.ofNat (tickGrossWord packed).toNat) ∧ I.perm = false
    · rw [if_pos hs] at hfees ⊢
      exact hfees
    · rw [if_neg hs] at hfees ⊢
      obtain ⟨k2, C2, rd2⟩ := hfees
      dsimp only [tickUpperNetInput] at rd2
      have hnet := tickUpperNetTrace (packed := packed) (delta := delta) v (by omega) hd rd2
      by_cases hn : signedFits ⟨128, by decide⟩ (tickNetAfter packed delta true)
      · rw [if_pos hn] at hnet ⊢
        obtain ⟨k3, C3, rd3⟩ := hnet
        exact ⟨k3, C3, rd3⟩
      · rw [if_neg hn] at hnet ⊢
        exact hnet
  · rw [if_neg hf] at hsum ⊢
    exact hsum

theorem tickUpperTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x5 x6 x7 ptr x9 x10 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨17774⟩
      (tickGrossWord (tickFieldWord evm id (EVM.signed tick) .liquidityPacked) :: EVM.wordOfInt delta :: ⟨7100⟩ ::
        tickUpperLiquidityTail id tick (tickFieldWord evm id (EVM.signed tick) .liquidityPacked) x5 x6 x7 ptr x9 x10 delta R)
      mem aw rdata evm.accountMap k C) :
    let packed := tickFieldWord evm id (EVM.signed tick) .liquidityPacked
    if liquidityAddFits (tickGrossWord packed) delta then
      if tickFeesNeeded evm id (EVM.signed tick) (Int.ofNat (tickGrossWord packed).toNat) ∧ I.perm = false then
        RDstatic (deployedRuntime v) g s0 else
      if signedFits ⟨128, by decide⟩ (tickNetAfter packed delta true) then ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ⟨7205⟩ (tickUpperStoreInput id tick packed x5 x6 x7 ptr x9 x10 delta R)
          mem aw' rdata (tickFeesPost evm id packed (EVM.signed tick)).accountMap k' C'
      else RDrev (deployedRuntime v) g s0
    else RDrev (deployedRuntime v) g s0 := by
  have hr := tickUpperExactTrace v hstack hI hm hd h
  dsimp only at hr ⊢
  split_ifs at hr ⊢
  all_goals first | exact hr | (obtain ⟨k', C', rd⟩ := hr; exact ⟨_, k', C', rd⟩)

end Benchmarks.UniswapV4PoolManager
