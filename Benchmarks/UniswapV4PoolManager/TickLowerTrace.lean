import Benchmarks.UniswapV4PoolManager.TickLowerFeeTrace
import Benchmarks.UniswapV4PoolManager.TickLowerNetTrace
import Benchmarks.UniswapV4PoolManager.LiquidityAddTrace
import Benchmarks.UniswapV4PoolManager.MappingScratchMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickLowerStoreInput (id tick packed x0 x1 x2 x3 x4 x5 x6 : UInt256) (delta : Int)
    (R : List UInt256) : List UInt256 :=
  EVM.wordOfInt (tickNetAfter packed delta false) :: tickSlot id (EVM.signed tick) ::
    EVM.wordOfInt (tickGrossAfterInt packed delta) :: UInt256.fromBool (tickFlipped packed delta) ::
    (poolSlot id+⟨4⟩) :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: EVM.wordOfInt delta :: tick :: R

theorem tickLowerExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 x2 x3 x4 x5 x6 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (ht : int24Canonical tick) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6949⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: EVM.wordOfInt delta :: tick :: R)
      mem aw rdata evm.accountMap k C) :
    let packed := tickFieldWord evm id (EVM.signed tick) .liquidityPacked
    if liquidityAddFits (tickGrossWord packed) delta then
      if tickFeesNeeded evm id (EVM.signed tick) (Int.ofNat (tickGrossWord packed).toNat) ∧ I.perm = false then
        RDstatic (deployedRuntime v) g s0 else
      if signedFits ⟨128, by decide⟩ (tickNetAfter packed delta false) then ∃ k' C',
        RD (deployedRuntime v) I g s0 ⟨7038⟩ (tickLowerStoreInput id tick packed x0 x1 x2 x3 x4 x5 x6 delta R)
          (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) (M aw (UInt256.ofNat 128) ⟨32⟩) rdata
          (tickFeesPost evm id packed (EVM.signed tick)).accountMap k' C'
      else RDrev (deployedRuntime v) g s0
    else RDrev (deployedRuntime v) g s0 := by
  dsimp only
  obtain ⟨k1, C1, rd1⟩ := tickLowerStartExactTrace v (by omega) hI hm ht hd h
  generalize hp : tickFieldWord evm id (EVM.signed tick) .liquidityPacked = packed at rd1 ⊢
  have hsum := liquidityAddTrace (x := tickGrossWord packed) (y := delta) (ret := ⟨7009⟩) v (by
      simp only [tickLowerLiquidityTail, List.length_cons]; omega) (tickGrossWord_bound packed) hd.1 hd.2
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  have hload : memLoad (UInt256.ofNat 128) (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) = poolSlot id := by
    have hpres := twoWordHashMem_loadWord (mem := mem) tick (poolSlot id+⟨4⟩) (UInt256.ofNat 128) (by decide) hmem
    rw [hpres]
    exact hm
  by_cases hf : liquidityAddFits (tickGrossWord packed) delta
  · rw [if_pos hf] at hsum ⊢
    obtain ⟨k2, C2, rd2⟩ := hsum
    have hfees := tickLowerFeeExactTrace (packed := packed) (delta := delta) v (by omega) hI hload hf rd2
    simp only [memoryWords_idem, ite_self] at hfees
    by_cases hs : tickFeesNeeded evm id (EVM.signed tick)
        (Int.ofNat (tickGrossWord packed).toNat) ∧ I.perm = false
    · rw [if_pos hs] at hfees ⊢
      exact hfees
    · rw [if_neg hs] at hfees ⊢
      obtain ⟨k3, C3, rd3⟩ := hfees
      dsimp only [tickLowerNetInput] at rd3
      have hnet := tickLowerNetTrace (packed := packed) (delta := delta) (ret := ⟨7038⟩)
        v (by simp only [List.length_cons]; omega) hd
        (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd3
      by_cases hn : signedFits ⟨128, by decide⟩ (tickNetAfter packed delta false)
      · rw [if_pos hn] at hnet ⊢
        obtain ⟨k4, C4, rd4⟩ := hnet
        exact ⟨k4, C4, rd4⟩
      · rw [if_neg hn] at hnet ⊢
        exact hnet
  · rw [if_neg hf] at hsum ⊢
    exact hsum

theorem tickLowerTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick x0 x1 x2 x3 x4 x5 x6 : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+21 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (ht : int24Canonical tick) (hd : signedFits ⟨128, by decide⟩ delta)
    (h : RD (deployedRuntime v) I g s0 ⟨6949⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: EVM.wordOfInt delta :: tick :: R)
      mem aw rdata evm.accountMap k C) :
    let packed := tickFieldWord evm id (EVM.signed tick) .liquidityPacked
    if liquidityAddFits (tickGrossWord packed) delta then
      if tickFeesNeeded evm id (EVM.signed tick) (Int.ofNat (tickGrossWord packed).toNat) ∧ I.perm = false then
        RDstatic (deployedRuntime v) g s0 else
      if signedFits ⟨128, by decide⟩ (tickNetAfter packed delta false) then ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ⟨7038⟩ (tickLowerStoreInput id tick packed x0 x1 x2 x3 x4 x5 x6 delta R)
          (twoWordHashMem tick (poolSlot id+⟨4⟩) mem) aw' rdata
          (tickFeesPost evm id packed (EVM.signed tick)).accountMap k' C'
      else RDrev (deployedRuntime v) g s0
    else RDrev (deployedRuntime v) g s0 := by
  have hr := tickLowerExactTrace v hstack hI hm hmem ht hd h
  dsimp only at hr ⊢
  split_ifs at hr ⊢
  all_goals first | exact hr | (obtain ⟨k', C', rd⟩ := hr; exact ⟨_, k', C', rd⟩)

end Benchmarks.UniswapV4PoolManager
