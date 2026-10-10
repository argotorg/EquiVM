import Benchmarks.UniswapV4PoolManager.TickBitmapStoreTrace
import Benchmarks.UniswapV4PoolManager.SignedModStep
import Benchmarks.UniswapV4PoolManager.WordSignextend24
import Benchmarks.UniswapV4PoolManager.FunctionResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

open poolManagerBlocks in
theorem tickBitmapExactTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick spacing ret : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (ht : int24Canonical tick) (hs : int24Canonical spacing) (hb : (EVM.signed tick).natAbs ≤ 887272)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16652⟩ ((poolSlot id+⟨5⟩) :: tick :: spacing :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    if tickBitmapAligned (EVM.signed tick) (EVM.signed spacing) then
      if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ k' C',
        RD (deployedRuntime v) I g s0 ret R
          (twoWordHashMem (EVM.wordOfInt (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)))
            (poolSlot id+⟨5⟩) mem) (tickBitmapActiveWords aw) rdata
          (tickBitmapPost evm id (EVM.signed tick) (EVM.signed spacing)).accountMap k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have rd1 := poolManager_block_16652 (by simp only [List.length_cons]; omega) h
  have ht' : UInt256.signextend (UInt256.ofNat 2) tick = tick := (signextend24_eq_iff tick).mpr ht
  have hs' : UInt256.signextend (UInt256.ofNat 2) spacing = spacing := (signextend24_eq_iff spacing).mpr hs
  simp only [poolManager_block_16652_stack, ht', hs'] at rd1
  have rd2 := rdSmod rd1
    (by immutable_decode(immutableLayout, poolManagerBytecode, wordsOf (immStore v), (⟨16665⟩ : UInt256), UInt8.ofNat 7,
      .SMOD, none, immutableLayout_inBounds, immutableTemplate_size64))
    (by simp only [List.length_cons]; omega)
  by_cases ha : tickBitmapAligned (EVM.signed tick) (EVM.signed spacing)
  · rw [if_pos ha]
    have hz : UInt256.smod tick spacing = UInt256.ofNat 0 := (tickBitmapAligned_word tick spacing hb).mpr ha
    have rd3 := poolManager_block_16666_fallthrough (by simp only [List.length_cons]; omega) hz rd2
    exact tickBitmapStoreExactTrace v (by omega) hI hb hret rd3
  · rw [if_neg ha]
    have hz : UInt256.smod tick spacing ≠ UInt256.ofNat 0 := fun he => ha ((tickBitmapAligned_word tick spacing hb).mp he)
    have rd3 := poolManager_block_16666_taken (by simp only [List.length_cons]; omega) hz
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
    exact poolManager_block_16698 (by simp only [List.length_cons]; omega) rd3

theorem tickBitmapTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick spacing ret : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (ht : int24Canonical tick) (hs : int24Canonical spacing) (hb : (EVM.signed tick).natAbs ≤ 887272)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨16652⟩ ((poolSlot id+⟨5⟩) :: tick :: spacing :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    if tickBitmapAligned (EVM.signed tick) (EVM.signed spacing) then
      if I.perm = false then RDstatic (deployedRuntime v) g s0 else ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ret R
          (twoWordHashMem (EVM.wordOfInt (tickBitmapPosition (EVM.signed tick) (EVM.signed spacing)))
            (poolSlot id+⟨5⟩) mem) aw' rdata
          (tickBitmapPost evm id (EVM.signed tick) (EVM.signed spacing)).accountMap k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hr := tickBitmapExactTrace v hstack hI ht hs hb hret h
  split_ifs at hr ⊢
  all_goals first | exact hr | (obtain ⟨k', C', rd⟩ := hr; exact ⟨_, k', C', rd⟩)

end Benchmarks.UniswapV4PoolManager
