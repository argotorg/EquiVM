import Benchmarks.CompoundIII.Comet.AccountSupplyRewardEvm
import Benchmarks.CompoundIII.Comet.AccountBorrowRewardEvm
import Benchmarks.CompoundIII.Comet.UpdateBaseFinishEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_054

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: swap operands to turn signed greater-than into signed less-than.
theorem uint256_sgt_swap (a b : UInt256) : UInt256.sgt a b = UInt256.slt b a := by
  unfold UInt256.sgt UInt256.slt UInt256.sgtBool UInt256.sltBool
  split_ifs <;> rfl

def updateBaseMemory (mem : ByteArray) (ptr : UInt256)
    (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (addr : AccountAddress) (basic : UserBasicData) (principal : UInt256) : ByteArray :=
  updateBaseFinishMemory
    (accountAccruedMemory
      (writeWord mem ptr.toNat (UInt256.signextend (UInt256.ofNat 12) principal)) ptr
      (basic.accrued + accountReward v evm basic basic.principal (principalBorrow basic.principal)))
    ptr evm addr principal

theorem cometUpdateBasePrincipal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ptr principal ret : UInt256}
    {basic : UserBasicData} {R : List UInt256} (addr : AccountAddress)
    (hstack : R.length + 25 ≤ 1024) (hm : UserBasicMemory mem ptr basic)
    (hptr : 96 ≤ ptr.toNat) (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11701⟩
      (EVM.word addr.val :: ptr :: principal :: ret :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0
      (updateBaseMemory mem ptr v evm addr basic principal) rdata ret R
      (updateBaseOutcome v evm addr basic principal) := by
  have r1 := cometWithExtendedAssetList_block_11701 (immWords := wordsOf (immStore v))
    (by change R.length + 1 + 8 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [cometWithExtendedAssetList_block_11701_stack] at r1
  rw [show memLoad ptr mem = UInt256.signextend (UInt256.ofNat 12) basic.principal from
      hm.principal,
    signextend104_idem] at r1
  have hm2 := hm.writePrincipal principal
  have hvalid (b : Bool) :
      AccountRewardValid v evm { basic with principal := principal } basic.principal b ↔
        AccountRewardValid v evm basic basic.principal b := Iff.rfl
  by_cases hn : signed104 basic.principal < 0
  · have hb : principalBorrow basic.principal = true := by simp [principalBorrow, hn]
    have r2 := cometWithExtendedAssetList_block_11720_taken (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 11 ≤ 1024; omega)
      (by rw [signextend104_idem, uint256_sgt_swap]; exact signed104_slt_neg hn)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have hr := cometAccountBorrowReward (v := v) (by change R.length + 2 + 23 ≤ 1024; omega)
      hm2 hs hn r2
    dsimp only at hr
    simp only [hvalid] at hr
    by_cases hv : AccountRewardValid v evm basic basic.principal true
    · rw [if_pos hv] at hr
      obtain ⟨_, _, _, hm3, r3⟩ := hr
      have hf := cometUpdateBaseFinish (v := v) addr (by omega) hm3 hptr hs hret r3
      simp only [updateBaseOutcome, updatedBaseBasic, hb, if_pos hv, updateBaseMemory, hs.env]
      exact hf
    · rw [if_neg hv] at hr
      simpa only [updateBaseOutcome, hb, if_neg hv, internalMemoryRun] using hr
  · have hp : 0 ≤ signed104 basic.principal := by omega
    have hb : principalBorrow basic.principal = false := by simp [principalBorrow, hn]
    have r2 := cometWithExtendedAssetList_block_11720_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 11 ≤ 1024; omega)
      (by rw [signextend104_idem, uint256_sgt_swap]; exact signed104_slt_nonneg hp) r1
    have hr := cometAccountSupplyReward (v := v) (by change R.length + 2 + 22 ≤ 1024; omega)
      hm2 hs hp r2
    dsimp only at hr
    simp only [hvalid] at hr
    by_cases hv : AccountRewardValid v evm basic basic.principal false
    · rw [if_pos hv] at hr
      obtain ⟨_, _, _, hm3, r3⟩ := hr
      have hf := cometUpdateBaseFinish (v := v) addr (by omega) hm3 hptr hs hret r3
      simp only [updateBaseOutcome, updatedBaseBasic, hb, if_pos hv, updateBaseMemory, hs.env]
      exact hf
    · rw [if_neg hv] at hr
      simpa only [updateBaseOutcome, hb, if_neg hv, internalMemoryRun] using hr

end Benchmarks.CompoundIII.Comet
