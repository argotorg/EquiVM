import Benchmarks.CompoundIII.Comet.UpdateBaseIndexEvm
import Benchmarks.CompoundIII.Comet.UserBasicStoreEvm
import Benchmarks.CompoundIII.Comet.InternalMemoryOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def updateBaseFinishMemory (mem : ByteArray) (ptr : UInt256) (evm : EVM.State)
    (addr : AccountAddress) (principal : UInt256) : ByteArray :=
  twoWordHashMem (EVM.word addr.val) ⟨5⟩
    (accountIndexMemory mem ptr (accountRewardIndex evm (principalBorrow principal)))

theorem cometUpdateBaseFinish {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ptr principal ret : UInt256}
    {basic : UserBasicData} {R : List UInt256} (addr : AccountAddress)
    (hstack : R.length + 13 ≤ 1024) (hm : UserBasicMemory mem ptr basic)
    (hptr : 96 ≤ ptr.toNat) (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11931⟩
      (principal :: ⟨0⟩ :: ⟨0⟩ :: EVM.word addr.val :: ⟨11980⟩ :: ptr :: ⟨3121⟩ :: ret :: R)
      mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0
      (updateBaseFinishMemory mem ptr evm addr principal) rdata ret R
      (if ee.perm then .ok (storeUserBasic evm addr (basicSetIndex evm basic principal))
        else .staticViolation) := by
  obtain ⟨_, _, _, hm1, r1⟩ := cometUpdateBaseIndex (v := v)
    (by change R.length + 2 + 8 ≤ 1024; omega) hm hs h
  have r2 := cometWithExtendedAssetList_block_11973 (immWords := wordsOf (immStore v))
    (by change R.length + 5 + 2 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_2428 (immWords := wordsOf (immStore v))
    (by change R.length + 3 + 6 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  dsimp only [cometWithExtendedAssetList_block_2428_stack,
    cometWithExtendedAssetList_block_2428_memory] at r3
  have haddr : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (EVM.word addr.val) = EVM.word addr.val :=
    solcAddrMask_clean_left (word_val_addr_canonical addr)
  rw [haddr] at r3
  change RD _ _ _ _ _
    (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (updateBaseFinishMemory mem ptr evm addr principal) :: ptr :: ⟨3121⟩ :: ret :: R)
    (updateBaseFinishMemory mem ptr evm addr principal) _ _ _ _ _ at r3
  have hhash : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (updateBaseFinishMemory mem ptr evm addr principal) = userBasicSlot addr :=
    twoWordHashMem_solcMappingSlot_any ⟨5⟩ (EVM.word addr.val) _
  rw [hhash] at r3
  have r4 := cometWithExtendedAssetList_block_11980 (immWords := wordsOf (immStore v))
    (by change R.length + 4 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  have hm2 := hm1.scratch hptr (EVM.word addr.val) ⟨5⟩
  cases hperm : ee.perm
  · simp only [Bool.false_eq_true, if_false, internalMemoryRun]
    exact cometStoreUserBasicStatic (v := v) (by change R.length + 2 + 9 ≤ 1024; omega) hperm r4
  · simp only [if_true, internalMemoryRun]
    obtain ⟨_, _, _, _, hs5, r5⟩ := cometStoreUserBasic (v := v) addr
      (basicSetIndex evm basic principal) (by change R.length + 1 + 12 ≤ 1024; omega)
      hperm hm2 hs (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
    have r6 := cometWithExtendedAssetList_block_3121 (immWords := wordsOf (immStore v))
      (by omega) hret r5
    exact ⟨_, _, _, _, hs5, r6⟩

end Benchmarks.CompoundIII.Comet
