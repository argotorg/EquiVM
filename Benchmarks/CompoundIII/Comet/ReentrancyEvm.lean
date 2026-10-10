import Benchmarks.CompoundIII.Comet.ReentrancyMemory
import Benchmarks.CompoundIII.Comet.ReentrancyStorage
import Benchmarks.CompoundIII.Comet.InternalMemoryOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_057
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometReentrancyWriteStatic {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw slot ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 3 ≤ 1024)
    (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 ⟨12270⟩ (slot :: ret :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  have r1 := h.push1 (UInt256.ofNat 1)
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨12270⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1,
      some ((UInt256.ofNat 1), 1), immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.swap1
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨12272⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r2 hperm
    (by immutable_decode(immutableLayout, cometWithExtendedAssetListBytecode,
      wordsOf (immStore v), (⟨12273⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

theorem cometReentrancyBefore {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨12245⟩ (ret :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 (reentrancyMemory v mem) rdata ret R
      (reentrancyOutcome evm true) := by
  have hcopy : memLoad (UInt256.ofNat 0)
      ((immutableLayout.runtime cometWithExtendedAssetListBytecode (wordsOf (immStore v))).write
        (UInt256.ofNat 18514).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat) =
      reentrancySlot := reentrancyCopyMemory_word v mem
  have hread : solcSlotWordAt reentrancySlot σ ee = reentrancyWord evm := by
    simpa only [reentrancyWord, hs.env] using (hs.storageRead reentrancySlot).symm
  have hcond : UInt256.eq (solcSlotWordAt reentrancySlot σ ee) (UInt256.ofNat 1) =
      UInt256.fromBool (decide ((reentrancyWord evm).toNat = 1)) := by
    rw [hread]
    unfold UInt256.eq
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro he; rw [he]; rfl
    · intro he; apply u256_inj; exact he
  by_cases hl : (reentrancyWord evm).toNat = 1
  · obtain ⟨_, _, r1⟩ := cometWithExtendedAssetList_block_12245_taken
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by rw [hcopy]; change UInt256.eq (solcSlotWordAt reentrancySlot σ ee) _ ≠ _
          rw [hcond, decide_eq_true hl]; decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [reentrancyOutcome, hl, decide_true, Bool.and_self, if_true, internalMemoryRun]
    exact cometWithExtendedAssetList_block_12275 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 3 ≤ 1024; omega) r1
  · obtain ⟨_, _, r1⟩ := cometWithExtendedAssetList_block_12245_fallthrough
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 5 ≤ 1024; omega)
      (by rw [hcopy]; change UInt256.eq (solcSlotWordAt reentrancySlot σ ee) _ = _
          rw [hcond, decide_eq_false hl]; rfl) h
    dsimp only [cometWithExtendedAssetList_block_12245_fallthrough_stack] at r1
    rw [hcopy] at r1
    change RD _ _ _ _ _ (reentrancySlot :: ret :: R) (reentrancyMemory v mem) _ _ _ _ _ at r1
    cases hp : evm.executionEnv.perm
    · simp only [reentrancyOutcome, hl, decide_false, Bool.and_false, Bool.false_eq_true,
        if_false, reentrancyWriteOutcome, hp, internalMemoryRun]
      exact cometReentrancyWriteStatic (by omega) (by simpa only [hs.env] using hp) r1
    · obtain ⟨_, _, r2⟩ := cometWithExtendedAssetList_block_12270
        (immWords := wordsOf (immStore v)) (by omega) (by simpa only [hs.env] using hp) hret r1
      simp only [reentrancyOutcome, hl, decide_false, Bool.and_false, Bool.false_eq_true,
        if_false, reentrancyWriteOutcome, hp, if_true, internalMemoryRun]
      exact ⟨_, _, _, _, sourceState_reentrancy hs true, r2⟩

theorem cometReentrancyAfterStop {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (hstack : R.length + 6 ≤ 1024)
    (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨2308⟩ R mem aw rdata σ k C) :
    ∃ σ', SourceState s0 ee σ' (reentrancyState evm false) ∧
      RDret (deployedRuntime v) g s0 σ' ByteArray.empty := by
  have hr := cometWithExtendedAssetList_block_2308
    (immWords := wordsOf (immStore v)) hstack hperm h
  have hcopy : memLoad (UInt256.ofNat 0)
      ((immutableLayout.runtime cometWithExtendedAssetListBytecode (wordsOf (immStore v))).write
        (UInt256.ofNat 18514).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat) =
      reentrancySlot := reentrancyCopyMemory_word v mem
  rw [hcopy] at hr
  exact ⟨_, sourceState_reentrancy hs false, hr⟩

end Benchmarks.CompoundIII.Comet
