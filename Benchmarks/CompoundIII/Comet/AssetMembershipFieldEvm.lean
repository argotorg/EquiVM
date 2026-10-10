import Benchmarks.CompoundIII.Comet.AssetMembershipStore
import Benchmarks.CompoundIII.Comet.MappingScratch
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_065
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_066
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_067

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def assetMembershipReadPc (add reserved : Bool) : UInt256 :=
  if add then if reserved then ⟨14302⟩ else ⟨14232⟩
  else if reserved then ⟨14455⟩ else ⟨14387⟩

def assetMembershipMask (add reserved : Bool) (bit : Nat) : UInt256 :=
  if add then UInt256.ofNat (2^bit)
  else uintCastWord (if reserved then ⟨8, by decide⟩ else ⟨16, by decide⟩)
    (UInt256.lnot (UInt256.ofNat (2^bit)))

def assetMembershipFieldResult (evm : EVM.State) (account : AccountAddress)
    (add reserved : Bool) (bit : Nat) : InternalOutcome :=
  if evm.executionEnv.perm then .ok (storePackedWord evm (userBasicSlot account)
    (typedBitUpdateWord add (if reserved then ⟨8, by decide⟩ else ⟨16, by decide⟩)
      (userBasicFieldWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (userBasicSlot account)) (if reserved then 3 else 2)) bit)
    (if reserved then 31 else 29) (if reserved then 1 else 2)) else .staticViolation

theorem cometMembershipReadStore {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (add reserved : Bool) (bit : Nat)
    (hstack : R.length + 8 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (assetMembershipReadPc add reserved)
      (userBasicSlot account :: assetMembershipMask add reserved bit :: ⟨3121⟩ :: ret :: R)
      mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0 mem rdata ret R
      (assetMembershipFieldResult evm account add reserved bit) := by
  have hstep : ∃ k' C', RD (deployedRuntime v) ee g s0 (assetMembershipStorePc reserved)
      (userBasicSlot account ::
        typedBitUpdateWord add (if reserved then ⟨8, by decide⟩ else ⟨16, by decide⟩)
          (userBasicFieldWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (userBasicSlot account)) (if reserved then 3 else 2)) bit :: ⟨3121⟩ :: ret :: R)
      mem aw rdata σ k' C' := by
    cases add <;> cases reserved
    · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_14387
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 6 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      have r2 := cometWithExtendedAssetList_block_14404
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      refine ⟨k1 + 5, C1 + 18, ?_⟩
      simp only [typedBitUpdateWord, Bool.false_eq_true, if_false,
        (userBasicFieldWords _).2.2.1, hs.storageRead]
      exact r2
    · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_14455
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      have r2 := cometWithExtendedAssetList_block_14467
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      refine ⟨k1 + 5, C1 + 18, ?_⟩
      simp only [typedBitUpdateWord, if_true, (userBasicFieldWords _).2.2.2, hs.storageRead]
      exact r2
    · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_14232
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 6 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      have r2 := cometWithExtendedAssetList_block_14249
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      refine ⟨k1 + 5, C1 + 18, ?_⟩
      simp only [typedBitUpdateWord, Bool.false_eq_true, if_false, if_true,
        (userBasicFieldWords _).2.2.1, hs.storageRead]
      exact r2
    · obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_14302
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      have r2 := cometWithExtendedAssetList_block_14314
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
      refine ⟨k1 + 5, C1 + 18, ?_⟩
      simp only [typedBitUpdateWord, if_true,
        (userBasicFieldWords _).2.2.2, hs.storageRead]
      exact r2
  obtain ⟨k1, C1, r1⟩ := hstep
  have hrun := cometStoreMembership reserved (by change R.length + 1 + 7 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) hs r1
  cases hp : evm.executionEnv.perm
  · simpa only [assetMembershipFieldResult, hp, Bool.false_eq_true, if_false] using hrun
  · simp only [hp, if_true, internalMemoryRun] at hrun
    obtain ⟨σ', aw', k2, C2, hs', r2⟩ := hrun
    have r3 := cometWithExtendedAssetList_block_3121
      (immWords := wordsOf (immStore v)) (by omega) hret r2
    simp only [assetMembershipFieldResult, hp, if_true]
    exact ⟨σ', aw', _, _, hs', r3⟩

theorem cometMembershipField {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (account : AccountAddress) (add reserved : Bool) (bit : Nat)
    (hstack : R.length + 9 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨14224⟩
      (assetMembershipMask add reserved bit :: assetMembershipReadPc add reserved ::
        EVM.word account.val :: ⟨3121⟩ :: ret :: R) mem aw rdata σ k C) :
    internalMemoryRun (deployedRuntime v) ee g s0
      (twoWordHashMem (EVM.word account.val) ⟨5⟩ mem) rdata ret R
      (assetMembershipFieldResult evm account add reserved bit) := by
  have r1 := cometWithExtendedAssetList_block_14224
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hread : (D_J (deployedRuntime v) 0).contains
      (assetMembershipReadPc add reserved) = true := by
    cases add <;> cases reserved <;>
      simp only [assetMembershipReadPc, Bool.false_eq_true, if_false, if_true] <;>
      rw [cometWithExtendedAssetListPatchedValidJumps v] <;> jump_dest
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 3 + 6 ≤ 1024; omega) (word_val_addr_canonical account)
    hread r1
  exact cometMembershipReadStore account add reserved bit (by omega) hret hs r2

end Benchmarks.CompoundIII.Comet
