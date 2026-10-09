import Benchmarks.CompoundIII.Comet.CollateralCheckModel
import Benchmarks.CompoundIII.Comet.MappingScratch
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_048
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_050
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_051
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def collateralCheckPc (borrow : Bool) : UInt256 := if borrow then ⟨10164⟩ else ⟨10805⟩
def collateralPrincipalPc (borrow : Bool) : UInt256 := if borrow then ⟨10185⟩ else ⟨10819⟩
def collateralAssetsPc (borrow : Bool) : UInt256 := if borrow then ⟨10225⟩ else ⟨10848⟩
def collateralLoopInitPc (borrow : Bool) : UInt256 := if borrow then ⟨10348⟩ else ⟨10869⟩

def collateralBasicMemory (mem : ByteArray) (account : AccountAddress) : ByteArray :=
  twoWordHashMem (EVM.word account.val) ⟨5⟩ mem

theorem collateralBasicMemory_size {mem : ByteArray} (account : AccountAddress)
    (hm : 64 ≤ mem.size) : (collateralBasicMemory mem account).size = mem.size :=
  twoWordHashMem_size_of_ge_64 _ _ hm

theorem collateralBasicMemory_free {mem : ByteArray} {free : UInt256}
    (account : AccountAddress) (hm : 96 ≤ mem.size) (hf : memLoad ⟨64⟩ mem = free) :
    memLoad ⟨64⟩ (collateralBasicMemory mem account) = free := by
  rw [collateralBasicMemory, twoWordHashMem_load_ge (ptr := ⟨64⟩) _ _ (by decide) hm, hf]

theorem cometCollateralPrincipalRead {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (account : AccountAddress) (hstack : R.length + 9 ≤ 1024)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (collateralCheckPc borrow)
      (EVM.word account.val :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (collateralPrincipalPc borrow)
      (UInt256.signextend (UInt256.ofNat 12) (collateralBasicWord evm account) ::
        EVM.word account.val :: ret :: R)
      (collateralBasicMemory mem account) aw' rdata σ k' C' := by
  have hstep : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨2428⟩
      (⟨5⟩ :: EVM.word account.val :: ⟨10178⟩ :: collateralPrincipalPc borrow ::
        EVM.word account.val :: ret :: R) mem aw rdata σ k' C' := by
    cases borrow
    · exact ⟨_, _, cometWithExtendedAssetList_block_10805
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h⟩
    · exact ⟨_, _, cometWithExtendedAssetList_block_10164
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h⟩
  obtain ⟨k1, C1, r1⟩ := hstep
  obtain ⟨aw2, k2, C2, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 3 + 6 ≤ 1024; omega) (word_val_addr_canonical account)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_10178
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 3 ≤ 1024; omega)
    (by cases borrow <;>
      rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v] <;> jump_dest) r2
  dsimp only [cometWithExtendedAssetList_block_10178_stack] at r3
  change RD _ _ _ _ _ (UInt256.signextend _ (solcSlotWord σ ee (userBasicSlot account)) :: _)
    _ _ _ _ _ _ at r3
  rw [← hs.storageRead] at r3
  exact ⟨_, _, _, r3⟩

theorem cometCollateralPrincipalSolvent {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw basic account ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (borrow : Bool) (hstack : R.length + 7 ≤ 1024) (hp : 0 ≤ signed104 basic)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (collateralPrincipalPc borrow)
      (UInt256.signextend (UInt256.ofNat 12) basic :: account :: ret :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret (boolWord borrow :: R)
      mem aw rdata σ k' C' := by
  have hcond : UInt256.isZero (UInt256.slt (UInt256.signextend (UInt256.ofNat 12)
      (UInt256.signextend (UInt256.ofNat 12) basic)) (UInt256.ofNat 0)) ≠ UInt256.ofNat 0 := by
    have hslt : UInt256.slt (UInt256.signextend (UInt256.ofNat 12) basic)
        (UInt256.ofNat 0) = UInt256.ofNat 0 := signed104_slt_nonneg hp
    rw [signextend104_idem, hslt]
    decide
  cases borrow with
  | false =>
      have r1 := cometWithExtendedAssetList_block_10819_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega) hcond
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      exact ⟨_, _, cometWithExtendedAssetList_block_11078
        (immWords := wordsOf (immStore v)) (by omega) hret r1⟩
  | true =>
      have r1 := cometWithExtendedAssetList_block_10185_taken
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 6 ≤ 1024; omega) hcond
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
      exact ⟨_, _, cometWithExtendedAssetList_block_10625
        (immWords := wordsOf (immStore v)) (by omega) hret r1⟩

end Benchmarks.CompoundIII.Comet
