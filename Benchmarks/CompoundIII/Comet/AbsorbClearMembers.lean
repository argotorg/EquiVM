import Benchmarks.CompoundIII.Comet.AssetMembershipStore
import Benchmarks.CompoundIII.Comet.MappingScratch
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_078

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbClearState (evm : EVM.State) (account : AccountAddress) : EVM.State :=
  storePackedWord (storePackedWord evm (userBasicSlot account) ⟨0⟩ 29 2)
    (userBasicSlot account) ⟨0⟩ 31 1

def absorbClearBlock : List Stmt :=
  [.assign .storage ⟨"userBasic", [.mindex (.var "account"), .field "assetsIn"]⟩ (.intLit 0),
    .assign .storage ⟨"userBasic", [.mindex (.var "account"), .field "_reserved"]⟩ (.intLit 0)]

theorem absorbClear_source (frame : Frame) (evm : EVM.State) (account : AccountAddress)
    (hc : frame.contract = contract) (hl : frame.locals.get? "userBasic" = none)
    (ha : frame.locals.get? "account" = some (.address account)) :
    ExecBlock config frame evm absorbClearBlock (.ok frame (absorbClearState evm account)) := by
  have he (evm' : EVM.State) : evalExpr? config frame evm' (.var "account") =
      .ok (.address account) := by simp only [evalExpr?, ha, EvalResult.ofOption]
  have h0 := assignUserBasicField frame evm account (.var "account") ⟨2, by decide⟩ ⟨0⟩
    hc hl (he evm)
  have h1 := assignUserBasicField frame (storePackedWord evm (userBasicSlot account) ⟨0⟩ 29 2)
    account (.var "account") ⟨3, by decide⟩ ⟨0⟩ hc hl (he _)
  exact ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure]; rfl) h0)
    (ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure]; rfl) h1) .nil)

def absorbClearMemory (mem : ByteArray) (account : AccountAddress) : ByteArray :=
  twoWordHashMem (EVM.word account.val) ⟨5⟩ (twoWordHashMem (EVM.word account.val) ⟨5⟩ mem)

theorem cometAbsorbClear {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {old oldBalance balance price scale principal : UInt256}
    {R : List UInt256} (account : AccountAddress) (hstack : R.length + 15 ≤ 1024)
    (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨17261⟩
      (old :: oldBalance :: balance :: price :: EVM.word account.val :: scale :: principal :: R)
      mem aw rdata σ k C) :
    ∃ σ' aw' k' C', SourceState s0 ee σ' (absorbClearState evm account) ∧
      RD (deployedRuntime v) ee g s0 ⟨17306⟩
        (principal :: old :: oldBalance :: balance :: price :: EVM.word account.val ::
          scale :: principal :: R) (absorbClearMemory mem account) aw' rdata σ' k' C' := by
  have r1 := cometWithExtendedAssetList_block_17261 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 9 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw1, k1, C1, r2⟩ := cometMappingHash (v := v)
    (by change R.length + 7 + 6 ≤ 1024; omega) (addressWord_val_canonical account)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  have r3 := cometWithExtendedAssetList_block_17272 (immWords := wordsOf (immStore v))
    (by change R.length + 7 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  obtain ⟨k3, C3, r4⟩ := cometWithExtendedAssetList_block_11547
    (immWords := wordsOf (immStore v)) (by change R.length + 7 + 6 ≤ 1024; omega) hperm
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  have hs' := sourceState_userBasicAssets hs (userBasicSlot account) ⟨0⟩
  have r5 := cometWithExtendedAssetList_block_17283 (immWords := wordsOf (immStore v))
    (by omega) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
  obtain ⟨aw5, k5, C5, r6⟩ := cometMappingHash (v := v)
    (by change R.length + 8 + 6 ≤ 1024; omega) (addressWord_val_canonical account)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
  have r7 := cometWithExtendedAssetList_block_17295 (immWords := wordsOf (immStore v))
    (by change R.length + 8 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
  obtain ⟨k7, C7, r8⟩ := cometWithExtendedAssetList_block_11083
    (immWords := wordsOf (immStore v)) (by change R.length + 8 + 7 ≤ 1024; omega) hperm
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
  exact ⟨_, _, _, _, sourceState_userBasicReserved hs' (userBasicSlot account) ⟨0⟩, r8⟩

end Benchmarks.CompoundIII.Comet
