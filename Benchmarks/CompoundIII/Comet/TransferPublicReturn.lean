import Benchmarks.CompoundIII.Comet.ReentrancyEvm
import Benchmarks.CompoundIII.Comet.FreeWordReturn
import Benchmarks.CompoundIII.Comet.ReturnOutcome
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def transferReturnPC (returnsBool : Bool) : UInt256 := if returnsBool then ⟨2116⟩ else ⟨2308⟩

def transferReturnData (returnsBool : Bool) : ByteArray :=
  if returnsBool then (UInt256.ofNat 1).toByteArray else ByteArray.empty

theorem transferReturnPC_valid (v : CometWithExtendedAssetListImmutables) (returnsBool : Bool) :
    (D_J (deployedRuntime v) 0).contains (transferReturnPC returnsBool) = true := by
  cases returnsBool <;> rw [cometWithExtendedAssetListPatchedValidJumps v] <;> jump_dest

theorem cometTransferPublicReturn {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (returnsBool : Bool)
    (hstack : R.length + 6 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (transferReturnPC returnsBool) R mem aw rdata σ k C) :
    returnOutcomeRun (deployedRuntime v) g s0 (transferReturnData returnsBool)
      (.ok (reentrancyState evm false)) := by
  cases returnsBool with
  | false =>
    obtain ⟨σ', hs', hr⟩ := cometReentrancyAfterStop hstack hperm hs h
    simpa only [returnOutcomeRun, transferReturnData, Bool.false_eq_true, if_false, hs'.accounts]
      using hr
  | true =>
    have hr := cometWithExtendedAssetList_block_2116
      (immWords := wordsOf (immStore v)) hstack hperm h
    have hcopy : memLoad (UInt256.ofNat 0)
        ((immutableLayout.runtime cometWithExtendedAssetListBytecode (wordsOf (immStore v))).write
          (UInt256.ofNat 18514).toNat mem (UInt256.ofNat 0).toNat (UInt256.ofNat 32).toNat) =
        reentrancySlot := reentrancyCopyMemory_word v mem
    rw [hcopy] at hr
    have hs' := sourceState_reentrancy hs false
    let m := reentrancyMemory v mem
    change RDret _ _ _ _ (((UInt256.ofNat 1).toByteArray.write 0 m
      (memLoad (UInt256.ofNat 64) m).toNat 32).readWithPadding
        (memLoad (UInt256.ofNat 64) m).toNat 32) at hr
    rw [freeWordReturnData] at hr
    change RDret (deployedRuntime v) g s0
      (sstoreAccountMap ee.codeOwner σ reentrancySlot (reentrancyValue false))
      (UInt256.ofNat 1).toByteArray at hr
    simpa only [returnOutcomeRun, transferReturnData, if_true, hs'.accounts] using hr

end Benchmarks.CompoundIII.Comet
