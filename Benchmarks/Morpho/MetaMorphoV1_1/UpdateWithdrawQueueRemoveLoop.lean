import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueOmitted
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueRemoveSelect
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_041

/-! Simulation of the removal loop, preserving both arrays across modular reader calls. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueRemoveBodySimulation {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {mem out : ByteArray} {aw : UInt256}
    {k C curr len i : Nat} {indexes : List Value} {seen : List Bool}
    {queue : List UInt256} {cursor : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 18 ≤ 1024)
    (hready : UpdateWithdrawQueueReady frame (immStore v) indexes curr i seen queue cursor)
    (hm : UpdateWithdrawQueueHeap mem curr len seen queue cursor) (hi : i < curr)
    (hcalldata : I.calldata.size < UInt256.size) (hs : SourceState s0 I evm.accountMap evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨8435⟩
      (UInt256.ofNat i :: ⟨128⟩ :: R) mem aw out evm.accountMap k C) :
    (ExecBlock config frame evm updateWithdrawQueueRemoveBody .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm updateWithdrawQueueRemoveBody .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    ∃ frame' evm' cursor' mem' out',
      SourceState s0 I evm'.accountMap evm' ∧
      UpdateWithdrawQueueReady frame' (immStore v) indexes curr i seen queue cursor' ∧
      UpdateWithdrawQueueHeap mem' curr len seen queue cursor' ∧
      ExecBlock config frame evm updateWithdrawQueueRemoveBody (.ok frame' evm') ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8452⟩
        (UInt256.ofNat i :: ⟨128⟩ :: R) mem' aw' out' evm'.accountMap k' C' := by
  rcases updateWithdrawQueueRemoveSelect v (by omega) hm hi rd with
    ⟨hb, aw1, k1, C1, r1⟩ | ⟨hb, aw1, k1, C1, r1⟩
  · exact .inr (.inr ⟨frame, evm, cursor, mem, out, hs, hready, hm,
      updateWithdrawQueueRetainedSource hready hb, aw1, k1, C1, r1⟩)
  · have hcond := updateWithdrawQueueUnseenSource (evm := evm) hready hb
    rcases updateWithdrawQueueOmittedSimulation v
        (by simp only [List.length_cons]; omega) hready hm hi hcalldata hs r1 with
      ⟨hbad, hrev⟩ | ⟨hbad, hstatic⟩ |
      ⟨frame', evm', cursor', mem', out', hs', hr', hm', hbody, hdone⟩
    · exact .inl ⟨ExecBlock.consRevert (ExecStmt.iteTrue hcond hbad), hrev⟩
    · exact .inr (.inl ⟨ExecBlock.consStatic (ExecStmt.iteTrue hcond hbad), hstatic⟩)
    · exact .inr (.inr ⟨frame', evm', cursor', mem', out', hs', hr', hm',
        ExecBlock.consNormal (ExecStmt.iteTrue hcond hbody) ExecBlock.nil, hdone⟩)

theorem updateWithdrawQueueRemoveLoopSimulation {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {mem out : ByteArray} {aw : UInt256}
    {k C curr len i : Nat} {indexes : List Value} {seen : List Bool}
    {queue : List UInt256} {cursor newData : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 21 ≤ 1024)
    (hready : UpdateWithdrawQueueReady frame (immStore v) indexes curr i seen queue cursor)
    (hm : UpdateWithdrawQueueHeap mem curr len seen queue cursor)
    (hcalldata : I.calldata.size < UInt256.size) (hs : SourceState s0 I evm.accountMap evm)
    (hdiff : curr = i + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨8175⟩
      ([UInt256.ofNat i, ⟨128⟩, UInt256.ofNat curr,
        UInt256.ofNat (160 + 32 * curr), newData] ++ R) mem aw out evm.accountMap k C) :
    (ExecForLoop config frame evm updateWithdrawQueueRemoveCondition updateWithdrawQueuePost
      updateWithdrawQueueRemoveBody .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecForLoop config frame evm updateWithdrawQueueRemoveCondition updateWithdrawQueuePost
      updateWithdrawQueueRemoveBody .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ frame' evm' cursor' mem' out',
      SourceState s0 I evm'.accountMap evm' ∧
      UpdateWithdrawQueueReady frame' (immStore v) indexes curr curr seen queue cursor' ∧
      UpdateWithdrawQueueHeap mem' curr len seen queue cursor' ∧
      ExecForLoop config frame evm updateWithdrawQueueRemoveCondition updateWithdrawQueuePost
        updateWithdrawQueueRemoveBody (.ok frame' evm') ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨8183⟩
        ([UInt256.ofNat curr, ⟨128⟩, UInt256.ofNat curr,
          UInt256.ofNat (160 + 32 * curr), newData] ++ R)
        mem' aw' out' evm'.accountMap k' C' := by
  have hcurr : curr < UInt256.size := by
    have hf := hm.seen.fit
    simp only [seenWords, List.length_map, hm.seenLength] at hf
    omega
  induction remaining generalizing evm frame mem out aw k C i cursor with
  | zero =>
      have heq : i = curr := by omega
      subst i
      have hcond := updateWithdrawQueueRemoveConditionSource (evm := evm) hready
      simp only [Nat.lt_irrefl, decide_false] at hcond
      have r1 := metaMorphoV1_1_block_8175_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 7 ≤ 1024; omega) (ult_zero (le_refl _)) rd
      exact .inr (.inr ⟨frame, evm, cursor, mem, out, hs, hready, hm,
        ExecForLoop.falseDone hcond, _, _, _, r1⟩)
  | succ n ih =>
      have hi : i < curr := by omega
      have hfit : i + 1 < UInt256.size := by omega
      have hcond := updateWithdrawQueueRemoveConditionSource (evm := evm) hready
      simp only [hi, decide_true] at hcond
      have r1 := metaMorphoV1_1_block_8175_taken (immWords := wordsOf (immStore v))
        (by change R.length + 7 ≤ 1024; omega)
        (by rw [ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hcurr]; exact hi)]
            decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      rcases updateWithdrawQueueRemoveBodySimulation v
          (by change R.length + 21 ≤ 1024; exact hstack) hready hm hi hcalldata hs r1 with
        ⟨hbad, hrev⟩ | ⟨hbad, hstatic⟩ |
        ⟨frame1, evm1, cursor1, mem1, out1, hs1, hr1, hm1, hbody, aw1, k1, C1, r2⟩
      · exact .inl ⟨ExecForLoop.bodyRevert hcond hbad, hrev⟩
      · exact .inr (.inl ⟨ExecForLoop.bodyStatic hcond hbad, hstatic⟩)
      · have hpost := updateWithdrawQueuePostSource (evm := evm1) hr1 hfit
        obtain ⟨k2, C2, r3⟩ := updateWithdrawQueueRemoveIncrement v
          (by change R.length + 6 ≤ 1024; omega) r2
        rcases ih (hr1.indexFrame (i + 1)) hm1 hs1 (by omega) r3 with
          ⟨hbad, hrev⟩ | ⟨hbad, hstatic⟩ |
          ⟨frame', evm', cursor', mem', out', hs', hr', hm', hloop, hdone⟩
        · exact .inl ⟨ExecForLoop.iterate hcond hbody hpost hbad, hrev⟩
        · exact .inr (.inl ⟨ExecForLoop.iterate hcond hbody hpost hbad, hstatic⟩)
        · exact .inr (.inr ⟨frame', evm', cursor', mem', out', hs', hr', hm',
            ExecForLoop.iterate hcond hbody hpost hloop, hdone⟩)

end Benchmarks.Morpho.MetaMorphoV1_1
