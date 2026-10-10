import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueBuildSource
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueBuildRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.UintArrayCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_041

/-! Simulation of the complete queue-construction loop, including both rejection paths. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueBuildLoopSimulation {evm s0 : State} {g : Sat256}
    {frame : Frame} {imms : Store} {mem out : ByteArray} {aw : UInt256}
    {k C curr i : Nat} {seen : List Bool} {queue : List UInt256}
    {cursor newData : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 15 ≤ 1024)
    (hc : WordArrayCalldataChecks evm.executionEnv.calldata)
    (hready : UpdateWithdrawQueueReady frame imms
      (calldataUintArrayValues evm.executionEnv.calldata) curr i seen queue cursor)
    (hm : UpdateWithdrawQueueMemory mem curr (calldataArrayLength evm.executionEnv.calldata)
      i seen queue)
    (hcurr : (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat = curr)
    (hdiff : calldataArrayLength evm.executionEnv.calldata = i + remaining)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8163⟩
      ([UInt256.ofNat i, UInt256.ofNat (calldataArrayLength evm.executionEnv.calldata),
        UInt256.ofNat (calldataArrayOffset evm.executionEnv.calldata + 36), ⟨128⟩,
        UInt256.ofNat curr, UInt256.ofNat (160 + 32 * curr), newData] ++ R)
      mem aw out evm.accountMap k C) :
    (ExecForLoop config frame evm updateWithdrawQueueBuildCondition updateWithdrawQueuePost
      updateWithdrawQueueBuildBody .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ frame' mem' seen' queue',
      UpdateWithdrawQueueReady frame' imms (calldataUintArrayValues evm.executionEnv.calldata)
        curr (calldataArrayLength evm.executionEnv.calldata) seen' queue' cursor ∧
      UpdateWithdrawQueueMemory mem' curr (calldataArrayLength evm.executionEnv.calldata)
        (calldataArrayLength evm.executionEnv.calldata) seen' queue' ∧
      ExecForLoop config frame evm updateWithdrawQueueBuildCondition updateWithdrawQueuePost
        updateWithdrawQueueBuildBody (.ok frame' evm) ∧
      ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨8171⟩
        ([UInt256.ofNat (calldataArrayLength evm.executionEnv.calldata),
          UInt256.ofNat (calldataArrayLength evm.executionEnv.calldata),
          UInt256.ofNat (calldataArrayOffset evm.executionEnv.calldata + 36), ⟨128⟩,
          UInt256.ofNat curr, UInt256.ofNat (160 + 32 * curr), newData] ++ R)
        mem' aw' out evm.accountMap k' C' := by
  have hlen : calldataArrayLength evm.executionEnv.calldata < UInt256.size :=
    lt_of_le_of_lt hc.length (by decide)
  induction remaining generalizing frame mem aw k C i seen queue with
  | zero =>
      have heq : i = calldataArrayLength evm.executionEnv.calldata := by omega
      subst i
      have hcond := updateWithdrawQueueBuildConditionSource (evm := evm) hready
      simp only [calldataUintArrayValues_length, Nat.lt_irrefl, decide_false] at hcond
      have r1 := metaMorphoV1_1_block_8163_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 9 ≤ 1024; omega) (ult_zero (le_refl _)) rd
      exact .inr ⟨frame, mem, seen, queue, hready, hm, ExecForLoop.falseDone hcond,
        _, _, _, r1⟩
  | succ n ih =>
      have hi : i < calldataArrayLength evm.executionEnv.calldata := by omega
      have hfit : i + 1 < UInt256.size := by omega
      have hcond := updateWithdrawQueueBuildConditionSource (evm := evm) hready
      simp only [calldataUintArrayValues_length, hi, decide_true] at hcond
      have r1 := metaMorphoV1_1_block_8163_taken (immWords := wordsOf (immStore v))
        (by change R.length + 9 ≤ 1024; omega)
        (by rw [ult_one (by rw [ulit_toNat' _ (by omega), ulit_toNat' _ hlen]; exact hi)]
            decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      let prev := calldataWord evm.executionEnv.calldata
        (calldataArrayOffset evm.executionEnv.calldata + 36 + 32 * i)
      let id := codeOwnerStorageWord evm.executionEnv evm.accountMap
        (uInt256OfByteArray (KEC (UInt256.toByteArray ⟨21⟩)) + prev)
      have hprev : (calldataUintArrayValues evm.executionEnv.calldata)[i]? =
          some (uint256Value prev) := calldataUintArrayValues_getElem _ i hi
      have hstep := updateWithdrawQueueBuildRuntime v hstack hm hi hcurr r1
      dsimp only at hstep
      rw [calldataArrayIndex_address hc hi] at hstep
      rcases hstep with ⟨hp, hrev⟩ | ⟨hp, hb, hrev⟩ | ⟨hp, hb, aw2, k2, C2, r2⟩
      · have hbad := updateWithdrawQueueBuildReadRevert (evm := evm) hready hprev (by
          change ¬ prev.toNat < (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat
          rw [hcurr]
          exact Nat.not_lt.mpr hp)
        exact .inl ⟨ExecForLoop.bodyRevert hcond hbad, hrev⟩
      · have hread := updateWithdrawQueueBuildRead (evm := evm) hready hprev (by
          change prev.toNat < (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat
          rw [hcurr]
          exact hp)
        have hbad := hread.run (updateWithdrawQueueBuildTailRevert hready.seen hb)
        exact .inl ⟨ExecForLoop.bodyRevert hcond hbad, hrev⟩
      · have hread := updateWithdrawQueueBuildRead (evm := evm) hready hprev (by
          change prev.toNat < (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat
          rw [hcurr]
          exact hp)
        have hbody := hread.run (updateWithdrawQueueBuildTailPass hready hb
          (by rw [hm.queueLength]; exact hi))
        have hready' := hready.stepFrame prev id
        have hpost := updateWithdrawQueuePostSource (evm := evm) hready' hfit
        have hm' := (hm.scratch ⟨21⟩).step hp hi id
        rcases ih (hready'.indexFrame (i + 1)) hm' (by omega) r2 with
          ⟨hbad, hrev⟩ | ⟨frame', mem', seen', queue', hr', hm', hloop, hdone⟩
        · exact .inl ⟨ExecForLoop.iterate hcond hbody hpost hbad, hrev⟩
        · exact .inr ⟨frame', mem', seen', queue', hr', hm',
            ExecForLoop.iterate hcond hbody hpost hloop, hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1
