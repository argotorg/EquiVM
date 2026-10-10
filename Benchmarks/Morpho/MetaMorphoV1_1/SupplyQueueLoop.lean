import Benchmarks.Morpho.MetaMorphoV1_1.SupplyQueueCapCheck

/-! Simulation of every capacity check in supply-queue replacement. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem supplyQueueLoopSimulation {evm s0 : State} {g : Sat256} {frame : Frame}
    {mem out : ByteArray} {aw : UInt256} {k C i : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 8 ≤ 1024)
    (hc : WordArrayCalldataChecks evm.executionEnv.calldata)
    (hready : SupplyQueueReady frame (calldataArrayValues evm.executionEnv.calldata) i)
    (hdiff : calldataArrayLength evm.executionEnv.calldata = i + remaining)
    (hmem : mem.size = 96)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨10055⟩
      ([UInt256.ofNat i, UInt256.ofNat (calldataArrayLength evm.executionEnv.calldata),
        UInt256.ofNat (calldataArrayOffset evm.executionEnv.calldata + 36)] ++ R)
      mem aw out evm.accountMap k C) :
    (ExecForLoop config frame evm supplyQueueLoopCondition maxDepositPost supplyQueueLoopBody
      .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ frame' mem',
      SupplyQueueReady frame' (calldataArrayValues evm.executionEnv.calldata)
        (calldataArrayLength evm.executionEnv.calldata) ∧ mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      ExecForLoop config frame evm supplyQueueLoopCondition maxDepositPost supplyQueueLoopBody
        (.ok frame' evm) ∧
      ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨10063⟩
        ([UInt256.ofNat (calldataArrayLength evm.executionEnv.calldata),
          UInt256.ofNat (calldataArrayLength evm.executionEnv.calldata),
          UInt256.ofNat (calldataArrayOffset evm.executionEnv.calldata + 36)] ++ R)
        mem' aw' out evm.accountMap k' C' := by
  have hlen : calldataArrayLength evm.executionEnv.calldata < UInt256.size :=
    lt_of_le_of_lt hc.length (by decide)
  induction remaining generalizing frame mem aw k C i with
  | zero =>
      have hi : i = calldataArrayLength evm.executionEnv.calldata := by omega
      subst i
      have hcond := supplyQueueConditionSource (evm := evm) hready
      simp only [calldataArrayValues_length, Nat.lt_irrefl, decide_false] at hcond
      have h1 := metaMorphoV1_1_block_10055_fallthrough
        (immWords := wordsOf (immStore v))
        (by change (_ :: R).length + 4 ≤ 1024; simp only [List.length_cons]; omega)
        (ult_zero (le_refl _)) rd
      exact .inr ⟨frame, mem, hready, hmem, hfree, ExecForLoop.falseDone hcond,
        _, _, _, h1⟩
  | succ n ih =>
      have hi : i < calldataArrayLength evm.executionEnv.calldata := by omega
      have hfit : i + 1 < UInt256.size := by omega
      have hword : (UInt256.ofNat i).toNat <
          (UInt256.ofNat (calldataArrayLength evm.executionEnv.calldata)).toNat := by
        rw [ulit_toNat' i (by omega), ulit_toNat' _ hlen]
        exact hi
      have hcond := supplyQueueConditionSource (evm := evm) hready
      simp only [calldataArrayValues_length, hi, decide_true] at hcond
      have h1 := metaMorphoV1_1_block_10055_taken (immWords := wordsOf (immStore v))
        (by change (_ :: R).length + 4 ≤ 1024; simp only [List.length_cons]; omega)
        (by rw [ult_one hword]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      have hcap := supplyQueueCapSource (evm := evm) hready
        (calldataArrayValues_getElem _ i hi)
      have hcheck := supplyQueueCapCheck v hstack hword h1
      dsimp only at hcheck
      rw [calldataArrayIndex_address hc hi] at hcheck
      rcases hcheck with ⟨hz, hrev⟩ | ⟨hz, aw2, k2, C2, h2⟩
      · simp only [hz, ne_eq, not_true_eq_false, decide_false] at hcap
        exact .inl ⟨ExecForLoop.bodyRevert hcond
          (ExecBlock.consRevert (ExecStmt.requireFalse hcap)), hrev⟩
      · simp only [ne_eq, hz, not_false_eq_true, decide_true] at hcap
        have hbody : ExecBlock config frame evm supplyQueueLoopBody (.ok frame evm) :=
          ExecBlock.consNormal (ExecStmt.requireTrue hcap) ExecBlock.nil
        have hpost := supplyQueuePostSource (evm := evm) hready hfit
        have h3 := metaMorphoV1_1_block_10348 (immWords := wordsOf (immStore v))
          (by change (_ :: _ :: R).length + 2 ≤ 1024
              simp only [List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
        have hadd : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
          u256_one_add_ofNat i
        simp only [metaMorphoV1_1_block_10348_stack, hadd] at h3
        rcases ih (supplyQueueIndexFrame_ready hready (i + 1)) (by omega)
            (twoWordHashMem_size_96 _ _ hmem) (twoWordHashMem_read64 _ _ hmem hfree) h3 with
          ⟨hbad, hrev⟩ | ⟨frame', mem', hready', hmem', hfree', hloop, hdone⟩
        · exact .inl ⟨ExecForLoop.iterate hcond hbody hpost hbad, hrev⟩
        · exact .inr ⟨frame', mem', hready', hmem', hfree',
            ExecForLoop.iterate hcond hbody hpost hloop, hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1
