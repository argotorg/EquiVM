import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueBuildLoop
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueRemoveLoop
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateWithdrawQueueStore

/-! Compose the two queue loops with storage replacement and the final event. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueForInit (frame : Frame) (evm : State) :
    ExecBlock config frame evm [.letDecl "i" (some abiUInt256) (.intLit 0)]
      (.ok (updateWithdrawQueueIndexFrame frame 0) evm) :=
  ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0)
    (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem updateWithdrawQueueLoopsSimulation {evm s0 : State} {g : Sat256}
    {frame : Frame} {mem out : ByteArray} {aw : UInt256} {k C curr : Nat}
    {seen : List Bool} {queue : List UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 21 ≤ 1024)
    (hc : WordArrayCalldataChecks evm.executionEnv.calldata)
    (hr : UpdateWithdrawQueueReady (updateWithdrawQueueIndexFrame frame 0) (immStore v)
      (calldataUintArrayValues evm.executionEnv.calldata) curr 0 seen queue
      (UInt256.ofNat (192 + 32 * curr + 32 * calldataArrayLength evm.executionEnv.calldata)))
    (hm : UpdateWithdrawQueueMemory mem curr (calldataArrayLength evm.executionEnv.calldata)
      0 seen queue)
    (hfit : 192 + 32 * curr + 32 * calldataArrayLength evm.executionEnv.calldata < 2 ^ 64)
    (hcurr : (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨21⟩).toNat = curr)
    (hs : SourceState s0 evm.executionEnv evm.accountMap evm)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨8163⟩
      ([⟨0⟩, UInt256.ofNat (calldataArrayLength evm.executionEnv.calldata),
        UInt256.ofNat (calldataArrayOffset evm.executionEnv.calldata + 36), ⟨128⟩,
        UInt256.ofNat curr, UInt256.ofNat (160 + 32 * curr),
        UInt256.ofNat (192 + 32 * curr)] ++ R) mem aw out evm.accountMap k C) :
    (ExecBlock config frame evm
      ([updateWithdrawQueueBuildLoop, updateWithdrawQueueRemoveLoop] ++ updateWithdrawQueueTail)
      .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm
      ([updateWithdrawQueueBuildLoop, updateWithdrawQueueRemoveLoop] ++ updateWithdrawQueueTail)
      .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ final evm', ExecBlock config frame evm
      ([updateWithdrawQueueBuildLoop, updateWithdrawQueueRemoveLoop] ++ updateWithdrawQueueTail)
      (.ok final evm') ∧ RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty := by
  rcases updateWithdrawQueueBuildLoopSimulation v
      (calldataArrayLength evm.executionEnv.calldata) (by omega) hc hr hm hcurr
      (Nat.zero_add _).symm rd with
    ⟨hbad, hrev⟩ | ⟨frame1, mem1, seen1, queue1, hr1, hm1, hbuild, aw1, k1, C1, r1⟩
  · exact .inl ⟨ExecBlock.consRevert
      (ExecStmt.for (updateWithdrawQueueForInit _ _) hbad), hrev⟩
  have hbuildPrefix (result : ExecResult)
      (ht : ExecBlock config frame1 evm (updateWithdrawQueueRemoveLoop :: updateWithdrawQueueTail)
        result) :
      ExecBlock config frame evm
        ([updateWithdrawQueueBuildLoop, updateWithdrawQueueRemoveLoop] ++ updateWithdrawQueueTail)
        result := ExecBlock.consNormal
          (ExecStmt.for (updateWithdrawQueueForInit _ _) hbuild) ht
  have r2 := metaMorphoV1_1_block_8171 (immWords := wordsOf (immStore v))
    (by change R.length + 7 ≤ 1024; omega) r1
  rcases updateWithdrawQueueRemoveLoopSimulation v curr hstack (hr1.indexFrame 0)
      (hm1.heap hfit) (lt_trans hc.size (by decide)) hs (Nat.zero_add _).symm r2 with
    ⟨hbad, hrev⟩ | ⟨hbad, hstatic⟩ |
    ⟨frame2, evm2, cursor2, mem2, out2, hs2, hr2, hm2, hremove, aw2, k2, C2, r3⟩
  · exact .inl ⟨hbuildPrefix _ (ExecBlock.consRevert
      (ExecStmt.for (updateWithdrawQueueForInit _ _) hbad)), hrev⟩
  · exact .inr (.inl ⟨hbuildPrefix _ (ExecBlock.consStatic
      (ExecStmt.for (updateWithdrawQueueForInit _ _) hbad)), hstatic⟩)
  have hheap : UpdateWithdrawQueueHeap mem2 curr queue1.length seen1 queue1 cursor2 := by
    simpa only [hm2.queueLength] using hm2
  rcases updateWithdrawQueueTailSimulation v (by omega) hr2 hheap hs2 r3 with
    ⟨hbad, hstatic⟩ | ⟨final, evm', htail, hret⟩
  · exact .inr (.inl ⟨hbuildPrefix _ (ExecBlock.consNormal
      (ExecStmt.for (updateWithdrawQueueForInit _ _) hremove) hbad), hstatic⟩)
  · exact .inr (.inr ⟨final, evm', hbuildPrefix _ (ExecBlock.consNormal
      (ExecStmt.for (updateWithdrawQueueForInit _ _) hremove) htail), hret⟩)

end Benchmarks.Morpho.MetaMorphoV1_1
