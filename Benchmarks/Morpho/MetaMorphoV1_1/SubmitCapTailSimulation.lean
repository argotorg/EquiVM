import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapImmediateSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapScheduleSource
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapScheduleRuntime

/-! All cap-submission outcomes after the last-update reader returns. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem pendingCapScheduledState_source {s0 evm : State} {I : ExecutionEnv}
    (hs : SourceState s0 I evm.accountMap evm) (id cap : UInt256) :
    SourceState s0 I (pendingCapScheduledState evm id cap).accountMap
      (pendingCapScheduledState evm id cap) := by
  refine ⟨?_, ?_, rfl⟩
  · simp only [pendingCapScheduledState, pendingCapTimeState, pendingCapValueState,
      storageStore_σ₀, hs.world]
  · rw [pendingCapScheduledState_env, hs.env]

theorem submitCapTailSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {p : MarketParamsData} {mem out : ByteArray}
    {aw ptr params cap id last first : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 34 ≤ 1024)
    (h : SubmitCapReady frame p id cap last ptr) (himms : frame.immutables = immStore v)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hmem : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hbytes : mem.readWithPadding params.toNat 160 = p.bytes)
    (hloads : MarketParamsLoads mem params p) (hs : SourceState s0 I evm.accountMap evm)
    (hlast : lastUpdateValue (memLoad first mem) = last)
    (rd : RD (deployedRuntime v) I g s0 ⟨9144⟩
      ([first, UInt256.ofNat (2 ^ 128 - 1), cap, params, id] ++ R)
      mem aw out evm.accountMap k C) :
    (ExecBlock config frame evm (submitCapGuards ++ [submitCapBranch]) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm (submitCapGuards ++ [submitCapBranch]) .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    ∃ evm' frame', SourceState s0 I evm'.accountMap evm' ∧
      ExecBlock config frame evm (submitCapGuards ++ [submitCapBranch]) (.ok frame' evm') ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty := by
  have rd0 := rd
  rw [← hs.env] at rd0
  rcases submitCapGuardsReach v (by omega) hlast rd0 with
    ⟨hbad, hrev⟩ | ⟨hgood, aw1, k1, C1, r1⟩
  · exact .inl ⟨submitCapGuardsRevert [submitCapBranch] h hbad, hrev⟩
  let f := submitCapCapFrame frame (marketRemovalCap evm id)
  have hf : SubmitCapReady f p id cap last ptr := h.supply _
  have hc := submitCapDecreaseSource (evm := evm) hf.cap (store_get_self _ _ _)
  have hprefix := submitCapGuardsPass [submitCapBranch] h hgood
  obtain ⟨k2, C2, r2⟩ := submitCapBranchChoice v
    (by change R.length + 2 + 3 ≤ 1024; omega) r1
  by_cases hd : cap.toNat < (marketRemovalCap evm id).toNat
  · rw [if_pos hd, hs.env] at r2
    have hc' : evalExpr? config f evm submitCapDecreaseCondition = .ok (.bool true) := by
      simpa only [hd, decide_true] using hc
    have hpres := submitCapGuardMemory_prefix mem id ptr.toNat
    have hb : (submitCapGuardMemory mem id).readWithPadding params.toNat 160 = p.bytes := by
      rw [memoryPrefix_read_words hpres 5 params.toNat hparamslo hparams (by omega)]
      exact hbytes
    have hl := hloads.prefix hpres hparamslo (by omega) hparams
      (lt_of_le_of_lt hparams ptr.val.isLt)
    rcases submitCapImmediateSimulation (params := params) (ptr := ptr) v hstack hf himms
      hcalldata (by rw [submitCapGuardMemory_free id (by omega)]; exact hfree) hlo
      (le_trans hmem hpres.size) hparamslo hparams hb hl hs hd r2 with
      ⟨hbranch, hrev⟩ | ⟨hbranch, hstatic⟩ | ⟨evm', final, hs', hbranch, hret⟩
    · exact .inl ⟨hprefix.run (ExecBlock.consRevert (ExecStmt.iteTrue hc' hbranch)), hrev⟩
    · exact .inr (.inl ⟨hprefix.run (ExecBlock.consStatic (ExecStmt.iteTrue hc' hbranch)),
        hstatic⟩)
    · exact .inr (.inr ⟨evm', final, hs',
        hprefix.run (ExecBlock.consNormal (ExecStmt.iteTrue hc' hbranch) ExecBlock.nil), hret⟩)
  · rw [if_neg hd] at r2
    have hc' : evalExpr? config f evm submitCapDecreaseCondition = .ok (.bool false) := by
      simpa only [hd, decide_false] using hc
    rcases submitCapScheduleRuntime v (by omega) r2 with
      ⟨hover, hrev⟩ | ⟨hcap, hperm, hstatic⟩ | ⟨hcap, hperm, hover, hrev⟩ |
        ⟨hcap, hperm, hfit, hret⟩
    · exact .inl ⟨hprefix.run (ExecBlock.consRevert (ExecStmt.iteFalse hc'
        (ExecBlock.consRevert (submitCapCastCallReverts hf false hover)))), hrev⟩
    · exact .inr (.inl ⟨hprefix.run (ExecBlock.consStatic (ExecStmt.iteFalse hc'
        (submitCapScheduledStatic hf hcap hperm))), hstatic⟩)
    · exact .inl ⟨hprefix.run (ExecBlock.consRevert (ExecStmt.iteFalse hc'
        (submitCapScheduledRevert hf hcap hover))), hrev⟩
    · obtain ⟨final, hbranch⟩ := submitCapScheduledReturns hf hcap hfit
      exact .inr (.inr ⟨_, final, pendingCapScheduledState_source hs id cap,
        hprefix.run (ExecBlock.consNormal (ExecStmt.iteFalse hc' hbranch) ExecBlock.nil), hret⟩)

end Benchmarks.Morpho.MetaMorphoV1_1
