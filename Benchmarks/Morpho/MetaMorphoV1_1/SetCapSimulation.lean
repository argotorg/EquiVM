import Benchmarks.Morpho.MetaMorphoV1_1.SetCapNewMarketSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapTailSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapEntryRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapExistingSource

/-! Complete simulation of the allocated internal cap setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem setCapSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params cap id ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 34 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size) (hcap : cap.toNat < 2 ^ 184)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hmem : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hbytes : mem.readWithPadding params.toNat 160 = p.bytes)
    (hloads : MarketParamsLoads mem params p) (hs : SourceState s0 I σ evm)
    (hacc : ∃ acc, σ.get? I.codeOwner = some acc)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13448⟩
      ([params, id, cap, ret] ++ R) mem aw rdata σ k C) :
    (ExecFuncBody config (setCapFrame (immStore v) p id cap ptr) evm
      allocatedSetCapFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecFuncBody config (setCapFrame (immStore v) p id cap ptr) evm
      allocatedSetCapFunction.body .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (final : Frame) (cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      ExecFuncBody config (setCapFrame (immStore v) p id cap ptr) evm
        allocatedSetCapFunction.body (.returned final evm' (some [uint256Value cursor])) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
        mem' aw' out evm'.accountMap k' C' := by
  have hready := setCapFrame_ready (immStore v) p id cap ptr
  obtain ⟨aw1, k1, C1, h1⟩ := setCapEntryRuntime v (by omega) hcap rd
  by_cases hz : cap = ⟨0⟩
  · subst cap
    rw [if_pos rfl] at h1
    cases hperm : I.perm with
    | false =>
        exact .inr (.inl ⟨setCapZeroStatic evm (immStore v) p id ptr
          (by rw [hs.env]; exact hperm), setCapTailStaticRuntime v (by omega) hperm h1⟩)
    | true =>
        obtain ⟨_, mem2, hs2, _, aw2, k2, C2, h2⟩ :=
          setCapTailSimulation v (by omega) hready hs hcap hperm hret h1
        obtain ⟨final, hsource⟩ := setCapZeroSource evm (immStore v) p id ptr
        exact .inr (.inr ⟨setCapFinalState evm id ⟨0⟩, final, ptr, mem2, rdata,
          hs2, hsource, aw2, k2, C2, h2⟩)
  rw [if_neg hz] at h1
  have hpositive : evalExpr? config (setCapAliasFrame (setCapFrame (immStore v) p id cap ptr) id)
      evm setCapCondition = .ok (.bool true) := by
    simpa only [ne_eq, hz, not_false_eq_true, decide_true] using setCapConditionSource hready.cap
  have henabled : marketRemovalEnabledWord evm id = setCapEnabledWord I σ id := by
    dsimp only [marketRemovalEnabledWord, marketRemovalConfigWord, setCapEnabledWord]
    rw [hs.storageRead]
  obtain ⟨k2, C2, h2⟩ := setCapEnabledRuntime v (by omega) h1
  by_cases hdisabled : setCapEnabledWord I σ id = ⟨0⟩
  · rw [if_pos hdisabled] at h2
    have hdisabledSource :
        evalExpr? config (setCapAliasFrame (setCapFrame (immStore v) p id cap ptr) id)
          evm setCapDisabledCondition = .ok (.bool true) := by
      rw [setCapDisabledSource hready.reference, henabled, hdisabled]
      rfl
    have hprefix0 : MemoryPrefix mem (wordAt0Mem id mem) ptr.toNat :=
      memoryPrefix_sparse_writeWord mem 0 ptr.toNat id (.inr (by decide))
    have hprefixMem : MemoryPrefix mem (twoWordHashMem id ⟨13⟩ mem) ptr.toNat :=
      hprefix0.trans
        (memoryPrefix_sparse_writeWord (wordAt0Mem id mem) 32 ptr.toNat ⟨13⟩ (.inr (by decide)))
    have hf0 : memLoad ⟨64⟩ (wordAt0Mem id mem) = memLoad ⟨64⟩ mem :=
      memLoad_write_disjoint _ _ _ _ (by change 96 ≤ mem.size; omega) (.inr (by decide))
    have hf1 : memLoad ⟨64⟩ (twoWordHashMem id ⟨13⟩ mem) =
        memLoad ⟨64⟩ (wordAt0Mem id mem) :=
      memLoad_write_disjoint _ _ _ _
        (by change 96 ≤ (wordAt0Mem id mem).size; have := hprefix0.size; omega)
        (.inr (by decide))
    have hbytes2 : (twoWordHashMem id ⟨13⟩ mem).readWithPadding params.toNat 160 = p.bytes := by
      rw [memoryPrefix_read_words hprefixMem 5 params.toNat hparamslo hparams (by omega)]
      exact hbytes
    have hloads2 := hloads.prefix hprefixMem hparamslo (by omega) hparams
      (lt_of_le_of_lt hparams ptr.val.isLt)
    rcases setCapNewMarketSimulation v p hstack hready rfl hcalldata
        (hf1.trans (hf0.trans hfree)) hlo (le_trans hmem hprefixMem.size) hparamslo
        hparams hbytes2 hloads2 hs hacc h2 with
      ⟨hbad, hrev⟩ | ⟨hstatic, hhalt⟩ |
        ⟨evm3, frame3, ptr3, mem3, out3, hs3, hready3, hsource3, hperm, aw3, k3, C3, h3⟩
    · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
      apply (setCapAliasPrefix evm (immStore v) p id cap ptr).run
      exact ExecBlock.consRevert (ExecStmt.iteTrue hpositive
        (ExecBlock.consRevert (ExecStmt.iteTrue hdisabledSource hbad)))
    · refine .inr (.inl ⟨ExecFuncBody.execBlockStatic ?_, hhalt⟩)
      apply (setCapAliasPrefix evm (immStore v) p id cap ptr).run
      exact ExecBlock.consStatic (ExecStmt.iteTrue hpositive
        (ExecBlock.consStatic (ExecStmt.iteTrue hdisabledSource hstatic)))
    · obtain ⟨final, mem4, hs4, htail, aw4, k4, C4, h4⟩ :=
        setCapClearAndTailSimulation v (by omega) hready3 hs3 hcap hperm hret h3
      refine .inr (.inr ⟨setCapFinalState (setCapClearTimeState evm3 id) id cap,
        final, ptr3, mem4, out3, hs4, ExecFuncBody.execBlockRet ?_, aw4, k4, C4, h4⟩)
      apply (setCapAliasPrefix evm (immStore v) p id cap ptr).run
      apply ExecBlock.consNormal (ExecStmt.iteTrue hpositive ?_) htail
      exact ExecBlock.consNormal (ExecStmt.iteTrue hdisabledSource hsource3)
        (ExecBlock.consNormal (setCapClearTimeAssign hready3.reference) ExecBlock.nil)
  · rw [if_neg hdisabled] at h2
    have henabledSource : marketRemovalEnabledWord evm id ≠ ⟨0⟩ := by
      rwa [henabled]
    cases hperm : I.perm with
    | false =>
        exact .inr (.inl ⟨setCapExistingStatic evm (immStore v) p id cap ptr hz henabledSource
          (by rw [hs.env]; exact hperm), setCapClearTimeStaticRuntime v (by omega) hperm h2⟩)
    | true =>
        obtain ⟨_, mem3, hs3, _, aw3, k3, C3, h3⟩ :=
          setCapClearAndTailSimulation v (by omega) hready hs hcap hperm hret h2
        obtain ⟨final, hsource⟩ :=
          setCapExistingSource evm (immStore v) p id cap ptr hz henabledSource
        exact .inr (.inr ⟨setCapFinalState (setCapClearTimeState evm id) id cap,
          final, ptr, mem3, rdata, hs3, hsource, aw3, k3, C3, h3⟩)

end Benchmarks.Morpho.MetaMorphoV1_1
