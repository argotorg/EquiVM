import Benchmarks.EAS.EAS.AttestFinishSource
import Benchmarks.EAS.EAS.AttestFinishControl
import Benchmarks.EAS.EAS.AttestLoopMemory
import Benchmarks.EAS.EAS.AttestResultMemory
import Benchmarks.EAS.EAS.ResolveManyCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem attestFinishRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {heap schema t3 t4 uidPtr available used : UInt256} {attester : AccountAddress} {last : Bool}
    {rs : List AttestationRequestRecord} {s : SchemaRecord} {ats : List AttestationRecord} {ptrs values uids R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+38 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : AttestLoopLocals L rs s schema attester available last ats values uids used i heap.toNat)
    (hm : AttestLoopMemory mem site t3 t4 uidPtr rs s attester ptrs values uids ats heap.toNat)
    (hvalues : WordArrayMemoryView mem (recordValuesPtr site t4) values heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hperm : rs.length=0 ∨ ee.perm=true)
    (hav : attestAvailableWord site = available) (hlast : attestLastWord site = last.toUInt256)
    (hresult : 160 ≤ (recordResultPtr site mem).toNat)
    (hret : (D_J (deployedRuntime v) 0).contains (attestReturnPC site) = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (attestLoopExitPC site)
      (recordNextStack site schema (UInt256.ofNat i) t3 t4 R) mem aw rdata σ k C) :
    (∃ (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256) (k' C' heap' : Nat),
      SourceState s0 ee σ' evm' ∧ heap.toNat ≤ heap' ∧ heap' ≤ 2^64-1 ∧ (resolveManyUsedValue s.resolver values).toNat ≤ available.toNat ∧
      MemoryPrefix mem mem' (recordResultPtr site mem).toNat ∧
      AttestResultMemoryView mem' (recordResultPtr site mem) uidPtr uids (resolveManyUsedValue s.resolver values) heap' ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap' ∧
      ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm attestFinishBody
        (.returned {contract := contract,locals := attestFinishLocals L uids (resolveManyUsedValue s.resolver values) heap',immutables := immStore v}
          evm' (some [attestationsResultValue uids (resolveManyUsedValue s.resolver values),.int (Int.ofNat heap')])) ∧
      RD fork (deployedRuntime v) ee g s0 (attestReturnPC site) (recordResultPtr site mem::R) mem' aw' out σ' k' C') ∨
    (ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm attestFinishBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm attestFinishBody .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  have hu := hm.uidArray.span
  have hc := hm.uidArray.covered
  have hulo := hm.uidLow
  have hrend := hm.resultEnd
  have hrcov := hm.resultCovered
  have hlen : ats.length = values.length := hm.regions.length_eq.symm.trans hm.lengthValues.symm
  have hpv : ee.perm=true ∨ ats=[] := by
    rcases hperm with hzero | hp
    · exact Or.inr (List.length_eq_zero_iff.mp (by have hl := hm.regions.length_eq; have hlr := hm.lengthRequests; omega))
    · exact Or.inl hp
  obtain ⟨a1,k1,C1,r1⟩ := easAttestResolveStart v site (by omega) rd
  rw [hav,hlast] at r1
  have hrun := resolveManyCallRun (locals := L) (imms := immStore v) (args := attestResolveArgs) (retVar := "__c5$allocation")
    (ats := ats) (words := values) (target := s.resolver) (ptr := heap) (record := s.value) (rev := false)
    (available := available) (last := last) (R := attestFinishSaved site R) (ret := attestFinishPC site)
    (schema := requestSchemaPtr site) (array := recordArrayPtr site t3 t4) (values := recordValuesPtr site t4) v
    (by simp only [attestResolveArgs,evalExprs?,evalExpr?,hf.schemaRecord,hf.attestations,hf.values,hf.available,hf.last,hf.heap,
      EvalResult.ofOption,EvalResult.bind,bind,pure]) rfl
    (by rw [hm.schemaView.resolver]; exact solcAddrMask_clean (word_val_addr_canonical s.resolver))
    (by cases site <;> simp only [attestFinishSaved,List.length_cons] <;> omega) hpv hs
    (hm.regions.arrayView hm.records (by omega)) hvalues hlen hh
    (by simpa only [u256_ofNat_toNat] using hm.heapRead)
    (by cases site <;> simp only [attestFinishPC] <;> rw [easPatchedValidJumps v] <;> jump_dest) r1
  rcases hrun with (⟨hbudget,⟨e1,σ1,m1,out,a2,k2,C2,next,hs1,hlo,hhi,hpre,hfree,hcall,r2⟩ | ⟨hcall,hrev⟩⟩ | ⟨hcall,hrev⟩) | ⟨hcall,hstatic⟩
  · have hresultEq := recordResultPtr_preserve site hpre (by omega) (by omega)
    have hcovered : (recordResultPtr site m1).toNat+32 ≤ m1.size := by rw [hresultEq]; have := hpre.size; omega
    obtain ⟨a3,k3,C3,r3⟩ := easAttestReturn v site (by omega) (by rw [hresultEq]; exact hresult) hcovered hret r2
    rw [hresultEq] at r3
    have hn : (recordResultPtr site mem+UInt256.ofNat 32).toNat = (recordResultPtr site mem).toNat+32 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    have hpointer : memLoad (recordResultPtr site mem+UInt256.ofNat 32) mem = uidPtr := by
      cases site <;> exact hm.uidPointer
    have hpointer' : memLoad (recordResultPtr site mem+UInt256.ofNat 32) m1 = uidPtr :=
      (memLoad_of_prefix hpre _ (by rw [hn]; omega) (by rw [hn]; omega) (by rw [hn]; omega)).trans hpointer
    have huids := (hm.uidArray.preserve hpre heap.val.isLt).mono hlo
    let result := recordResultPtr site mem
    let value := resolveManyUsedValue s.resolver values
    let final := Reasoning.Theory.writeWord m1 result.toNat value
    have hfrees : memLoad (UInt256.ofNat 64) final = UInt256.ofNat next :=
      (memLoad_write_below m1 result.toNat (UInt256.ofNat 64) value (by change 96 ≤ result.toNat; exact hm.resultLow)
        (by change 96 ≤ m1.size; have := hpre.size; omega)).trans hfree
    exact Or.inl ⟨e1,σ1,final,out,a3,k3,C3,next,hs1,hlo,hhi,hbudget,
      (hpre.mono (by omega)).trans (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))),
      attestResultMemory_store value hm.resultLow hm.resultEnd (le_trans hm.resultCovered hpre.size) hpointer' huids
        (by change next < 2^256; omega),hfrees,attestFinishSource hf.result hf.heap hcall,r3⟩
  · exact Or.inr (Or.inl ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert hcall),hrev⟩)
  · exact Or.inr (Or.inl ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert hcall),hrev⟩)
  · exact Or.inr (Or.inr ⟨ExecFuncBody.execBlockStatic (ExecBlock.consStatic hcall),hstatic⟩)

end Benchmarks.EAS.EAS
