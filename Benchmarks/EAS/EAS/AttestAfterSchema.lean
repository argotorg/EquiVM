import Benchmarks.EAS.EAS.AttestArraysRun
import Benchmarks.EAS.EAS.AttestLoopRun
import Benchmarks.EAS.EAS.AttestFinishRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestAfterSchemaBody : Body := attestArraysBody ++ [attestLoopStmt] ++ attestFinishBody

theorem attestAfterSchemaBody_eq : attestFunction.body.drop 15 = attestAfterSchemaBody := by native_decide

theorem attestAfterSchemaRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema available heap t3 t4 uidPtr : UInt256} {attester : AccountAddress} {last : Bool}
    {rs : List AttestationRequestRecord} {s : SchemaRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+38 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : AttestSetupLocals L rs s schema attester available last heap.toNat)
    (hm : AttestSetupMemory mem site uidPtr rs s attester heap.toNat)
    (hlen : attestLoopLength site = UInt256.ofNat rs.length)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hcd : ee.calldata.size < UInt256.size) (ha : recordArrayPtr site t3 t4 = heap)
    (hv : recordValuesPtr site t4 = UInt256.ofNat (allocateNext heap.toNat (32+352*rs.length)))
    (hav : attestAvailableWord site = available) (hlast : attestLastWord site = last.toUInt256)
    (hresult : 160 ≤ (recordResultPtr site mem).toNat)
    (hret : (D_J (deployedRuntime v) 0).contains (attestReturnPC site) = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (attestArraysStartPC site)
      (attestArraysStartStack site schema R) mem aw rdata σ k C) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256)
        (k' C' heap' : Nat) (uids : List UInt256) (used : UInt256),
      SourceState s0 ee σ' evm' ∧ heap.toNat ≤ heap' ∧ heap' ≤ 2^64-1 ∧ uids.length = rs.length ∧ used.toNat ≤ available.toNat ∧
      MemoryPrefix mem mem' (recordResultPtr site mem).toNat ∧
      AttestResultMemoryView mem' (recordResultPtr site mem) uidPtr uids used heap' ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap' ∧
      ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm attestAfterSchemaBody
        (.returned {contract := contract,locals := L',immutables := immStore v} evm'
          (some [attestationsResultValue uids used,.int (Int.ofNat heap')])) ∧
      RD fork (deployedRuntime v) ee g s0 (attestReturnPC site) (recordResultPtr site mem::R) mem' aw' out σ' k' C') ∨
    (ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm attestAfterSchemaBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm attestAfterSchemaBody .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  have hu := hm.uidLow
  have hus := hm.uidArray.span
  have huc := hm.uidArray.covered
  have hrend := hm.resultEnd
  simp only [List.length_replicate] at hus huc
  have hrun := attestArraysRun (evm := evm) v site (by omega) hf hm hlen hh hheap hcd ha hv rd
  dsimp only at hrun
  rcases hrun with ⟨hlo1,hhi1,hp1,hm1,hf1,hsrc1,a1,k1,C1,r1⟩ | ⟨hsrc,hrev⟩
  · let middle := allocateNext heap.toNat (32+352*rs.length)
    let next := allocateNext middle (32+32*rs.length)
    let m1 := attestArraysMemory mem ee.calldata heap rs.length
    have hn : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; exact lt_of_le_of_lt hhi1 (by decide))
    have hloop := attestLoopRun (heap := UInt256.ofNat next) v site (by omega) hs
      (by simpa only [hn] using hf1) (by simpa only [hn] using hm1) (by rw [hn]; exact hhi1) hlen r1
    rcases hloop with ⟨L2,e2,σ2,m2,a2,k2,C2,heap2,ptrs2,ats2,values2,uids2,hlo2,hhi2,hperm2,hs2,hp2,hf2,hm2,hvs2,hsrc2,r2⟩ |
      ⟨hsrc2,hrev⟩ | ⟨hsrc2,hstatic⟩
    · have hfoot : MemoryPrefix mem m2 uidPtr.toNat := (hp1.mono (by omega)).trans hp2
      have hresult2 := recordResultPtr_preserve site hfoot (by omega) (by omega)
      have hn2 : (UInt256.ofNat heap2).toNat = heap2 := ulit_toNat' _ (by change heap2 < 2^256; omega)
      have hfinish := attestFinishRun (heap := UInt256.ofNat heap2) v site hstack hs2
        (by simpa only [hn2] using hf2) (by simpa only [hn2] using hm2) (by simpa only [hn2] using hvs2)
        (by rw [hn2]; exact hhi2) hperm2 hav hlast (by rw [hresult2]; exact hresult) hret r2
      rcases hfinish with ⟨e3,σ3,m3,out,a3,k3,C3,heap3,hs3,hlo3,hhi3,hbudget,hp3,hres3,hfree3,hsrc3,r3⟩ |
        ⟨hsrc3,hrev⟩ | ⟨hsrc3,hstatic⟩
      · rw [hresult2] at hp3 hres3 r3
        have hsource := execFuncBody_append hsrc1 (execFuncBody_append (ExecBlock.consNormal hsrc2 ExecBlock.nil) hsrc3)
        refine Or.inl ⟨attestFinishLocals L2 uids2 (resolveManyUsedValue s.resolver values2) heap3,e3,σ3,m3,out,a3,k3,C3,heap3,uids2,resolveManyUsedValue s.resolver values2,
          hs3,?_,hhi3,hm2.lengthUIDs.trans hm2.lengthRequests,hbudget,(hfoot.mono (by omega)).trans hp3,hres3,hfree3,?_,r3⟩
        · rw [hn] at hlo2
          rw [hn2] at hlo3
          exact le_trans hlo1 (le_trans hlo2 hlo3)
        · simpa only [attestAfterSchemaBody,List.append_assoc] using hsource
      · refine Or.inr (Or.inl ⟨?_,hrev⟩)
        simpa only [attestAfterSchemaBody,List.append_assoc] using
          execFuncBody_append hsrc1 (execFuncBody_append (ExecBlock.consNormal hsrc2 ExecBlock.nil) hsrc3)
      · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
        simpa only [attestAfterSchemaBody,List.append_assoc] using
          execFuncBody_append hsrc1 (execFuncBody_append (ExecBlock.consNormal hsrc2 ExecBlock.nil) hsrc3)
    · refine Or.inr (Or.inl ⟨?_,hrev⟩)
      apply execFuncBody_append hsrc1
      exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert hsrc2)
    · refine Or.inr (Or.inr ⟨?_,hstatic⟩)
      apply execFuncBody_append hsrc1
      exact ExecFuncBody.execBlockStatic (ExecBlock.consStatic hsrc2)
  · refine Or.inr (Or.inl ⟨?_,hrev⟩)
    apply ExecFuncBody.execBlockRevert
    simpa only [attestAfterSchemaBody,List.append_assoc] using
      execBlock_append_term (s2 := [attestLoopStmt] ++ attestFinishBody) hsrc (by intros;exact nofun)

end Benchmarks.EAS.EAS
