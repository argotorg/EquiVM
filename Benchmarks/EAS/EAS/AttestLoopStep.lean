import Benchmarks.EAS.EAS.AttestLoopMemoryNext

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem attestLoopStep {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {heap schema t3 t4 uidPtr available used : UInt256} {attester : AccountAddress} {last : Bool}
    {rs : List AttestationRequestRecord} {s : SchemaRecord} {ats : List AttestationRecord} {ptrs values uids R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+34 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hf : AttestLoopLocals L rs s schema attester available last ats values uids used i heap.toNat)
    (hm : AttestLoopMemory mem site t3 t4 uidPtr rs s attester ptrs values uids ats heap.toNat)
    (hi : i < rs.length) (hh : heap.toNat ≤ 2^64-1)
    (hreglen : attestLoopLength site = UInt256.ofNat rs.length)
    (rd : RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
      (recordNextStack site schema (UInt256.ofNat i) t3 t4 R) mem aw rdata σ k C) :
    (∃ L' evm' σ' mem' aw' k' C' heap' word,
      let a := {newAttestation rs[i] schema (easTimeWord ee) attester with uid := word}
      ee.perm = true ∧ heap.toNat ≤ heap' ∧ heap' ≤ 2^64-1 ∧
      AttestLoopLocals L' rs s schema attester available last (ats.set i a) (values.set i rs[i].value) (uids.set i word) used (i+1) heap' ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestIteration
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      SourceState s0 ee σ' evm' ∧ MemoryPrefix mem mem' uidPtr.toNat ∧
      AttestLoopMemory mem' site t3 t4 uidPtr rs s attester (ptrs.set i heap) (values.set i rs[i].value) (uids.set i word) (ats.set i a) heap' ∧
      (recordValuesPtr site t4).toNat+32+32*values.length ≤ mem'.size ∧
      RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
        (recordNextStack site schema (UInt256.ofNat (i+1)) t3 t4 R) mem' aw' rdata σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestIteration .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestIteration .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  have hu := hm.uidArray.span
  have huc := hm.uidArray.covered
  have hul := hm.uidLow
  have hrs := hm.requests.span
  have hlen : rs.length < UInt256.size := by change rs.length < 2^256; omega
  have hix : (UInt256.ofNat i).toNat = i := ulit_toNat' _ (by omega)
  have htest := easAttestLoopTest v site (by omega) rd
  obtain ⟨aw1,k1,C1,rd1⟩ := htest
  rw [if_pos (by rw [hix,hreglen,ulit_toNat' _ hlen]; exact hi)] at rd1
  obtain ⟨ptr,dp,hcell,hview,hpend,hdend⟩ := hm.requests.requests i hi
  let current := attestRequestSite site ptr
  let reg := attestRequestT3 site t3 ptr
  have hmcurrent : AttestLoopMemory mem current reg t4 uidPtr rs s attester ptrs values uids ats heap.toNat :=
    (attestLoopMemory_requestSite _ _ _ _ _ _ _ _ _ _ _ _ _ _).mpr hm
  have hcurrent : RD fork (deployedRuntime v) ee g s0 (requestReadPC current)
      (recordNextStack current schema (UInt256.ofNat i) reg t4 R) mem aw1 rdata σ k1 C1 := by
    simpa only [current,reg,attestRequestSite_readPC,attestRequestSite_nextStack] using rd1
  have hrun := attestIterationRun v current hstack hs hf hi (by omega) (by omega) (by omega)
    (by simpa only [current,attestRequestSite_requests] using lt_of_le_of_lt hrs uidPtr.val.isLt)
    (by simpa only [current,attestRequestSite_requests] using hm.requests.length)
    (by simpa only [current,reg,attestRequestSite_requests,attestRequestSite_ref] using hcell)
    (by simpa only [current,reg,attestRequestSite_ref] using hview)
    (by simpa only [current,attestRequestSite_schema] using hm.schemaView) hdend
    (by simpa only [current,attestRequestSite_attester] using hm.attesterWord)
    (by simpa only [u256_ofNat_toNat] using hm.heapRead) (hm.tailView hview hpend)
    hm.regions.length_eq.symm hm.lengthRequests hcurrent
  rcases hrun with ⟨L1,e1,σ1,m1,aw2,k2,C2,heap2,word,hperm,hgrowth,hcap,hf1,hsol,hstate,hfoot,hcore,hv1,hv2,hm1,hu2,ha2,hvs2,hh2,hr2⟩ |
      ⟨hsol,hrev⟩ | ⟨hsol,hstatic⟩
  · have hb : heap2 < UInt256.size := by change heap2 < 2^256; omega
    have hnext := hmcurrent.next hcore hfoot hm1 hv1 (by rw [hm.lengthRequests]; exact hi) hb hgrowth hdend hu2 ha2 hvs2 hh2
    refine Or.inl ⟨L1,e1,σ1,recordTailMemory m1 site heap t3 t4 rs[i].value uidPtr word i,
      aw2,k2,C2,heap2,word,hperm,by omega,hcap,hf1,hsol,hstate,?_,?_,?_,?_⟩
    · simpa only [current,reg,attestRequestSite_tail] using hfoot
    · simpa only [current,reg,attestRequestSite_tail,attestLoopMemory_requestSite] using hnext
    · simpa only [current,reg,attestRequestSite_tail,attestRequestSite_values,List.length_set] using hvs2.covered
    · simpa only [current,reg,attestRequestSite_tail,attestRequestSite_nextPC,attestRequestSite_nextStack] using hr2
  · exact Or.inr (Or.inl ⟨hsol,hrev⟩)
  · exact Or.inr (Or.inr ⟨hsol,hstatic⟩)

end Benchmarks.EAS.EAS
