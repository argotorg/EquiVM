import Benchmarks.EAS.EAS.RevokeSource
import Benchmarks.EAS.EAS.RevokeStore
import Benchmarks.EAS.EAS.CopyStoredRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def revokeStoreCopyBody : Body := readTimeBlock "__c1$allocation" "__c1" ++ ([revokeWriteTime] ++ revokeCopyBody)
def revokeStoreCopyLocals (L : Store) (time : UInt256) (old heap : Nat) (a : AttestationRecord) : Store :=
  heapResultLocals (readTimeLocals L "__c1$allocation" "__c1" time old)
    "copied$allocation" "copied" "$EAS.freeMemory" a.value heap

theorem revokeStoreCopyRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {request idx heap : UInt256} {r : RevocationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (ha : L.get? "attestation" = some (.storageRef (attestationER r.uid) attestationType))
    (hr : L.get? "request" = some r.struct) (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hlo : 96 ≤ heap.toNat) (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.writePC
      (revokeWriteStack site.kind request idx (dbSlot r.uid) site.schema (UInt256.ofNat site.revoker.val)
        (revokeGuardRest site ee R)) mem aw rdata σ k C) :
    (∃ evm' σ' mem' aw' k' C' next dataPtr,
      SourceState s0 ee σ' evm' ∧ ee.perm = true ∧
      heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem mem' heap.toNat ∧
      MemoryPrefix (recordPadding mem heap.toNat) mem' heap.toNat ∧ dataPtr.toNat = heap.toNat+320 ∧
      AttestationMemoryView mem' heap dataPtr (storedAttestationRecord evm' r.uid) ∧
      heap.toNat+320 ≤ next ∧ dataPtr.toNat+32+32*(((storedAttestationRecord evm' r.uid).data.size+31)/32) ≤ next ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokeStoreCopyBody
        (.ok {contract := contract,locals := (revokeStoreCopyLocals L (easTimeWord ee) heap.toNat next
          (storedAttestationRecord evm' r.uid)),immutables := immStore v} evm') ∧
      RD fork (deployedRuntime v) ee g s0 site.kind.copyReturnPC
        (heap::revokeCopySaved site ee request idx r.uid R) mem' aw' rdata σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokeStoreCopyBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm revokeStoreCopyBody .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  let L1 := readTimeLocals L "__c1$allocation" "__c1" (easTimeWord ee) heap.toNat
  have htime := readTimeBlock_source (fork := fork) (cfg := config) (imms := immStore v) (evm := evm) "__c1$allocation" "__c1" hh
    (by decide) (by decide) (by decide)
  rw [hs.env] at htime
  have ha1 : L1.get? "attestation" = some (.storageRef (attestationER r.uid) attestationType) :=
    (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans ha
  have hr1 : L1.get? "request" = some r.struct :=
    (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hr
  have hh1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)) := heapResultLocals_heap _ _ _ _ _ _
  have ht1 : L1.get? "__c1" = some (.int (Int.ofNat (easTimeWord ee).toNat)) := heapResultLocals_result _ _ _ _ _ _ (by decide)
  cases hp : ee.perm with
  | false =>
    refine Or.inr (Or.inr ⟨?_,easRevokeStore_static v site (by omega) hp rd⟩)
    exact execBlock_append htime (ExecBlock.consStatic (revokeWriteTime_static ha1 ht1 (by rw [hs.env]; exact hp)))
  | true =>
    obtain ⟨aw1,k1,C1,rd1⟩ := easRevokeStore_ok v site (by omega) hp rd
    let f := revokeTimeField r.uid (easTimeWord ee)
    have hs1 : SourceState s0 ee (f.accounts σ ee) (f.apply evm) :=
      hs.readModifyWrite f.loc.slot (fun old => packedSliceWord old f.word (8*f.loc.offset.val) (8*f.loc.size.val))
    have hwrite := revokeWriteTime_source (fork := fork) (imms := immStore v) (evm := evm) ha1 ht1
    simp only [hs.env, hp, if_true] at hwrite
    have he : evalExprs? config {contract := contract,locals := L1,immutables := immStore v} (f.apply evm) revokeCopyArgs =
        .ok [wordBytes32Value r.uid,.int (Int.ofNat heap.toNat)] := by
      have hu : evalExpr? config {contract := contract,locals := L1,immutables := immStore v} (f.apply evm)
          (.field (.var "request") "uid") = .ok (wordBytes32Value r.uid) :=
        revokeRequestField_eval (cfg := config) (frame := {contract := contract,locals := L1,immutables := immStore v})
          (evm := f.apply evm) (r := r) hr1 "uid" (wordBytes32Value r.uid) rfl
      simp only [revokeCopyArgs,evalExprs?,hu,
        evalExpr?,hh1,EvalResult.ofOption,EvalResult.bind,bind,pure]
    have hret : (D_J (deployedRuntime v) 0).contains site.kind.copyReturnPC = true := by
      rw [easPatchedValidJumps v]
      cases site.kind <;> simp only [RevokeKind.copyReturnPC] <;> jump_dest
    have hc := copyStoredCallRun (retVar := "copied$allocation") v
      (by cases hk : site.kind <;> simp only [revokeCopySaved,hk,List.length_append,List.length_cons,List.length_nil] <;> omega)
      hs1 he hlo hfree hret rd1
    rcases hc with ⟨mem',aw',k',C',next,dp,hgrow,hcap,hprefix,hpadding,hdp,hview,hsource,hdata,hheap,hcall,rd'⟩ | ⟨hcall,hrev⟩
    · refine Or.inl ⟨f.apply evm,f.accounts σ ee,mem',aw',k',C',next,dp,hs1,rfl,hgrow,hcap,hprefix,hpadding,hdp,hview,hsource,hdata,hheap,?_,rd'⟩
      exact execBlock_append htime (ExecBlock.consNormal hwrite (heapResultBlock_ok hcall hh1 (by decide) (by decide) (by decide)))
    · exact Or.inr (Or.inl ⟨execBlock_append htime (ExecBlock.consNormal hwrite (ExecBlock.consRevert hcall)),hrev⟩)

end Benchmarks.EAS.EAS
