import Benchmarks.EAS.EAS.MultiRevokeUpdateSource
import Benchmarks.EAS.EAS.MultiRevokeUpdate
import Benchmarks.EAS.EAS.MultiAttestFacts

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem multiRevokeCallUpdateRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C n i : Nat}
    {schema data base available heap : UInt256} {requests : List Value} {rs : List RevocationRequestRecord} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+48 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hf : MultiRevokeLocals L requests available heap.toNat i) (hh : heap.toNat ≤ 2^64-1)
    (hi : i<n) (hn : n<UInt256.size)
    (hrow : L.get? "multiRequest" = some (multiRevocationTuple schema rs))
    (hlast : L.get? "last" = some (.bool (decide (i=n-1))))
    (hd : RevocationRequestArrayMemoryView mem data rs heap.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hsize : ee.calldata.size < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨12743⟩
      (schema::data::UInt256.ofNat ee.source.val::available::multiAttestLastWord n i::multiRevokeSaved n i base available R)
      mem aw rdata σ k C) :
    (∃ (L' : Store) (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256)
        (k' C' next : Nat) (used : UInt256),
      SourceState s0 ee σ' evm' ∧ heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧
      MultiRevokeLocals L' requests (UInt256.sub available used) next (i+1) ∧
      128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiRevokeCall++multiRevokeUpdate)
        (.ok {contract := contract,locals := L',immutables := immStore v} evm') ∧
      RD fork (deployedRuntime v) ee g s0 ⟨3396⟩
        (multiRevokeLoopStack n (i+1) base (UInt256.sub available used) R) mem' aw' out σ' k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiRevokeCall++multiRevokeUpdate) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm (multiRevokeCall++multiRevokeUpdate) .staticViolation ∧
      RDstatic fork (deployedRuntime v) g s0) := by
  have he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm multiAttestCallArgs =
      .ok [wordBytes32Value schema,.array (rs.map RevocationRequestRecord.tuple),.address ee.source,
        .int (Int.ofNat available.toNat),.bool (decide (i=n-1)),.int (Int.ofNat heap.toNat)] := by
    simp only [multiAttestCallArgs,evalExprs?,evalExpr?,hrow,hf.available,hlast,hf.heap,multiRevocationTuple,
      EvalResult.ofOption,bind,EvalResult.bind,pure,envValue,hstate.env]
    rfl
  obtain ⟨used,hr⟩ := revokeCallRun (retVar := "__c0$allocation") (ret := ⟨1710⟩)
    (R := available::⟨3537⟩::⟨1⟩::UInt256.ofNat n::UInt256.ofNat i::base::(UInt256.ofNat n-⟨1⟩)::R)
    v .many (by simp only [List.length_cons]; omega) hstate he hd hh hfree hzero (by intro h; cases h)
    hsize (by rw [easPatchedValidJumps v]; jump_dest)
    (by simpa only [revokeEntryStack,RevokeKind.entryPC,multiAttestLastWord_eq hi hn] using rd)
  rcases hr with (⟨hu,hr⟩ | ⟨hcall,hrev⟩) | ⟨hcall,hstatic⟩
  · rcases hr with ⟨e1,σ1,m1,out,a1,k1,C1,next,hs1,hlo,hb,hp,hfree1,hcall,r1⟩ | ⟨hcall,hrev⟩
    · let L1 := multiRevokeCallLocals L used next
      let L2 := multiRevokeNextLocals L1 available used i
      have hf1 : MultiRevokeLocals L1 requests available next i := hf.called used next
      have hres : L1.get? "__c0" = some (.int (Int.ofNat used.toNat)) := heapResultLocals_result _ _ _ _ _ _ (by decide)
      have hsol1 : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm multiRevokeCall
          (.ok {contract := contract,locals := L1,immutables := immStore v} e1) :=
        heapResultBlock_ok hcall hf.heap (by decide) (by decide) (by decide)
      have hsol2 := multiRevokeUpdateSource (fork := fork) (evm := e1) (imms := immStore v) hf1 hres (by omega) hu
      obtain ⟨a2,k2,C2,r2⟩ := easMultiRevokeUpdate v (by omega) hu r1
      have hheaplo : 128 ≤ heap.toNat := by have := hd.low; have := hd.span; omega
      have hmemlo : 128 ≤ mem.size := by have := hd.low; have := hd.covered; omega
      have hz : memLoad (UInt256.ofNat 96) m1 = ⟨0⟩ :=
        (memLoad_of_prefix hp (UInt256.ofNat 96) (by decide) hheaplo hmemlo).trans hzero
      exact Or.inl ⟨L2,e1,σ1,m1,out,a2,k2,C2,next,used,hs1,hlo,hb,hf1.next used,
        le_trans hmemlo hp.size,hfree1,hz,execBlock_append hsol1 hsol2,r2⟩
    · exact Or.inr (Or.inl ⟨execBlock_append_term (ExecBlock.consRevert hcall) (by intros; exact nofun),hrev⟩)
  · exact Or.inr (Or.inl ⟨execBlock_append_term (ExecBlock.consRevert hcall) (by intros; exact nofun),hrev⟩)
  · exact Or.inr (Or.inr ⟨execBlock_append_term (ExecBlock.consStatic hcall) (by intros; exact nofun),hstatic⟩)

end Benchmarks.EAS.EAS
