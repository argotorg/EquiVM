import Benchmarks.EAS.EAS.RevokeFromSchema
import Benchmarks.EAS.EAS.RevocationRequestMemory
import Benchmarks.EAS.EAS.GetSchemaCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem revoke_body_split : revokeFunction.body = attestSchemaBody ++ revokeFromSchemaBody := by
  rw [revoke_body]
  simp only [revokeFromSchemaBody,List.append_assoc]

theorem revokeSchemaRun {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw gasArg schema data available ret ptr : UInt256}
    {σ : AccountMap} {k C : Nat} {rs : List RevocationRequestRecord} {revoker : AccountAddress} {last : Bool} {R : List UInt256}
    (v : EASImmutables) (kind : RevokeKind) (hstack : R.length+37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hdata : RevocationRequestArrayMemoryView mem data rs ptr.toNat)
    (hh : ptr.toNat ≤ 2^64-1) (hin : ptr.toNat ≤ mem.size) (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hlast : kind = .single → last = true) (hpayload : mem.readWithPadding ptr.toNat 36 = getSchemaPayload schema)
    (hcd : ee.calldata.size < UInt256.size) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (schemaCallPC kind.schemaSite)
      (gasArg::UInt256.land (EVM.word v._schemaRegistry.val) solcAddrMask::ptr::⟨36⟩::ptr::⟨0⟩::
        schemaCallSaved kind.schemaSite ptr (revokeSchemaSaved kind schema data (UInt256.ofNat revoker.val) available last.toUInt256 ret R))
      mem aw rdata σ k C) :
    ∃ used : UInt256, HeapReturnPostOrStatic fork (used.toNat ≤ available.toNat)
      config (deployedRuntime v) ee g s0
      {contract := contract,locals := revokeArgs schema rs revoker available last ptr.toNat,immutables := immStore v}
      evm revokeFunction.body (.int (Int.ofNat used.toNat)) ret (used::R) mem ptr.toNat := by
  let L := revokeArgs schema rs revoker available last ptr.toNat
  have hheap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat ptr.toNat)) := by
    simp (disch := decide) only [L,revokeArgs,store_get_ne,store_get_self]
  have hschema : L.get? "schema" = some (wordBytes32Value schema) := store_get_self _ _ _
  have hdlo := hdata.low
  have hdspan := hdata.span
  have hdcovered := hdata.covered
  have hcall := getSchemaCallRun (locals := L) (args := attestSchemaArgs) (retVar := "schemaRecord$allocation")
    v kind.schemaSite
    (by simp only [attestSchemaArgs,evalExprs?,evalExpr?,hschema,hheap,EvalResult.ofOption,EvalResult.bind,bind,pure])
    (by cases kind <;> simp only [revokeSchemaSaved,List.length_cons] <;> omega) hs (by omega) hh hin hpayload rd
  rw [revoke_body_split]
  rcases hcall with ⟨s,record,heap1,e1,σ1,m1,out,a1,k1,C1,hs1,hlo1,hhi1,hrecordLow,hrecordHigh,hp1,hsv,hfree1,hsrc1,r1⟩ | ⟨hsrc,hrev⟩
  · let site : RevokeSite := {
      kind := kind,schema := schema,data := data,revoker := revoker,available := available,
      last := last,ret := ret,schemaPtr := record,records := UInt256.ofNat heap1,
      values := UInt256.ofNat (allocateNext heap1 (32+352*rs.length)),length := rs.length}
    have hn : (UInt256.ofNat heap1).toNat = heap1 := ulit_toNat' _ (by change heap1 < 2^256; omega)
    have hz : memLoad (UInt256.ofNat 96) m1 = ⟨0⟩ :=
      (memLoad_of_prefix hp1 _ (by decide) (by change 128 ≤ ptr.toNat; omega) (by change 128 ≤ mem.size; omega)).trans hzero
    have hm : RevokeSetupMemory m1 site rs s :=
      ⟨(hdata.preserve hp1 ptr.val.isLt).mono hrecordLow,hsv,by change record.toNat+128 ≤ (UInt256.ofNat heap1).toNat; rw [hn]; exact hrecordHigh,hz⟩
    have hf : RevokeSetupLocals ((attestSchemaLocals L s heap1).insert "length" (.int (Int.ofNat rs.length)))
        site rs s site.records.toNat := by
      simpa only [site,hn,L] using revokeSetupLocals_of_schema site rs s ptr.toNat
    obtain ⟨used,hafter⟩ := revokeFromSchemaRun v site hstack hs1 hf hm rfl (by change (UInt256.ofNat heap1).toNat ≤ _; rw [hn]; exact hhi1)
      hfree1 hcd (by change _ = UInt256.ofNat (allocateNext (UInt256.ofNat heap1).toNat _); rw [hn]) hlast hret r1
    change HeapReturnPostOrStatic fork (used.toNat ≤ available.toNat) config (deployedRuntime v) ee g s0
      {contract := contract,locals := attestSchemaLocals L s heap1,immutables := immStore v} e1
      revokeFromSchemaBody (.int (Int.ofNat used.toNat)) ret (used::R) m1 (UInt256.ofNat heap1).toNat at hafter
    rw [hn] at hafter
    exact ⟨used,hafter.prepend (attestSchemaSource hheap hsrc1) hp1 hlo1⟩
  · exact ⟨⟨0⟩,HeapReturnPostOrStatic.of_revert_prefix (ExecBlock.consRevert hsrc) hrev⟩

end Benchmarks.EAS.EAS
