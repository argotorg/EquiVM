import Benchmarks.EAS.EAS.AttestFromSchema
import Benchmarks.EAS.EAS.AttestInitialControl
import Benchmarks.EAS.EAS.AttestSchemaSource
import Benchmarks.EAS.EAS.AttestSchemaMemory
import Benchmarks.EAS.EAS.GetSchemaCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestUIDSite (kind : AttestCallKind) (len record data attester available last ret result values : UInt256) : UIDSite :=
  match kind with
  | .single => .single len record available ret data values result attester
  | .many => .many available last ret record len data

def attestInitialT4 (kind : AttestCallKind) (records values : UInt256) : UInt256 :=
  match kind with
  | .single => records | .many => values

theorem attestSchemaRun {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw gasArg schema available ret data result uidPtr ptr : UInt256}
    {σ : AccountMap} {k C initial first : Nat} {rs : List AttestationRequestRecord}
    {attester : AccountAddress} {last : Bool} {R : List UInt256}
    (v : EASImmutables) (kind : AttestCallKind) (hstack : R.length+38 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hdata : AttestationRequestArrayMemoryView mem data rs uidPtr.toNat)
    (hresult : AttestResultMemoryView mem result uidPtr (List.replicate rs.length ⟨0⟩) ⟨0⟩ ptr.toNat)
    (huid : 224 ≤ uidPtr.toNat) (hrlow : 160 ≤ result.toNat)
    (hreg : kind = .many → memLoad (UInt256.ofNat 128) mem = result ∧
      memLoad (UInt256.ofNat 160) mem = UInt256.ofNat attester.val ∧ memLoad (UInt256.ofNat 192) mem = data)
    (hlast : kind = .single → last = true)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hh : ptr.toNat ≤ 2^64-1) (hin : ptr.toNat ≤ mem.size)
    (hpayload : mem.readWithPadding ptr.toNat 36 = getSchemaPayload schema)
    (hcd : ee.calldata.size < UInt256.size) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0
      (schemaCallPC (attestCallSchemaSite kind schema available last.toUInt256 ret (UInt256.ofNat rs.length)))
      (gasArg::UInt256.land (EVM.word v._schemaRegistry.val) solcAddrMask::ptr::⟨36⟩::ptr::⟨0⟩::
        schemaCallSaved (attestCallSchemaSite kind schema available last.toUInt256 ret (UInt256.ofNat rs.length)) ptr
          (attestCallSchemaSaved kind data (UInt256.ofNat attester.val) available ret result R)) mem aw rdata σ k C) :
    AttestReturnRun fork v ee g s0
      (attestInitialLocals (attestArgs schema rs attester available last initial) rs.length first ptr.toNat)
      evm (attestSchemaBody ++ attestFromSchemaBody) result uidPtr available rs.length ret R mem result.toNat ptr.toNat := by
  let L := attestInitialLocals (attestArgs schema rs attester available last initial) rs.length first ptr.toNat
  have hheap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat ptr.toNat)) := by
    simp (disch := decide) only [L,attestInitialLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
  have hschema : L.get? "schema" = some (wordBytes32Value schema) := by
    simp (disch := decide) only [L,attestInitialLocals,attestDeclaredLocals,allocateBlockLocals_get,attestArgs,store_get_ne,store_get_self]
  have hspan := hresult.uids.span
  have hcover := hresult.uids.covered
  have hrspan := hresult.span
  simp only [List.length_replicate] at hspan hcover
  have hcall := getSchemaCallRun (locals := L) (args := attestSchemaArgs) (retVar := "schemaRecord$allocation")
    v (attestCallSchemaSite kind schema available last.toUInt256 ret (UInt256.ofNat rs.length))
    (by simp only [attestSchemaArgs,evalExprs?,evalExpr?,hschema,hheap,EvalResult.ofOption,EvalResult.bind,bind,pure])
    (by cases kind <;> simp only [attestCallSchemaSaved,List.length_cons] <;> omega) hstate (by omega) hh hin hpayload rd
  rcases hcall with ⟨s,record,heap1,e1,σ1,m1,out,a1,k1,C1,hs1,hlo1,hhi1,hrecordLow,hrecordHigh,hp1,hsv,hfree1,hsrc1,r1⟩ | ⟨hsrc,hrev⟩
  · let values := UInt256.ofNat (allocateNext heap1 (32+352*rs.length))
    let site := attestUIDSite kind (UInt256.ofNat rs.length) record data (UInt256.ofNat attester.val)
      available last.toUInt256 ret result values
    have hresult0 : recordResultPtr site mem = result := by
      cases kind with
      | single => rfl
      | many => exact (hreg rfl).1
    have hrequest0 : attestRequestArrayPtr site mem = data := by
      cases kind with
      | single => rfl
      | many => exact (hreg rfl).2.2
    have hatter : recordCreateAttester site mem = UInt256.ofNat attester.val := by
      cases kind with
      | single => exact solcAddrMask_clean (word_val_addr_canonical attester)
      | many =>
        change UInt256.land (memLoad (UInt256.ofNat 160) mem) solcAddrMask = _
        rw [(hreg rfl).2.1]
        exact solcAddrMask_clean (word_val_addr_canonical attester)
    have hschema1 : requestSchemaPtr site = record := by cases kind <;> rfl
    have hm : AttestSetupMemory m1 site uidPtr rs s attester heap1 :=
      attestSetupMemory_of_schema hp1 ptr.val.isLt huid (by rw [hrequest0]; exact hdata)
        (by rw [hresult0]; exact hresult) hatter hzero (by rw [hschema1]; exact hsv)
        (by rw [hschema1]; omega) (by rw [hschema1]; exact hrecordHigh) hlo1
    have hresult1 : recordResultPtr site m1 = result :=
      (recordResultPtr_preserve site hp1 (by omega) (by omega)).trans hresult0
    have hnorm : (UInt256.ofNat heap1).toNat = heap1 := ulit_toNat' _ (by change heap1 < 2^256; omega)
    have hlen : attestLoopLength site = UInt256.ofNat rs.length := by cases kind <;> rfl
    have hval : recordValuesPtr site (attestInitialT4 kind (UInt256.ofNat heap1) values) =
        UInt256.ofNat (allocateNext (UInt256.ofNat heap1).toNat (32+352*rs.length)) := by
      rw [hnorm]
      cases kind <;> rfl
    have hafter : RD fork (deployedRuntime v) ee g s0 (schemaDonePC (attestSchemaSite site schema))
        (schemaDoneStack v (attestSchemaSite site schema) (requestSchemaPtr site) (attestSchemaSaved site R)) m1 a1 out σ1 k1 C1 := by
      cases kind <;> exact r1
    have hrun := attestFromSchemaRun (heap := UInt256.ofNat heap1) (t3 := UInt256.ofNat heap1)
      (t4 := attestInitialT4 kind (UInt256.ofNat heap1) values) v site hstack hs1
      (by simpa only [hnorm] using attestSchemaLocals_view schema rs attester available last initial first ptr.toNat s heap1)
      (by simpa only [hnorm] using hm) hlen (by rw [hnorm]; exact hhi1) hfree1 hcd
      (by cases kind <;> rfl) hval (by cases kind <;> rfl)
      (by cases kind with
          | single => rw [hlast rfl]; rfl
          | many => rfl)
      (by rw [hresult1]; exact hrlow) (by cases kind <;> exact hret) hafter
    have hpc : attestReturnPC site = ret := by cases kind <;> rfl
    rw [hresult1,hpc,hnorm] at hrun
    exact hrun.prepend (attestSchemaSource hheap hsrc1) (hp1.mono (by omega)) (le_refl _) hlo1
  · exact AttestReturnRun.of_revert_prefix (ExecBlock.consRevert hsrc) hrev

end Benchmarks.EAS.EAS
