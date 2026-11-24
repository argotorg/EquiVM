import Benchmarks.EAS.EAS.AttestSchemaRun
import Benchmarks.EAS.EAS.AttestInitialViews
import Benchmarks.EAS.EAS.AttestAllocationRequests

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem attestRun {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw schema data available ret heap : UInt256}
    {σ : AccountMap} {k C : Nat} {rs : List AttestationRequestRecord}
    {attester : AccountAddress} {last : Bool} {R : List UInt256}
    (v : EASImmutables) (kind : AttestCallKind) (hstack : R.length+38 ≤ 1024) (hstate : SourceState s0 ee σ evm)
    (hdata : AttestationRequestArrayRegion mem data rs 224 heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (hlast : kind = .single → last = true)
    (hcd : ee.calldata.size < UInt256.size) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 kind.entryPC
      (attestEntryStack kind schema data (UInt256.ofNat attester.val) available last.toUInt256 ret R) mem aw rdata σ k C) :
    AttestReturnRun fork v ee g s0 (attestArgs schema rs attester available last heap.toNat) evm attestFunction.body
      (UInt256.ofNat (allocateNext heap.toNat 64)) (UInt256.ofNat (allocateNext heap.toNat 128)) available rs.length ret R
      (attestAllocationMemory kind mem heap data (UInt256.ofNat attester.val)) heap.toNat heap.toNat := by
  rw [attest_body,List.append_assoc]
  have hlo := hdata.arrayLow
  have hspan := hdata.view.span
  have hcovered := hdata.view.covered
  have hl : rs.length ≤ 2^64-1 := by omega
  have hlb : rs.length < UInt256.size := by change _ < 2^256; omega
  have hsrc := attestInitialSource (fork := fork) (imms := immStore v) (evm := evm)
    (show (attestArgs schema rs attester available last heap.toNat).get? "data" =
      some (.array (rs.map AttestationRequestRecord.tuple)) from by
        simp (disch := decide) only [attestArgs,store_get_ne,store_get_self])
    (show (attestArgs schema rs attester available last heap.toNat).get? "$EAS.freeMemory" =
      some (.int (Int.ofNat heap.toNat)) from by
        simp (disch := decide) only [attestArgs,store_get_ne,store_get_self])
  have hr := easAttestInitial v kind (by omega) hlo (by omega) (by omega) hh hheap hzero
    hdata.view.length hlb hcd rd
  dsimp only at hsrc hr
  by_cases hg : allocateNext heap.toNat 128 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 128
  · rw [if_pos hg,if_pos hl] at hsrc hr
    by_cases hn : allocateNext (allocateNext heap.toNat 128) (32+32*rs.length) ≤ 2^64-1 ∧
        allocateNext heap.toNat 128 ≤ allocateNext (allocateNext heap.toNat 128) (32+32*rs.length)
    · rw [if_pos hn] at hsrc hr
      obtain ⟨gasArg,a1,k1,C1,r1⟩ := hr
      obtain ⟨hp,hrequests,hresult,huid,hrlow,hrge,hregs,hzero1,hsize,hpayload⟩ :=
        attestInitialMemory_view kind mem ee.calldata heap data schema attester rs hlo (by omega) (by omega)
          hh hheap hzero hg.1 hl (attestAllocationMemory_requests kind (UInt256.ofNat attester.val) hdata hh hg.1).view
      have hptr : (UInt256.ofNat (allocateNext (allocateNext heap.toNat 128) (32+32*rs.length))).toNat =
          allocateNext (allocateNext heap.toNat 128) (32+32*rs.length) := ulit_toNat' _ (by change _ < 2^256; omega)
      have hc := attestSchemaRun (initial := heap.toNat) (first := allocateNext heap.toNat 128)
        v kind hstack hstate hrequests (by rw [hptr]; exact hresult) huid hrlow hregs hlast hzero1
        (by rw [hptr]; exact hn.1) (by rw [hptr]; exact hsize) (by rw [hptr]; exact hpayload) hcd hret r1
      rw [hptr] at hc
      exact hc.prepend hsrc hp hrge (le_trans hg.2 hn.2)
    · rw [if_neg hn] at hsrc hr
      exact AttestReturnRun.of_revert_prefix hsrc hr
  · rw [if_neg hg] at hsrc hr
    exact AttestReturnRun.of_revert_prefix hsrc hr

end Benchmarks.EAS.EAS
