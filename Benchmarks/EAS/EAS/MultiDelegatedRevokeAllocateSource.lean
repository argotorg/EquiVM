import Benchmarks.EAS.EAS.MultiDelegatedRevokeSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedRevokeAllocatedLocals (L : Store) (r : DelegatedRevocationBatch) (heap : Nat) : Store :=
  allocateBlockLocals (allocateBlockLocals (allocateBlockLocals L (heap+128)) (heap+160+96*r.data.length))
    (heap+192+96*r.data.length+128*r.signatures.length)

theorem multiDelegatedRevokeAllocateSource {L imms : Store} {evm : EVM.State} {r : DelegatedRevocationBatch} {heap : Nat}
    (hd : L.get? "data" = some (.array (r.data.map RevocationRequestRecord.tuple)))
    (hs : L.get? "signatures" = some (.array (r.signatures.map SignatureRecord.tuple)))
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hh : heap ≤ 2^64-1) (hld : r.data.length ≤ 2^64-1) (hls : r.signatures.length ≤ 2^64-1) :
    if heap+192+96*r.data.length+128*r.signatures.length ≤ 2^64-1 then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokeAllocate
        (.ok {contract := contract,locals := multiDelegatedRevokeAllocatedLocals L r heap,immutables := imms} evm)
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokeAllocate .reverted := by
  have hn0 := allocateNext_128 hh
  have he0 : evalExpr? config {contract := contract,locals := L,immutables := imms} evm (.intLit 128) =
      .ok (.int (Int.ofNat 128)) := by simp only [evalExpr?,pure]; rfl
  by_cases h0 : heap+128 ≤ 2^64-1
  · have ha0 := allocateBlock_ok (fork := fork) he0 hf (by rw [hn0]; exact ⟨h0,by omega⟩)
    rw [hn0] at ha0
    let L1 := allocateBlockLocals L (heap+128)
    have hd1 : L1.get? "data" = some (.array (r.data.map RevocationRequestRecord.tuple)) :=
      (allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hd
    have hf1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat (heap+128))) := by
      simp only [L1,allocateBlockLocals,unpackHeapLocals,store_get_self]
    have ha1 := arrayAllocateExprSource (fork := fork) (cfg := config) (L := L1) (imms := imms) (evm := evm)
      (evalLocalArrayLength hd1) hf1 96
    have hn1 : allocateNext (heap+128) (32+96*r.data.length) = heap+160+96*r.data.length := by
      rw [allocateNext_small h0 (by omega)]
      omega
    simp only [List.length_map,if_pos hld,hn1] at ha1
    by_cases h1 : heap+160+96*r.data.length ≤ 2^64-1
    · rw [if_pos ⟨h1,by omega⟩] at ha1
      let L2 := allocateBlockLocals L1 (heap+160+96*r.data.length)
      have hs2 : L2.get? "signatures" = some (.array (r.signatures.map SignatureRecord.tuple)) := by
        simpa (disch := decide) only [L2,L1,allocateBlockLocals_get] using hs
      have hf2 : L2.get? "$EAS.freeMemory" = some (.int (Int.ofNat (heap+160+96*r.data.length))) := by
        simp only [L2,allocateBlockLocals,unpackHeapLocals,store_get_self]
      have ha2 := arrayAllocateExprSource (fork := fork) (cfg := config) (L := L2) (imms := imms) (evm := evm)
        (evalLocalArrayLength hs2) hf2 128
      have hn2 : allocateNext (heap+160+96*r.data.length) (32+128*r.signatures.length) =
          heap+192+96*r.data.length+128*r.signatures.length := by
        rw [allocateNext_small h1 (by omega)]
        omega
      simp only [List.length_map,if_pos hls,hn2] at ha2
      by_cases h2 : heap+192+96*r.data.length+128*r.signatures.length ≤ 2^64-1
      · rw [if_pos h2]
        rw [if_pos ⟨h2,by omega⟩] at ha2
        exact execBlock_append (execBlock_append ha0 ha1) ha2
      · rw [if_neg h2]
        rw [if_neg (fun h => h2 h.1)] at ha2
        exact execBlock_append (execBlock_append ha0 ha1) ha2
    · rw [if_neg (fun h => h1 h.1)] at ha1
      rw [if_neg (by omega : ¬ heap+192+96*r.data.length+128*r.signatures.length ≤ 2^64-1)]
      simpa only [multiDelegatedRevokeAllocate,List.append_assoc] using execBlock_append ha0 (execBlock_append_term
        (s2 := arrayAllocateExprBlock (.arrayLength .localVar {base := "signatures"}) 128) ha1 (by intros; exact nofun))
  · rw [if_neg (by omega : ¬ heap+192+96*r.data.length+128*r.signatures.length ≤ 2^64-1)]
    simpa only [multiDelegatedRevokeAllocate,List.append_assoc] using execBlock_append_term
      (s2 := arrayAllocateExprBlock (.arrayLength .localVar {base := "data"}) 96 ++
        arrayAllocateExprBlock (.arrayLength .localVar {base := "signatures"}) 128)
      (allocateBlock_revert he0 hf (by rw [hn0]; exact fun h => h0 h.1)) (by intros; exact nofun)

end Benchmarks.EAS.EAS
