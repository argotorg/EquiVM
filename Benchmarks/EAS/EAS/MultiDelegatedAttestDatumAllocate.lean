import Benchmarks.EAS.EAS.MultiDelegatedAttestDatumSource
import Benchmarks.EAS.EAS.CopyRequestCall
import Benchmarks.EAS.EAS.MultiAttestUpdateSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedAttestDatumAllocate : Body := allocateBlock (.intLit 128) ++ multiDelegatedAttestDatumCopy ++ allocateBlock (.intLit 96)
def multiDelegatedAttestDatumAllocatedLocals (L : Store) (heap : Nat) (r : AttestationRequestRecord) : Store :=
  allocateBlockLocals (multiAttestCopyLocals (allocateBlockLocals L (heap+128)) (copyRequestNext (heap+128) r.data.size))
    (copyRequestNext (heap+128) r.data.size+96)

theorem multiDelegatedAttestDatumAllocateSource {L imms : Store} {evm : EVM.State} {r : AttestationRequestRecord} {heap : Nat}
    (hd : L.get? "datum"=some r.tuple) (hf : L.get? "$EAS.freeMemory"=some (.int (Int.ofNat heap)))
    (hh : heap≤2^64-1) :
    if heap+128≤2^64-1 ∧ copyRequestValid (heap+128) r.data.size ∧ copyRequestNext (heap+128) r.data.size+96≤2^64-1 then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestDatumAllocate
        (.ok {contract := contract,locals := multiDelegatedAttestDatumAllocatedLocals L heap r,immutables := imms} evm)
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestDatumAllocate .reverted := by
  simp only [multiDelegatedAttestDatumAllocate,List.append_assoc]
  have hn128 : allocateNext heap 128=heap+128 := allocateNext_128 hh
  by_cases ha : heap+128≤2^64-1
  · let L1 := allocateBlockLocals L (heap+128)
    have hsol1 : ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm (allocateBlock (.intLit 128))
        (.ok {contract := contract,locals := L1,immutables := imms} evm) := by
      have h := allocateBlock_ok (fork := fork) (cfg := config) (imms := imms) (evm := evm) (size := .intLit 128) (by simp only [evalExpr?,pure];rfl) hf
        (show allocateNext heap 128≤2^64-1 ∧ heap≤allocateNext heap 128 by rw [hn128];exact ⟨ha,by omega⟩)
      simpa only [hn128] using h
    have hd1 : L1.get? "datum"=some r.tuple := (allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hd
    have hf1 : L1.get? "$EAS.freeMemory"=some (.int (Int.ofNat (heap+128))) := by
      simp only [L1,allocateBlockLocals,unpackHeapLocals,store_get_self]
    have he : evalExprs? config {contract := contract,locals := L1,immutables := imms} evm [.var "datum",.var "$EAS.freeMemory"]=
        .ok [r.tuple,.int (Int.ofNat (heap+128))] := by
      simp only [evalExprs?,evalExpr?,hd1,hf1,EvalResult.ofOption,bind,EvalResult.bind,pure]
    have hcopy := copyRequestCall_branches (fork := fork) (retVar := "allocation$allocation") he
    by_cases hc : copyRequestValid (heap+128) r.data.size
    · let next := copyRequestNext (heap+128) r.data.size
      let L2 := multiAttestCopyLocals L1 next
      have hsol2 : ExecBlock fork config {contract := contract,locals := L1,immutables := imms} evm multiDelegatedAttestDatumCopy
          (.ok {contract := contract,locals := L2,immutables := imms} evm) :=
        heapResultBlock_ok (result := "allocation") (cursor := "$EAS.freeMemory") (hcopy.1 hc) hf1 (by decide) (by decide) (by decide)
      have hf2 : L2.get? "$EAS.freeMemory"=some (.int (Int.ofNat next)) := heapResultLocals_heap ..
      have hn96 : allocateNext next 96=next+96 := fixedAllocation_next .bytes96 hc.2.2.1
      by_cases hs : next+96≤2^64-1
      · rw [if_pos ⟨ha,hc,hs⟩]
        have hsol3 := allocateBlock_ok (fork := fork) (cfg := config) (imms := imms) (evm := evm) (size := .intLit 96) (by simp only [evalExpr?,pure];rfl) hf2
          (show allocateNext next 96≤2^64-1 ∧ next≤allocateNext next 96 by rw [hn96];exact ⟨hs,by omega⟩)
        rw [hn96] at hsol3
        exact execBlock_append hsol1 (execBlock_append hsol2 hsol3)
      · rw [if_neg (fun h => hs h.2.2)]
        have hsol3 := allocateBlock_revert (fork := fork) (cfg := config) (imms := imms) (evm := evm) (size := .intLit 96) (by simp only [evalExpr?,pure];rfl) hf2
          (show ¬(allocateNext next 96≤2^64-1 ∧ next≤allocateNext next 96) by rw [hn96];exact fun h => hs h.1)
        exact execBlock_append hsol1 (execBlock_append hsol2 hsol3)
    · rw [if_neg (fun h => hc h.2.1)]
      exact execBlock_append hsol1 (execBlock_append_term
        (s2 := allocateBlock (.intLit 96)) (ExecBlock.consRevert (stmts := (multiDelegatedAttestDatumCopy.drop 1)) (hcopy.2 hc))
        (by intros;exact nofun))
  · rw [if_neg (fun h => ha h.1)]
    have hsol1 := allocateBlock_revert (fork := fork) (cfg := config) (imms := imms) (evm := evm) (size := .intLit 128) (by simp only [evalExpr?,pure];rfl) hf
      (show ¬(allocateNext heap 128≤2^64-1 ∧ heap≤allocateNext heap 128) by rw [hn128];exact fun h => ha h.1)
    exact execBlock_append_term (s2 := multiDelegatedAttestDatumCopy ++ allocateBlock (.intLit 96)) hsol1 (by intros;exact nofun)

end Benchmarks.EAS.EAS
