import Benchmarks.EAS.EAS.MergeUIDOuter
import Benchmarks.EAS.EAS.MergeUIDAllocate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: uniform component lengths bound a flattened list.
theorem flattenLength_le {α : Type} (groups : List (List α)) (bound : Nat)
    (h : ∀ xs ∈ groups, xs.length ≤ bound) : groups.flatten.length ≤ groups.length*bound := by
  induction groups with
  | nil => simp only [List.flatten_nil,List.length_nil,Nat.zero_mul,le_refl]
  | cons xs rest ih =>
    have hx := h xs (List.mem_cons_self ..)
    have hr := ih (fun ys hy => h ys (List.mem_cons_of_mem _ hy))
    simp only [List.flatten_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem WordArrayArrayMemoryView.flatten_fit {mem : ByteArray} {ptr : UInt256} {groups : List (List UInt256)} {limit : Nat}
    (h : WordArrayArrayMemoryView mem ptr groups limit) (hb : limit ≤ 2^64-1) : groups.flatten.length < UInt256.size := by
  have hlen : groups.length ≤ 2^64-1 := by have := h.span; omega
  have ht := flattenLength_le groups (2^64-1) (by
    intro xs hx
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨p,_,hv⟩ := h.arrays i hi
    have hs := hv.span
    rw [he] at hs
    omega)
  have hm := Nat.mul_le_mul_right (2^64-1) hlen
  change _ < 2^256
  omega

theorem mergeUIDRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lists heap ret : UInt256} {groups : List (List UInt256)} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+18 ≤ 1024) (hh : heap.toNat ≤ 2^64-1) (hlo : 96 ≤ heap.toNat)
    (hd : L.get? "uidLists" = some (.array (groups.map wordListValue)))
    (hn : L.get? "uidsCount" = some (.int (Int.ofNat groups.flatten.length)))
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hm : WordArrayArrayMemoryView mem lists groups heap.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap) (hsize : ee.calldata.size < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨11975⟩
      (lists::UInt256.ofNat groups.flatten.length::ret::R) mem aw rdata σ k C) :
    let next := allocateNext heap.toNat (32+32*groups.flatten.length)
    (∃ L' mem' aw' k' C' words, words.length = groups.flatten.length ∧ next ≤ 2^64-1 ∧
      MemoryPrefix mem mem' heap.toNat ∧ WordArrayMemoryView mem' heap words next ∧
      memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat next ∧
      ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm mergeUIDFunction.body
        (.returned {contract := contract,locals := L',immutables := immStore v} evm (some [wordListValue words,.int (Int.ofNat next)])) ∧
      RD fork (deployedRuntime v) ee g s0 ret (heap::R) mem' aw' rdata σ k' C') ∨
    (ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm mergeUIDFunction.body .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  dsimp only
  let n := groups.flatten.length
  let next := allocateNext heap.toNat (32+32*n)
  have hlen : (UInt256.ofNat n).toNat = n := ulit_toNat' _ (hm.flatten_fit hh)
  have hhead := easMergeUIDAllocate v (by omega) hh hfree hsize rd
  rw [hlen] at hhead
  have hprefix := mergeUIDPrefixSource (fork := fork) (imms := immStore v) (evm := evm) hd hn hf
  dsimp only at hprefix
  by_cases hv : n ≤ 2^64-1 ∧ (next ≤ 2^64-1 ∧ heap.toNat ≤ next)
  · obtain ⟨a1,k1,C1,r1⟩ := hhead.1 hv
    obtain ⟨hs0,hf0⟩ := hprefix.1 hv
    have hnword : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by have := hv.2.1; change _ < 2^256; omega)
    have hm0 := mergeUIDAllocateMemory mem ee.calldata heap n hlo hh hv.1
    let m1 := wordArrayAllocationMemory mem ee.calldata heap n
    have hs1 : WordArrayArrayMemoryView m1 lists groups heap.toNat := hm.preserve hm0.1 heap.val.isLt
    have hf1 : MergeUIDLocals (mergeUIDInitialLocals L n next) groups (List.replicate n ⟨0⟩) (UInt256.ofNat next).toNat 0 0 := by
      rw [hnword]; exact hf0
    have hm1 : WordArrayPrefixView m1 heap (List.replicate n ⟨0⟩) 0 (UInt256.ofNat next).toNat := by
      rw [hnword]; exact hm0.2.1
    obtain ⟨L2,m2,a2,k2,C2,words,hwords,hpre,hf2,hm2,hfree2,hsol2,r2⟩ := mergeUIDOuterLoop v hstack
      (heap := UInt256.ofNat next) (by rw [hnword]; exact hv.2.1) hret groups.length (by omega)
      (by simp only [List.drop_zero,List.length_replicate,Nat.zero_add]; rfl) hf1 hm1 hs1 hm0.2.2 r1
    rw [hnword] at hf2 hm2
    simp only [List.length_replicate] at hwords
    have hreturn : ExecBlock fork config {contract := contract,locals := L2,immutables := immStore v} evm mergeUIDReturn
        (.returned {contract := contract,locals := L2,immutables := immStore v} evm (some [wordListValue words,.int (Int.ofNat next)])) := by
      apply ExecBlock.consReturn
      apply ExecStmt.return
      simp only [evalExprs?,evalExpr?,hf2.words,hf2.heap,EvalResult.ofOption,EvalResult.bind,bind,pure]
    have hsol : ExecFuncBody fork config {contract := contract,locals := L,immutables := immStore v} evm mergeUIDFunction.body
        (.returned {contract := contract,locals := L2,immutables := immStore v} evm (some [wordListValue words,.int (Int.ofNat next)])) := by
      rw [mergeUID_body]
      exact ExecFuncBody.execBlockRet (execBlock_append hs0 (ExecBlock.consNormal hsol2 hreturn))
    exact Or.inl ⟨L2,m2,a2,k2,C2,words,hwords,hv.2.1,hm0.1.trans hpre,hm2,hfree2,hsol,r2⟩
  · refine Or.inr ⟨?_,hhead.2 hv⟩
    rw [mergeUID_body]
    exact ExecFuncBody.execBlockRevert (execBlock_append_term (hprefix.2 hv) (by intros; exact nofun))

end Benchmarks.EAS.EAS
