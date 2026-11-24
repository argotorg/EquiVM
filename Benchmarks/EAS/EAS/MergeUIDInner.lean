import Benchmarks.EAS.EAS.MergeUIDSource
import Benchmarks.EAS.EAS.MergeUIDControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem mergeUIDInnerLoop {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lists out src heap ret : UInt256} {i j c : Nat} {groups : List (List UInt256)} {words values : List UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+18 ≤ 1024) (hh : heap.toNat ≤ 2^64-1)
    (n : Nat) (hj : j+n = values.length) (hspace : c+n ≤ words.length)
    (hf : MergeUIDInnerLocals L groups words values heap.toNat c i j)
    (hm : WordArrayPrefixView mem out words c heap.toNat) (hs : WordArrayMemoryView mem src values out.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨12017⟩
      (UInt256.ofNat j::lists::out::ret::UInt256.ofNat i::src::UInt256.ofNat c::R) mem aw rdata σ k C) :
    ∃ L' mem' aw' k' C' words', words'.length = words.length ∧ MemoryPrefix mem mem' out.toNat ∧
      MergeUIDInnerLocals L' groups words' values heap.toNat (c+n) i values.length ∧
      WordArrayPrefixView mem' out words' (c+n) heap.toNat ∧ memLoad (UInt256.ofNat 64) mem' = heap ∧
      ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm
        (.while (localArrayGuard "j" "currentUids") mergeUIDInnerIteration)
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      RD fork (deployedRuntime v) ee g s0 ⟨11990⟩
        (out::UInt256.ofNat (c+n)::UInt256.ofNat (i+1)::lists::ret::R) mem' aw' rdata σ k' C' := by
  induction n generalizing L mem aw k C j c words with
  | zero =>
    have hj0 : j = values.length := by omega
    subst j
    obtain ⟨a1,k1,C1,r1⟩ := easMergeUIDInnerDone v (by omega) hs.length rd
    have hguard : evalExpr? config {contract := contract,locals := L,immutables := immStore v} evm (localArrayGuard "j" "currentUids") = .ok (.bool false) := by
      simpa only [List.length_map,decide_eq_false (Nat.lt_irrefl values.length)] using
        evalLocalArrayGuard (cfg := config) (evm := evm) (frame := {contract := contract,locals := L,immutables := immStore v}) hf.index hf.current
    exact ⟨L,mem,a1,k1,C1,words,rfl,MemoryPrefix.refl _ _,hf,hm,hfree,ExecStmt.whileFalse hguard,r1⟩
  | succ n ih =>
    have hj0 : j < values.length := by omega
    have hc : c < words.length := by omega
    have hout := hm.span
    have hsrc := hs.span
    have hlo := hm.low
    have hcovered := hm.covered
    have hlen : words.length ≤ 2^64-1 := by omega
    have hcb : c+1 < UInt256.size := by change _ < 2^256; omega
    have hjb : j+1 < UInt256.size := by change _ < 2^256; omega
    have hguard : evalExpr? config {contract := contract,locals := L,immutables := immStore v} evm (localArrayGuard "j" "currentUids") = .ok (.bool true) := by
      simpa only [List.length_map,decide_eq_true hj0] using
        evalLocalArrayGuard (cfg := config) (evm := evm) (frame := {contract := contract,locals := L,immutables := immStore v}) hf.index hf.current
    have hsol := mergeUIDInnerSource (fork := fork) (imms := immStore v) (evm := evm) hf hc hj0 hcb hjb
    obtain ⟨a1,k1,C1,r1⟩ := easMergeUIDInnerStep v hstack hs hj0 hm.length hc hlen rd
    have hdst : (UInt256.ofNat (out.toNat+32+32*c)).toNat = out.toNat+32+32*c := ulit_toNat' _ (by change _ < 2^256; omega)
    rw [hdst] at r1
    let final := Reasoning.Theory.writeWord mem (out.toNat+32+32*c) values[j]
    have hp : MemoryPrefix mem final out.toNat := memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega))
    have hm1 : WordArrayPrefixView final out (words.set c values[j]) (c+1) heap.toNat := hm.set hc values[j] (by change _ < 2^256; omega)
    have hs1 : WordArrayMemoryView final src values out.toNat := hs.preserve hp out.val.isLt
    have hf1 := hf.next values[j]
    have hfree1 : memLoad (UInt256.ofNat 64) final = heap :=
      (memLoad_write_below _ _ _ _ (by change 96 ≤ _; omega) (by change 96 ≤ mem.size; omega)).trans hfree
    obtain ⟨L2,m2,a2,k2,C2,words2,hlen2,hp2,hf2,hm2,hfree2,hsol2,r2⟩ := ih
      (by omega) (by rw [List.length_set]; omega) hf1 hm1 hs1 hfree1 r1
    rw [List.length_set] at hlen2
    have hc2 : c+1+n = c+(n+1) := by omega
    rw [hc2] at hf2 hm2 r2
    exact ⟨L2,m2,a2,k2,C2,words2,hlen2,hp.trans hp2,hf2,hm2,hfree2,ExecStmt.whileTrue hguard hsol hsol2,r2⟩

end Benchmarks.EAS.EAS
