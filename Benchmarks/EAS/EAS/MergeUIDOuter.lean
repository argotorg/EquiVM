import Benchmarks.EAS.EAS.MergeUIDInner

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem mergeUIDOuterLoop {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lists out heap ret : UInt256} {i c : Nat} {groups : List (List UInt256)} {words : List UInt256} {R : List UInt256}
    (v : EASImmutables) (hstack : R.length+18 ≤ 1024) (hh : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (n : Nat) (hi : i+n = groups.length) (hspace : c+(groups.drop i).flatten.length = words.length)
    (hf : MergeUIDLocals L groups words heap.toNat c i)
    (hm : WordArrayPrefixView mem out words c heap.toNat) (hs : WordArrayArrayMemoryView mem lists groups out.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨11990⟩
      (out::UInt256.ofNat c::UInt256.ofNat i::lists::ret::R) mem aw rdata σ k C) :
    ∃ L' mem' aw' k' C' words', words'.length = words.length ∧ MemoryPrefix mem mem' out.toNat ∧
      MergeUIDLocals L' groups words' heap.toNat words'.length groups.length ∧
      WordArrayMemoryView mem' out words' heap.toNat ∧ memLoad (UInt256.ofNat 64) mem' = heap ∧
      ExecStmt fork config {contract := contract,locals := L,immutables := immStore v} evm
        (.while (localArrayGuard "i" "uidLists") mergeUIDOuterIteration)
        (.ok {contract := contract,locals := L',immutables := immStore v} evm) ∧
      RD fork (deployedRuntime v) ee g s0 ret (out::R) mem' aw' rdata σ k' C' := by
  induction n generalizing L mem aw k C i c words with
  | zero =>
    have hi0 : i = groups.length := by omega
    subst i
    have hc : c = words.length := by simpa only [List.drop_length,List.flatten_nil,List.length_nil,Nat.add_zero] using hspace
    rw [hc] at hf hm rd
    obtain ⟨a1,k1,C1,r1⟩ := easMergeUIDDone v (by omega) hs.length hret rd
    have hguard : evalExpr? config {contract := contract,locals := L,immutables := immStore v} evm (localArrayGuard "i" "uidLists") = .ok (.bool false) := by
      simpa only [List.length_map,decide_eq_false (Nat.lt_irrefl groups.length)] using
        evalLocalArrayGuard (cfg := config) (evm := evm) (frame := {contract := contract,locals := L,immutables := immStore v}) hf.index hf.groups
    exact ⟨L,mem,a1,k1,C1,words,rfl,MemoryPrefix.refl _ _,hf,hm.finish,hfree,ExecStmt.whileFalse hguard,r1⟩
  | succ n ih =>
    have hi0 : i < groups.length := by omega
    have hout := hm.span
    have hsrc := hs.span
    have hib : i+1 < UInt256.size := by change _ < 2^256; omega
    have hcount : (groups.drop i).flatten.length = groups[i].length+(groups.drop (i+1)).flatten.length := by
      rw [List.drop_eq_getElem_cons hi0,List.flatten_cons,List.length_append]
    have hguard : evalExpr? config {contract := contract,locals := L,immutables := immStore v} evm (localArrayGuard "i" "uidLists") = .ok (.bool true) := by
      simpa only [List.length_map,decide_eq_true hi0] using
        evalLocalArrayGuard (cfg := config) (evm := evm) (frame := {contract := contract,locals := L,immutables := immStore v}) hf.index hf.groups
    obtain ⟨hsol0,hf0⟩ := mergeUIDOuterInitialSource (imms := immStore v) (evm := evm) hf hi0
    obtain ⟨ptr,a1,k1,C1,hptr,r1⟩ := easMergeUIDOuterEnter v (by omega) hs hi0 rd
    obtain ⟨L2,m2,a2,k2,C2,words2,hlen2,hp2,hf2,hm2,hfree2,hsol2,r2⟩ := mergeUIDInnerLoop v hstack hh
      groups[i].length (by omega) (by omega) hf0 hm hptr hfree r1
    let L3 := L2.insert "i" (.int (Int.ofNat (i+1)))
    have hsol3 : ExecStmt fork config {contract := contract,locals := L2,immutables := immStore v} evm (localCastIncrement "i")
        (.ok {contract := contract,locals := L3,immutables := immStore v} evm) := execLocalCastIncrement hf2.outer.index hib
    have hf3 : MergeUIDLocals L3 groups words2 heap.toNat (c+groups[i].length) (i+1) := hf2.outer.increment
    have hs2 : WordArrayArrayMemoryView m2 lists groups out.toNat := hs.preserve hp2 out.val.isLt
    have hstep : ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm mergeUIDOuterIteration
        (.ok {contract := contract,locals := L3,immutables := immStore v} evm) :=
      execBlock_append hsol0 (ExecBlock.consNormal hsol2 (ExecBlock.consNormal hsol3 ExecBlock.nil))
    obtain ⟨L4,m4,a4,k4,C4,words4,hlen4,hp4,hf4,hm4,hfree4,hsol4,r4⟩ := ih
      (by omega) (by omega) hf3 hm2 hs2 hfree2 r2
    exact ⟨L4,m4,a4,k4,C4,words4,hlen4.trans hlen2,hp2.trans hp4,hf4,hm4,hfree4,ExecStmt.whileTrue hguard hstep hsol4,r4⟩

end Benchmarks.EAS.EAS
