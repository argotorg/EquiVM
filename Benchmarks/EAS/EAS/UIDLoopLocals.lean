import Benchmarks.EAS.EAS.UIDLoopSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem uidComputeLocals_heap (L : Store) (word : UInt256) (heap : Nat) :
    (uidComputeLocals L word heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  simp only [uidComputeLocals,unpackHeapLocals,store_get_ne _ _ (by decide : ("uid" == "$EAS.freeMemory") = false),store_get_self]

theorem UIDLoopLocals.compute {L : Store} {a : AttestationRecord} {bump word : UInt256} {heap next : Nat}
    (h : UIDLoopLocals L a bump heap) : UIDLoopLocals (uidComputeLocals L word next) a bump next := by
  refine ⟨?_,?_,uidComputeLocals_heap _ _ _,⟨wordBytes32Value word,store_get_self _ _ _⟩,?_⟩
  · exact (uidComputeLocals_get _ _ _ _ (by decide) (by decide) (by decide) (by decide)).trans h.attestation
  · exact (uidComputeLocals_get _ _ _ _ (by decide) (by decide) (by decide) (by decide)).trans h.bump
  · exact (uidComputeLocals_get _ _ _ _ (by decide) (by decide) (by decide) (by decide)).trans h.db

theorem UIDLoopLocals.next {L : Store} {a : AttestationRecord} {bump word : UInt256} {heap next : Nat}
    (h : UIDLoopLocals L a bump heap) : UIDLoopLocals (uidNextLocals L word bump next) a (nextUIDBump bump) next := by
  have hc := h.compute (word := word) (next := next)
  refine ⟨?_,store_get_self _ _ _,?_,?_,?_⟩
  · simpa only [uidNextLocals,store_get_ne _ _ (by decide : ("bump" == "attestation") = false)] using hc.attestation
  · simpa only [uidNextLocals,store_get_ne _ _ (by decide : ("bump" == "$EAS.freeMemory") = false)] using hc.heap
  · exact ⟨wordBytes32Value word,by simp only [uidNextLocals,uidComputeLocals,
      store_get_ne _ _ (by decide : ("bump" == "uid") = false),store_get_self]⟩
  · simpa only [uidNextLocals,store_get_ne _ _ (by decide : ("bump" == "_db") = false)] using hc.db

def UIDLoopKeep (before after : Store) : Prop := ∀ name,
  ("uid" == name) = false → ("$EAS.freeMemory" == name) = false → ("__c3" == name) = false →
  ("__c3$allocation" == name) = false → ("bump" == name) = false → after.get? name = before.get? name

theorem UIDLoopKeep.refl (L : Store) : UIDLoopKeep L L := by intro name _ _ _ _ _; rfl
theorem UIDLoopKeep.trans {L L' L'' : Store} (h : UIDLoopKeep L L') (h' : UIDLoopKeep L' L'') : UIDLoopKeep L L'' := by
  intro name h1 h2 h3 h4 h5
  exact (h' name h1 h2 h3 h4 h5).trans (h name h1 h2 h3 h4 h5)
theorem uidComputeLocals_keep (L : Store) (word : UInt256) (heap : Nat) : UIDLoopKeep L (uidComputeLocals L word heap) := by
  intro name h1 h2 h3 h4 _
  exact uidComputeLocals_get _ _ _ _ h1 h2 h3 h4
theorem uidNextLocals_keep (L : Store) (word bump : UInt256) (heap : Nat) : UIDLoopKeep L (uidNextLocals L word bump heap) := by
  intro name h1 h2 h3 h4 h5
  simp only [uidNextLocals,store_get_ne _ _ h5,uidComputeLocals_get _ _ _ _ h1 h2 h3 h4]

theorem uidIteration_break {L imms : Store} {evm : EVM.State} {a : AttestationRecord} {bump word : UInt256} {heap next : Nat}
    (hf : UIDLoopLocals L a bump heap) (hz : dbUIDWord evm word = ⟨0⟩)
    (hc : ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm uidCompute
      (.ok {contract := contract,locals := uidComputeLocals L word next,immutables := imms} evm)) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm uidIteration
      (.break {contract := contract,locals := uidComputeLocals L word next,immutables := imms} evm) := by
  apply execBlock_append hc
  apply ExecBlock.consBreak
  apply ExecStmt.iteTrue
  · simpa only [decide_eq_true hz] using uidAvailable_eval (imms := imms) (evm := evm)
      (hf.compute (word := word) (next := next)).db (store_get_self _ _ _)
  · exact ExecBlock.consBreak ExecStmt.break

theorem uidIteration_next {L imms : Store} {evm : EVM.State} {a : AttestationRecord} {bump word : UInt256} {heap next : Nat}
    (hf : UIDLoopLocals L a bump heap) (hz : dbUIDWord evm word ≠ ⟨0⟩) (hb : bump.toNat < 2^32)
    (hc : ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm uidCompute
      (.ok {contract := contract,locals := uidComputeLocals L word next,immutables := imms} evm)) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm uidIteration
      (.ok {contract := contract,locals := uidNextLocals L word bump next,immutables := imms} evm) := by
  apply execBlock_append hc
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
  · simpa only [decide_eq_false hz] using uidAvailable_eval (imms := imms) (evm := evm)
      (hf.compute (word := word) (next := next)).db (store_get_self _ _ _)
  · exact ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›)
      (uidBump_eval (hf.compute (word := word) (next := next)).bump hb)
      (assignLocalBase_ok (hf.compute (word := word) (next := next)).bump)) ExecBlock.nil

end Benchmarks.EAS.EAS
