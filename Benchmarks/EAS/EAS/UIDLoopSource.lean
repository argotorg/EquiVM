import Benchmarks.EAS.EAS.GetUIDCall
import Benchmarks.EAS.EAS.UIDControl
import Benchmarks.EAS.EAS.Time
import Benchmarks.EAS.EAS.AllocateBounds

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def uidAvailableExpr : Expr := .binary .eq (.storage dbUIDRef) (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩))
def uidBumpExpr : Expr := .cast (.binary .add (.var "bump") (.intLit 1)) (.elem (.int (.uint ⟨32,by decide⟩)))
def uidCompute : Body := [
  .internalCall "_getUID" [.var "attestation",.var "bump",.var "$EAS.freeMemory"] "__c3$allocation",
  .letDecl "__c3" none (.tupleGet (.var "__c3$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c3$allocation") 1),
  .assign .localVar {base := "uid"} (.var "__c3")]
def uidIteration : Body := uidCompute ++ [
  .ite uidAvailableExpr [.break] [],.assign .localVar {base := "bump"} uidBumpExpr]
def uidComputeLocals (L : Store) (word : UInt256) (heap : Nat) : Store :=
  (unpackHeapLocals (L.insert "__c3$allocation" (.tuple [wordBytes32Value word,.int (Int.ofNat heap)]))
    "__c3" "$EAS.freeMemory" (wordBytes32Value word) heap).insert "uid" (wordBytes32Value word)
def uidNextLocals (L : Store) (word bump : UInt256) (heap : Nat) : Store :=
  (uidComputeLocals L word heap).insert "bump" (.int (Int.ofNat (nextUIDBump bump).toNat))

structure UIDLoopLocals (L : Store) (a : AttestationRecord) (bump : UInt256) (heap : Nat) : Prop where
  attestation : L.get? "attestation" = some a.value
  bump : L.get? "bump" = some (.int (Int.ofNat bump.toNat))
  heap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  uid : ∃ old, L.get? "uid" = some old
  db : L.get? "_db" = none

theorem uidComputeSource {cfg : Config} {L imms : Store} {evm : EVM.State} {word : UInt256} {heap : Nat} {old oldHeap : Value}
    (hh : L.get? "$EAS.freeMemory" = some oldHeap) (hu : L.get? "uid" = some old)
    (hc : ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} evm uidCompute[0]!
      (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms} "__c3$allocation"
        (some [wordBytes32Value word,.int (Int.ofNat heap)])) evm)) :
    ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm uidCompute
      (.ok {contract := contract,locals := uidComputeLocals L word heap,immutables := imms} evm) := by
  apply ExecBlock.consNormal hc
  let first := L.insert "__c3$allocation" (.tuple [wordBytes32Value word,.int (Int.ofNat heap)])
  let mid := unpackHeapLocals (L.insert "__c3$allocation" (.tuple [wordBytes32Value word,.int (Int.ofNat heap)]))
    "__c3" "$EAS.freeMemory" (wordBytes32Value word) heap
  have hret : first.get? "__c3$allocation" = some (.tuple [wordBytes32Value word,.int (Int.ofNat heap)]) := store_get_self _ _ _
  have hheap : first.get? "$EAS.freeMemory" = some oldHeap := by
    simpa only [first,store_get_ne _ _ (by decide : ("__c3$allocation" == "$EAS.freeMemory") = false)] using hh
  have hUnpack := unpackHeapResult (fork := fork) (cfg := cfg) (frame := {contract := contract,locals := first,immutables := imms}) (evm := evm)
    (tmp := "__c3$allocation") (result := "__c3") (cursor := "$EAS.freeMemory") hret hheap (by decide) (by decide)
  apply execBlock_append (s2 := [.assign .localVar {base := "uid"} (.var "__c3")]) hUnpack
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) ?_ (assignLocalBase_ok (old := old) ?_)) ExecBlock.nil
  · simp only [evalExpr?,unpackHeapLocals,store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "__c3") = false),
      store_get_self,EvalResult.ofOption]
  · simpa only [unpackHeapLocals,first,store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "uid") = false),
      store_get_ne _ _ (by decide : ("__c3" == "uid") = false),
      store_get_ne _ _ (by decide : ("__c3$allocation" == "uid") = false)] using hu

theorem uidComputeLocals_get (L : Store) (word : UInt256) (heap : Nat) (name : Ident)
    (h1 : ("uid" == name) = false) (h2 : ("$EAS.freeMemory" == name) = false)
    (h3 : ("__c3" == name) = false) (h4 : ("__c3$allocation" == name) = false) :
    (uidComputeLocals L word heap).get? name = L.get? name := by
  simp only [uidComputeLocals,unpackHeapLocals,store_get_ne _ _ h1,store_get_ne _ _ h2,store_get_ne _ _ h3,store_get_ne _ _ h4]

-- GENERALIZES evalBytes32Ne to the equality operator.
theorem evalBytes32Eq (a b : UInt256) :
    evalBinaryOp? .eq (wordBytes32Value a) (wordBytes32Value b) = .ok (.bool (decide (a = b))) := by
  have hv : (wordBytes32Value a == wordBytes32Value b) = (EVM.Word.toBytesBE a == EVM.Word.toBytesBE b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [wordBytes32Value,beq_iff_eq,Value.fixedBytes.injEq,true_and]
  simp only [evalBinaryOp?,hv,wordBytesBE_beq]

theorem uidAvailable_eval {L imms : Store} {evm : EVM.State} {word : UInt256}
    (hd : L.get? "_db" = none) (hu : L.get? "uid" = some (wordBytes32Value word)) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm uidAvailableExpr =
      .ok (.bool (decide (dbUIDWord evm word = ⟨0⟩))) := by
  have he := dbUID_read (evm := evm) (imms := imms) hd hu
  simp only [uidAvailableExpr,evalExpr?,he,EvalResult.bind,bind,pure]
  exact evalBytes32Eq _ _

theorem nextUIDBump_lt (bump : UInt256) : (nextUIDBump bump).toNat < 2^32 := by
  rw [nextUIDBump,u256_land_comm]
  exact u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem uidBump_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {bump : UInt256}
    (hb : frame.locals.get? "bump" = some (.int (Int.ofNat bump.toNat))) (hfit : bump.toNat < 2^32) :
    evalExpr? cfg frame evm uidBumpExpr = .ok (.int (Int.ofNat (nextUIDBump bump).toNat)) := by
  have hs : (UInt256.ofNat 1+bump).toNat = bump.toNat+1 := by
    rw [u256_add_comm,uadd_word_ofNat_toNat _ _ (by change bump.toNat+1 < 2^256; omega)]
  have he : evalExpr? cfg frame evm (.binary .add (.var "bump") (.intLit 1)) =
      .ok (.int (Int.ofNat (UInt256.ofNat 1+bump).toNat)) := by
    simp only [evalExpr?,hb,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?,hs]
    rfl
  have hc := evalWordAsUint (⟨32,by decide⟩ : ABI.BitWidth) he
  simpa only [uidBumpExpr,nextUIDBump,u256_land_comm] using hc

theorem uidHeap_grows (heap len : Nat) (hh : heap ≤ 2^64-1) (hl : len < 2^64) :
    heap+160 ≤ allocateNext heap (157+len) := by
  rw [allocateNext_small hh (by change 157+len < 2^138; omega)]
  omega

end Benchmarks.EAS.EAS
