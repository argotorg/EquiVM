import Benchmarks.EAS.EAS.AttestArraysSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestArgs (schema : UInt256) (rs : List AttestationRequestRecord) (attester : AccountAddress)
    (available : UInt256) (last : Bool) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "last" (.bool last)
    |>.insert "availableValue" (.int (Int.ofNat available.toNat)) |>.insert "attester" (.address attester)
    |>.insert "data" (.array (rs.map AttestationRequestRecord.tuple)) |>.insert "schema" (wordBytes32Value schema)

theorem attest_lookup : lookupCallable? contract "_attest" = some attestFunction.toCallable := rfl

theorem attest_bind (schema : UInt256) (rs : List AttestationRequestRecord) (attester : AccountAddress)
    (available : UInt256) (last : Bool) (heap : Nat) :
    bindParams? attestFunction.params [wordBytes32Value schema,.array (rs.map AttestationRequestRecord.tuple),
      .address attester,.int (Int.ofNat available.toNat),.bool last,.int (Int.ofNat heap)] =
      some (attestArgs schema rs attester available last heap) := rfl

def attestInitialDecls : Body := [
  .letDecl "length" (some abiUInt256) (.arrayLength .localVar {base := "data"}),
  .letDecl "empty" (some (.dynamicArray abiBytes32)) (.newArray (.elem (.bytes abiBytes32Width)) (.intLit 0)),
  .letDecl "res" (some (.tuple [abiUInt256,.dynamicArray abiBytes32]))
    (.structLit "AttestationsResult" [("usedValue",.intLit 0),("uids",.var "empty")])]
def attestUIDDecl : Stmt := .assign .localVar {base := "res",steps := [.field "uids"]}
  (.newArray (.elem (.bytes abiBytes32Width)) (.var "length"))
def attestInitialBody : Body := allocateBlock (.intLit 128) ++ attestInitialDecls ++ arrayAllocateBlock 32 ++ [attestUIDDecl]

theorem attestInitialBody_eq : attestFunction.body.take 11 = attestInitialBody := by native_decide

def attestDeclaredLocals (L : Store) (len : Nat) : Store :=
  L.insert "length" (.int (Int.ofNat len)) |>.insert "empty" (.array []) |>.insert "res" (attestationsResultValue [] ⟨0⟩)
def attestInitialLocals (L : Store) (len first next : Nat) : Store :=
  (allocateBlockLocals (attestDeclaredLocals (allocateBlockLocals L first) len) next).insert
    "res" (attestationsResultValue (List.replicate len ⟨0⟩) ⟨0⟩)

theorem attestInitialDecls_source {L imms : Store} {evm : EVM.State} {rs : List AttestationRequestRecord}
    (hd : L.get? "data" = some (.array (rs.map AttestationRequestRecord.tuple))) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestInitialDecls
      (.ok {contract := contract,locals := attestDeclaredLocals L rs.length,immutables := imms} evm) := by
  have hlen : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.arrayLength .localVar {base := "data"}) = .ok (.int (Int.ofNat rs.length)) := by
    simpa only [List.length_map] using evalLocalArrayLength (cfg := config) (stele := {contract := contract,locals := L,immutables := imms}) (evm := evm) hd
  apply ExecBlock.consNormal (ExecStmt.letDecl hlen)
  have hempty : ∀ frame, evalExpr? config frame evm (.newArray (.elem (.bytes abiBytes32Width)) (.intLit 0)) = .ok (.array []) := by
    intro frame
    have hd : defaultValue? (.elem (.bytes abiBytes32Width)) = .ok (wordBytes32Value ⟨0⟩) := by native_decide
    simp only [evalExpr?,hd,pure,EvalResult.bind,bind,show ¬(0 : Int)<0 by decide,if_false]
    rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl (hempty _))
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  simp only [evalExpr?,evalStructFields?,store_get_self,EvalResult.ofOption,EvalResult.bind,bind,pure]
  rfl

theorem attestUIDDecl_source {L imms : Store} {evm : EVM.State} {len : Nat}
    (hl : L.get? "length" = some (.int (Int.ofNat len)))
    (hr : L.get? "res" = some (attestationsResultValue [] ⟨0⟩)) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm attestUIDDecl
      (.ok {contract := contract,locals := L.insert "res" (attestationsResultValue (List.replicate len ⟨0⟩) ⟨0⟩),immutables := imms} evm) := by
  have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.newArray (.elem (.bytes abiBytes32Width)) (.var "length")) =
      .ok (.array ((List.replicate len (⟨0⟩ : UInt256)).map wordBytes32Value)) := by
    rw [List.map_replicate]
    exact evalLocalNewArray hl (by native_decide)
  apply ExecStmt.assign (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) he
  simp only [assignStorageRef?,hr,updateLocalPath?,attestationsResultValue,lookupField?,
    EvalResult.ofOption,EvalResult.bind,bind,pure]
  rfl

theorem attestInitialSource {L imms : Store} {evm : EVM.State} {rs : List AttestationRequestRecord} {heap : Nat}
    (hd : L.get? "data" = some (.array (rs.map AttestationRequestRecord.tuple)))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    let first := allocateNext heap 128
    let next := allocateNext first (32+32*rs.length)
    if first ≤ 2^64-1 ∧ heap ≤ first then
      if rs.length ≤ 2^64-1 then
        if next ≤ 2^64-1 ∧ first ≤ next then
          ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestInitialBody
            (.ok {contract := contract,locals := attestInitialLocals L rs.length first next,immutables := imms} evm)
        else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestInitialBody .reverted
      else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestInitialBody .reverted
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestInitialBody .reverted := by
  dsimp only
  have hsize : evalExpr? config {contract := contract,locals := L,immutables := imms} evm (.intLit 128) = .ok (.int (Int.ofNat 128)) := by simp only [evalExpr?,pure]; rfl
  by_cases hg : allocateNext heap 128 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 128
  · rw [if_pos hg]
    have h1 := allocateBlock_ok (fork := fork) hsize hh hg
    have hd1 := (allocateBlockLocals_get (heap := allocateNext heap 128)
      (by decide : ("allocation$allocation" == "data") = false) (by decide) (by decide)).trans hd
    have hdecl := attestInitialDecls_source (fork := fork) (imms := imms) (evm := evm) hd1
    have hlen : (attestDeclaredLocals (allocateBlockLocals L (allocateNext heap 128)) rs.length).get? "length" =
        some (.int (Int.ofNat rs.length)) := by
      simp (disch := decide) only [attestDeclaredLocals,store_get_ne,store_get_self]
    have hfree : (attestDeclaredLocals (allocateBlockLocals L (allocateNext heap 128)) rs.length).get? "$EAS.freeMemory" =
        some (.int (Int.ofNat (allocateNext heap 128))) := by
      simp (disch := decide) only [attestDeclaredLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
    have ha := arrayAllocateSource (fork := fork) (cfg := config) (imms := imms) (evm := evm) hlen hfree 32
    have hprefix := execBlock_append h1 hdecl
    by_cases hl : rs.length ≤ 2^64-1
    · rw [if_pos hl] at ha ⊢
      split at ha
      · rename_i hb
        rw [if_pos hb]
        have hlen' := (allocateBlockLocals_get (heap := allocateNext (allocateNext heap 128) (32+32*rs.length))
          (by decide : ("allocation$allocation" == "length") = false) (by decide) (by decide)).trans hlen
        have hr : (allocateBlockLocals (attestDeclaredLocals (allocateBlockLocals L (allocateNext heap 128)) rs.length)
            (allocateNext (allocateNext heap 128) (32+32*rs.length))).get? "res" = some (attestationsResultValue [] ⟨0⟩) := by
          simp (disch := decide) only [allocateBlockLocals_get,attestDeclaredLocals,store_get_self]
        exact execBlock_append (execBlock_append hprefix ha) (ExecBlock.consNormal (attestUIDDecl_source hlen' hr) ExecBlock.nil)
      · rename_i hb
        rw [if_neg hb]
        simpa only [attestInitialBody,List.append_assoc] using
          execBlock_append hprefix (execBlock_append_term (s2 := [attestUIDDecl]) ha (by intros;exact nofun))
    · rw [if_neg hl] at ha ⊢
      simpa only [attestInitialBody,List.append_assoc] using
        execBlock_append hprefix (execBlock_append_term (s2 := [attestUIDDecl]) ha (by intros;exact nofun))
  · rw [if_neg hg]
    simpa only [attestInitialBody,List.append_assoc] using execBlock_append_term
      (s2 := attestInitialDecls ++ arrayAllocateBlock 32 ++ [attestUIDDecl]) (allocateBlock_revert hsize hh hg) (by intros;exact nofun)

end Benchmarks.EAS.EAS
