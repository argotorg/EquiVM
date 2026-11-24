import Benchmarks.EAS.EAS.AttestationWriteSource
import Benchmarks.EAS.EAS.AliasStorage

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: compose the successful scalar assignments of a struct prefix.
theorem execScalarAssignments {cfg : Config} {frame : Frame} (fs : List ScalarFieldWrite)
    (ref : ScalarFieldWrite → StorageRef) (expr : ScalarFieldWrite → Expr) (evm : EVM.State)
    (hstep : ∀ f ∈ fs, ∀ e, e.executionEnv.perm = true →
      ExecStmt fork cfg frame e (.assign .storage (ref f) (expr f)) (.ok frame (f.apply e)))
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork cfg frame evm (fs.map fun f => .assign .storage (ref f) (expr f))
      (.ok frame (writeScalarFields fs evm)) := by
  induction fs generalizing evm with
  | nil => exact ExecBlock.nil
  | cons f fs ih =>
    exact ExecBlock.consNormal (hstep f List.mem_cons_self evm hperm)
      (ih (f.apply evm) (fun x hx => hstep x (List.mem_cons_of_mem f hx))
        (by simpa [ScalarFieldWrite.apply] using hperm))

def attestationFieldRef (field : Ident) : StorageRef :=
  {base := "_db",steps := [.mindex (.var "uid"),.field field]}
def attestationWriteStmt (field : Ident) : Stmt :=
  .assign .storage (attestationFieldRef field) (.field (.var "attestation") field)

theorem attestationField_evalRef {evm : EVM.State} {L imms : Store} {word : UInt256}
    (hu : L.get? "uid" = some (wordBytes32Value word)) (field : Ident) :
    evalStorageRef config {contract := contract,locals := L,immutables := imms} evm (attestationFieldRef field) =
      .ok (attestationFieldER word field) := by
  have hlen : (EVM.Word.toBytesBE word).length = 32 := by simpa using word_toBytesBE_toByteArray_size word
  simp only [evalStorageRef,attestationFieldRef,evalStorageRefSteps,evalStorageRefStep,evalExpr?,hu,
    wordBytes32Value,EvalResult.ofOption,valueToKey?,hlen,abiBytes32Width,
    show (31 : Nat)+1 = 32 from rfl,if_true,pure,bind,EvalResult.bind]
  rfl

theorem attestationScalarWrites_type (word : UInt256) (a : AttestationRecord) :
    ∀ f ∈ attestationScalarWrites (dbSlot word) a,
      storageTypeAt? contract.storage (attestationFieldER word f.name) = some (.elem f.loc.type) := by
  intro f hf
  simp only [attestationScalarWrites,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem attestationScalarWrites_value (slot : UInt256) (a : AttestationRecord) :
    ∀ f ∈ attestationScalarWrites slot a, lookupField? a.value f.name = some f.value := by
  intro f hf
  simp only [attestationScalarWrites,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem attestationScalarStmtRun {L imms : Store} {evm : EVM.State} {word : UInt256} {a : AttestationRecord}
    (hd : L.get? "_db" = none) (hu : L.get? "uid" = some (wordBytes32Value word))
    (ha : L.get? "attestation" = some a.value) {f : ScalarFieldWrite} (hf : f ∈ attestationScalarWrites (dbSlot word) a) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm (attestationWriteStmt f.name)
      (if evm.executionEnv.perm then .ok {contract := contract,locals := L,immutables := imms} (f.apply evm) else .staticViolation) := by
  apply execStmt_assign_storage (attestationRecord_field ha _ _ (attestationScalarWrites_value _ _ _ hf))
  apply assignStorageRef_resolved_value
    (resolveStorageRef?_ok hd (attestationField_evalRef hu f.name) (attestationScalarWrites_type word a f hf)) easStorageBackend
  · exact attestationScalarWrites_layout word a f hf
  · exact Or.inl ⟨_,rfl⟩
  · exact storageLocStore_packedSlice evm f.loc f.value f.word f.byteAligned f.valueWord

theorem attestationScalarAssignmentsRun {L imms : Store} {evm : EVM.State} {word : UInt256} {a : AttestationRecord}
    (hd : L.get? "_db" = none) (hu : L.get? "uid" = some (wordBytes32Value word))
    (ha : L.get? "attestation" = some a.value) (fs : List ScalarFieldWrite)
    (hfs : ∀ f ∈ fs, f ∈ attestationScalarWrites (dbSlot word) a)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm
      (fs.map fun f => attestationWriteStmt f.name)
      (.ok {contract := contract,locals := L,immutables := imms} (writeScalarFields fs evm)) := by
  exact execScalarAssignments fs (fun f => attestationFieldRef f.name) (fun f => .field (.var "attestation") f.name) evm
    (fun f hf e hp => by simpa only [hp, if_true] using
      attestationScalarStmtRun (evm := e) hd hu ha (hfs f hf)) hperm

theorem attestationWriteStatic {L imms : Store} {evm : EVM.State} {word : UInt256} {a : AttestationRecord} {rest : Body}
    (hd : L.get? "_db" = none) (hu : L.get? "uid" = some (wordBytes32Value word))
    (ha : L.get? "attestation" = some a.value) (hp : evm.executionEnv.perm = false) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm
      (attestationWriteStmt "uid" :: rest) .staticViolation := by
  have h := attestationScalarStmtRun (fork := fork) (evm := evm) (imms := imms) hd hu ha
    (f := attestationWordWrite "uid" (dbSlot word) a.uid) List.mem_cons_self
  exact ExecBlock.consStatic (execStmt_assign_static h hp)

end Benchmarks.EAS.EAS
