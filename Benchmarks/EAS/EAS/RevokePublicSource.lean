import Benchmarks.EAS.EAS.AttestPublicSource
import Benchmarks.EAS.EAS.RevokeDecode

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def revokePublicPrefix : Body := easPayableEntryPrefix ++ allocateBlock (.intLit 192)
def revokePublicPrefixLocals (L : Store) (cd : ByteArray) : Store := allocateBlockLocals (easEntryLocals L cd) 416

def revocationDataType : StorageType := .struct "RevocationRequestData" [
  ("uid",.elem (.bytes 31)),("value",.elem (.int (.uint ⟨256,by decide⟩)))]
def defaultRevocationRecord : RevocationRequestRecord := ⟨⟨0⟩,⟨0⟩⟩
def revokePublicRequests : Body := [
  .letDecl "requests" (some (.dynamicArray revocationDataABI)) (.newArray revocationDataType (.intLit 1)),
  .assign .localVar {base := "requests",steps := [.aindex (.intLit 0)]} (.tupleGet (.var "request") 1)]
def revokePublicRequestsLocals (L : Store) (r : RevocationRequestRecord) : Store :=
  (L.insert "requests" (.array [defaultRevocationRecord.struct])).insert "requests" (.array [r.tuple])
def revokePublicCall : Stmt := .internalCall "_revoke" attestPublicCallArgs "__c0$allocation"
def revokePublicFinish : Body := [
  .letDecl "__c0" none (.tupleGet (.var "__c0$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c0$allocation") 1)]
theorem revokePublic_body : revokeTransition.body =
    revokePublicPrefix ++ revokePublicRequests ++ [revokePublicCall] ++ revokePublicFinish := by native_decide

theorem revokePublicPrefixSource {L imms : Store} {evm : EVM.State}
    (hsz : 4 ≤ evm.executionEnv.calldata.size) (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hguard : evm.executionEnv.calldata.size-4 < 2^255) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm revokePublicPrefix
      (.ok {contract := contract,locals := revokePublicPrefixLocals L evm.executionEnv.calldata,immutables := imms} evm) := by
  apply execBlock_append (easPayableEntryPrefix_ok hsz hsize hguard)
  have ha := allocateBlock_ok (fork := fork) (cfg := config) (evm := evm) (locals := easEntryLocals L evm.executionEnv.calldata)
    (imms := imms) (size := .intLit 192) (n := 192) (heap := 224)
    (by simp only [evalExpr?,pure,Int.ofNat_eq_natCast]; norm_num) (by simp (disch := decide) only [easEntryLocals,store_get_ne,store_get_self,Int.ofNat_eq_natCast]; norm_num) (by decide)
  simpa only [show allocateNext 224 192 = 416 by native_decide] using ha

theorem revokePublicRequestsSource {L imms : Store} {evm : EVM.State}
    {schema : UInt256} {r : RevocationRequestRecord}
    (hreq : L.get? "request" = some (.tuple [wordBytes32Value schema,r.tuple])) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm revokePublicRequests
      (.ok {contract := contract,locals := revokePublicRequestsLocals L r,immutables := imms} evm) := by
  have hd : defaultValue? revocationDataType = .ok defaultRevocationRecord.struct := by native_decide
  have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.newArray revocationDataType (.intLit 1)) = .ok (.array [defaultRevocationRecord.struct]) := by
    simp only [evalExpr?,pure,bind,EvalResult.bind,show ¬ (1 : Int) < 0 by decide,if_false,hd]
    rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl he)
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := r.tuple) ?_ ?_) ExecBlock.nil
  · simp only [evalExpr?,store_get_ne _ _ (by decide : ("requests" == "request") = false),hreq,EvalResult.ofOption,EvalResult.bind,bind]
    rfl
  · exact assignLocalArrayExpr (cfg := config) (evm := evm)
      (frame := {contract := contract,locals := L.insert "requests" (.array [defaultRevocationRecord.struct]),immutables := imms})
      (name := "requests") (values := [defaultRevocationRecord.struct]) (index := .intLit 0) (i := 0) (value := r.tuple)
      (store_get_self _ _ _) (by simp only [evalExpr?,pure,Int.ofNat_eq_natCast]; norm_num) (by simp)


end Benchmarks.EAS.EAS
