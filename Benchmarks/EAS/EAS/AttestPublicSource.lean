import Benchmarks.EAS.EAS.AttestDecode
import Benchmarks.EAS.EAS.AllocateBlock
import Benchmarks.EAS.EAS.LocalArrayStore
import Benchmarks.EAS.EAS.AttestCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def easPayableEntryPrefix : Body := [
  .letDecl "$EAS.freeMemory" none (.intLit 224),
  .letDecl "__calldata" (some .bytes) (.env .msgData),
  .require easCalldataGuard]

theorem easPayableEntryPrefix_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    (hsz : 4 ≤ evm.executionEnv.calldata.size) (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hguard : evm.executionEnv.calldata.size-4 < 2^255) :
    ExecBlock fork cfg frame evm easPayableEntryPrefix
      (.ok {frame with locals := easEntryLocals frame.locals evm.executionEnv.calldata} evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 224) (by simp only [evalExpr?,pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes evm.executionEnv.calldata) (by simp only [evalExpr?,pure,envValue])) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  simpa only [hguard,decide_true] using evalCalldataSizeGuard
    (cfg := cfg) (evm := evm) (store_get_self _ _ _) hsz hsize

def attestPublicPrefix : Body := easPayableEntryPrefix ++ allocateBlock (.intLit 256)
def attestPublicPrefixLocals (L : Store) (cd : ByteArray) : Store := allocateBlockLocals (easEntryLocals L cd) 480

def attestPublicCopyArgs : List Expr := [.tupleGet (.var "request") 1,.var "$EAS.freeMemory"]
def attestPublicCopy : Stmt := .internalCall "_copyAttestationData" attestPublicCopyArgs "allocation$allocation"
def attestPublicCopyUnpack : Body := [
  .letDecl "allocation" none (.tupleGet (.var "allocation$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "allocation$allocation") 1)]

def requestDataType : StorageType := .struct "AttestationRequestData" [
  ("recipient",.elem .address),("expirationTime",.elem (.int (.uint ⟨64,by decide⟩))),
  ("revocable",.elem .bool),("refUID",.elem (.bytes 31)),("data",.bytes),("value",.elem (.int (.uint ⟨256,by decide⟩)))]
def defaultRequestRecord : AttestationRequestRecord :=
  ⟨AccountAddress.ofNat 0,⟨0⟩,false,⟨0⟩,ByteArray.empty,⟨0⟩⟩
def attestPublicRequests : Body := [
  .letDecl "requests" (some (.dynamicArray requestDataABI)) (.newArray requestDataType (.intLit 1)),
  .assign .localVar {base := "requests",steps := [.aindex (.intLit 0)]} (.tupleGet (.var "request") 1)]
def attestPublicRequestsLocals (L : Store) (r : AttestationRequestRecord) : Store :=
  (L.insert "requests" (.array [defaultRequestRecord.struct])).insert "requests" (.array [r.tuple])
def attestPublicCallArgs : List Expr := [
  .tupleGet (.var "request") 0,.var "requests",.env .caller,.env .callvalue,.boolLit true,.var "$EAS.freeMemory"]
def attestPublicCall : Stmt := .internalCall "_attest" attestPublicCallArgs "__c0$allocation"
def attestPublicFinish : Body := [
  .letDecl "__c0" none (.tupleGet (.var "__c0$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c0$allocation") 1),
  .return [.index (.field (.var "__c0") "uids") (.intLit 0)]]

theorem attestPublic_body : attestTransition.body = attestPublicPrefix ++ [attestPublicCopy] ++
    attestPublicCopyUnpack ++ attestPublicRequests ++ [attestPublicCall] ++ attestPublicFinish := by native_decide

theorem attestPublicPrefixSource {L imms : Store} {evm : EVM.State}
    (hsz : 4 ≤ evm.executionEnv.calldata.size) (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hguard : evm.executionEnv.calldata.size-4 < 2^255) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestPublicPrefix
      (.ok {contract := contract,locals := attestPublicPrefixLocals L evm.executionEnv.calldata,immutables := imms} evm) := by
  apply execBlock_append (easPayableEntryPrefix_ok hsz hsize hguard)
  have ha := allocateBlock_ok (fork := fork) (cfg := config) (evm := evm) (locals := easEntryLocals L evm.executionEnv.calldata)
    (imms := imms) (size := .intLit 256) (n := 256) (heap := 224)
    (by simp only [evalExpr?,pure,Int.ofNat_eq_natCast]; norm_num) (by simp (disch := decide) only [easEntryLocals,store_get_ne,store_get_self,Int.ofNat_eq_natCast]; norm_num) (by decide)
  simpa only [show allocateNext 224 256 = 480 by native_decide] using ha

theorem attestPublicRequestsSource {L imms : Store} {evm : EVM.State}
    {schema : UInt256} {r : AttestationRequestRecord}
    (hreq : L.get? "request" = some (.tuple [wordBytes32Value schema,r.tuple])) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestPublicRequests
      (.ok {contract := contract,locals := attestPublicRequestsLocals L r,immutables := imms} evm) := by
  have hd : defaultValue? requestDataType = .ok defaultRequestRecord.struct := by native_decide
  have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.newArray requestDataType (.intLit 1)) = .ok (.array [defaultRequestRecord.struct]) := by
    simp only [evalExpr?,pure,bind,EvalResult.bind,show ¬ (1 : Int) < 0 by decide,if_false,hd]
    rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl he)
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := r.tuple) ?_ ?_) ExecBlock.nil
  · simp only [evalExpr?,store_get_ne _ _ (by decide : ("requests" == "request") = false),hreq,EvalResult.ofOption,EvalResult.bind,bind]
    rfl
  · exact assignLocalArrayExpr (cfg := config) (evm := evm)
      (frame := {contract := contract,locals := L.insert "requests" (.array [defaultRequestRecord.struct]),immutables := imms})
      (name := "requests") (values := [defaultRequestRecord.struct]) (index := .intLit 0) (i := 0) (value := r.tuple)
      (store_get_self _ _ _) (by simp only [evalExpr?,pure,Int.ofNat_eq_natCast]; norm_num) (by simp)

theorem attestPublicFinishSource {L imms : Store} {evm : EVM.State} {uid used : UInt256} {heap : Nat} {old : Value}
    (hr : L.get? "__c0$allocation" = some (.tuple [attestationsResultValue [uid] used,.int (Int.ofNat heap)]))
    (hh : L.get? "$EAS.freeMemory" = some old) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestPublicFinish
      (.returned {contract := contract,locals := (unpackHeapLocals L "__c0" "$EAS.freeMemory" (attestationsResultValue [uid] used) heap),immutables := imms} evm (some [wordBytes32Value uid])) := by
  have hu := unpackHeapResult (fork := fork) (cfg := config) (evm := evm) (frame := {contract := contract,locals := L,immutables := imms})
    (result := "__c0") hr hh (by decide) (by decide)
  change ExecBlock fork _ _ _ ([.letDecl "__c0" none (.tupleGet (.var "__c0$allocation") 0),
    .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c0$allocation") 1)] ++
    [.return [.index (.field (.var "__c0") "uids") (.intLit 0)]]) _
  apply execBlock_append hu
  apply ExecBlock.consReturn (ExecStmt.return _)
  simp (disch := decide) only [evalExprs?,evalExpr?,unpackHeapLocals,store_get_ne,store_get_self,
    EvalResult.ofOption,bind,EvalResult.bind,pure,attestationsResultValue,lookupField?,lookupIndex?]
  rfl

end Benchmarks.EAS.EAS
