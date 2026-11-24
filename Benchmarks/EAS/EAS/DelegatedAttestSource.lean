import Benchmarks.EAS.EAS.DelegatedRevokeSource
import Benchmarks.EAS.EAS.DelegatedAttestDecode
import Benchmarks.EAS.EAS.CopyRequestCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestBegin : Body := easPayableEntryPrefix ++ allocateBlock (.intLit 128)
def delegatedAttestBeginLocals (L : Store) (cd : ByteArray) : Store := allocateBlockLocals (easEntryLocals L cd) 352
def delegatedAttestCopyArgs : List Expr := [.tupleGet (.var "delegatedRequest") 1,.var "$EAS.freeMemory"]
def delegatedAttestCopy : Body := heapResultBlock "_copyAttestationData" delegatedAttestCopyArgs
  "allocation$allocation" "allocation" "$EAS.freeMemory"
def delegatedAttestRecordStmt : Stmt := .letDecl "delegatedRequest" none
  (.structLit "DelegatedAttestationRequest" [("schema",.tupleGet (.var "delegatedRequest") 0),
    ("data",.tupleGet (.var "delegatedRequest") 1),("signature",.tupleGet (.var "delegatedRequest") 2),
    ("attester",.tupleGet (.var "delegatedRequest") 3)])
def delegatedAttestPrefix : Body := delegatedAttestBegin ++ delegatedAttestCopy ++ allocateBlock (.intLit 96) ++ [delegatedAttestRecordStmt]
def delegatedAttestPrefixLocals (L : Store) (cd : ByteArray) (r : DelegatedAttestationRecord) : Store :=
  (allocateBlockLocals (heapResultLocals (delegatedAttestBeginLocals L cd) "allocation$allocation" "allocation" "$EAS.freeMemory"
    (.tuple []) (copyRequestNext 352 r.data.data.size)) (copyRequestNext 352 r.data.data.size+96)).insert "delegatedRequest" r.struct

def delegatedAttestVerifyArgs : List Expr := [.var "delegatedRequest",.var "$EAS.freeMemory"]
def delegatedAttestVerify : Body := heapResultBlock "_verifyAttest" delegatedAttestVerifyArgs
  "__c0$allocation" "__c0" "$EAS.freeMemory"
def delegatedAttestTailCopyArgs : List Expr := [.field (.var "delegatedRequest") "data",.var "$EAS.freeMemory"]
def delegatedAttestTailCopy : Body := heapResultBlock "_copyAttestationData" delegatedAttestTailCopyArgs
  "allocation$allocation" "allocation" "$EAS.freeMemory"
def delegatedAttestDataBlock : Body := [
  .letDecl "data" (some (.dynamicArray requestDataABI)) (.newArray requestDataType (.intLit 1)),
  .assign .localVar {base := "data",steps := [.aindex (.intLit 0)]} (.field (.var "delegatedRequest") "data")]
def delegatedAttestDataLocals (L : Store) (r : AttestationRequestRecord) : Store :=
  (L.insert "data" (.array [defaultRequestRecord.struct])).insert "data" (.array [r.tuple])
def delegatedAttestCallArgs : List Expr := [.field (.var "delegatedRequest") "schema",.var "data",
  .field (.var "delegatedRequest") "attester",.env .callvalue,.boolLit true,.var "$EAS.freeMemory"]
def delegatedAttestCall : Body := heapResultBlock "_attest" delegatedAttestCallArgs
  "__c1$allocation" "__c1" "$EAS.freeMemory"
def delegatedAttestFinish : Body := [.return [.index (.field (.var "__c1") "uids") (.intLit 0)]]
def delegatedAttestTail : Body := allocateBlock (.intLit 256) ++ delegatedAttestTailCopy ++ delegatedAttestDataBlock ++ delegatedAttestCall ++ delegatedAttestFinish

theorem delegatedAttest_body : attestByDelegationTransition.body = delegatedAttestPrefix ++ delegatedAttestVerify ++ delegatedAttestTail := by native_decide

theorem delegatedAttestBeginSource {L imms : Store} {evm : EVM.State}
    (hsz : 4 ≤ evm.executionEnv.calldata.size) (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hguard : evm.executionEnv.calldata.size-4 < 2^255) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm delegatedAttestBegin
      (.ok {contract := contract,locals := delegatedAttestBeginLocals L evm.executionEnv.calldata,immutables := imms} evm) := by
  apply execBlock_append (easPayableEntryPrefix_ok hsz hsize hguard)
  have ha := allocateBlock_ok (fork := fork) (cfg := config) (evm := evm) (locals := easEntryLocals L evm.executionEnv.calldata)
    (imms := imms) (size := .intLit 128) (n := 128) (heap := 224)
    (by simp only [evalExpr?,pure]; rfl)
    (by simp (disch := decide) only [easEntryLocals,store_get_ne,store_get_self]; rfl) (by decide)
  simpa only [show allocateNext 224 128 = 352 by native_decide] using ha

theorem delegatedAttestPrefixSource {L imms : Store} {evm : EVM.State} {r : DelegatedAttestationRecord}
    (hr : L.get? "delegatedRequest" = some r.tuple)
    (hsz : 4 ≤ evm.executionEnv.calldata.size) (hsize : evm.executionEnv.calldata.size < UInt256.size)
    (hguard : evm.executionEnv.calldata.size-4 < 2^255) :
    ((copyRequestValid 352 r.data.data.size ∧ copyRequestNext 352 r.data.data.size+96 ≤ 2^64-1) →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm delegatedAttestPrefix
        (.ok {contract := contract,locals := delegatedAttestPrefixLocals L evm.executionEnv.calldata r,immutables := imms} evm)) ∧
    (¬ (copyRequestValid 352 r.data.data.size ∧ copyRequestNext 352 r.data.data.size+96 ≤ 2^64-1) →
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm delegatedAttestPrefix .reverted) := by
  let L1 := delegatedAttestBeginLocals L evm.executionEnv.calldata
  have hbegin := delegatedAttestBeginSource (fork := fork) (L := L) (imms := imms) hsz hsize hguard
  have hr1 : L1.get? "delegatedRequest" = some r.tuple := by
    simpa (disch := decide) only [L1,delegatedAttestBeginLocals,allocateBlockLocals_get,easEntryLocals,store_get_ne] using hr
  have hf1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat 352)) := store_get_self _ _ _
  have he : evalExprs? config {contract := contract,locals := L1,immutables := imms} evm delegatedAttestCopyArgs =
      .ok [r.data.tuple,.int (Int.ofNat 352)] := by
    simp only [delegatedAttestCopyArgs,evalExprs?,evalExpr?,hr1,hf1,DelegatedAttestationRecord.tuple,EvalResult.ofOption,bind,EvalResult.bind,pure]
    rfl
  have hcopy := copyRequestCall_branches (fork := fork) (retVar := "allocation$allocation") he
  by_cases hv : copyRequestValid 352 r.data.data.size
  · have hc := heapResultBlock_ok (result := "allocation") (cursor := "$EAS.freeMemory") (hcopy.1 hv) hf1 (by decide) (by decide) (by decide)
    let L2 := heapResultLocals L1 "allocation$allocation" "allocation" "$EAS.freeMemory" (.tuple []) (copyRequestNext 352 r.data.data.size)
    have hf2 : L2.get? "$EAS.freeMemory" = some (.int (Int.ofNat (copyRequestNext 352 r.data.data.size))) := store_get_self _ _ _
    have hn : allocateNext (copyRequestNext 352 r.data.data.size) 96 = copyRequestNext 352 r.data.data.size+96 := fixedAllocation_next .bytes96 hv.2.2.1
    have hsize96 : evalExpr? config {contract := contract,locals := L2,immutables := imms} evm (.intLit 96) = .ok (.int (Int.ofNat 96)) := by simp only [evalExpr?,pure]; rfl
    by_cases hh : copyRequestNext 352 r.data.data.size+96 ≤ 2^64-1
    · have ha := allocateBlock_ok (fork := fork) hsize96 hf2 (by rw [hn]; exact ⟨hh,by omega⟩)
      rw [hn] at ha
      have hr3 : (allocateBlockLocals L2 (copyRequestNext 352 r.data.data.size+96)).get? "delegatedRequest" = some r.tuple := by
        rw [allocateBlockLocals_get (by decide) (by decide) (by decide)]
        exact (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hr1
      have hrecord : ExecBlock fork config
          {contract := contract,locals := allocateBlockLocals L2 (copyRequestNext 352 r.data.data.size+96),immutables := imms}
          evm [delegatedAttestRecordStmt]
          (.ok {contract := contract,locals := delegatedAttestPrefixLocals L evm.executionEnv.calldata r,immutables := imms} evm) := by
        refine ExecBlock.consNormal (ExecStmt.letDecl (value := r.struct) ?_) ExecBlock.nil
        simp only [evalExpr?,evalStructFields?,hr3,DelegatedAttestationRecord.tuple,DelegatedAttestationRecord.struct,
          EvalResult.ofOption,bind,EvalResult.bind,pure]
        rfl
      exact ⟨fun _ => execBlock_append (execBlock_append (execBlock_append hbegin hc) ha) hrecord,
        fun h => False.elim (h ⟨hv,hh⟩)⟩
    · have ha := allocateBlock_revert (fork := fork) hsize96 hf2 (by rw [hn]; intro h; exact hh h.1)
      have hrev := execBlock_append_term (s2 := [delegatedAttestRecordStmt])
        (execBlock_append (execBlock_append hbegin hc) ha) (by intros;exact nofun)
      exact ⟨fun h => False.elim (hh h.2),fun _ => hrev⟩
  · have hc : ExecBlock fork config {contract := contract,locals := L1,immutables := imms} evm delegatedAttestCopy .reverted :=
      ExecBlock.consRevert (hcopy.2 hv)
    have hrev := execBlock_append_term (s2 := allocateBlock (.intLit 96) ++ [delegatedAttestRecordStmt])
      (execBlock_append hbegin hc) (by intros;exact nofun)
    exact ⟨fun h => False.elim (hv h.1),fun _ => by simpa only [delegatedAttestPrefix,List.append_assoc] using hrev⟩

theorem delegatedAttestDataSource {L imms : Store} {evm : EVM.State} {r : DelegatedAttestationRecord}
    (hr : L.get? "delegatedRequest" = some r.struct) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm delegatedAttestDataBlock
      (.ok {contract := contract,locals := delegatedAttestDataLocals L r.data,immutables := imms} evm) := by
  have hd : defaultValue? requestDataType = .ok defaultRequestRecord.struct := by native_decide
  have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.newArray requestDataType (.intLit 1)) = .ok (.array [defaultRequestRecord.struct]) := by
    simp only [evalExpr?,pure,bind,EvalResult.bind,show ¬ (1 : Int) < 0 by decide,if_false,hd]
    rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl he)
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := r.data.tuple) ?_ ?_) ExecBlock.nil
  · apply evalRecordField (record := r.struct) ?_ rfl
    simp only [evalExpr?,store_get_ne _ _ (by decide : ("data" == "delegatedRequest") = false),hr,EvalResult.ofOption]
  · exact assignLocalArrayExpr (cfg := config) (evm := evm)
      (frame := {contract := contract,locals := L.insert "data" (.array [defaultRequestRecord.struct]),immutables := imms})
      (name := "data") (values := [defaultRequestRecord.struct]) (index := .intLit 0) (i := 0) (value := r.data.tuple)
      (store_get_self _ _ _) (by simp only [evalExpr?,pure]; rfl) (by simp)

end Benchmarks.EAS.EAS
