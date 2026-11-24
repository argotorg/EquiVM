import Benchmarks.EAS.EAS.CopyStoredSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def getAttestationReturnExpr : Expr := .tupleLit [
  .field (.var "attestation") "uid", .field (.var "attestation") "schema",
  .field (.var "attestation") "time", .field (.var "attestation") "expirationTime",
  .field (.var "attestation") "revocationTime", .field (.var "attestation") "refUID",
  .field (.var "attestation") "recipient", .field (.var "attestation") "attester",
  .field (.var "attestation") "revocable", .field (.var "attestation") "data"]

def getAttestationTuple (evm : EVM.State) (word : UInt256) : Value :=
  .tuple ((attestationStoredFields evm (dbSlot word)).map Prod.snd ++ [.bytes (attestationPayload evm word)])

def getAttestationTail : Body := [
  .internalCall "_copyStoredAttestation" [.var "uid", .var "$EAS.freeMemory"] "attestation$allocation",
  .letDecl "attestation" none (.tupleGet (.var "attestation$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "attestation$allocation") 1),
  .return [getAttestationReturnExpr]]

theorem getAttestation_body : getAttestationTransition.body = easEntryPrefix ++
    (allocateBlock (.intLit 320) ++ getAttestationTail) := by native_decide

theorem getAttestationReturn_eval {evm : EVM.State} {frame : Frame} {word : UInt256}
    (ha : frame.locals.get? "attestation" = some (attestationValue evm word (.bytes (attestationPayload evm word)))) :
    evalExpr? config frame evm getAttestationReturnExpr = .ok (getAttestationTuple evm word) := by
  simp only [getAttestationReturnExpr, evalExpr?, evalExprList?, ha, EvalResult.ofOption, EvalResult.bind, bind, pure,
    getAttestationTuple, attestationValue, attestationStoredFields, List.append_nil,
    List.cons_append, List.nil_append, List.map_cons, List.map_nil, lookupField?]
  rfl

def getAttestationFinalLocals (locals : Store) (evm : EVM.State) (word : UInt256) : Store :=
  unpackHeapLocals
    (locals.insert "attestation$allocation" (.tuple [attestationValue evm word (.bytes (attestationPayload evm word)),
      .int (Int.ofNat (copyStoredNext 544 (attestationPayload evm word)))]))
    "attestation" "$EAS.freeMemory" (attestationValue evm word (.bytes (attestationPayload evm word)))
    (copyStoredNext 544 (attestationPayload evm word))

theorem getAttestationTail_ok {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hk : locals.get? "uid" = some (wordBytes32Value word))
    (hh : locals.get? "$EAS.freeMemory" = some (.int 544))
    (hv : copyStoredValid evm word 544) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm getAttestationTail
      (.returned {contract := contract, locals := getAttestationFinalLocals locals evm word, immutables := imms}
        evm (some [getAttestationTuple evm word])) := by
  refine ExecBlock.consNormal (copyStoredCall_ok (heap := 544)
    (by simp only [evalExprs?, evalExpr?, hk, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]; rfl) hv) ?_
  apply execBlock_append (unpackHeapResult (result := "attestation") (cursor := "$EAS.freeMemory")
    (tmp := "attestation$allocation") (store_get_self _ _ _)
    (by simpa only [store_get_ne _ _ (by decide : ("attestation$allocation" == "$EAS.freeMemory") = false)] using hh)
    (by decide) (by decide))
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have ha : (getAttestationFinalLocals locals evm word).get? "attestation" =
      some (attestationValue evm word (.bytes (attestationPayload evm word))) := by
    simp only [getAttestationFinalLocals, unpackHeapLocals,
      store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "attestation") = false), store_get_self]
  change evalExprs? config {contract := contract, locals := getAttestationFinalLocals locals evm word, immutables := imms}
    evm [getAttestationReturnExpr] = _
  simp only [evalExprs?, getAttestationReturn_eval (evm := evm) (word := word)
    (frame := {contract := contract, locals := getAttestationFinalLocals locals evm word, immutables := imms}) ha, EvalResult.bind, bind, pure]

theorem getAttestationTail_revert {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hk : locals.get? "uid" = some (wordBytes32Value word))
    (hh : locals.get? "$EAS.freeMemory" = some (.int 544))
    (hv : ¬ copyStoredValid evm word 544) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm getAttestationTail .reverted := by
  exact ExecBlock.consRevert (copyStoredCall_revert (heap := 544)
    (by simp only [evalExprs?, evalExpr?, hk, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]; rfl) hv)

def getAttestationPrefixLocals (locals : Store) (evm : EVM.State) : Store :=
  allocateBlockLocals (easEntryLocals locals evm.executionEnv.calldata) 544

theorem getAttestationPrefix_ok {evm : EVM.State} {locals imms : Store}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size) (hguard : evm.executionEnv.calldata.size - 4 < 2^255) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm
      (easEntryPrefix ++ allocateBlock (.intLit 320))
      (.ok {contract := contract, locals := getAttestationPrefixLocals locals evm, immutables := imms} evm) := by
  apply execBlock_append (easEntryPrefix_ok hvalue hsz hsize hguard)
  exact allocateBlock_ok (n := 320) (heap := 224) (by simp only [evalExpr?, pure]; rfl)
    (by simp only [easEntryLocals, store_get_ne _ _ (by decide : ("__calldata" == "$EAS.freeMemory") = false), store_get_self]; rfl)
    (by decide)

theorem getAttestationPrefix_uid {evm : EVM.State} {locals : Store} {word : UInt256}
    (hk : locals.get? "uid" = some (wordBytes32Value word)) :
    (getAttestationPrefixLocals locals evm).get? "uid" = some (wordBytes32Value word) := by
  rw [getAttestationPrefixLocals, allocateBlockLocals_get (by decide) (by decide) (by decide)]
  simp only [easEntryLocals, store_get_ne _ _ (by decide : ("__calldata" == "uid") = false),
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "uid") = false), hk]

theorem getAttestationSource_ok {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hk : locals.get? "uid" = some (wordBytes32Value word))
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size) (hguard : evm.executionEnv.calldata.size - 4 < 2^255)
    (hv : copyStoredValid evm word 544) :
    ExecTransitionBody fork config contract evm locals getAttestationTransition.body
      (.returned {contract := contract, locals := getAttestationFinalLocals (getAttestationPrefixLocals locals evm) evm word, immutables := imms}
        evm (some [getAttestationTuple evm word])) imms := by
  rw [getAttestation_body, ← List.append_assoc]
  apply ExecFuncBody.execBlockRet
  apply execBlock_append (getAttestationPrefix_ok hvalue hsz hsize hguard)
  exact getAttestationTail_ok (getAttestationPrefix_uid hk) (store_get_self _ _ _) hv

theorem getAttestationSource_revert {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hk : locals.get? "uid" = some (wordBytes32Value word))
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩) (hsz : 4 ≤ evm.executionEnv.calldata.size)
    (hsize : evm.executionEnv.calldata.size < UInt256.size) (hguard : evm.executionEnv.calldata.size - 4 < 2^255)
    (hv : ¬ copyStoredValid evm word 544) :
    ExecTransitionBody fork config contract evm locals getAttestationTransition.body .reverted imms := by
  rw [getAttestation_body, ← List.append_assoc]
  apply ExecFuncBody.execBlockRevert
  apply execBlock_append (getAttestationPrefix_ok hvalue hsz hsize hguard)
  exact getAttestationTail_revert (getAttestationPrefix_uid hk) (store_get_self _ _ _) hv

end Benchmarks.EAS.EAS
