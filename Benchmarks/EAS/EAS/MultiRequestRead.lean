import Benchmarks.EAS.EAS.BatchRowRead

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiAttestReadLocals (L : Store) (last : Bool) (row : Value) : Store :=
  (L.insert "last" (.bool false)).insert "last" (.bool last) |>.insert "multiRequest" row

def multiRequestRead (ty : ABIType) : Body := [
  .letDecl "last" (some (.elem .bool)) (.boolLit false),
  .assign .localVar {base := "last"} multiAttestLast,
  .letDecl "multiRequest" (some ty) (.index (.var "multiRequests") (.var "i"))]

-- LIBRARY CANDIDATE: read one batch row and compute the last-row flag, independent of row type.
theorem multiRequestReadSource {L imms : Store} {evm : EVM.State} {requests : List Value}
    {i : Nat} (ty : ABIType)
    (hrequests : L.get? "multiRequests" = some (.array requests))
    (hindex : L.get? "i" = some (.int (Int.ofNat i))) (hi : i < requests.length)
    (hlen : requests.length < UInt256.size) (hnorm : normalizeRawBoolWord? requests[i] = .ok requests[i]) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm (multiRequestRead ty)
      (.ok {contract := contract,locals := multiAttestReadLocals L (decide (i=requests.length-1)) requests[i],immutables := imms} evm) := by
  exact batchRowReadSource ty "multiRequests" "multiRequest" (by decide) hrequests hindex hi hlen hnorm

theorem multiRequestCheck_ok {L imms : Store} {evm : EVM.State} {fields : List Value}
    (h : L.get? "multiRequest" = some (.tuple fields)) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm multiAttestCheck
      (.ok {contract := contract,locals := L,immutables := imms} evm) := by
  apply ExecStmt.requireTrue
  simp only [evalExpr?,h,EvalResult.ofOption,bind,EvalResult.bind,pure,evalStructFields?,multiAttestCheck]
  rfl

theorem multiRequestCheck_bad {L imms : Store} {evm : EVM.State}
    (h : L.get? "multiRequest" = some ABI.Solc08Calldata.decodeFailure) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm multiAttestCheck .reverted := by
  apply ExecStmt.requireFalse
  simp only [evalExpr?,h,EvalResult.ofOption,bind,EvalResult.bind,pure,evalStructFields?,multiAttestCheck]
  rfl

end Benchmarks.EAS.EAS
