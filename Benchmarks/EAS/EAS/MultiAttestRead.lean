import Benchmarks.EAS.EAS.MultiRequestRead

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem MultiAttestLocals.read {L : Store} {requests : List Value} {groups : List (List UInt256)}
    {available : UInt256} {heap i : Nat} (h : MultiAttestLocals L requests groups available heap i)
    (last : Bool) (row : Value) :
    MultiAttestLocals (multiAttestReadLocals L last row) requests groups available heap i := by
  constructor <;> simp (disch := decide) only [multiAttestReadLocals,store_get_ne] <;>
    first | exact h.requests | exact h.groups | exact h.count | exact h.available | exact h.heap | exact h.index

theorem multiAttestReadSource {L imms : Store} {evm : EVM.State} {requests : List Value}
    {groups : List (List UInt256)} {available : UInt256} {heap i : Nat}
    (h : MultiAttestLocals L requests groups available heap i) (hi : i < requests.length)
    (hlen : requests.length < UInt256.size) (hnorm : normalizeRawBoolWord? requests[i] = .ok requests[i]) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiAttestRead
      (.ok {contract := contract,locals := multiAttestReadLocals L (decide (i=requests.length-1)) requests[i],immutables := imms} evm) := by
  exact multiRequestReadSource multiRequestABI h.requests h.index hi hlen hnorm

theorem multiAttestCheck_ok {L imms : Store} {evm : EVM.State} {schema : UInt256} {rs : List AttestationRequestRecord}
    (h : L.get? "multiRequest" = some (multiRequestTuple schema rs)) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm multiAttestCheck
      (.ok {contract := contract,locals := L,immutables := imms} evm) := by
  exact multiRequestCheck_ok h

theorem multiAttestCheck_bad {L imms : Store} {evm : EVM.State}
    (h : L.get? "multiRequest" = some ABI.Solc08Calldata.decodeFailure) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm multiAttestCheck .reverted := by
  exact multiRequestCheck_bad h

end Benchmarks.EAS.EAS
