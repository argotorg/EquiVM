import Benchmarks.EAS.EAS.MultiDelegatedAttestLocals

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem multiDelegatedAttestAllocateSource {L imms : Store} {evm : EVM.State} {requests : List Value} {heap : Nat}
    (hd : L.get? "multiDelegatedRequests" = some (.array requests))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hlen : requests.length ≤ 2^64-1) :
    let next := allocateNext heap (32+32*requests.length)
    if next ≤ 2^64-1 ∧ heap ≤ next then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestAllocate
        (.ok {contract := contract,locals := multiAttestInitialLocals L requests.length next evm.executionEnv.weiValue,immutables := imms} evm) ∧
      MultiDelegatedAttestLocals (multiAttestInitialLocals L requests.length next evm.executionEnv.weiValue)
        requests (List.replicate requests.length []) evm.executionEnv.weiValue next 0
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedAttestAllocate .reverted := by
  dsimp only
  have hd' (next : Nat) : (allocateBlockLocals L next).get? "multiDelegatedRequests"=some (.array requests) := by
    simpa (disch := decide) only [allocateBlockLocals_get] using hd
  have hs := batchAttestAllocateSource (fork := fork) (length := multiDelegatedAttestLength) (evalLocalArrayLength (cfg := config) (stele := {contract := contract,locals := L,immutables := imms}) (evm := evm) hd)
    (fun next => evalLocalArrayLength (hd' next)) hh hlen
  dsimp only at hs
  split <;> rename_i hg
  · rw [if_pos hg] at hs
    refine ⟨hs,?_⟩
    constructor
    · simpa (disch := decide) only [multiAttestInitialLocals,store_get_ne] using hd' _
    · simp (disch := decide) only [multiAttestInitialLocals,store_get_self,store_get_ne]
    · simp (disch := decide) only [multiAttestInitialLocals,store_get_self,store_get_ne,List.flatten_replicate_nil,List.length_nil,Int.ofNat_eq_natCast,Nat.cast_zero]
    · simp (disch := decide) only [multiAttestInitialLocals,store_get_self,store_get_ne]
    · simp (disch := decide) only [multiAttestInitialLocals,allocateBlockLocals,unpackHeapLocals,store_get_self,store_get_ne]
    · exact store_get_self _ _ _
  · simpa only [if_neg hg] using hs

end Benchmarks.EAS.EAS
