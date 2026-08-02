import Examples.Ripemd160.SolmHashTail

/-!
# RIPEMD-160 Solm hash function

Composition of the source initialization, outer compression loop, and final digest return.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Ripemd160

def hashBody : List Stmt := hashPrelude ++ [compressionBlockFor] ++ hashTail

theorem hashFunction_body : hashFunction.body = hashBody := by
  rfl

def hashLocals (data : ByteArray) : Store :=
  (∅ : Store).insert "data" (.bytes data)

@[simp] theorem hashLocals_data (data : ByteArray) :
    (hashLocals data).get? "data" = some (.bytes data) := by
  simp [hashLocals]

theorem hashFunction_bindParams (data : ByteArray) :
    bindParams? hashFunction.params [.bytes data] = some (hashLocals data) := by
  rfl

theorem hashFunctionBodyReturns (evm : EVM.State) (data : ByteArray)
    (hsmall : data.size ≤ maxFallbackCalldataSize) :
    let final := sourceChainRun data (Model.paddedLength data.size / 64) runtimeInitialChain
    ∃ L', ExecFuncBody config { contract := contract, locals := hashLocals data } evm
        hashFunction.body
        (.returned { contract := contract, locals := L' } evm
          (some [digestBytes20 final])) := by
  dsimp only
  obtain ⟨hprelude, hchain0, hbound0, hdata0, hbit0, hpad0, hnum0, hwords0,
    hmask0⟩ := hashPreludeReturns evm data (hashLocals_data data)
  obtain ⟨L1, hloop, hchain1, hbound1, _, _, _, _, _, _, _⟩ :=
    compressionBlockForReturns evm data runtimeInitialChain hsmall hbound0 hdata0 hbit0
      hpad0 hnum0 hwords0 hmask0 hchain0
  obtain ⟨L2, htail, _⟩ := hashTailReturns evm
    (sourceChainRun data (Model.paddedLength data.size / 64) runtimeInitialChain)
    hchain1 hbound1
  have hloopBlock : ExecBlock config
      { contract := contract, locals := hashPreludeStore (hashLocals data) data } evm
      [compressionBlockFor] (.ok { contract := contract, locals := L1 } evm) :=
    ExecBlock.consNormal hloop ExecBlock.nil
  have hthroughLoop := execBlock_append hprelude hloopBlock
  have hbody := execBlock_append hthroughLoop htail
  refine ⟨L2, ExecFuncBody.execBlockRet ?_⟩
  rw [hashFunction_body]
  simpa only [hashBody, List.append_assoc] using hbody

end Ripemd160
