import Benchmarks.Morpho.MorphoBlue.AuthorizationSigRecoveryMemory
import Benchmarks.Morpho.MorphoBlue.EcrecoverFacts
import Benchmarks.Morpho.MorphoBlue.StaticCallBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def authorizationRecoveryExpr : Expr := .abiEncodePacked [
  (abiBytes32, .var "digest"), (abiUInt256, .tupleGet (.var "signature") 0),
  (abiBytes32, .tupleGet (.var "signature") 1), (abiBytes32, .tupleGet (.var "signature") 2)]

theorem evalAuthorizationRecoveryInput (v : MorphoImmutables) (a : AuthorizationWords)
    (cd : ByteArray) (locals imms : Store) (evm : EVM.State)
    (hd : locals.get? "digest" = some (wordBytes32Value (authorizationDigest v a)))
    (hs : locals.get? "signature" = some (signatureValue cd)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      authorizationRecoveryExpr = .ok (.bytes (returnWordBytes (authorizationRecoveryWords v a cd))) := by
  have h0 : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "digest") = .ok (wordBytes32Value (authorizationDigest v a)) := by
    simp only [evalExpr?, hd, EvalResult.ofOption]
  have h1 : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "signature") 0) = .ok (.int (Int.ofNat (signatureRecoveryWord cd).toNat)) := by
    simp only [evalExpr?, hs, signatureValue, bind, EvalResult.bind, EvalResult.ofOption, tupleGetValue?]; rfl
  have h2 : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "signature") 1) = .ok (wordBytes32Value (calldataWord cd 196)) := by
    simp only [evalExpr?, hs, signatureValue, bind, EvalResult.bind, EvalResult.ofOption, tupleGetValue?]; rfl
  have h3 : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "signature") 2) = .ok (wordBytes32Value (calldataWord cd 228)) := by
    simp only [evalExpr?, hs, signatureValue, bind, EvalResult.bind, EvalResult.ofOption, tupleGetValue?]; rfl
  have hp := evalPackedArgs_cons h0 (encodePacked_bytes32 _)
    (evalPackedArgs_cons h1 (encodePacked_uint256 _)
      (evalPackedArgs_cons h2 (encodePacked_bytes32 _)
        (evalPackedArgs_single h3 (encodePacked_bytes32 _))))
  have he : evalPackedArgs? config { contract := contract, locals := locals, immutables := imms } evm
      [(abiBytes32, .var "digest"), (abiUInt256, .tupleGet (.var "signature") 0),
        (abiBytes32, .tupleGet (.var "signature") 1), (abiBytes32, .tupleGet (.var "signature") 2)] =
      .ok (returnWordBytes (authorizationRecoveryWords v a cd)).toList := by
    simpa only [returnWordBytes_toList, authorizationRecoveryWords, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc] using hp
  simp only [authorizationRecoveryExpr, evalExpr?, he, bind, EvalResult.bind, pure]
  congr 2
  apply byteArray_eq_of_toList_eq
  simp only [byteArray_toList_eq, List.toList_toArray]

def authorizationRecoveredLocals (locals : Store) (z : Bool) (out : ByteArray) : Store :=
  (locals.insert "success" (.bool z)).insert "recovered" (.bytes out)

theorem morphoAuthorizationRecoverySource (v : MorphoImmutables) (a : AuthorizationWords)
    (cd : ByteArray) (locals imms : Store) (evm evm' : EVM.State) (z : Bool) (out : ByteArray)
    (hd : locals.get? "digest" = some (wordBytes32Value (authorizationDigest v a)))
    (hs : locals.get? "signature" = some (signatureValue cd))
    (hp : locals.get? "precompile" = some (.address (AccountAddress.ofNat 1)))
    (hc : callViaEVM evm (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) 0
      (returnWordBytes (authorizationRecoveryWords v a cd)) (z, evm', out) false) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      setAuthorizationWithSigTransition.body[18]!
      (.ok {
        contract := contract, locals := authorizationRecoveredLocals locals z out,
        immutables := imms } evm') := by
  have ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "precompile") = .ok (.address (AccountAddress.ofNat 1)) := by
    simp only [evalExpr?, hp, EvalResult.ofOption]
  have hv : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.intLit 0) = .ok (.int 0) := by simp only [evalExpr?, pure]
  have hi := evalAuthorizationRecoveryInput v a cd locals imms evm hd hs
  cases z
  · exact ExecStmt.lowLevelCallFailure ht hv hi (by simpa only [eVM_address_id] using hc)
  · exact ExecStmt.lowLevelCallSuccess ht hv hi (by simpa only [eVM_address_id] using hc)


theorem morphoAuthorizationRecoveryCall {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {rdata : ByteArray} {aw gasArg : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (a : AuthorizationWords)
    (hs : SourceState s0 ee σ evm) (hstack : R.length + 24 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6409)
      ([gasArg, UInt256.ofNat 1, UInt256.ofNat 768, UInt256.ofNat 128,
        UInt256.ofNat 0, UInt256.ofNat 32] ++ authorizationRecoveryTail R)
      (authorizationRecoveryMem v a ee.calldata) aw rdata σ k C) :
    ∃ evm' z out aw' k' C',
      callViaEVM evm (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) 0
        (returnWordBytes (authorizationRecoveryWords v a ee.calldata)) (z, evm', out) false ∧
      SourceState s0 ee evm'.accountMap evm' ∧ EcrecoverOutput out ∧
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 6410)
        ((if z then ⟨1⟩ else ⟨0⟩) :: authorizationRecoveryTail R)
        (callOutputMem (authorizationRecoveryMem v a ee.calldata) out (UInt256.ofNat 0) (UInt256.ofNat 32))
        aw' out evm'.accountMap k' C' := by
  obtain ⟨evm', σ', z, out, k', C', hcall, hs', rd, hout⟩ := staticCallBridge h hs
    (by immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨6409⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64))
    (authorizationRecoveryMem_properties v a ee.calldata).2.2.2
    (by rw [returnWordBytes_size]; change 128 ≤ Ethereum.EVM.maxReturnDataSizeByGas; decide)
    (by simp [authorizationRecoveryTail]; omega)
  rw [hs'.accounts] at rd
  rw [show UInt256.ofNat 6409 + (⟨1⟩ : UInt256) = UInt256.ofNat 6410 by decide] at rd
  exact ⟨evm', z, out, _, k', C', hcall, ⟨hs'.world, hs'.env, rfl⟩,
    callViaEVM_ecrecover_output_shape hcall, rd⟩

end Benchmarks.Morpho.MorphoBlue
