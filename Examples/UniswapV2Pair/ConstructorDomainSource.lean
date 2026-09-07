import Examples.UniswapV2Pair.ConstructorDomainHashRuntime
import Examples.UniswapV2Pair.PackedWordSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

theorem constructorTypeHashWord_bytes :
    constructorTypeHashWord.toByteArray = ffi.KEC eip712DomainTypehashBytes := by
  have h := toBytesBE_keccak_uInt256OfByteArray eip712DomainTypehashBytes
  rw [← keccakSlot_eq, word_toBytesBE_eq_toByteArray_toList] at h
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [byteArray_toList_eq] using h

theorem evalExpr_constructor_hashLiteral {caller : Frame} (evm : EVM.State)
    (bytes : ByteArray) (word : UInt256) (h : ffi.KEC bytes = word.toByteArray) :
    evalExpr? config caller evm (.keccak256 (.bytesLit bytes)) =
      .ok (permitWordBytes32Value word) := by
  simp only [evalExpr?, EvalResult.bind, bind, pure, h, permitWordBytes32Value,
    word_toBytesBE_eq_toByteArray_toList, bytes32Width]

theorem evalExpr_constructor_thisWord {caller : Frame} (evm : EVM.State) :
    evalExpr? config caller evm (addressAsUint256 this) =
      .ok (uniswapUint256Value (UInt256.ofNat evm.executionEnv.codeOwner.val)) := by
  have hlt : evm.executionEnv.codeOwner.val < EVM.twoPow 256 :=
    lt_trans evm.executionEnv.codeOwner.isLt (by decide)
  simp only [addressAsUint256, this, evalExpr?, envValue, EvalResult.bind, bind, pure,
    castValue?, uint256St, uint256Int, Fin.toNat, if_pos hlt, EvalResult.ofOption,
    uniswapUint256Value, uint256Value]
  rw [UInt256.toNat_ofNat_of_lt hlt]

theorem evalPackedArgs_constructor_domain {caller : Frame} (evm : EVM.State) :
    evalPackedArgs? config caller evm
      [(bytes32, eip712DomainTypehashExpr), (bytes32, nameHashExpr), (bytes32, versionHashExpr),
        (uint256, .env .chainid), (uint256, addressAsUint256 this)] =
      .ok (constructorDomainBytes constructorTypeHashWord
        (UInt256.ofNat evm.executionEnv.codeOwner.val)).toList := by
  simp only [constructorDomainBytes, byteArray_toList_append,
    ← word_toBytesBE_eq_toByteArray_toList, List.append_assoc]
  refine permitEvalPackedArgs_cons
    (evalExpr_constructor_hashLiteral evm _ _ constructorTypeHashWord_bytes.symm)
    (permitEncodePacked_bytes32 _) ?_
  refine permitEvalPackedArgs_cons
    (evalExpr_constructor_hashLiteral evm _ _ constructorNameHash)
    (permitEncodePacked_bytes32 _) ?_
  refine permitEvalPackedArgs_cons
    (evalExpr_constructor_hashLiteral evm _ _ constructorVersionHash)
    (permitEncodePacked_bytes32 _) ?_
  refine permitEvalPackedArgs_cons (v := uniswapUint256Value ⟨1⟩)
    (by
      simp only [evalExpr?, envValue, pure, uniswapUint256Value, uint256Value, Ethereum.chainId]
      rfl)
    (permitEncodePacked_uint256 _) ?_
  exact permitEvalPackedArgs_single (evalExpr_constructor_thisWord evm)
    (permitEncodePacked_uint256 _)

theorem evalExpr_constructor_domain {caller : Frame} (evm : EVM.State) :
    evalExpr? config caller evm domainSeparatorExpr =
      .ok (permitWordBytes32Value
        (constructorDomainHashWord (UInt256.ofNat evm.executionEnv.codeOwner.val))) := by
  rw [domainSeparatorExpr, evalExpr?, evalExpr?]
  simp only [evalPackedArgs_constructor_domain, EvalResult.bind, bind, byteArray_mk_toList_toArray]
  simp only [permitWordBytes32Value, constructorDomainHashWord]
  rw [keccakSlot_eq, toBytesBE_keccak_uInt256OfByteArray]
  rfl

end UniswapV2Pair
