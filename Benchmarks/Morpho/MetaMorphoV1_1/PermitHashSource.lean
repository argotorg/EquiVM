import Benchmarks.Morpho.MetaMorphoV1_1.NonceSource
import Benchmarks.Morpho.MetaMorphoV1_1.TypedDataHashSource

/-! The six packed words authenticated by a permit signature. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def permitTypeHash : UInt256 :=
  ⟨49955707469362902507454157297736832118868343942642399513960811609542965143241⟩

def permitStructWords (owner spender : AccountAddress) (value nonce deadline : UInt256) :
    List UInt256 :=
  [permitTypeHash, UInt256.ofNat owner.toNat, UInt256.ofNat spender.toNat, value, nonce, deadline]

def permitStructHash (owner spender : AccountAddress) (value nonce deadline : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (wordBytes (permitStructWords owner spender value nonce deadline)))

def permitTypeHashExpr : Expr :=
  .fixedBytesLit abiBytes32Width
    [110, 113, 237, 174, 18, 177, 185, 127, 77, 31, 96, 55, 15, 239, 16, 16,
      95, 162, 250, 174, 1, 38, 17, 74, 22, 156, 100, 132, 93, 97, 38, 201]

def permitStructHashExpr : Expr :=
  .keccak256 (.abiEncodePacked
    [(abiBytes32, permitTypeHashExpr),
      (abiUInt256, .cast (.var "owner") (.elem (.int (.uint ⟨256, by decide⟩)))),
      (abiUInt256, .cast (.var "spender") (.elem (.int (.uint ⟨256, by decide⟩)))),
      (abiUInt256, .var "value"), (abiUInt256, .var "__c0"), (abiUInt256, .var "deadline")])

theorem permitStructHashSource {evm : State} {frame : Frame} {owner spender : AccountAddress}
    {value nonce deadline : UInt256}
    (ho : frame.locals.get? "owner" = some (.address owner))
    (hsp : frame.locals.get? "spender" = some (.address spender))
    (hv : frame.locals.get? "value" = some (uint256Value value))
    (hn : frame.locals.get? "__c0" = some (uint256Value nonce))
    (hd : frame.locals.get? "deadline" = some (uint256Value deadline)) :
    evalExpr? config frame evm permitStructHashExpr =
      .ok (wordBytes32Value (permitStructHash owner spender value nonce deadline)) := by
  have ht : evalExpr? config frame evm permitTypeHashExpr =
      .ok (wordBytes32Value permitTypeHash) := by
    simp only [permitTypeHashExpr, evalExpr?, pure]
    native_decide
  have howner := evalExpr_addressToWord
    (show evalExpr? config frame evm (.var "owner") = .ok (.address owner) by
      simp only [evalExpr?, ho, EvalResult.ofOption])
  have hspender := evalExpr_addressToWord
    (show evalExpr? config frame evm (.var "spender") = .ok (.address spender) by
      simp only [evalExpr?, hsp, EvalResult.ofOption])
  have hvalue : evalExpr? config frame evm (.var "value") = .ok (uint256Value value) := by
    simp only [evalExpr?, hv, EvalResult.ofOption]
  have hnonce : evalExpr? config frame evm (.var "__c0") = .ok (uint256Value nonce) := by
    simp only [evalExpr?, hn, EvalResult.ofOption]
  have hdeadline : evalExpr? config frame evm (.var "deadline") = .ok (uint256Value deadline) := by
    simp only [evalExpr?, hd, EvalResult.ofOption]
  have hpack := evalExpr_packed (evalPackedArgs_cons ht (encodePacked_bytes32 permitTypeHash)
    (evalPackedArgs_cons howner (encodePacked_uint256 (UInt256.ofNat owner.toNat))
      (evalPackedArgs_cons hspender (encodePacked_uint256 (UInt256.ofNat spender.toNat))
        (evalPackedArgs_cons hvalue (encodePacked_uint256 value)
          (evalPackedArgs_cons hnonce (encodePacked_uint256 nonce)
            (evalPackedArgs_cons (args := []) (tail := []) hdeadline
              (encodePacked_uint256 deadline) (by simp only [evalPackedArgs?, pure])))))))
  apply evalExpr_keccakWord
  simpa only [permitStructHash, permitStructWords, wordBytes, List.toByteArray_append,
    List.append_nil, word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_empty] using hpack

end Benchmarks.Morpho.MetaMorphoV1_1
