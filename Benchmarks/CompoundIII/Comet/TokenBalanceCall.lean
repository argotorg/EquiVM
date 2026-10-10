import Benchmarks.CompoundIII.Comet.StaticCallBridge
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def tokenBalancePayload (owner : AccountAddress) : ByteArray :=
  ⟨([112, 160, 130, 49] ++ EVM.Word.toBytesBE (EVM.word owner.val)).toArray⟩

theorem tokenBalancePayload_size (owner : AccountAddress) :
    (tokenBalancePayload owner).size = 36 := by
  have hl : (EVM.Word.toBytesBE (EVM.word owner.val)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (EVM.word owner.val)
  change ([112, 160, 130, 49] ++ EVM.Word.toBytesBE (EVM.word owner.val)).toArray.size = 36
  simp only [List.size_toArray, List.length_append, List.length_cons, List.length_nil, hl]

theorem tokenBalancePayload_encode (I : ExecutionEnv) :
    config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some (tokenBalancePayload I.codeOwner) := by
  change encodeCallWithSelector? (selectorBytes 112 160 130 49)
    [abiAddress] [.address I.codeOwner] = _
  unfold encodeCallWithSelector?
  rw [encodeABIValues?, abiTupleHeadSize_scalarWords_eq (by decide)]
  simp only [bind, Option.bind]
  rw [encodeABIValuesFrom?, encodeABIValue_this_address]
  simp only [isDynamicABIType, Bool.false_eq_true, if_false, bind, Option.bind]
  rw [encodeABIValuesFrom?]
  simp only [bind, Option.bind, List.append_nil, List.nil_append]
  rw [toByteArray_eq_toBytesBE]
  congr 1
  apply ByteArray.ext
  simp [tokenBalancePayload, selectorBytes, byteArray_toList_eq, List.append_toArray]

theorem tokenBalance_decode_ok {out : ByteArray} (hlo : 32 ≤ out.size)
    (hhi : out.size < 2^255) :
    config.externalABI.decode? "balanceOf" out =
      some [.int (Int.ofNat (calldataWord out 0).toNat)] := by
  change (decodeReturnValue? abiUInt256 out).map (fun v ↦ [v]) = _
  rw [decodeReturnUint_long hlo hhi]
  rfl

theorem tokenBalance_decode_short {out : ByteArray} (hlo : out.size < 32) :
    config.externalABI.decode? "balanceOf" out = none := by
  change (decodeReturnValue? abiUInt256 out).map (fun v ↦ [v]) = _
  rw [decodeReturnUint_short hlo]
  rfl

theorem tokenBalance_typed {evm evm' : EVM.State} {asset : AccountAddress}
    {z : Bool} {out : ByteArray}
    (hc : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (z, evm', out) false) :
    typedCallViaEVM config evm asset "balanceOf" 0 [.address evm.executionEnv.codeOwner]
      (z, evm', out) false := ⟨_, tokenBalancePayload_encode _, hc⟩

theorem tokenBalance_source_ok {frame : Frame} {evm evm' : EVM.State}
    {asset : AccountAddress} {expr : Expr} {ret : Ident} {out : ByteArray}
    (he : evalExpr? config frame evm expr = .ok (.address asset))
    (hc : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (true, evm', out) false) (hlo : 32 ≤ out.size) (hhi : out.size < 2^255) :
    ExecStmt config frame evm (.externalCall expr "balanceOf" (.intLit 0) [.env .this] ret
      (perm := false))
      (.ok { frame with locals :=
        frame.locals.insert ret (.int (Int.ofNat (calldataWord out 0).toNat)) } evm') := by
  rw [← addressOfAddress asset] at hc
  exact ExecStmt.externalCallSuccess he (by simp only [evalExpr?, pure])
    (by simp only [evalExprs?, evalExpr?, envValue, bind, EvalResult.bind, pure])
    (tokenBalance_typed hc) (tokenBalance_decode_ok hlo hhi)

theorem tokenBalance_source_revert {frame : Frame} {evm evm' : EVM.State}
    {asset : AccountAddress} {expr : Expr} {ret : Ident} {z : Bool} {out : ByteArray}
    (he : evalExpr? config frame evm expr = .ok (.address asset))
    (hc : callViaEVM evm asset 0 (tokenBalancePayload evm.executionEnv.codeOwner)
      (z, evm', out) false) (hv : ¬ (z = true ∧ 32 ≤ out.size)) :
    ExecStmt config frame evm (.externalCall expr "balanceOf" (.intLit 0) [.env .this] ret
      (perm := false)) .reverted := by
  rw [← addressOfAddress asset] at hc
  cases z with
  | false =>
      exact ExecStmt.externalCallFailure he (by simp only [evalExpr?, pure])
        (by simp only [evalExprs?, evalExpr?, envValue, bind, EvalResult.bind, pure])
        (tokenBalance_typed hc)
  | true =>
      exact ExecStmt.externalCallReturnDecodeRevert he (by simp only [evalExpr?, pure])
        (by simp only [evalExprs?, evalExpr?, envValue, bind, EvalResult.bind, pure])
        (tokenBalance_typed hc)
        (tokenBalance_decode_short (Nat.lt_of_not_ge (fun h ↦ hv ⟨rfl, h⟩)))

end Benchmarks.CompoundIII.Comet
