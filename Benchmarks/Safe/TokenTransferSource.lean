import Benchmarks.Safe.PreModuleCallEncoding
import Benchmarks.Safe.P256Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure TokenTransferInput where
  token : EVM.Address
  receiver : EVM.Address
  amount : UInt256

namespace TokenTransferInput

def args (p : TokenTransferInput) : Store :=
  (((∅ : Store).insert "amount" (uint256Value p.amount)).insert
    "receiver" (.address p.receiver)).insert "token" (.address p.token)

def frame (p : TokenTransferInput) : Frame := { contract := contract, locals := p.args }

def callBytes (p : TokenTransferInput) : ByteArray :=
  transferSelector ++ (UInt256.ofNat p.receiver.val).toByteArray ++ p.amount.toByteArray

def finalFrame (p : TokenTransferInput) (z : Bool) (out : ByteArray) : Frame :=
  { p.frame with
    locals := (p.args.insert "tokenSuccess" (.bool z)).insert "tokenData" (.bytes out) }

end TokenTransferInput

def tokenTransferResult (z : Bool) (out : ByteArray) : Bool :=
  if out.size = 0 then z else if out.size = 32 then z && decide (calldataWord out 0 ≠ ⟨0⟩)
  else false

theorem tokenTransferCallEncoding (p : TokenTransferInput) :
    config.externalABI.encode? "transfer" [.address p.receiver, uint256Value p.amount] =
      some p.callBytes := by
  have hr := encodeABIValue_address_ofUInt256_of_canonical (UInt256.ofNat p.receiver.val)
    (by rw [ulit_toNat' _ (lt_trans p.receiver.isLt (by decide))]; exact p.receiver.isLt)
  rw [accountAddress_roundtrip] at hr
  have ha := encodeABIValue_uint256_word p.amount
  change ABI.encodeCallWithSelector? transferSelector [addr, uint256] _ = _
  simp only [addr, uint256, uint256Int, uint256Value, abiUInt256, abiUInt256Int] at ha ⊢
  simp only [encodeCallWithSelector?, encodeABIValues?, abiTupleHeadSize?, isDynamicABIType,
    staticABIEncodedSize?, encodeABIValuesFrom?, hr, ha, bind, Option.bind, pure,
    Bool.false_eq_true, Bool.true_eq, ite_false, ite_true, List.nil_append, List.append_nil,
    List.length_nil, Nat.add_zero]
  simp only [byteArray_mk_toArray_eq_toByteArray, list_toByteArray_append,
    byteArray_toList_toByteArray, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc, TokenTransferInput.callBytes]

theorem evalTokenTransferResult (p : TokenTransferInput) (evm : EVM.State)
    (z : Bool) (out : ByteArray) :
    evalExpr? config (p.finalFrame z out) evm
      (.ite (eqE (localLength "tokenData") (.intLit 0)) (.var "tokenSuccess")
        (.ite (eqE (localLength "tokenData") (.intLit 32))
          (andE (.var "tokenSuccess")
            (neE (.abiDecode uint256 (.var "tokenData")) (.intLit 0))) (.boolLit false))) =
      .ok (.bool (tokenTransferResult z out)) := by
  have hsuccess : (p.finalFrame z out).locals["tokenSuccess"]? = some (.bool z) := by
    simp [TokenTransferInput.finalFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  have hdata : (p.finalFrame z out).locals["tokenData"]? = some (.bytes out) := by
    simp [TokenTransferInput.finalFrame, Std.HashMap.getElem?_insert]
  by_cases hz : out.size = 0
  · simp [evalExpr?, eqE, localLength, varRef, hdata, hsuccess, readLocalPath?,
      EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp_eq_int_ok,
      hz, tokenTransferResult]
  have hez : (Value.int (out.size : Int) == Value.int 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq, Value.int.injEq]; omega
  by_cases hs : out.size = 32
  · have hd := decodeReturnUint_long (out := out) (by omega) (by rw [hs]; decide)
    change ABI.decodeReturnValueWithMode? config.abiDecodeMode uint256 out = _ at hd
    have heq : (Value.int (Int.ofNat (calldataWord out 0).toNat) == Value.int 0) =
        decide (calldataWord out 0 = ⟨0⟩) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
      have he : Int.ofNat (calldataWord out 0).toNat = 0 ↔ calldataWord out 0 = ⟨0⟩ := by
        constructor
        · intro h; apply uint256_toNat_eq_zero; exact Int.ofNat.inj h
        · intro h; rw [h]; rfl
      exact he
    have h320 : (Value.int 32 == Value.int 0) = false := by decide +kernel
    simp only [Int.ofNat_eq_natCast] at heq
    cases z <;> simp [evalExpr?, eqE, neE, andE, localLength, varRef, hdata, hsuccess,
      readLocalPath?, EvalResult.ofOption, EvalResult.bind, bind, pure, hs, hz,
      evalBinaryOp_eq_int_ok, evalBinaryOp_ne_int_ok, hd, heq, h320, tokenTransferResult]
  · have hes : (Value.int (out.size : Int) == Value.int 32) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, Value.int.injEq]; omega
    simp [evalExpr?, eqE, localLength, varRef, hdata, hsuccess, readLocalPath?,
      EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp_eq_int_ok,
      hez, hes, hz, hs, tokenTransferResult]

theorem safeTokenTransferSource {evm evm' : EVM.State} {p : TokenTransferInput}
    {z : Bool} {out : ByteArray}
    (hc : callViaEVM evm (EVM.address p.token) 0 p.callBytes (z, evm', out)) :
    ExecFuncBody config p.frame evm transferTokenFunction.body
      (.returned (p.finalFrame z out) evm' (some [.bool (tokenTransferResult z out)])) := by
  apply ExecFuncBody.execBlockRet
  refine .consNormal ?_ (.consReturn (.return
    (evalExprs?_singleton (evalTokenTransferResult p evm' z out))))
  have ht : evalExpr? config p.frame evm (.var "token") = .ok (.address p.token) :=
    evalLocalValue (by simp [TokenTransferInput.frame, TokenTransferInput.args,
      Std.HashMap.getElem?_insert])
  have hv : evalExpr? config p.frame evm (.intLit 0) = .ok (.int 0) := by
    simp only [evalExpr?, pure]
  have hd : evalExpr? config p.frame evm
      (.abiEncodeCall "transfer" [.var "receiver", .var "amount"]) = .ok (.bytes p.callBytes) := by
    simp [evalExpr?, evalExprList?, TokenTransferInput.frame, TokenTransferInput.args,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, EvalResult.ofOption,
      EvalResult.bind, bind, pure, tokenTransferCallEncoding]
  cases z
  · exact .lowLevelCallFailure ht hv hd hc
  · exact .lowLevelCallSuccess ht hv hd hc

end Benchmarks.Safe
