import Benchmarks.EAS.Attester.MultiAttestSource
import Benchmarks.EAS.Attester.MultiAttestReturnTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.EAS.Attester

def multiAttestCallLocals (locals : Store) (data : ByteArray) (z : Bool) (out : ByteArray) : Store
    :=
  (((locals.insert "encodedRequest" (.bytes data)).insert "ok" (.bool z)).insert
    "rawReturn" (.bytes out))

theorem multiAttestSourceCall {imms locals : Store} {evm evm' : State} {cd data out : ByteArray}
    {eas : EVM.Address} {z : Bool}
    (heas : locals.get? "eas" = some (.address eas))
    (hrequest : locals.get? "multiRequests" = some (multiAttestRequests cd))
    (hencode : config.externalABI.encode? "multiAttest" [multiAttestRequests cd] = some data)
    (hcall : typedCallViaEVM config evm eas "multiAttest" 0 [multiAttestRequests cd] (z, evm',
        out)) :
    ExecBlock config ⟨contract, locals, imms⟩ evm ((multiAttestTransition.body.drop 7).take 2)
      (.ok ⟨contract, multiAttestCallLocals locals data z out, imms⟩ evm') := by
  obtain ⟨data', hencode', hraw⟩ := hcall
  rw [hencode] at hencode'
  cases Option.some.inj hencode'
  have hreceiver : evalExpr? config
      ⟨contract, locals.insert "encodedRequest" (.bytes data), imms⟩ evm (.var "eas") =
      .ok (.address eas) := by
    apply evalLocalValue
    simpa [Std.HashMap.getElem?_insert] using heas
  have hdata : evalExpr? config
      ⟨contract, locals.insert "encodedRequest" (.bytes data), imms⟩ evm (.var "encodedRequest") =
      .ok (.bytes data) := evalLocalValue (by simp)
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes data) ?_) ?_
  · simp only [evalExpr?, evalExprList?, hrequest, EvalResult.ofOption, bind, EvalResult.bind,
      pure, hencode]
  cases z with
  | false =>
      exact ExecBlock.consNormal (ExecStmt.lowLevelCallFailure (sendVal := 0) hreceiver
        (by simp only [evalExpr?, pure]) hdata
        (by simpa only [address_of_val] using hraw)) ExecBlock.nil
  | true =>
      exact ExecBlock.consNormal (ExecStmt.lowLevelCallSuccess (sendVal := 0) hreceiver
        (by simp only [evalExpr?, pure]) hdata
        (by simpa only [address_of_val] using hraw)) ExecBlock.nil

def multiAttestReturnGuard : Expr :=
  .binary .le
    (.binary .add
      (.binary .add (.var "allocationEnd")
        (.binary .mul (.intLit 32)
          (.binary .div (.binary .add (.arrayLength .localVar ⟨"rawReturn", []⟩) (.intLit 31))
            (.intLit 32))))
      (.binary .mul (.intLit 32)
        (.binary .add (.arrayLength .localVar ⟨"uids", []⟩) (.intLit 1))))
    (.intLit 18446744073709551615)

theorem multiAttestReturnGuard_eval {cfg solm evm} {base : Nat} {out : ByteArray}
    (hbase : solm.locals.get? "allocationEnd" = some (.int (Int.ofNat base)))
    (hout : solm.locals.get? "rawReturn" = some (.bytes out))
    (huids : solm.locals.get? "uids" = some (.array (returnArrayValues out))) :
    evalExpr? cfg solm evm multiAttestReturnGuard =
      .ok (.bool (decide (returnArrayEnd base out ≤ solcMaxU64))) := by
  have heq : (base : Int) + 32 * (((out.size : Int) + 31) / 32) +
      32 * ((returnArrayCount out : Int) + 1) = (returnArrayEnd base out : Int) := by
    simp only [returnArrayEnd, returnArrayFree, Nat.cast_add, Nat.cast_mul,
      Int.natCast_ediv, Nat.cast_ofNat]
    ring
  simp only [multiAttestReturnGuard, evalExpr?, hbase, hout, huids, readLocalPath?,
    EvalResult.ofOption, bind, EvalResult.bind, pure, evalBinaryOp?,
    returnArrayValues, wordArrayValues_length, Int.ofNat_eq_natCast,
    show (32 : Int) ≠ 0 by decide, if_false, heq]
  change EvalResult.ok (Value.bool (decide ((returnArrayEnd base out : Int) ≤
    (solcMaxU64 : Int)))) = _
  simp only [Int.ofNat_le]

theorem multiAttestSourceCallFailure {imms locals : Store} {evm evm' : State}
    {cd data out : ByteArray} {eas : EVM.Address}
    (heas : locals.get? "eas" = some (.address eas))
    (hrequest : locals.get? "multiRequests" = some (multiAttestRequests cd))
    (hencode : config.externalABI.encode? "multiAttest" [multiAttestRequests cd] = some data)
    (hcall : typedCallViaEVM config evm eas "multiAttest" 0 [multiAttestRequests cd]
      (false, evm', out)) :
    ExecBlock config ⟨contract, locals, imms⟩ evm (multiAttestTransition.body.drop 7) .reverted :=
        by
  rw [← List.take_append_drop 2 (multiAttestTransition.body.drop 7)]
  apply execBlock_append (multiAttestSourceCall heas hrequest hencode hcall)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  apply evalLocalValue
  simp [multiAttestCallLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem multiAttestSourceCallSuccessPrefix {imms locals : Store} {evm evm' : State}
    {cd data out : ByteArray} {eas : EVM.Address} {result : ExecResult}
    (heas : locals.get? "eas" = some (.address eas))
    (hrequest : locals.get? "multiRequests" = some (multiAttestRequests cd))
    (hencode : config.externalABI.encode? "multiAttest" [multiAttestRequests cd] = some data)
    (hcall : typedCallViaEVM config evm eas "multiAttest" 0 [multiAttestRequests cd] (true, evm',
        out))
    (hrest : ExecBlock config ⟨contract, multiAttestCallLocals locals data true out, imms⟩ evm'
      (multiAttestTransition.body.drop 10) result) :
    ExecBlock config ⟨contract, locals, imms⟩ evm (multiAttestTransition.body.drop 7) result := by
  rw [← List.take_append_drop 2 (multiAttestTransition.body.drop 7)]
  apply execBlock_append (multiAttestSourceCall heas hrequest hencode hcall)
  apply ExecBlock.consNormal (ExecStmt.requireTrue (evalLocalValue ?_)) hrest
  simp [multiAttestCallLocals, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]

theorem multiAttestSourceReturnDecodeFailure {imms locals : Store} {evm : State}
    {out : ByteArray} (hout : locals.get? "rawReturn" = some (.bytes out))
    (hdecode : decodeReturnValue? bytes32Array out = none) :
    ExecBlock config ⟨contract, locals, imms⟩ evm (multiAttestTransition.body.drop 10) .reverted :=
        by
  apply ExecBlock.consRevert
  apply ExecStmt.letDeclRevert
  change evalExpr? config ⟨contract, locals, imms⟩ evm
    (.abiDecode bytes32Array (.var "rawReturn")) = .revert
  simp only [evalExpr?, hout, EvalResult.ofOption, bind, EvalResult.bind,
    show config.abiDecodeMode = .modern from rfl, decodeReturnValueWithMode?, hdecode]

theorem multiAttestSourceReturnDecode {imms locals : Store} {evm : State} {out : ByteArray}
    {result : ExecResult} (hout : locals.get? "rawReturn" = some (.bytes out))
    (hdecode : decodeReturnValue? bytes32Array out = some (.array (returnArrayValues out)))
    (hrest : ExecBlock config
      ⟨contract, locals.insert "uids" (.array (returnArrayValues out)), imms⟩ evm
      (multiAttestTransition.body.drop 11) result) :
    ExecBlock config ⟨contract, locals, imms⟩ evm (multiAttestTransition.body.drop 10) result := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .array (returnArrayValues out)) ?_) hrest
  change evalExpr? config ⟨contract, locals, imms⟩ evm
    (.abiDecode bytes32Array (.var "rawReturn")) = .ok (.array (returnArrayValues out))
  simp only [evalExpr?, hout, EvalResult.ofOption, bind, EvalResult.bind,
    show config.abiDecodeMode = .modern from rfl, decodeReturnValueWithMode?, hdecode, pure]

theorem multiAttestSourceReturn {imms locals : Store} {evm : State} {base : Nat} {out : ByteArray}
    (hbase : locals.get? "allocationEnd" = some (.int (Int.ofNat base)))
    (hout : locals.get? "rawReturn" = some (.bytes out)) (hhi : out.size < 2 ^ 255) :
    ((¬ ReturnArrayChecks out ∨ ¬ returnArrayEnd base out ≤ solcMaxU64) →
      ExecBlock config ⟨contract, locals, imms⟩ evm
        (multiAttestTransition.body.drop 10) .reverted) ∧
    (ReturnArrayChecks out → returnArrayEnd base out ≤ solcMaxU64 →
      ExecBlock config ⟨contract, locals, imms⟩ evm (multiAttestTransition.body.drop 10)
        (.returned ⟨contract, locals.insert "uids" (.array (returnArrayValues out)), imms⟩ evm
          (some [.array (returnArrayValues out)]))) := by
  have hguard := multiAttestReturnGuard_eval (cfg := config) (evm := evm)
    (solm := ⟨contract, locals.insert "uids" (.array (returnArrayValues out)), imms⟩)
    (base := base) (out := out)
    (by simpa [Std.HashMap.getElem?_insert] using hbase)
    (by simpa [Std.HashMap.getElem?_insert] using hout) (by simp)
  constructor
  · intro hbad
    by_cases hc : ReturnArrayChecks out
    · apply multiAttestSourceReturnDecode hout (returnArrayDecode_ok hhi hc)
      apply ExecBlock.consRevert
      apply ExecStmt.requireFalse
      have hcap : ¬ returnArrayEnd base out ≤ solcMaxU64 := hbad.resolve_left (not_not.mpr hc)
      simpa only [decide_eq_false hcap] using hguard
    · exact multiAttestSourceReturnDecodeFailure hout (returnArrayDecode_bad hhi hc)
  · intro hc hcap
    apply multiAttestSourceReturnDecode hout (returnArrayDecode_ok hhi hc)
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simpa only [decide_eq_true hcap] using hguard
    refine ExecBlock.consReturn (ExecStmt.return ?_)
    simp [evalExprs?, evalExprList?, evalExpr?, EvalResult.ofOption, bind, pure, EvalResult.bind,
      collapseReturns]

end Benchmarks.EAS.Attester
