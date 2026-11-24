import Benchmarks.EAS.EAS.BoolCallBlock
import Benchmarks.EAS.EAS.ResolverOneSource
import Benchmarks.EAS.EAS.RefundSource
import Benchmarks.EAS.EAS.WordExpr

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev resolveOneFunction : FunctionDecl := contract.functions[29]!
def resolveOneZeroExpr : Expr := .binary .eq (.var "resolver") (.cast (.intLit 0) (.elem .address))
def resolveOneValueNonzero : Expr := .binary .ne (.var "value") (.intLit 0)
def resolveOneZeroBody : Body := [
  .require (.binary .eq (.var "value") (.intLit 0)), .return [.intLit 0,.var "$EAS.freeMemory"]]
def resolveOnePrefix : Body := [
  .letDecl "resolver" (some (.elem .address)) (.field (.var "schemaRecord") "resolver"),
  .ite resolveOneZeroExpr resolveOneZeroBody []]
def resolveOnePayment : Stmt := .ite resolveOneValueNonzero payableCheckBlock []
def resolveOneAmountBlock : Body := [
  .require (.binary .le (.var "value") (.var "availableValue")),
  .assign .localVar {base := "availableValue"}
    (.cast (.binary .sub (.var "availableValue") (.var "value")) (.elem (.int (.uint ⟨256,by decide⟩))))]
def resolveOneCallTmp (rev : Bool) : Ident := if rev then "__c1$allocation" else "__c2$allocation"
def resolveOneCallResult (rev : Bool) : Ident := if rev then "__c1" else "__c2"
def resolveOneResolverBlock (rev : Bool) : Body :=
  boolCallBlock "_resolverOne" [.var "resolver", .var "attestation", .boolLit rev, .var "value", .var "$EAS.freeMemory"]
    (resolveOneCallTmp rev) (resolveOneCallResult rev)
def resolveOneResolver : Stmt := .ite (.var "isRevocation") (resolveOneResolverBlock true) (resolveOneResolverBlock false)
def resolveOneRefundBlock : Body := [
  .internalCall "_refund" [.var "availableValue", .var "$EAS.freeMemory"] "__c3$allocation",
  .letDecl "__c3" none (.tupleGet (.var "__c3$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c3$allocation") 1)]
def resolveOneRefund : Stmt := .ite (.var "last") resolveOneRefundBlock []
def resolveOneReturn : Body := [
  .return [.var "value", .var "$EAS.freeMemory"], .return [.tupleLit [],.var "$EAS.freeMemory"]]
def resolveOneSuffix : Body := [resolveOnePayment] ++ resolveOneAmountBlock ++
  [resolveOneResolver, resolveOneRefund] ++ resolveOneReturn

theorem resolveOne_body : resolveOneFunction.body = resolveOnePrefix ++ resolveOneSuffix := by native_decide

theorem resolveOneZeroExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {target : AccountAddress}
    (hr : frame.locals.get? "resolver" = some (.address target)) :
    evalExpr? cfg frame evm resolveOneZeroExpr = .ok (.bool (decide (target = EVM.address 0))) := by
  simp only [resolveOneZeroExpr, evalExpr?, hr, EvalResult.ofOption, EvalResult.bind, bind, pure, castValue?]
  change evalBinaryOp? .eq (.address target) (.address (EVM.address 0)) = _
  simp only [evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq]

theorem resolveOnePrefixSource {cfg : Config} {locals imms : Store} {evm : EVM.State} {target : AccountAddress}
    (hr : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm
      (.field (.var "schemaRecord") "resolver") = .ok (.address target)) (hn : target ≠ EVM.address 0) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveOnePrefix
      (.ok {contract := contract, locals := locals.insert "resolver" (.address target), immutables := imms} evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl hr)
  apply ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil
  simpa only [decide_eq_false hn] using resolveOneZeroExpr_eval (cfg := cfg)
    (frame := {contract := contract, locals := locals.insert "resolver" (.address target), immutables := imms})
    (evm := evm) (store_get_self _ _ _)

theorem resolveOneSource_zero {cfg : Config} {locals imms : Store} {evm : EVM.State} {value : UInt256} {heap : Nat}
    (hr : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm
      (.field (.var "schemaRecord") "resolver") = .ok (.address (EVM.address 0)))
    (hv : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    if value = ⟨0⟩ then
      ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveOneFunction.body
        (.returned {contract := contract, locals := locals.insert "resolver" (.address (EVM.address 0)), immutables := imms}
          evm (some [.int 0,.int (Int.ofNat heap)]))
    else ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveOneFunction.body .reverted := by
  have hrz : evalExpr? cfg {contract := contract, locals := locals.insert "resolver" (.address (EVM.address 0)), immutables := imms}
      evm resolveOneZeroExpr = .ok (.bool true) := by
    simpa only [decide_true] using resolveOneZeroExpr_eval (cfg := cfg)
      (frame := {contract := contract, locals := locals.insert "resolver" (.address (EVM.address 0)), immutables := imms})
      (evm := evm) (store_get_self _ _ _)
  have hvz : evalExpr? cfg {contract := contract, locals := locals.insert "resolver" (.address (EVM.address 0)), immutables := imms}
      evm (.binary .eq (.var "value") (.intLit 0)) = .ok (.bool (decide (value = ⟨0⟩))) := by
    exact evalWordEqZero (by simp only [evalExpr?, store_get_ne _ _ (by decide : ("resolver" == "value") = false), hv, EvalResult.ofOption])
  rw [resolveOne_body]
  by_cases hz : value = ⟨0⟩
  · rw [if_pos hz]
    apply ExecFuncBody.execBlockRet
    apply ExecBlock.consNormal (ExecStmt.letDecl hr)
    apply ExecBlock.consReturn (ExecStmt.iteTrue hrz ?_)
    apply ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [decide_eq_true hz] using hvz))
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, store_get_ne _ _ (by decide : ("resolver" == "$EAS.freeMemory") = false),
      hh, EvalResult.ofOption, EvalResult.bind, bind, pure]
  · rw [if_neg hz]
    apply ExecFuncBody.execBlockRevert
    apply ExecBlock.consNormal (ExecStmt.letDecl hr)
    exact ExecBlock.consRevert (ExecStmt.iteTrue hrz
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [decide_eq_false hz] using hvz))))

theorem resolveOneAmountSource {cfg : Config} {locals imms : Store} {evm : EVM.State} {value available : UInt256}
    (hv : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (ha : locals.get? "availableValue" = some (.int (Int.ofNat available.toNat))) :
    if value.toNat ≤ available.toNat then
      ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveOneAmountBlock
        (.ok {contract := contract, locals := locals.insert "availableValue" (.int (Int.ofNat (UInt256.sub available value).toNat)), immutables := imms} evm)
    else ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveOneAmountBlock .reverted := by
  have he := naturalLeSource (cfg := cfg) (frame := {contract := contract, locals := locals, immutables := imms}) (evm := evm)
    (by simp only [evalExpr?, hv, EvalResult.ofOption] : evalExpr? cfg _ evm (.var "value") = .ok (.int (Int.ofNat value.toNat)))
    (by simp only [evalExpr?, ha, EvalResult.ofOption] : evalExpr? cfg _ evm (.var "availableValue") = .ok (.int (Int.ofNat available.toNat)))
  by_cases hb : value.toNat ≤ available.toNat
  · rw [if_pos hb]
    apply ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [decide_eq_true hb] using he))
    apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (evalCastUint256Sub
      (by simp only [evalExpr?, ha, EvalResult.ofOption]) (by simp only [evalExpr?, hv, EvalResult.ofOption]) hb)
      (assignLocalBase_ok (frame := {contract := contract, locals := locals, immutables := imms}) ha)) ExecBlock.nil
  · rw [if_neg hb]
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [decide_eq_false hb] using he))


def resolveOneResolverLocals (locals : Store) (rev : Bool) (heap : Nat) (out : ByteArray) : Store :=
  boolCallBlockLocals locals (resolveOneCallTmp rev) (resolveOneCallResult rev) heap out

theorem resolveOneResolverSource {locals imms : Store} {evm evm' : EVM.State} {a : AttestationRecord}
    {target : AccountAddress} {value : UInt256} {rev success : Bool} {heap : Nat} {out : ByteArray}
    (hr : locals.get? "resolver" = some (.address target)) (ha : locals.get? "attestation" = some a.value)
    (hv : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hrv : locals.get? "isRevocation" = some (.bool rev)) (hsize : a.data.size < UInt256.size)
    (hc : callViaEVM fork evm target (Int.ofNat value.toNat) (resolverOnePayload a rev) (success,evm',out))
    (hout : out.size < 2^255)
    (hperm : EVM.wordOfInt (Int.ofNat value.toNat) = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
    if callBoolAccepted heap success out then
      ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm resolveOneResolver
        (.ok {contract := contract, locals := resolveOneResolverLocals locals rev heap out, immutables := imms} evm')
    else ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm resolveOneResolver .reverted := by
  have hcall := resolverOneCall (hperm := hperm) (heap := heap) (imms := imms) (locals := locals)
    (args := [.var "resolver", .var "attestation", .boolLit rev, .var "value", .var "$EAS.freeMemory"])
    (retVar := resolveOneCallTmp rev)
    (by simp only [evalExprs?, evalExpr?, hr, ha, hv, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]) hsize hc hout
  have hb := boolCallBlockSource (result := resolveOneCallResult rev) hh
    (by cases rev <;> decide) (by cases rev <;> decide) (by cases rev <;> decide) hcall
  have he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm (.var "isRevocation") =
      .ok (.bool rev) := by simp only [evalExpr?, hrv, EvalResult.ofOption]
  by_cases hg : callBoolAccepted heap success out
  · rw [if_pos hg] at hb ⊢
    cases rev with
    | false => exact ExecStmt.iteFalse he hb
    | true => exact ExecStmt.iteTrue he hb
  · rw [if_neg hg] at hb ⊢
    cases rev with
    | false => exact ExecStmt.iteFalse he hb
    | true => exact ExecStmt.iteTrue he hb

def resolveOneRefundLocals (locals : Store) (heap : Nat) : Store :=
  unpackHeapLocals (locals.insert "__c3$allocation" (.tuple [.tuple [],.int (Int.ofNat heap)]))
    "__c3" "$EAS.freeMemory" (.tuple []) heap

theorem resolveOneRefundBlockSource {cfg : Config} {locals imms : Store} {evm evm' : EVM.State} {old heap : Nat}
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat old)))
    (hc : ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_refund" [.var "availableValue", .var "$EAS.freeMemory"] "__c3$allocation")
      (.ok {contract := contract, locals := locals.insert "__c3$allocation" (.tuple [.tuple [],.int (Int.ofNat heap)]), immutables := imms} evm')) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveOneRefundBlock
      (.ok {contract := contract, locals := resolveOneRefundLocals locals heap, immutables := imms} evm') := by
  apply ExecBlock.consNormal hc
  exact unpackHeapResult (store_get_self _ _ _)
    (by simpa only [store_get_ne _ _ (by decide : ("__c3$allocation" == "$EAS.freeMemory") = false)] using hh)
    (by decide) (by decide)

theorem resolveOneReturnSource {cfg : Config} {locals imms : Store} {evm : EVM.State} {value : UInt256} {heap : Nat}
    (hv : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveOneReturn
      (.returned {contract := contract, locals := locals, immutables := imms} evm
        (some [.int (Int.ofNat value.toNat),.int (Int.ofNat heap)])) := by
  apply ExecFuncBody.execBlockRet (ExecBlock.consReturn (ExecStmt.return ?_))
  simp only [evalExprs?, evalExpr?, hv, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem resolveOneSource_nonzero {cfg : Config} {locals imms : Store} {evm : EVM.State} {target : AccountAddress} {result : ExecResult}
    (hr : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm
      (.field (.var "schemaRecord") "resolver") = .ok (.address target)) (hn : target ≠ EVM.address 0)
    (ht : ExecFuncBody fork cfg {contract := contract, locals := locals.insert "resolver" (.address target), immutables := imms}
      evm resolveOneSuffix result) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveOneFunction.body result := by
  rw [resolveOne_body]
  exact execFuncBody_append (resolveOnePrefixSource hr hn) ht

def resolveOneArgs (record : Value) (a : AttestationRecord) (value : UInt256) (rev : Bool) (available : UInt256)
    (last : Bool) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "last" (.bool last)
    |>.insert "availableValue" (.int (Int.ofNat available.toNat)) |>.insert "isRevocation" (.bool rev)
    |>.insert "value" (.int (Int.ofNat value.toNat)) |>.insert "attestation" a.value |>.insert "schemaRecord" record

theorem resolveOne_lookup : lookupCallable? contract "_resolveAttestation" = some resolveOneFunction.toCallable := by rfl

theorem resolveOne_bind (record : Value) (a : AttestationRecord) (value : UInt256) (rev : Bool) (available : UInt256)
    (last : Bool) (heap : Nat) :
    bindParams? resolveOneFunction.params [record,a.value,.int (Int.ofNat value.toNat),.bool rev,
      .int (Int.ofNat available.toNat),.bool last,.int (Int.ofNat heap)] =
      some (resolveOneArgs record a value rev available last heap) := by rfl

end Benchmarks.EAS.EAS
