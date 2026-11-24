import Benchmarks.EAS.EAS.ResolveOneSource
import Benchmarks.EAS.EAS.ResolverManySource
import Benchmarks.EAS.EAS.TimeArray

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev resolveManyFunction : FunctionDecl := contract.functions[26]!
def resolveManyLength : Stmt := .letDecl "length" (some abiUInt256) (.arrayLength .localVar {base := "attestations"})
def resolveManySingleArgs : List Expr := [.var "schemaRecord", .index (.var "attestations") (.intLit 0),
  .index (.var "values") (.intLit 0), .var "isRevocation", .var "availableValue", .var "last", .var "$EAS.freeMemory"]
def resolveManySingleBody : Body := [
  .internalCall "_resolveAttestation" resolveManySingleArgs "__c0$allocation",
  .letDecl "__c0" none (.tupleGet (.var "__c0$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c0$allocation") 1),
  .return [.var "__c0", .var "$EAS.freeMemory"]]
def resolveManySingle : Stmt := .ite (.binary .eq (.var "length") (.intLit 1)) resolveManySingleBody []
def resolveManyIndexInit : Stmt := .letDecl "i" (some abiUInt256) (.intLit 0)
def resolveManyIncrement : Stmt := .assign .localVar {base := "i"}
  (.cast (.binary .add (.var "i") (.intLit 1)) (.elem (.int (.uint ⟨256,by decide⟩))))
def resolveManyZeroIteration : Body := [
  .require (.binary .eq (.index (.var "values") (.var "i")) (.intLit 0)), resolveManyIncrement]
def resolveManyZeroBody : Body := [resolveManyIndexInit, .while timeArrayGuard resolveManyZeroIteration,
  .return [.intLit 0,.var "$EAS.freeMemory"]]
def resolveManyResolverInit : Stmt := .letDecl "resolver" (some (.elem .address)) (.field (.var "schemaRecord") "resolver")
def resolveManyZero : Stmt := .ite resolveOneZeroExpr resolveManyZeroBody []
def resolveManyTotalInit : Stmt := .letDecl "totalUsedValue" (some abiUInt256) (.intLit 0)
def resolveManyTotalUpdate : Stmt := .assign .localVar {base := "totalUsedValue"}
  (.cast (.binary .add (.var "totalUsedValue") (.var "value")) (.elem (.int (.uint ⟨256,by decide⟩))))
def resolveManyIteration : Body :=
  [.letDecl "value" (some abiUInt256) (.index (.var "values") (.var "i")),resolveOnePayment] ++
  resolveOneAmountBlock ++ [resolveManyTotalUpdate,resolveManyIncrement]
def resolveManyCallTmp (rev : Bool) : Ident := if rev then "__c2$allocation" else "__c3$allocation"
def resolveManyCallResult (rev : Bool) : Ident := if rev then "__c2" else "__c3"
def resolveManyResolverBlock (rev : Bool) : Body := boolCallBlock "_resolverMany"
  [.var "resolver",.var "attestations",.var "values",.boolLit rev,.var "totalUsedValue",.var "$EAS.freeMemory"]
  (resolveManyCallTmp rev) (resolveManyCallResult rev)
def resolveManyResolver : Stmt := .ite (.var "isRevocation") (resolveManyResolverBlock true) (resolveManyResolverBlock false)
def resolveManyRefundBlock : Body := [
  .internalCall "_refund" [.var "availableValue", .var "$EAS.freeMemory"] "__c4$allocation",
  .letDecl "__c4" none (.tupleGet (.var "__c4$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c4$allocation") 1)]
def resolveManyRefund : Stmt := .ite (.var "last") resolveManyRefundBlock []
def resolveManyReturn : Body := [.return [.var "totalUsedValue",.var "$EAS.freeMemory"],
  .return [.tupleLit [],.var "$EAS.freeMemory"]]
def resolveManySuffix : Body := [resolveManyTotalInit,resolveManyIndexInit,
  .while timeArrayGuard resolveManyIteration,resolveManyResolver,resolveManyRefund] ++ resolveManyReturn

theorem resolveMany_body : resolveManyFunction.body =
    [resolveManyLength,resolveManySingle,resolveManyResolverInit,resolveManyZero] ++ resolveManySuffix := by native_decide

-- LIBRARY CANDIDATE: a source array index reads a chosen element after normalizing raw boolean words.
theorem evalArrayIndex {cfg : Config} {frame : Frame} {evm : EVM.State} {arr idx : Expr}
    {xs : List Value} {i : Nat} {x : Value}
    (ha : evalExpr? cfg frame evm arr = .ok (.array xs))
    (hi : evalExpr? cfg frame evm idx = .ok (.int (Int.ofNat i))) (hb : i < xs.length)
    (hx : xs[i] = x) (hn : normalizeRawBoolWord? x = .ok x) :
    evalExpr? cfg frame evm (.index arr idx) = .ok x := by
  simp only [evalExpr?, ha, hi, EvalResult.bind, bind, evalIndex?, Int.ofNat_eq_natCast,
    Int.natCast_nonneg, Nat.cast_lt, hb, and_self, if_true, Int.toNat_natCast,
    lookupNth_getElem, List.getElem?_eq_getElem hb, hx, EvalResult.ofOption, hn]

theorem evalWordArrayIndex {cfg : Config} {frame : Frame} {evm : EVM.State} {arr idx : Expr}
    {words : List UInt256} {i : Nat}
    (ha : evalExpr? cfg frame evm arr = .ok (.array (words.map fun w => .int (Int.ofNat w.toNat))))
    (hi : evalExpr? cfg frame evm idx = .ok (.int (Int.ofNat i))) (hb : i < words.length) :
    evalExpr? cfg frame evm (.index arr idx) = .ok (.int (Int.ofNat words[i].toNat)) := by
  exact evalArrayIndex ha hi (by simpa only [List.length_map] using hb) (List.getElem_map ..) rfl

theorem resolveManyIncrementSource {cfg : Config} {locals imms : Store} {evm : EVM.State} {i : Nat}
    (hi : locals.get? "i" = some (.int (Int.ofNat i))) (hb : i+1 < UInt256.size) :
    ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveManyIncrement
      (.ok {contract := contract, locals := locals.insert "i" (.int (Int.ofNat (i+1))), immutables := imms} evm) := by
  have he := evalCastUint256Add (cfg := cfg) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms})
    (a := .var "i") (b := .intLit 1) (x := i) (y := 1)
    (by simp only [evalExpr?, hi, EvalResult.ofOption]) (by simp only [evalExpr?]; rfl)
  rw [Nat.mod_eq_of_lt hb] at he
  exact ExecStmt.assign (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) he (assignLocalBase_ok hi)

structure ResolveManyZeroLocals (locals : Store) (words : List UInt256) (heap i : Nat) : Prop where
  values : locals.get? "values" = some (.array (words.map fun w => .int (Int.ofNat w.toNat)))
  length : locals.get? "length" = some (.int (Int.ofNat words.length))
  index : locals.get? "i" = some (.int (Int.ofNat i))
  heap : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))

theorem ResolveManyZeroLocals.next {locals : Store} {words : List UInt256} {heap i : Nat}
    (h : ResolveManyZeroLocals locals words heap i) :
    ResolveManyZeroLocals (locals.insert "i" (.int (Int.ofNat (i+1)))) words heap (i+1) := by
  rcases h with ⟨hv,hl,hi,hh⟩
  constructor <;> simp (disch := decide) only [store_get_self,store_get_ne] <;> assumption

theorem resolveManyZeroGuardSource {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {words : List UInt256} {heap i : Nat} (h : ResolveManyZeroLocals locals words heap i) :
    evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm timeArrayGuard =
      .ok (.bool (decide (i < words.length))) := by
  simp only [timeArrayGuard,evalExpr?,h.index,h.length,EvalResult.ofOption,EvalResult.bind,bind,
    evalBinaryOp_lt_int_ok,Int.ofNat_eq_natCast,Nat.cast_lt]

theorem resolveManyZeroIterationSource {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {words : List UInt256} {heap i : Nat} (h : ResolveManyZeroLocals locals words heap i)
    (hi : i < words.length) (hlen : words.length < UInt256.size) :
    if words[i] = ⟨0⟩ then
      ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveManyZeroIteration
        (.ok {contract := contract, locals := locals.insert "i" (.int (Int.ofNat (i+1))), immutables := imms} evm)
    else ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveManyZeroIteration .reverted := by
  have he := evalWordEqZero (cfg := cfg) (frame := {contract := contract, locals := locals, immutables := imms})
    (evm := evm) (evalWordArrayIndex (arr := .var "values") (idx := .var "i")
      (by simp only [evalExpr?,h.values,EvalResult.ofOption]) (by simp only [evalExpr?,h.index,EvalResult.ofOption]) hi)
  by_cases hz : words[i] = ⟨0⟩
  · rw [if_pos hz]
    exact ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [decide_eq_true hz] using he))
      (ExecBlock.consNormal (resolveManyIncrementSource h.index (by omega)) ExecBlock.nil)
  · rw [if_neg hz]
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [decide_eq_false hz] using he))

def resolveManyArgs (record : Value) (ats : List AttestationRecord) (words : List UInt256) (rev : Bool)
    (available : UInt256) (last : Bool) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "last" (.bool last)
    |>.insert "availableValue" (.int (Int.ofNat available.toNat)) |>.insert "isRevocation" (.bool rev)
    |>.insert "values" (.array (words.map fun w => .int (Int.ofNat w.toNat)))
    |>.insert "attestations" (.array (ats.map AttestationRecord.value)) |>.insert "schemaRecord" record

theorem resolveMany_lookup : lookupCallable? contract "_resolveAttestations" = some resolveManyFunction.toCallable := by rfl
theorem resolveMany_bind (record : Value) (ats : List AttestationRecord) (words : List UInt256) (rev : Bool)
    (available : UInt256) (last : Bool) (heap : Nat) :
    bindParams? resolveManyFunction.params [record,.array (ats.map AttestationRecord.value),
      .array (words.map fun w => .int (Int.ofNat w.toNat)),.bool rev,.int (Int.ofNat available.toNat),
      .bool last,.int (Int.ofNat heap)] = some (resolveManyArgs record ats words rev available last heap) := by rfl

end Benchmarks.EAS.EAS
