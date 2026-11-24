import Benchmarks.EAS.EAS.BuildDomain

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the uint256-to-bytes32 cast preserves the entire word.
theorem evalWordAsBytes32 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {w : UInt256} (he : evalExpr? cfg frame evm e = .ok (.int (Int.ofNat w.toNat))) :
    evalExpr? cfg frame evm (.cast e (.elem (.bytes abiBytes32Width))) = .ok (wordBytes32Value w) := by
  have hn : ¬ (Int.ofNat w.toNat) < 0 := by simp only [Int.ofNat_eq_natCast]; omega
  simp only [evalExpr?, he, EvalResult.bind, bind, castValue?, if_neg hn, abiBytes32Width,
    Int.ofNat_eq_natCast, Int.toNat_natCast, Nat.reduceAdd, Nat.sub_self, List.drop_zero, EvalResult.ofOption, wordBytes32Value]
  rw [show EVM.Word.ofNat w.toNat = w from u256_ofNat_toNat w]
  rfl

abbrev domainFunction : FunctionDecl := contract.functions[22]!

def domainCacheHit (v : EASImmutables) (owner : AccountAddress) : Prop :=
  owner = v._CACHED_THIS ∧ Ethereum.chainId = v._CACHED_CHAIN_ID.toNat
instance (v : EASImmutables) (owner : AccountAddress) : Decidable (domainCacheHit v owner) :=
  inferInstanceAs (Decidable (_ ∧ _))

def domainGuard : Expr := .binary .and
  (.binary .eq (.env .this) (.immutable "_CACHED_THIS"))
  (.binary .eq (.env .chainid) (.immutable "_CACHED_CHAIN_ID"))

def domainBuildArgs : List Expr := [
  .cast (.immutable "_TYPE_HASH") (.elem (.bytes abiBytes32Width)),
  .cast (.immutable "_HASHED_NAME") (.elem (.bytes abiBytes32Width)),
  .cast (.immutable "_HASHED_VERSION") (.elem (.bytes abiBytes32Width)), .var "$EAS.freeMemory"]

def domainCachedBody : Body :=
  [.return [.cast (.immutable "_CACHED_DOMAIN_SEPARATOR") (.elem (.bytes abiBytes32Width)), .var "$EAS.freeMemory"]]

def domainRebuiltBody : Body := [
  .internalCall "_buildDomainSeparator" domainBuildArgs "__c0$allocation",
  .letDecl "__c0" none (.tupleGet (.var "__c0$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c0$allocation") 1),
  .return [.var "__c0", .var "$EAS.freeMemory"]]

theorem domain_body : domainFunction.body = [
    .ite domainGuard domainCachedBody domainRebuiltBody,
    .return [.tupleLit [], .var "$EAS.freeMemory"]] := by native_decide

theorem domainGuard_eval {cfg : Config} {locals : Store} {evm : EVM.State} (v : EASImmutables) :
    evalExpr? cfg {contract := contract, locals := locals, immutables := immStore v} evm domainGuard =
      .ok (.bool (decide (domainCacheHit v evm.executionEnv.codeOwner))) := by
  have ha : (Value.address evm.executionEnv.codeOwner == Value.address v._CACHED_THIS) =
      decide (evm.executionEnv.codeOwner = v._CACHED_THIS) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq]
  have hi : (Value.int (Int.ofNat Ethereum.chainId) == Value.int (Int.ofNat v._CACHED_CHAIN_ID.toNat)) =
      decide (Ethereum.chainId = v._CACHED_CHAIN_ID.toNat) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.int.injEq, Int.ofNat_eq_natCast, Int.natCast_inj, decide_eq_true_eq]
  simp only [domainGuard, evalExpr?, envValue, immStore_get__CACHED_THIS, immStore_get__CACHED_CHAIN_ID,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, ha, hi, domainCacheHit]
  by_cases h : evm.executionEnv.codeOwner = v._CACHED_THIS <;> simp [h]

theorem domainBuildArgs_eval {cfg : Config} {locals : Store} {evm : EVM.State}
    (v : EASImmutables) {heap : Nat}
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    evalExprs? cfg {contract := contract, locals := locals, immutables := immStore v} evm domainBuildArgs =
      .ok [wordBytes32Value v._TYPE_HASH, wordBytes32Value v._HASHED_NAME, wordBytes32Value v._HASHED_VERSION,
        .int (Int.ofNat heap)] := by
  have ht := evalWordAsBytes32 (evalImmutable__TYPE_HASH cfg contract locals evm v)
  have hn := evalWordAsBytes32 (evalImmutable__HASHED_NAME cfg contract locals evm v)
  have hv := evalWordAsBytes32 (evalImmutable__HASHED_VERSION cfg contract locals evm v)
  simp only [domainBuildArgs, evalExprs?, ht, hn, hv, evalExpr?, hh, EvalResult.ofOption,
    EvalResult.bind, bind, pure]

theorem domainSource_cached {cfg : Config} {locals : Store} {evm : EVM.State}
    (v : EASImmutables) {heap : Nat}
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hc : domainCacheHit v evm.executionEnv.codeOwner) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := immStore v} evm domainFunction.body
      (.returned {contract := contract, locals := locals, immutables := immStore v} evm
        (some [wordBytes32Value v._CACHED_DOMAIN_SEPARATOR, .int (Int.ofNat heap)])) := by
  rw [domain_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.iteTrue
  · simpa only [hc, decide_true] using domainGuard_eval (cfg := cfg) (locals := locals) (evm := evm) v
  · apply ExecBlock.consReturn
    apply ExecStmt.return
    have h := evalWordAsBytes32 (evalImmutable__CACHED_DOMAIN_SEPARATOR cfg contract locals evm v)
    simp only [evalExprs?, h, evalExpr?, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]

def domainRebuiltLocals (locals : Store) (heap : Nat) (v : EASImmutables) (owner : AccountAddress) : Store :=
  let value := wordBytes32Value (builtDomainWord v._TYPE_HASH v._HASHED_NAME v._HASHED_VERSION owner)
  unpackHeapLocals (locals.insert "__c0$allocation" (.tuple [value, .int (Int.ofNat (allocateNext heap 192))]))
    "__c0" "$EAS.freeMemory" value (allocateNext heap 192)

theorem domainSource_rebuilt {cfg : Config} {locals : Store} {evm : EVM.State}
    (v : EASImmutables) {heap : Nat}
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hc : ¬ domainCacheHit v evm.executionEnv.codeOwner)
    (hguard : allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := immStore v} evm domainFunction.body
      (.returned {
        contract := contract
        locals := domainRebuiltLocals locals heap v evm.executionEnv.codeOwner
        immutables := immStore v} evm (some [
          wordBytes32Value (builtDomainWord v._TYPE_HASH v._HASHED_NAME v._HASHED_VERSION evm.executionEnv.codeOwner),
          .int (Int.ofNat (allocateNext heap 192))])) := by
  rw [domain_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.iteFalse
  · simpa only [hc, decide_false] using domainGuard_eval (cfg := cfg) (locals := locals) (evm := evm) v
  · have hcall := internalCallFunctionReturn (fork := fork) (retVar := "__c0$allocation") (domainBuildArgs_eval (cfg := cfg) (evm := evm) v hh)
      buildDomain_lookup (buildDomain_bind _ _ _ heap)
      (buildDomainSource_ok (fork := fork) (buildDomainArgs_type _ _ _ _) (buildDomainArgs_name _ _ _ _)
        (buildDomainArgs_version _ _ _ _) (buildDomainArgs_heap _ _ _ _) hguard)
    apply ExecBlock.consNormal hcall
    have hunpack := unpackHeapResult (fork := fork) (cfg := cfg) (evm := evm)
      (frame := {
        contract := contract
        locals := locals.insert "__c0$allocation" (.tuple [
          wordBytes32Value (builtDomainWord v._TYPE_HASH v._HASHED_NAME v._HASHED_VERSION evm.executionEnv.codeOwner),
          .int (Int.ofNat (allocateNext heap 192))])
        immutables := immStore v}) (result := "__c0") (cursor := "$EAS.freeMemory")
      (old := .int (Int.ofNat heap)) (store_get_self _ _ _)
      (by simpa only [store_get_ne _ _ (by decide : ("__c0$allocation" == "$EAS.freeMemory") = false)] using hh)
      (by decide) (by decide)
    apply execBlock_append hunpack
    apply ExecBlock.consReturn
    apply ExecStmt.return
    simp only [unpackHeapLocals, evalExprs?, evalExpr?,
      store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "__c0") = false), store_get_self,
      EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem domainSource_revert {cfg : Config} {locals : Store} {evm : EVM.State}
    (v : EASImmutables) {heap : Nat}
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hc : ¬ domainCacheHit v evm.executionEnv.codeOwner)
    (hguard : ¬ (allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192)) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := immStore v} evm domainFunction.body
      .reverted := by
  rw [domain_body]
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.iteFalse
  · simpa only [hc, decide_false] using domainGuard_eval (cfg := cfg) (locals := locals) (evm := evm) v
  · apply ExecBlock.consRevert
    exact internalCallFunctionRevert (domainBuildArgs_eval v hh) buildDomain_lookup (buildDomain_bind _ _ _ heap)
      (buildDomainSource_revert (buildDomainArgs_heap _ _ _ _) hguard)


def domainWord (v : EASImmutables) (owner : AccountAddress) : UInt256 :=
  if domainCacheHit v owner then v._CACHED_DOMAIN_SEPARATOR
  else builtDomainWord v._TYPE_HASH v._HASHED_NAME v._HASHED_VERSION owner

def domainNext (v : EASImmutables) (owner : AccountAddress) (heap : Nat) : Nat :=
  if domainCacheHit v owner then heap else allocateNext heap 192

def domainFinalLocals (locals : Store) (heap : Nat) (v : EASImmutables) (owner : AccountAddress) : Store :=
  if domainCacheHit v owner then locals else domainRebuiltLocals locals heap v owner

theorem domainSource_ok {cfg : Config} {locals : Store} {evm : EVM.State}
    (v : EASImmutables) {heap : Nat}
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hguard : domainCacheHit v evm.executionEnv.codeOwner ∨
      (allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192)) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := immStore v} evm domainFunction.body
      (.returned {
        contract := contract
        locals := domainFinalLocals locals heap v evm.executionEnv.codeOwner
        immutables := immStore v} evm (some [wordBytes32Value (domainWord v evm.executionEnv.codeOwner),
          .int (Int.ofNat (domainNext v evm.executionEnv.codeOwner heap))])) := by
  by_cases hc : domainCacheHit v evm.executionEnv.codeOwner
  · simpa only [domainFinalLocals, domainWord, domainNext, if_pos hc] using domainSource_cached v hh hc
  · simpa only [domainFinalLocals, domainWord, domainNext, if_neg hc] using
      domainSource_rebuilt v hh hc (hguard.resolve_left hc)

def domainArgs (heap : Nat) : Store := (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap))

theorem domain_lookup : lookupCallable? contract "_domainSeparatorV4" = some domainFunction.toCallable := by rfl

theorem domain_bind (heap : Nat) : bindParams? domainFunction.params [.int (Int.ofNat heap)] =
    some (domainArgs heap) := by rfl

theorem domainCall_ok {cfg : Config} {locals : Store} {evm : EVM.State}
    (v : EASImmutables) {heap : Nat} {heapExpr : Expr} {retVar : Ident}
    (he : evalExpr? cfg {contract := contract, locals := locals, immutables := immStore v} evm heapExpr =
      .ok (.int (Int.ofNat heap)))
    (hguard : domainCacheHit v evm.executionEnv.codeOwner ∨
      (allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192)) :
    ExecStmt fork cfg {contract := contract, locals := locals, immutables := immStore v} evm
      (.internalCall "_domainSeparatorV4" [heapExpr] retVar)
      (.ok {
        contract := contract
        locals := locals.insert retVar (.tuple [wordBytes32Value (domainWord v evm.executionEnv.codeOwner),
          .int (Int.ofNat (domainNext v evm.executionEnv.codeOwner heap))])
        immutables := immStore v} evm) := by
  exact internalCallFunctionReturn (cfg := cfg) (evm := evm)
    (caller := {contract := contract, locals := locals, immutables := immStore v}) (args := [heapExpr]) (argVals := [.int (Int.ofNat heap)])
    (by simp only [evalExprs?, he, EvalResult.bind, bind, pure])
    domain_lookup (domain_bind heap) (domainSource_ok v (store_get_self _ _ _) hguard)

theorem domainCall_revert {cfg : Config} {locals : Store} {evm : EVM.State}
    (v : EASImmutables) {heap : Nat} {heapExpr : Expr} {retVar : Ident}
    (he : evalExpr? cfg {contract := contract, locals := locals, immutables := immStore v} evm heapExpr =
      .ok (.int (Int.ofNat heap)))
    (hc : ¬ domainCacheHit v evm.executionEnv.codeOwner)
    (hguard : ¬ (allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192)) :
    ExecStmt fork cfg {contract := contract, locals := locals, immutables := immStore v} evm
      (.internalCall "_domainSeparatorV4" [heapExpr] retVar) .reverted := by
  exact internalCallFunctionRevert (by simp only [evalExprs?, he, EvalResult.bind, bind, pure])
    domain_lookup (domain_bind heap) (domainSource_revert v (store_get_self _ _ _) hc hguard)

end Benchmarks.EAS.EAS
