import Benchmarks.EAS.EAS.Allocate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def domainPayload (typeHash nameHash versionHash : UInt256) (owner : AccountAddress) : ByteArray :=
  ⟨(EVM.Word.toBytesBE typeHash ++ EVM.Word.toBytesBE nameHash ++ EVM.Word.toBytesBE versionHash ++
    EVM.Word.toBytesBE (UInt256.ofNat Ethereum.chainId) ++ EVM.Word.toBytesBE (UInt256.ofNat owner.val)).toArray⟩

def builtDomainWord (typeHash nameHash versionHash : UInt256) (owner : AccountAddress) : UInt256 :=
  uInt256OfByteArray (KEC (domainPayload typeHash nameHash versionHash owner))

def buildDomainExpr : Expr := .keccak256 (.abiEncodePacked [
  (abiBytes32, .var "typeHash"), (abiBytes32, .var "nameHash"), (abiBytes32, .var "versionHash"),
  (abiUInt256, .env .chainid), (abiUInt256, .cast (.env .this) (.elem (.int (.uint ⟨256, by decide⟩))))])

-- LIBRARY CANDIDATE: evaluate an address cast to uint256.
theorem evalAddressAsUint256 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {e : Expr} {a : AccountAddress} (he : evalExpr? cfg frame evm e = .ok (.address a)) :
    evalExpr? cfg frame evm (.cast e (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (UInt256.ofNat a.val).toNat)) := by
  have hb : a.toNat < EVM.twoPow 256 := lt_of_lt_of_le a.isLt (by decide)
  have hw : (UInt256.ofNat a.val).toNat = a.val := addressWord_toNat_val a
  simp only [evalExpr?, he, EvalResult.bind, bind, castValue?, if_pos hb, EvalResult.ofOption, hw]
  rfl

theorem buildDomain_eval {cfg : Config} {frame : Frame} {evm : EVM.State}
    {typeHash nameHash versionHash : UInt256}
    (ht : frame.locals.get? "typeHash" = some (wordBytes32Value typeHash))
    (hn : frame.locals.get? "nameHash" = some (wordBytes32Value nameHash))
    (hv : frame.locals.get? "versionHash" = some (wordBytes32Value versionHash)) :
    evalExpr? cfg frame evm buildDomainExpr = .ok
      (wordBytes32Value (builtDomainWord typeHash nameHash versionHash evm.executionEnv.codeOwner)) := by
  have hp : evalPackedArgs? cfg frame evm [
      (abiBytes32, .var "typeHash"), (abiBytes32, .var "nameHash"), (abiBytes32, .var "versionHash"),
      (abiUInt256, .env .chainid), (abiUInt256, .cast (.env .this) (.elem (.int (.uint ⟨256, by decide⟩))))] =
      .ok (EVM.Word.toBytesBE typeHash ++ (EVM.Word.toBytesBE nameHash ++ (EVM.Word.toBytesBE versionHash ++
        (EVM.Word.toBytesBE (UInt256.ofNat Ethereum.chainId) ++ EVM.Word.toBytesBE (UInt256.ofNat evm.executionEnv.codeOwner.val))))) := by
    apply evalPackedArgs_cons (by simp only [evalExpr?, ht, EvalResult.ofOption]) (encodePacked_bytes32 typeHash)
    apply evalPackedArgs_cons (by simp only [evalExpr?, hn, EvalResult.ofOption]) (encodePacked_bytes32 nameHash)
    apply evalPackedArgs_cons (by simp only [evalExpr?, hv, EvalResult.ofOption]) (encodePacked_bytes32 versionHash)
    apply evalPackedArgs_cons (by simp only [evalExpr?, envValue, pure]; rfl) (encodePacked_uint256 (UInt256.ofNat Ethereum.chainId))
    exact evalPackedArgs_single (evalAddressAsUint256 (by simp only [evalExpr?, envValue, pure])) (encodePacked_uint256 _)
  simp only [buildDomainExpr, evalExpr?, hp, EvalResult.bind, bind, pure]
  simp only [wordBytes32Value, builtDomainWord, toBytesBE_keccak_uInt256OfByteArray,
    domainPayload, List.append_assoc]
  rfl

abbrev buildDomainFunction : FunctionDecl := contract.functions[23]!

def buildDomainPrefix : Body := [
  .internalCall "_allocate" [.intLit 192, .var "$EAS.freeMemory"] "allocation$allocation",
  .letDecl "allocation" none (.tupleGet (.var "allocation$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "allocation$allocation") 1)]

theorem buildDomain_body : buildDomainFunction.body = buildDomainPrefix ++
    [.return [buildDomainExpr, .var "$EAS.freeMemory"], .return [.tupleLit [], .var "$EAS.freeMemory"]] := by
  native_decide

def buildDomainLocals (locals : Store) (heap : Nat) : Store :=
  unpackHeapLocals
    (locals.insert "allocation$allocation" (.tuple [.tuple [], .int (Int.ofNat (allocateNext heap 192))]))
    "allocation" "$EAS.freeMemory" (.tuple []) (allocateNext heap 192)

theorem buildDomainSource_ok {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {typeHash nameHash versionHash : UInt256} {heap : Nat}
    (ht : locals.get? "typeHash" = some (wordBytes32Value typeHash))
    (hn : locals.get? "nameHash" = some (wordBytes32Value nameHash))
    (hv : locals.get? "versionHash" = some (wordBytes32Value versionHash))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hguard : allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm buildDomainFunction.body
      (.returned {contract := contract, locals := buildDomainLocals locals heap, immutables := imms}
        evm (some [wordBytes32Value (builtDomainWord typeHash nameHash versionHash evm.executionEnv.codeOwner),
          .int (Int.ofNat (allocateNext heap 192))])) := by
  rw [buildDomain_body]
  apply ExecFuncBody.execBlockRet
  have hcall := allocateCall_ok (fork := fork) (retVar := "allocation$allocation")
    (show evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm (.intLit 192) =
      .ok (.int (Int.ofNat (192 : Nat))) by simp only [evalExpr?, pure]; rfl)
    (show evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm (.var "$EAS.freeMemory") =
      .ok (.int (Int.ofNat heap)) by simp only [evalExpr?, hh, EvalResult.ofOption]) hguard
  have hunpack := unpackHeapResult (fork := fork) (cfg := cfg) (evm := evm)
    (frame := {
      contract := contract
      locals := locals.insert "allocation$allocation" (.tuple [.tuple [], .int (Int.ofNat (allocateNext heap 192))]),
      immutables := imms}) (result := "allocation") (cursor := "$EAS.freeMemory") (old := .int (Int.ofNat heap)) (store_get_self _ _ _)
    (by simpa only [store_get_ne _ _ (by decide : ("allocation$allocation" == "$EAS.freeMemory") = false)] using hh)
    (by decide) (by decide)
  apply execBlock_append (ExecBlock.consNormal hcall hunpack)
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have ht' : (buildDomainLocals locals heap).get? "typeHash" = some (wordBytes32Value typeHash) := by
    simpa only [buildDomainLocals, unpackHeapLocals, store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "typeHash") = false),
      store_get_ne _ _ (by decide : ("allocation" == "typeHash") = false),
      store_get_ne _ _ (by decide : ("allocation$allocation" == "typeHash") = false)] using ht
  have hn' : (buildDomainLocals locals heap).get? "nameHash" = some (wordBytes32Value nameHash) := by
    simpa only [buildDomainLocals, unpackHeapLocals, store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "nameHash") = false),
      store_get_ne _ _ (by decide : ("allocation" == "nameHash") = false),
      store_get_ne _ _ (by decide : ("allocation$allocation" == "nameHash") = false)] using hn
  have hv' : (buildDomainLocals locals heap).get? "versionHash" = some (wordBytes32Value versionHash) := by
    simpa only [buildDomainLocals, unpackHeapLocals, store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "versionHash") = false),
      store_get_ne _ _ (by decide : ("allocation" == "versionHash") = false),
      store_get_ne _ _ (by decide : ("allocation$allocation" == "versionHash") = false)] using hv
  have he := buildDomain_eval (cfg := cfg)
    (frame := {contract := contract, locals := buildDomainLocals locals heap, immutables := imms}) (evm := evm) ht' hn' hv'
  simp only [buildDomainLocals, unpackHeapLocals] at he
  simp only [unpackHeapLocals, evalExprs?, he, evalExpr?, store_get_self,
    EvalResult.ofOption, EvalResult.bind, bind, pure]


theorem buildDomainSource_revert {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {heap : Nat} (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hguard : ¬ (allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192)) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm buildDomainFunction.body
      .reverted := by
  rw [buildDomain_body]
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply allocateCall_revert (heap := heap) (size := 192) _ _ hguard
  · simp only [evalExpr?, pure]; rfl
  · simp only [evalExpr?, hh, EvalResult.ofOption]

def buildDomainArgs (t n v : UInt256) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap))
    |>.insert "versionHash" (wordBytes32Value v)
    |>.insert "nameHash" (wordBytes32Value n)
    |>.insert "typeHash" (wordBytes32Value t)

theorem buildDomain_lookup : lookupCallable? contract "_buildDomainSeparator" = some buildDomainFunction.toCallable := by rfl

theorem buildDomain_bind (t n v : UInt256) (heap : Nat) :
    bindParams? buildDomainFunction.params
      [wordBytes32Value t, wordBytes32Value n, wordBytes32Value v, .int (Int.ofNat heap)] =
      some (buildDomainArgs t n v heap) := by rfl

theorem buildDomainArgs_type (t n v : UInt256) (heap : Nat) :
    (buildDomainArgs t n v heap).get? "typeHash" = some (wordBytes32Value t) := store_get_self _ _ _
theorem buildDomainArgs_name (t n v : UInt256) (heap : Nat) :
    (buildDomainArgs t n v heap).get? "nameHash" = some (wordBytes32Value n) := by
  simp only [buildDomainArgs, store_get_ne _ _ (by decide : ("typeHash" == "nameHash") = false), store_get_self]
theorem buildDomainArgs_version (t n v : UInt256) (heap : Nat) :
    (buildDomainArgs t n v heap).get? "versionHash" = some (wordBytes32Value v) := by
  simp only [buildDomainArgs, store_get_ne _ _ (by decide : ("typeHash" == "versionHash") = false),
    store_get_ne _ _ (by decide : ("nameHash" == "versionHash") = false), store_get_self]
theorem buildDomainArgs_heap (t n v : UInt256) (heap : Nat) :
    (buildDomainArgs t n v heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  simp only [buildDomainArgs, store_get_ne _ _ (by decide : ("typeHash" == "$EAS.freeMemory") = false),
    store_get_ne _ _ (by decide : ("nameHash" == "$EAS.freeMemory") = false),
    store_get_ne _ _ (by decide : ("versionHash" == "$EAS.freeMemory") = false), store_get_self]

end Benchmarks.EAS.EAS
