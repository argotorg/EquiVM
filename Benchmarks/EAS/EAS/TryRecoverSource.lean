import Benchmarks.EAS.EAS.TryRecoverExpr
import Benchmarks.EAS.EAS.EcrecoverOutput

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

abbrev tryRecoverFunction : FunctionDecl := contract.functions[32]!
def tryRecoverReturn (signer : Expr) (error : Nat) : Stmt :=
  .return [.tupleLit [signer,.intLit (Int.ofNat error)],.var "$EAS.freeMemory"]
def tryRecoverInit : Body := [
  .letDecl "precompile" (some (.elem .address)) (.cast (.intLit 1) (.elem .address)),
  .letDecl "payload" (some .bytes) tryRecoverPayloadExpr]
def tryRecoverInvoke : Stmt :=
  .lowLevelCall (.var "precompile") (.intLit 0) (.var "payload") "ok" "result" false

def tryRecoverDecode : Stmt := .ite
  (.binary .ge (.arrayLength .localVar {base := "result"}) (.intLit 32))
  [.assign .localVar {base := "signer"} (.abiDecode (.elem .address) (.var "result"))] []
def tryRecoverZeroGuard : Expr := .binary .eq (.var "signer") (.cast (.intLit 0) (.elem .address))
def tryRecoverTail : Body := [
  .require (.var "ok"),
  .letDecl "signer" (some (.elem .address)) (.cast (.intLit 0) (.elem .address)),
  tryRecoverDecode,
  .ite tryRecoverZeroGuard [tryRecoverReturn (.cast (.intLit 0) (.elem .address)) 1] [],
  tryRecoverReturn (.var "signer") 0,
  .return [.tupleLit [],.var "$EAS.freeMemory"]]

theorem tryRecover_body : tryRecoverFunction.body =
    [.ite tryRecoverGuard [tryRecoverReturn (.cast (.intLit 0) (.elem .address)) 3] []] ++
    tryRecoverInit ++ [tryRecoverInvoke] ++ tryRecoverTail := by native_decide

theorem tryRecoverReturnSource {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {a : AccountAddress} {error heap : Nat}
    (he : evalExpr? cfg frame evm expr = .ok (.address a))
    (hh : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecStmt fork cfg frame evm (tryRecoverReturn expr error)
      (.returned frame evm (some [.tuple [.address a,.int (Int.ofNat error)],.int (Int.ofNat heap)])) := by
  apply ExecStmt.return
  simp only [evalExprs?,evalExpr?,evalExprList?,he,hh,EvalResult.ofOption,EvalResult.bind,bind,pure]

theorem tryRecoverHighSource {cfg : Config} {frame : Frame} {evm : EVM.State} {s : UInt256} {heap : Nat}
    (hs : frame.locals.get? "s" = some (wordBytes32Value s))
    (hh : frame.locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hi : ecdsaHalfOrder < s.toNat) :
    ExecFuncBody fork cfg frame evm tryRecoverFunction.body
      (.returned frame evm (some [.tuple [.address 0,.int 3],.int (Int.ofNat heap)])) := by
  rw [tryRecover_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.iteTrue
  · simpa only [hi,decide_true] using tryRecoverGuard_eval (cfg := cfg) (frame := frame) (evm := evm) hs
  exact ExecBlock.consReturn (tryRecoverReturnSource (by simp only [evalExpr?,pure,EvalResult.bind,bind,castValue?,EvalResult.ofOption]; rfl) hh)

def tryRecoverInputLocals (L : Store) (hash v r s : UInt256) : Store :=
  L.insert "precompile" (.address 1) |>.insert "payload" (.bytes (tryRecoverPayload hash v r s))

theorem tryRecoverInitSource {cfg : Config} {L imms : Store} {evm : EVM.State} {hash v r s : UInt256}
    (hh : L.get? "hash" = some (wordBytes32Value hash))
    (hv : L.get? "v" = some (.int (Int.ofNat v.toNat)))
    (hr : L.get? "r" = some (wordBytes32Value r))
    (hs : L.get? "s" = some (wordBytes32Value s)) :
    ExecBlock fork cfg {contract := contract,locals := L,immutables := imms} evm tryRecoverInit
      (.ok {contract := contract,locals := tryRecoverInputLocals L hash v r s,immutables := imms} evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .address 1)
    (by simp only [evalExpr?,pure,EvalResult.bind,bind,castValue?,EvalResult.ofOption]; rfl))
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  apply tryRecoverPayload_eval
  all_goals simpa (disch := decide) only [store_get_ne] using ‹_›

theorem tryRecoverDecodeSource {L imms : Store} {evm : EVM.State} {out : ByteArray} {a : AccountAddress} {heap : Nat}
    (hr : L.get? "result" = some (.bytes out)) (hz : L.get? "signer" = some (.address 0))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hout : (out = ByteArray.empty ∧ a = 0) ∨ out = (UInt256.ofNat a.val).toByteArray) :
    ∃ L', ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm tryRecoverDecode
      (.ok {contract := contract,locals := L',immutables := imms} evm) ∧
      L'.get? "signer" = some (.address a) ∧ L'.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  rcases hout with ⟨rfl,rfl⟩ | rfl
  · refine ⟨L,?_,hz,hh⟩
    apply ExecStmt.iteFalse
    · simp only [tryRecoverDecode,evalExpr?,readLocalPath?,hr,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?]
      rfl
    exact ExecBlock.nil
  · refine ⟨L.insert "signer" (.address a),?_,store_get_self _ _ _,?_⟩
    · apply ExecStmt.iteTrue
      · simp only [tryRecoverDecode,evalExpr?,readLocalPath?,hr,toByteArray_size,EvalResult.ofOption,EvalResult.bind,bind,pure,evalBinaryOp?]
        rfl
      apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) ?_ (assignLocalBase_ok hz)) ExecBlock.nil
      simp only [evalExpr?,hr,EvalResult.ofOption,EvalResult.bind,bind]
      have hd := decodeReturnSolc08Address_word easPlanTable a
      change config.externalABI.decodeValue? (.elem .address) _ = _ at hd
      rw [hd]
      rfl
    · simpa (disch := decide) only [store_get_ne] using hh

theorem tryRecoverZeroGuard_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {a : AccountAddress}
    (ha : frame.locals.get? "signer" = some (.address a)) :
    evalExpr? cfg frame evm tryRecoverZeroGuard = .ok (.bool (decide (a = 0))) := by
  simp only [tryRecoverZeroGuard,evalExpr?,ha,EvalResult.ofOption,EvalResult.bind,bind,pure,castValue?]
  change EvalResult.ok (Value.bool (Value.address a == Value.address 0)) = _
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,Value.address.injEq,decide_eq_true_eq]

def recoveryError (a : AccountAddress) : Nat := if a = 0 then 1 else 0

theorem tryRecoverTailSource {L imms : Store} {evm : EVM.State} {out : ByteArray} {a : AccountAddress}
    {heap : Nat} {success : Bool}
    (ho : L.get? "ok" = some (.bool success)) (hr : L.get? "result" = some (.bytes out))
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hout : (out = ByteArray.empty ∧ a = 0) ∨ out = (UInt256.ofNat a.val).toByteArray) :
    if success then ∃ L', ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm tryRecoverTail
      (.returned {contract := contract,locals := L',immutables := imms} evm
        (some [.tuple [.address a,.int (Int.ofNat (recoveryError a))],.int (Int.ofNat heap)]))
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm tryRecoverTail .reverted := by
  cases success with
  | false =>
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?,ho,EvalResult.ofOption]))
  | true =>
    let L0 := L.insert "signer" (.address 0)
    obtain ⟨L1,hd,ha,hh1⟩ := tryRecoverDecodeSource (L := L0) (imms := imms) (evm := evm) (heap := heap)
      (by simpa (disch := decide) only [L0,store_get_ne] using hr) (store_get_self _ _ _)
      (by simpa (disch := decide) only [L0,store_get_ne] using hh) hout
    refine ⟨L1,ExecBlock.consNormal (ExecStmt.requireTrue (by simp only [evalExpr?,ho,EvalResult.ofOption])) ?_⟩
    apply ExecBlock.consNormal (ExecStmt.letDecl (value := .address 0)
      (by simp only [evalExpr?,pure,EvalResult.bind,bind,castValue?,EvalResult.ofOption]; rfl))
    apply ExecBlock.consNormal hd
    have he := tryRecoverZeroGuard_eval (cfg := config) (evm := evm)
      (frame := {contract := contract,locals := L1,immutables := imms}) ha
    by_cases hz : a = 0
    · rw [recoveryError,if_pos hz]
      apply ExecBlock.consReturn
      apply ExecStmt.iteTrue
      · simpa only [hz,decide_true] using he
      apply ExecBlock.consReturn
      apply tryRecoverReturnSource _ hh1
      rw [hz]
      simp only [evalExpr?,pure,EvalResult.bind,bind,castValue?,EvalResult.ofOption]
      rfl
    · rw [recoveryError,if_neg hz]
      apply ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [hz,decide_false] using he) ExecBlock.nil)
      apply ExecBlock.consReturn
      exact tryRecoverReturnSource (by simp only [evalExpr?,ha,EvalResult.ofOption]) hh1

end Benchmarks.EAS.EAS
