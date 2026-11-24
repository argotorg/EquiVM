import Benchmarks.EAS.EAS.GetUIDExpr

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def getUIDArgs (a : AttestationRecord) (bump : UInt256) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "bump" (.int (Int.ofNat bump.toNat))
    |>.insert "attestation" a.value

theorem getUID_lookup : lookupCallable? contract "_getUID" = some getUIDFunction.toCallable := rfl

theorem getUID_bind (a : AttestationRecord) (bump : UInt256) (heap : Nat) :
    bindParams? getUIDFunction.params [a.value,.int (Int.ofNat bump.toNat),.int (Int.ofNat heap)] =
      some (getUIDArgs a bump heap) := rfl

theorem getUIDBodySource {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {a : AttestationRecord} {bump : UInt256} {heap : Nat}
    (ha : locals.get? "attestation" = some a.value)
    (hb : locals.get? "bump" = some (.int (Int.ofNat bump.toNat)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (ht : a.time.toNat < 2^64) (he : a.expirationTime.toNat < 2^64) (hc : bump.toNat < 2^32) :
    if allocateNext heap (157+a.data.size) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (157+a.data.size) then
      ∃ locals', ExecFuncBody fork cfg {contract := contract,locals := locals,immutables := imms} evm getUIDFunction.body
        (.returned {contract := contract,locals := locals',immutables := imms} evm
          (some [wordBytes32Value (getUIDWord a bump),.int (Int.ofNat (allocateNext heap (157+a.data.size)))]))
    else ExecFuncBody fork cfg {contract := contract,locals := locals,immutables := imms} evm getUIDFunction.body .reverted := by
  let L := locals.insert "payload" (.bytes a.data)
  have hp : ExecBlock fork cfg {contract := contract,locals := locals,immutables := imms} evm
      [.letDecl "payload" (some .bytes) (.field (.var "attestation") "data")]
      (.ok {contract := contract,locals := L,immutables := imms} evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl (attestationRecord_field ha "data" _ rfl)) ExecBlock.nil
  have hh1 : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
    simpa only [L,store_get_ne _ _ (by decide : ("payload" == "$EAS.freeMemory") = false)] using hh
  have hsize : evalExpr? cfg {contract := contract,locals := L,immutables := imms} evm getUIDAllocateExpr =
      .ok (.int (Int.ofNat (157+a.data.size))) := by
    simp only [getUIDAllocateExpr,evalExpr?,readLocalPath?,L,store_get_self,EvalResult.bind,bind,pure,evalBinaryOp?]
    rfl
  by_cases hg : allocateNext heap (157+a.data.size) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (157+a.data.size)
  · rw [if_pos hg]
    let final := allocateBlockLocals L (allocateNext heap (157+a.data.size))
    refine ⟨final,?_⟩
    rw [getUID_body,List.append_assoc]
    apply ExecFuncBody.execBlockRet
    apply execBlock_append hp
    apply execBlock_append (allocateBlock_ok hsize hh1 hg)
    apply ExecBlock.consReturn
    apply ExecStmt.return
    have ha' : final.get? "attestation" = some a.value := by
      rw [allocateBlockLocals_get (by decide) (by decide) (by decide)]
      simpa only [L,store_get_ne _ _ (by decide : ("payload" == "attestation") = false)] using ha
    have hb' : final.get? "bump" = some (.int (Int.ofNat bump.toNat)) := by
      rw [allocateBlockLocals_get (by decide) (by decide) (by decide)]
      simpa only [L,store_get_ne _ _ (by decide : ("payload" == "bump") = false)] using hb
    have hu := getUIDExpr_eval (cfg := cfg) (evm := evm)
      (frame := {contract := contract,locals := final,immutables := imms}) ha' hb' ht he hc
    change evalExprs? cfg {contract := contract,locals := final,immutables := imms} evm
      [getUIDExpr,.var "$EAS.freeMemory"] = _
    simp only [evalExprs?,hu,EvalResult.bind,bind,pure]
    simp only [evalExpr?,final,allocateBlockLocals,unpackHeapLocals,store_get_self,EvalResult.ofOption,EvalResult.bind,bind,pure]
  · rw [if_neg hg,getUID_body,List.append_assoc]
    apply ExecFuncBody.execBlockRevert
    apply execBlock_append hp
    exact execBlock_append_term (allocateBlock_revert hsize hh1 hg) (by intros;exact nofun)

end Benchmarks.EAS.EAS
