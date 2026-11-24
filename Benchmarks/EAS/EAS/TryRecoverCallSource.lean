import Benchmarks.EAS.EAS.TryRecoverSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def tryRecoverCallLocals (L : Store) (hash v r s : UInt256) (success : Bool) (out : ByteArray) : Store :=
  tryRecoverInputLocals L hash v r s |>.insert "ok" (.bool success) |>.insert "result" (.bytes out)

theorem tryRecoverLowSource {L imms : Store} {evm evm' : EVM.State} {hash v r s : UInt256}
    {heap : Nat} {success : Bool} {out : ByteArray} {a : AccountAddress}
    (hh : L.get? "hash" = some (wordBytes32Value hash))
    (hv : L.get? "v" = some (.int (Int.ofNat v.toNat)))
    (hr : L.get? "r" = some (wordBytes32Value r))
    (hs : L.get? "s" = some (wordBytes32Value s))
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hi : ¬ ecdsaHalfOrder < s.toNat)
    (hc : callViaEVM fork evm (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) 0 (tryRecoverPayload hash v r s)
      (success,evm',out) false)
    (hout : (out = ByteArray.empty ∧ a = 0) ∨ out = (UInt256.ofNat a.val).toByteArray) :
    if success then ∃ L', ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm tryRecoverFunction.body
      (.returned {contract := contract,locals := L',immutables := imms} evm'
        (some [.tuple [.address a,.int (Int.ofNat (recoveryError a))],.int (Int.ofNat heap)]))
    else ExecFuncBody fork config {contract := contract,locals := L,immutables := imms} evm tryRecoverFunction.body .reverted := by
  have hguard := tryRecoverGuard_eval (cfg := config) (evm := evm)
    (frame := {contract := contract,locals := L,immutables := imms}) hs
  have hinvoke : ExecStmt fork config {contract := contract,locals := tryRecoverInputLocals L hash v r s,immutables := imms} evm
      tryRecoverInvoke
      (.ok {contract := contract,locals := tryRecoverCallLocals L hash v r s success out,immutables := imms} evm') := by
    apply lowLevelCallSource_perm (hperm := Or.inl rfl) (target := AccountAddress.ofUInt256 (⟨1⟩ : UInt256)) _ _ _ hc
    · simp (disch := decide) only [evalExpr?,tryRecoverInputLocals,store_get_ne,store_get_self,EvalResult.ofOption]
      rfl
    · simp only [evalExpr?,pure]
    · simp only [evalExpr?,tryRecoverInputLocals,store_get_self,EvalResult.ofOption]
  have htail := tryRecoverTailSource (fork := fork) (L := tryRecoverCallLocals L hash v r s success out) (imms := imms)
    (evm := evm') (heap := heap) (success := success) (out := out) (a := a)
    (by simp (disch := decide) only [tryRecoverCallLocals,store_get_ne,store_get_self])
    (store_get_self _ _ _)
    (by simpa (disch := decide) only [tryRecoverCallLocals,tryRecoverInputLocals,store_get_ne] using hf) hout
  cases success with
  | false =>
    simp only [Bool.false_eq_true,if_false] at htail ⊢
    rw [tryRecover_body]
    simp only [List.append_assoc]
    apply ExecFuncBody.execBlockRevert
    apply execBlock_append (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [hi,decide_false] using hguard) ExecBlock.nil) ExecBlock.nil)
    apply execBlock_append (tryRecoverInitSource hh hv hr hs)
    exact execBlock_append (ExecBlock.consNormal hinvoke ExecBlock.nil) htail
  | true =>
    simp only [if_true] at htail ⊢
    obtain ⟨L',htail⟩ := htail
    refine ⟨L',?_⟩
    rw [tryRecover_body]
    simp only [List.append_assoc]
    apply ExecFuncBody.execBlockRet
    apply execBlock_append (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [hi,decide_false] using hguard) ExecBlock.nil) ExecBlock.nil)
    apply execBlock_append (tryRecoverInitSource hh hv hr hs)
    exact execBlock_append (ExecBlock.consNormal hinvoke ExecBlock.nil) htail

def tryRecoverArgs (hash v r s : UInt256) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "s" (wordBytes32Value s)
    |>.insert "r" (wordBytes32Value r) |>.insert "v" (.int (Int.ofNat v.toNat)) |>.insert "hash" (wordBytes32Value hash)
theorem tryRecover_lookup : lookupCallable? contract "ECDSA_tryRecover" = some tryRecoverFunction.toCallable := rfl
theorem tryRecover_bind (hash v r s : UInt256) (heap : Nat) :
    bindParams? tryRecoverFunction.params [wordBytes32Value hash,.int (Int.ofNat v.toNat),wordBytes32Value r,
      wordBytes32Value s,.int (Int.ofNat heap)] = some (tryRecoverArgs hash v r s heap) := rfl

end Benchmarks.EAS.EAS
