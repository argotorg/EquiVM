import Benchmarks.EAS.EAS.ResolveManyLocals

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolveManyResolverLocals (locals : Store) (rev : Bool) (heap : Nat) (out : ByteArray) : Store :=
  boolCallBlockLocals locals (resolveManyCallTmp rev) (resolveManyCallResult rev) heap out
def resolveManyRefundLocals (locals : Store) (heap : Nat) : Store :=
  unpackHeapLocals (locals.insert "__c4$allocation" (.tuple [.tuple [],.int (Int.ofNat heap)]))
    "__c4" "$EAS.freeMemory" (.tuple []) heap

theorem ResolveManyLocals.resolved {locals : Store} {ats : List AttestationRecord} {words : List UInt256}
    {target : AccountAddress} {available total : UInt256} {rev last : Bool} {heap i : Nat}
    (h : ResolveManyLocals locals ats words target available total rev last heap i) (out : ByteArray) :
    ResolveManyLocals (resolveManyResolverLocals locals rev heap out) ats words target available total rev last
      (allocateNext heap (min out.size 32)) i := by
  rcases h with ⟨hr,ha,hv,hl,hi,hav,ht,hrv,hlast,hh⟩
  cases rev <;> constructor <;> simp (disch := decide) only [resolveManyResolverLocals,boolCallBlockLocals,
    resolveManyCallTmp,resolveManyCallResult,Bool.false_eq_true,if_true,if_false,unpackHeapLocals,
    store_get_self,store_get_ne] <;> assumption

theorem ResolveManyLocals.refunded {locals : Store} {ats : List AttestationRecord} {words : List UInt256}
    {target : AccountAddress} {available total : UInt256} {rev last : Bool} {heap i : Nat}
    (h : ResolveManyLocals locals ats words target available total rev last heap i) (heap' : Nat) :
    ResolveManyLocals (resolveManyRefundLocals locals heap') ats words target available total rev last heap' i := by
  rcases h with ⟨hr,ha,hv,hl,hi,hav,ht,hrv,hlast,hh⟩
  constructor <;> simp (disch := decide) only [resolveManyRefundLocals,unpackHeapLocals,store_get_self,store_get_ne] <;> assumption

theorem resolveManyResolverSource {locals imms : Store} {evm evm' : EVM.State}
    {ats : List AttestationRecord} {words : List UInt256} {target : AccountAddress} {total available : UInt256}
    {rev last success : Bool} {heap i : Nat} {out : ByteArray}
    (h : ResolveManyLocals locals ats words target available total rev last heap i)
    (hdata : ∀ a ∈ ats, a.data.size < UInt256.size) (hbound : attestationArrayOffset ats ats.length < UInt256.size)
    (hvlen : words.length < UInt256.size) (hsize : 64+(attestationArrayEncoding ats).size < UInt256.size)
    (hc : callViaEVM fork evm target (Int.ofNat total.toNat) (resolverManyPayload ats words rev) (success,evm',out))
    (hout : out.size < 2^255)
    (hperm : EVM.wordOfInt (Int.ofNat total.toNat) = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
    if callBoolAccepted heap success out then
      ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm resolveManyResolver
        (.ok {contract := contract, locals := resolveManyResolverLocals locals rev heap out, immutables := imms} evm')
    else ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm resolveManyResolver .reverted := by
  have hcall := resolverManyCall (hperm := hperm) (heap := heap) (imms := imms)
    (locals := locals) (retVar := resolveManyCallTmp rev)
    (args := [.var "resolver",.var "attestations",.var "values",.boolLit rev,.var "totalUsedValue",.var "$EAS.freeMemory"])
    (by simp only [evalExprs?,evalExpr?,h.resolver,h.attestations,h.values,h.total,h.heap,EvalResult.ofOption,EvalResult.bind,bind,pure])
    hdata hbound hvlen hsize hc hout
  have hb := boolCallBlockSource (result := resolveManyCallResult rev) h.heap
    (by cases rev <;> decide) (by cases rev <;> decide) (by cases rev <;> decide) hcall
  have he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm (.var "isRevocation") =
      .ok (.bool rev) := by simp only [evalExpr?,h.revocation,EvalResult.ofOption]
  by_cases hg : callBoolAccepted heap success out
  · rw [if_pos hg] at hb ⊢
    cases rev with
    | false => exact ExecStmt.iteFalse he hb
    | true => exact ExecStmt.iteTrue he hb
  · rw [if_neg hg] at hb ⊢
    cases rev with
    | false => exact ExecStmt.iteFalse he hb
    | true => exact ExecStmt.iteTrue he hb

theorem resolveManyRefundBlockSource {cfg : Config} {locals imms : Store} {evm evm' : EVM.State} {old heap : Nat}
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat old)))
    (hc : ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_refund" [.var "availableValue", .var "$EAS.freeMemory"] "__c4$allocation")
      (.ok {contract := contract, locals := locals.insert "__c4$allocation" (.tuple [.tuple [],.int (Int.ofNat heap)]), immutables := imms} evm')) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveManyRefundBlock
      (.ok {contract := contract, locals := resolveManyRefundLocals locals heap, immutables := imms} evm') := by
  apply ExecBlock.consNormal hc
  exact unpackHeapResult (store_get_self _ _ _)
    (by simpa only [store_get_ne _ _ (by decide : ("__c4$allocation" == "$EAS.freeMemory") = false)] using hh)
    (by decide) (by decide)

theorem resolveManyReturnSource {cfg : Config} {locals imms : Store} {evm : EVM.State} {total : UInt256} {heap : Nat}
    (ht : locals.get? "totalUsedValue" = some (.int (Int.ofNat total.toNat)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm resolveManyReturn
      (.returned {contract := contract, locals := locals, immutables := imms} evm
        (some [.int (Int.ofNat total.toNat),.int (Int.ofNat heap)])) := by
  apply ExecFuncBody.execBlockRet (ExecBlock.consReturn (ExecStmt.return ?_))
  simp only [evalExprs?,evalExpr?,ht,hh,EvalResult.ofOption,EvalResult.bind,bind,pure]

end Benchmarks.EAS.EAS
