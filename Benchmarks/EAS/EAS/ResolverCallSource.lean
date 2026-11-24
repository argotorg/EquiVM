import Benchmarks.EAS.EAS.ResolverResultSource
import Benchmarks.EAS.EAS.ReturnDecode

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- Shared with both resolver call shapes: allocation and strict ABI bool decoding.
def resolverCallValid (heap : Nat) (success : Bool) (out : ByteArray) : Prop :=
  success = true ∧
  (allocateNext heap (min out.size 32) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (min out.size 32)) ∧
  BoolReturnValid out

instance (heap : Nat) (success : Bool) (out : ByteArray) : Decidable (resolverCallValid heap success out) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (32 ≤ out.size ∧ (_ = _ ∨ _ = _))))

def resolverResultFinalLocals (locals : Store) (out : ByteArray) (heap : Nat) : Store :=
  (resolverResultLocals locals out heap).insert "accepted" (.bool (decide (calldataWord out 0 ≠ ⟨0⟩)))

theorem resolverCallResultSource {locals imms : Store} {evm : EVM.State}
    {heap : Nat} {success : Bool} {out : ByteArray}
    (hok : locals.get? "ok" = some (.bool success))
    (hor : locals.get? "result" = some (.bytes out))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hout : out.size < 2^255) :
    if resolverCallValid heap success out then
      ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm
        (.require (.var "ok") :: resolverResultTail)
        (.returned {contract := contract, locals := resolverResultFinalLocals locals out heap, immutables := imms}
          evm (some [.bool (decide (calldataWord out 0 ≠ ⟨0⟩)), .int (Int.ofNat (allocateNext heap (min out.size 32)))]))
    else ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm
      (.require (.var "ok") :: resolverResultTail) .reverted := by
  have heok : evalExpr? config {contract := contract, locals := locals, immutables := imms}
      evm (.var "ok") = .ok (.bool success) := by simp only [evalExpr?, hok, EvalResult.ofOption]
  by_cases hvalid : resolverCallValid heap success out
  · rw [if_pos hvalid]
    apply ExecFuncBody.execBlockRet
    apply ExecBlock.consNormal (ExecStmt.requireTrue (heok.trans (congrArg (fun z => EvalResult.ok (Value.bool z)) hvalid.1)))
    exact resolverResultTail_ok hor hh hvalid.2.1 (easDecodeReturnBool_valid hvalid.2.2 hout)
  · rw [if_neg hvalid]
    apply ExecFuncBody.execBlockRevert
    cases success with
    | false => exact ExecBlock.consRevert (ExecStmt.requireFalse heok)
    | true =>
      apply ExecBlock.consNormal (ExecStmt.requireTrue heok)
      by_cases hg : allocateNext heap (min out.size 32) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (min out.size 32)
      · have hb : ¬ BoolReturnValid out := by
          intro h
          apply hvalid
          exact ⟨rfl, hg, h⟩
        exact resolverResultTail_decode_revert hor hh hg (easDecodeReturnBool_invalid hb hout)
      · exact resolverResultTail_allocation_revert hor hh hg

end Benchmarks.EAS.EAS
