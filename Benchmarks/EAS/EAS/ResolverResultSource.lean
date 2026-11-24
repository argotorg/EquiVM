import Benchmarks.EAS.EAS.AllocateBlock
import Reasoning.ABIComposite

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolverCopyPrefix : Body := [
  .letDecl "copied" (some abiUInt256) (.arrayLength .localVar {base := "result"}),
  .ite (.binary .gt (.var "copied") (.intLit 32))
    [.assign .localVar {base := "copied"} (.intLit 32)] []]

def resolverCopiedLocals (locals : Store) (n : Nat) : Store :=
  if 32 < n then (locals.insert "copied" (.int (Int.ofNat n))).insert "copied" (.int 32)
  else locals.insert "copied" (.int (Int.ofNat n))

theorem resolverCopiedLocals_copied (locals : Store) (n : Nat) :
    (resolverCopiedLocals locals n).get? "copied" = some (.int (Int.ofNat (min n 32))) := by
  unfold resolverCopiedLocals
  split <;> simp only [store_get_self]
  · rw [Nat.min_eq_right (by omega)]; rfl
  · rw [Nat.min_eq_left (by omega)]

theorem resolverCopiedLocals_get (locals : Store) (n : Nat) (name : Ident)
    (hne : ("copied" == name) = false) :
    (resolverCopiedLocals locals n).get? name = locals.get? name := by
  unfold resolverCopiedLocals
  split <;> simp only [store_get_ne _ _ hne]

theorem resolverCopyPrefix_exec {cfg : Config} {locals imms : Store} {evm : EVM.State} {out : ByteArray}
    (ho : locals.get? "result" = some (.bytes out)) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolverCopyPrefix
      (.ok {contract := contract, locals := resolverCopiedLocals locals out.size, immutables := imms} evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .int (Int.ofNat out.size)) (by
    simp only [evalExpr?, readLocalPath?, ho, EvalResult.bind, bind, pure]))
  have hc : evalExpr? cfg {contract := contract, locals := locals.insert "copied" (.int (Int.ofNat out.size)), immutables := imms}
      evm (.binary .gt (.var "copied") (.intLit 32)) = .ok (.bool (decide (32 < out.size))) := by
    have hgt : (Int.ofNat out.size > (32 : Int)) = (32 < out.size) := by apply propext; simp only [Int.ofNat_eq_natCast]; omega
    simp only [evalExpr?, store_get_self, EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, hgt]
  by_cases hgt : 32 < out.size
  · rw [resolverCopiedLocals, if_pos hgt]
    apply ExecBlock.consNormal (ExecStmt.iteTrue (by simpa only [hgt, decide_true] using hc) ?_) ExecBlock.nil
    exact ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (by simp only [evalExpr?, pure])
      (assignLocalBase_ok (store_get_self _ _ _))) ExecBlock.nil
  · rw [resolverCopiedLocals, if_neg hgt]
    exact ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [hgt, decide_false] using hc) ExecBlock.nil) ExecBlock.nil

def resolverReturnSuffix : Body := [
  .letDecl "accepted" (some abiBool) (.abiDecode abiBool (.var "result")),
  .return [.var "accepted", .var "$EAS.freeMemory"],
  .return [.tupleLit [], .var "$EAS.freeMemory"]]

def resolverResultTail : Body := resolverCopyPrefix ++ allocateBlock (.var "copied") ++ resolverReturnSuffix

def resolverResultLocals (locals : Store) (out : ByteArray) (heap : Nat) : Store :=
  allocateBlockLocals (resolverCopiedLocals locals out.size) (allocateNext heap (min out.size 32))

theorem resolverResultAllocation {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {out : ByteArray} {heap : Nat}
    (ho : locals.get? "result" = some (.bytes out))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : allocateNext heap (min out.size 32) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (min out.size 32)) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm
      (resolverCopyPrefix ++ allocateBlock (.var "copied"))
      (.ok {contract := contract, locals := resolverResultLocals locals out heap, immutables := imms} evm) := by
  apply execBlock_append (resolverCopyPrefix_exec ho)
  apply allocateBlock_ok
  · simp only [evalExpr?, resolverCopiedLocals_copied, EvalResult.ofOption]
  · simpa only [resolverCopiedLocals_get _ _ "$EAS.freeMemory" (by decide)] using hh
  · exact hg

theorem resolverResultLocals_result (locals : Store) (out : ByteArray) (heap : Nat) :
    (resolverResultLocals locals out heap).get? "result" = locals.get? "result" := by
  rw [resolverResultLocals, allocateBlockLocals_get (by decide) (by decide) (by decide),
    resolverCopiedLocals_get _ _ _ (by decide)]

theorem resolverResultLocals_heap (locals : Store) (out : ByteArray) (heap : Nat) :
    (resolverResultLocals locals out heap).get? "$EAS.freeMemory" =
      some (.int (Int.ofNat (allocateNext heap (min out.size 32)))) := by
  exact store_get_self _ _ _

theorem resolverResultTail_ok {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {out : ByteArray} {heap : Nat} {accepted : Bool}
    (ho : locals.get? "result" = some (.bytes out))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : allocateNext heap (min out.size 32) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (min out.size 32))
    (hd : cfg.externalABI.decodeValue? abiBool out = some (.bool accepted)) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolverResultTail
      (.returned {contract := contract, locals := (resolverResultLocals locals out heap).insert "accepted" (.bool accepted), immutables := imms}
        evm (some [.bool accepted, .int (Int.ofNat (allocateNext heap (min out.size 32)))])) := by
  apply execBlock_append (resolverResultAllocation ho hh hg)
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .bool accepted) (by
    simp only [evalExpr?, resolverResultLocals_result, ho, EvalResult.ofOption, EvalResult.bind, bind, hd, pure]))
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, store_get_self,
    store_get_ne _ _ (by decide : ("accepted" == "$EAS.freeMemory") = false),
    resolverResultLocals_heap, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem resolverResultTail_decode_revert {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {out : ByteArray} {heap : Nat}
    (ho : locals.get? "result" = some (.bytes out))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : allocateNext heap (min out.size 32) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (min out.size 32))
    (hd : cfg.externalABI.decodeValue? abiBool out = none) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolverResultTail .reverted := by
  apply execBlock_append (resolverResultAllocation ho hh hg)
  apply ExecBlock.consRevert (ExecStmt.letDeclRevert ?_)
  simp only [evalExpr?, resolverResultLocals_result, ho, EvalResult.ofOption, EvalResult.bind, bind, hd]

theorem resolverResultTail_allocation_revert {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {out : ByteArray} {heap : Nat}
    (ho : locals.get? "result" = some (.bytes out))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : ¬ (allocateNext heap (min out.size 32) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (min out.size 32))) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolverResultTail .reverted := by
  rw [resolverResultTail, List.append_assoc]
  apply execBlock_append (resolverCopyPrefix_exec ho)
  apply execBlock_append_term (allocateBlock_revert (n := min out.size 32)
    (by simp only [evalExpr?, resolverCopiedLocals_copied, EvalResult.ofOption])
    (by simpa only [resolverCopiedLocals_get _ _ "$EAS.freeMemory" (by decide)] using hh) hg)
  intro _ _ h
  cases h

end Benchmarks.EAS.EAS
