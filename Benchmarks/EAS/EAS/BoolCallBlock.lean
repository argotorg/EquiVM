import Benchmarks.EAS.EAS.PayableCheck

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def boolCallBlock (callee : Ident) (args : List Expr) (tmp result : Ident) : Body := [
  .internalCall callee args tmp,
  .letDecl result none (.tupleGet (.var tmp) 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var tmp) 1),
  .require (.var result)]

def boolCallBlockLocals (locals : Store) (tmp result : Ident) (heap : Nat) (out : ByteArray) : Store :=
  unpackHeapLocals (locals.insert tmp (.tuple [
    .bool (decide (calldataWord out 0 ≠ ⟨0⟩)), .int (Int.ofNat (allocateNext heap (min out.size 32)))]))
    result "$EAS.freeMemory" (.bool (decide (calldataWord out 0 ≠ ⟨0⟩))) (allocateNext heap (min out.size 32))

-- The common caller-side argument for a resolver bool plus its updated allocation cursor.
theorem boolCallBlockSource {cfg : Config} {locals imms : Store} {evm evm' : EVM.State}
    {heap : Nat} {success : Bool} {out : ByteArray} {callee tmp result : Ident} {args : List Expr}
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (ht : (tmp == "$EAS.freeMemory") = false) (hrt : (result == tmp) = false)
    (hrh : (result == "$EAS.freeMemory") = false)
    (hc : if resolverCallValid heap success out then
      ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.internalCall callee args tmp)
        (.ok {contract := contract, locals := locals.insert tmp (.tuple [
          .bool (decide (calldataWord out 0 ≠ ⟨0⟩)), .int (Int.ofNat (allocateNext heap (min out.size 32)))]), immutables := imms} evm')
      else ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.internalCall callee args tmp) .reverted) :
    if callBoolAccepted heap success out then
      ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm (boolCallBlock callee args tmp result)
        (.ok {contract := contract, locals := boolCallBlockLocals locals tmp result heap out, immutables := imms} evm')
    else ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm (boolCallBlock callee args tmp result) .reverted := by
  by_cases hv : resolverCallValid heap success out
  · rw [if_pos hv] at hc
    have hu := unpackHeapResult (fork := fork) (cfg := cfg) (evm := evm')
      (frame := {contract := contract, locals := locals.insert tmp (.tuple [
        .bool (decide (calldataWord out 0 ≠ ⟨0⟩)), .int (Int.ofNat (allocateNext heap (min out.size 32)))]), immutables := imms})
      (result := result) (cursor := "$EAS.freeMemory") (tmp := tmp)
      (store_get_self _ _ _) (by simpa only [store_get_ne _ _ ht] using hh) hrt hrh
    have hhr : ("$EAS.freeMemory" == result) = false := by
      apply beq_eq_false_iff_ne.mpr
      exact (beq_eq_false_iff_ne.mp hrh).symm
    have he : evalExpr? cfg {contract := contract, locals := boolCallBlockLocals locals tmp result heap out, immutables := imms}
        evm' (.var result) = .ok (.bool (decide (calldataWord out 0 ≠ ⟨0⟩))) := by
      simp only [boolCallBlockLocals, unpackHeapLocals, evalExpr?, store_get_ne _ _ hhr, store_get_self, EvalResult.ofOption]
    by_cases hn : calldataWord out 0 ≠ ⟨0⟩
    · rw [if_pos (show callBoolAccepted heap success out from ⟨hv,hn⟩)]
      apply ExecBlock.consNormal hc
      exact execBlock_append hu (ExecBlock.consNormal (ExecStmt.requireTrue (by
        simpa only [boolCallBlockLocals, decide_eq_true hn] using he)) ExecBlock.nil)
    · rw [if_neg (show ¬ callBoolAccepted heap success out from fun h => hn h.2)]
      apply ExecBlock.consNormal hc
      exact execBlock_append hu (ExecBlock.consRevert (ExecStmt.requireFalse (by
        simpa only [boolCallBlockLocals, decide_eq_false hn] using he)))
  · rw [if_neg hv] at hc
    rw [if_neg (show ¬ callBoolAccepted heap success out from fun h => hv h.1)]
    exact ExecBlock.consRevert hc

theorem boolCallBlockLocals_heap (locals : Store) (tmp result : Ident) (heap : Nat) (out : ByteArray) :
    (boolCallBlockLocals locals tmp result heap out).get? "$EAS.freeMemory" =
      some (.int (Int.ofNat (allocateNext heap (min out.size 32)))) := by
  exact store_get_self _ _ _

theorem boolCallBlockLocals_get {locals : Store} {tmp result name : Ident} {heap : Nat} {out : ByteArray}
    (ht : (tmp == name) = false) (hr : (result == name) = false) (hh : ("$EAS.freeMemory" == name) = false) :
    (boolCallBlockLocals locals tmp result heap out).get? name = locals.get? name := by
  simp only [boolCallBlockLocals, unpackHeapLocals, store_get_ne _ _ ht, store_get_ne _ _ hr, store_get_ne _ _ hh]

end Benchmarks.EAS.EAS
