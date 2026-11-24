import Benchmarks.EAS.EAS.Allocate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def allocateBlock (size : Expr) : Body := [
  .internalCall "_allocate" [size, .var "$EAS.freeMemory"] "allocation$allocation",
  .letDecl "allocation" none (.tupleGet (.var "allocation$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "allocation$allocation") 1)]

def allocateBlockLocals (locals : Store) (heap : Nat) : Store :=
  unpackHeapLocals (locals.insert "allocation$allocation" (.tuple [.tuple [], .int (Int.ofNat heap)]))
    "allocation" "$EAS.freeMemory" (.tuple []) heap

theorem allocateBlock_ok {cfg : Config} {evm : EVM.State} {locals imms : Store} {size : Expr} {n heap : Nat}
    (hs : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm size = .ok (.int (Int.ofNat n)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : allocateNext heap n ≤ 2^64-1 ∧ heap ≤ allocateNext heap n) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm (allocateBlock size)
      (.ok {contract := contract, locals := allocateBlockLocals locals (allocateNext heap n), immutables := imms} evm) := by
  apply ExecBlock.consNormal (allocateCall_ok hs (by simp only [evalExpr?, hh, EvalResult.ofOption]) hg)
  exact unpackHeapResult (store_get_self _ _ _)
    (by simpa only [store_get_ne _ _ (by decide : ("allocation$allocation" == "$EAS.freeMemory") = false)] using hh)
    (by decide) (by decide)

theorem allocateBlock_revert {cfg : Config} {evm : EVM.State} {locals imms : Store} {size : Expr} {n heap : Nat}
    (hs : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm size = .ok (.int (Int.ofNat n)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hg : ¬ (allocateNext heap n ≤ 2^64-1 ∧ heap ≤ allocateNext heap n)) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm (allocateBlock size) .reverted := by
  exact ExecBlock.consRevert (allocateCall_revert hs (by simp only [evalExpr?, hh, EvalResult.ofOption]) hg)

theorem allocateBlockLocals_get {locals : Store} {heap : Nat} {name : Ident}
    (h1 : ("allocation$allocation" == name) = false)
    (h2 : ("allocation" == name) = false) (h3 : ("$EAS.freeMemory" == name) = false) :
    (allocateBlockLocals locals heap).get? name = locals.get? name := by
  simp only [allocateBlockLocals, unpackHeapLocals, store_get_ne _ _ h1, store_get_ne _ _ h2, store_get_ne _ _ h3]

end Benchmarks.EAS.EAS
