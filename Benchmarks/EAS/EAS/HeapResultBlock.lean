import Benchmarks.EAS.EAS.AllocateBlock

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a modular internal call followed by result and heap unpacking.
def heapResultBlock (callee : Ident) (args : List Expr) (tmp result cursor : Ident) : Body := [
  .internalCall callee args tmp,.letDecl result none (.tupleGet (.var tmp) 0),
  .assign .localVar {base := cursor} (.tupleGet (.var tmp) 1)]
def heapResultLocals (L : Store) (tmp result cursor : Ident) (value : Value) (heap : Nat) : Store :=
  unpackHeapLocals (L.insert tmp (.tuple [value,.int (Int.ofNat heap)])) result cursor value heap

theorem heapResultBlock_ok {cfg : Config} {frame : Frame} {evm evm' : EVM.State}
    {callee tmp result cursor : Ident} {args : List Expr} {value oldHeap : Value} {heap : Nat}
    (hc : ExecStmt fork cfg frame evm (.internalCall callee args tmp)
      (.ok (resumeAfterInternalCall frame tmp (some [value,.int (Int.ofNat heap)])) evm'))
    (hh : frame.locals.get? cursor = some oldHeap)
    (htc : (tmp == cursor) = false) (htr : (result == tmp) = false) (hrc : (result == cursor) = false) :
    ExecBlock fork cfg frame evm (heapResultBlock callee args tmp result cursor)
      (.ok {frame with locals := heapResultLocals frame.locals tmp result cursor value heap} evm') := by
  apply ExecBlock.consNormal hc
  exact unpackHeapResult (store_get_self _ _ _) ((store_get_ne _ _ htc).trans hh) htr hrc

theorem heapResultLocals_get (L : Store) (tmp result cursor : Ident) (value : Value) (heap : Nat)
    (name : Ident) (ht : (tmp == name) = false) (hr : (result == name) = false) (hc : (cursor == name) = false) :
    (heapResultLocals L tmp result cursor value heap).get? name = L.get? name := by
  simp only [heapResultLocals,unpackHeapLocals,store_get_ne _ _ ht,store_get_ne _ _ hr,store_get_ne _ _ hc]

theorem heapResultLocals_heap (L : Store) (tmp result cursor : Ident) (value : Value) (heap : Nat) :
    (heapResultLocals L tmp result cursor value heap).get? cursor = some (.int (Int.ofNat heap)) :=
  store_get_self _ _ _

theorem heapResultLocals_result (L : Store) (tmp result cursor : Ident) (value : Value) (heap : Nat)
    (hc : (cursor == result) = false) :
    (heapResultLocals L tmp result cursor value heap).get? result = some value := by
  simp only [heapResultLocals,unpackHeapLocals,store_get_ne _ _ hc,store_get_self]

end Benchmarks.EAS.EAS
