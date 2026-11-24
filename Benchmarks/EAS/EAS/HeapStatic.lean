import Benchmarks.EAS.EAS.HeapCall
import Benchmarks.EAS.EAS.HeapBranch
import Benchmarks.EAS.EAS.TimestampSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: coupled heap-returning calls with a possible static-mode halt.
def HeapReturnOrStatic (fork : Ethereum.Fork) (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (frame : Frame) (evm : EVM.State) (body : Body) (value : Value) (pc : UInt256) (stack : List UInt256)
    (mem : ByteArray) (heap : Nat) : Prop :=
  HeapReturnRun fork cfg code ee g s0 frame evm body value pc stack mem heap ∨
    (ExecFuncBody fork cfg frame evm body .staticViolation ∧ RDstatic fork code g s0)

def HeapCallOrStatic (fork : Ethereum.Fork) (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (caller : Frame) (evm : EVM.State) (name : Ident) (args : List Expr) (retVar : Ident)
    (value : Value) (pc : UInt256) (stack : List UInt256) (mem : ByteArray) (heap : Nat) : Prop :=
  HeapCallRun fork cfg code ee g s0 caller evm name args retVar value pc stack mem heap ∨
    (ExecStmt fork cfg caller evm (.internalCall name args retVar) .staticViolation ∧ RDstatic fork code g s0)

theorem HeapReturnOrStatic.prepend {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {frame frame1 : Frame} {evm evm1 : EVM.State} {front suffix : Body} {value : Value}
    {pc : UInt256} {stack : List UInt256} {mem mem1 : ByteArray} {heap heap1 : Nat}
    (h : HeapReturnOrStatic fork cfg code ee g s0 frame1 evm1 suffix value pc stack mem1 heap1)
    (hp : ExecBlock fork cfg frame evm front (.ok frame1 evm1))
    (hm : MemoryPrefix mem mem1 heap) (hle : heap ≤ heap1) :
    HeapReturnOrStatic fork cfg code ee g s0 frame evm (front ++ suffix) value pc stack mem heap := by
  rcases h with h | ⟨hsrc,hr⟩
  · exact Or.inl (h.prepend hp hm hle)
  · exact Or.inr ⟨execFuncBody_append hp hsrc,hr⟩

theorem HeapReturnOrStatic.of_revert_prefix {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {frame : Frame} {evm : EVM.State} {front suffix : Body} {value : Value}
    {pc : UInt256} {stack : List UInt256} {mem : ByteArray} {heap : Nat}
    (hp : ExecBlock fork cfg frame evm front .reverted) (hr : RDrev fork code g s0) :
    HeapReturnOrStatic fork cfg code ee g s0 frame evm (front ++ suffix) value pc stack mem heap :=
  Or.inl (HeapReturnRun.of_revert_prefix hp hr)

theorem HeapReturnOrStatic.call {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {caller : Frame} {evm : EVM.State} {callee : FunctionDecl} {name retVar : Ident} {args : List Expr}
    {argVals : List Value} {bindings : Store} {value : Value} {pc : UInt256} {stack : List UInt256}
    {mem : ByteArray} {heap : Nat}
    (h : HeapReturnOrStatic fork cfg code ee g s0 {caller with locals := bindings} evm callee.body value pc stack mem heap)
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some bindings) :
    HeapCallOrStatic fork cfg code ee g s0 caller evm name args retVar value pc stack mem heap := by
  rcases h with h | ⟨hsrc,hr⟩
  · exact Or.inl (h.call hargs hlookup hbind)
  · exact Or.inr ⟨internalCallFunctionStatic hargs hlookup hbind hsrc,hr⟩

end Benchmarks.EAS.EAS
