import Benchmarks.EAS.EAS.HeapStatic

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a pure postcondition required only along returning paths.
def HeapReturnPost (fork : Ethereum.Fork) (post : Prop) (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (frame : Frame) (evm : EVM.State) (body : Body) (value : Value) (pc : UInt256) (stack : List UInt256)
    (mem : ByteArray) (heap : Nat) : Prop :=
  (post ∧ HeapReturnRun fork cfg code ee g s0 frame evm body value pc stack mem heap) ∨
  (ExecFuncBody fork cfg frame evm body .reverted ∧ RDrev fork code g s0)

def HeapCallPost (fork : Ethereum.Fork) (post : Prop) (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (caller : Frame) (evm : EVM.State) (name : Ident) (args : List Expr) (retVar : Ident)
    (value : Value) (pc : UInt256) (stack : List UInt256) (mem : ByteArray) (heap : Nat) : Prop :=
  (post ∧ HeapCallRun fork cfg code ee g s0 caller evm name args retVar value pc stack mem heap) ∨
  (ExecStmt fork cfg caller evm (.internalCall name args retVar) .reverted ∧ RDrev fork code g s0)

def HeapReturnPostOrStatic (fork : Ethereum.Fork) (post : Prop) (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (frame : Frame) (evm : EVM.State) (body : Body) (value : Value) (pc : UInt256) (stack : List UInt256)
    (mem : ByteArray) (heap : Nat) : Prop :=
  HeapReturnPost fork post cfg code ee g s0 frame evm body value pc stack mem heap ∨
  (ExecFuncBody fork cfg frame evm body .staticViolation ∧ RDstatic fork code g s0)

def HeapCallPostOrStatic (fork : Ethereum.Fork) (post : Prop) (cfg : Config) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : EVM.State)
    (caller : Frame) (evm : EVM.State) (name : Ident) (args : List Expr) (retVar : Ident)
    (value : Value) (pc : UInt256) (stack : List UInt256) (mem : ByteArray) (heap : Nat) : Prop :=
  HeapCallPost fork post cfg code ee g s0 caller evm name args retVar value pc stack mem heap ∨
  (ExecStmt fork cfg caller evm (.internalCall name args retVar) .staticViolation ∧ RDstatic fork code g s0)

variable {post : Prop} {cfg : Config} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
  {frame frame1 : Frame} {evm evm1 : EVM.State} {body front suffix : Body} {value : Value}
  {pc : UInt256} {stack : List UInt256} {mem mem1 : ByteArray} {heap heap1 : Nat}

theorem HeapReturnRun.withPost (h : HeapReturnRun fork cfg code ee g s0 frame evm body value pc stack mem heap)
    (hp : post) : HeapReturnPost fork post cfg code ee g s0 frame evm body value pc stack mem heap := Or.inl ⟨hp,h⟩

theorem HeapReturnPost.forget (h : HeapReturnPost fork post cfg code ee g s0 frame evm body value pc stack mem heap) :
    HeapReturnRun fork cfg code ee g s0 frame evm body value pc stack mem heap := by
  rcases h with ⟨_,h⟩ | h
  · exact h
  · exact Or.inr h

theorem HeapReturnPost.prepend
    (h : HeapReturnPost fork post cfg code ee g s0 frame1 evm1 suffix value pc stack mem1 heap1)
    (hp : ExecBlock fork cfg frame evm front (.ok frame1 evm1))
    (hm : MemoryPrefix mem mem1 heap) (hle : heap ≤ heap1) :
    HeapReturnPost fork post cfg code ee g s0 frame evm (front++suffix) value pc stack mem heap := by
  rcases h with ⟨hb,h⟩ | ⟨hsrc,hr⟩
  · exact (h.prepend hp hm hle).withPost hb
  · exact Or.inr ⟨execFuncBody_append hp hsrc,hr⟩

theorem HeapReturnPost.of_revert_prefix
    (hp : ExecBlock fork cfg frame evm front .reverted) (hr : RDrev fork code g s0) :
    HeapReturnPost fork post cfg code ee g s0 frame evm (front++suffix) value pc stack mem heap :=
  Or.inr ⟨ExecFuncBody.execBlockRevert (execBlock_append_term hp (by intros; exact nofun)),hr⟩

theorem HeapReturnPost.iteTrue {cond : Expr} {thenB elseB : Body}
    (h : HeapReturnPost fork post cfg code ee g s0 frame evm thenB value pc stack mem heap)
    (he : evalExpr? cfg frame evm cond = .ok (.bool true)) :
    HeapReturnPost fork post cfg code ee g s0 frame evm (.ite cond thenB elseB::suffix) value pc stack mem heap := by
  rcases h with ⟨hb,h⟩ | ⟨hsrc,hr⟩
  · exact (h.iteTrue he).withPost hb
  · cases hsrc with
    | execBlockRevert hblock =>
      exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.iteTrue he hblock)),hr⟩

theorem HeapReturnPost.call {caller : Frame} {callee : FunctionDecl} {name retVar : Ident} {args : List Expr}
    {argVals : List Value} {bindings : Store}
    (h : HeapReturnPost fork post cfg code ee g s0 {caller with locals := bindings} evm callee.body value pc stack mem heap)
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some bindings) :
    HeapCallPost fork post cfg code ee g s0 caller evm name args retVar value pc stack mem heap := by
  rcases h with ⟨hb,h⟩ | ⟨hsrc,hr⟩
  · exact Or.inl ⟨hb,h.call hargs hlookup hbind⟩
  · exact Or.inr ⟨internalCallFunctionRevert hargs hlookup hbind hsrc,hr⟩

theorem HeapReturnOrStatic.withPost
    (h : HeapReturnOrStatic fork cfg code ee g s0 frame evm body value pc stack mem heap) (hp : post) :
    HeapReturnPostOrStatic fork post cfg code ee g s0 frame evm body value pc stack mem heap := by
  rcases h with h | h
  · exact Or.inl (h.withPost hp)
  · exact Or.inr h

theorem HeapReturnPostOrStatic.forget
    (h : HeapReturnPostOrStatic fork post cfg code ee g s0 frame evm body value pc stack mem heap) :
    HeapReturnOrStatic fork cfg code ee g s0 frame evm body value pc stack mem heap := by
  rcases h with h | h
  · exact Or.inl h.forget
  · exact Or.inr h

theorem HeapReturnPostOrStatic.prepend
    (h : HeapReturnPostOrStatic fork post cfg code ee g s0 frame1 evm1 suffix value pc stack mem1 heap1)
    (hp : ExecBlock fork cfg frame evm front (.ok frame1 evm1))
    (hm : MemoryPrefix mem mem1 heap) (hle : heap ≤ heap1) :
    HeapReturnPostOrStatic fork post cfg code ee g s0 frame evm (front++suffix) value pc stack mem heap := by
  rcases h with h | ⟨hsrc,hr⟩
  · exact Or.inl (h.prepend hp hm hle)
  · exact Or.inr ⟨execFuncBody_append hp hsrc,hr⟩

theorem HeapReturnPostOrStatic.of_revert_prefix
    (hp : ExecBlock fork cfg frame evm front .reverted) (hr : RDrev fork code g s0) :
    HeapReturnPostOrStatic fork post cfg code ee g s0 frame evm (front++suffix) value pc stack mem heap :=
  Or.inl (HeapReturnPost.of_revert_prefix hp hr)

theorem HeapReturnPostOrStatic.call {caller : Frame} {callee : FunctionDecl} {name retVar : Ident} {args : List Expr}
    {argVals : List Value} {bindings : Store}
    (h : HeapReturnPostOrStatic fork post cfg code ee g s0 {caller with locals := bindings} evm callee.body value pc stack mem heap)
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some bindings) :
    HeapCallPostOrStatic fork post cfg code ee g s0 caller evm name args retVar value pc stack mem heap := by
  rcases h with h | ⟨hsrc,hr⟩
  · exact Or.inl (h.call hargs hlookup hbind)
  · exact Or.inr ⟨internalCallFunctionStatic hargs hlookup hbind hsrc,hr⟩

end Benchmarks.EAS.EAS
