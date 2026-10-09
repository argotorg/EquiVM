import Solidity.Elab
import Solidity.Layout
import Solidity.Value
import Solidity.Errors
import Solidity.Events
import ABI.Decode

/-!
# Semantic state

The spec executes directly on the EVM state (`EVM.State`, as Sol⁻ does), so account maps, logs
and the environment are shared with the bytecode side; storage is read and written through the
Sol⁻ storage backend (`Config.storageBackend`).  Memory is an abstract heap; locals live
in a per-call `Frame`.  Nondeterminism (`gasleft()`, gas and non-log substate handed to sub-calls)
is drawn from an explicit `Oracle` through the machine's `tick`, so every rule is deterministic
given the oracle.
-/

namespace Solidity

structure Config where
  /-- Storage operations (`storageBackend` of the derived layout table by default). -/
  storageBackend : Solm.StorageBackend
  abiDecodeMode : ABI.DecodeMode := .modern
  /-- Init code (creation bytecode ++ encoded constructor arguments) for `new C(args)`. -/
  creationCode : Ident → List Solm.Value → Option EVM.Bytes := fun _ _ => none
  /-- Init code for deploying this contract itself. -/
  selfDeployment : EVM.Bytes → List Solm.Value → Option EVM.Bytes
  /-- `type(C).creationCode` and `type(C).runtimeCode`. -/
  typeCreationCode : Ident → Option EVM.Bytes := fun _ => none
  typeRuntimeCode : Ident → Option EVM.Bytes := fun _ => none

structure Oracle where
  /-- Value of the n-th `gasleft()`. -/
  gasleft : Nat → EVM.Word
  /-- The 63/64 cap of the n-th sub-call / creation: all but one 64th of the gas remaining after the
      call's own costs (EIP-150), the one gas quantity the source does not determine. -/
  callGas : Nat → Ethereum.UInt256
  /-- Non-log substate fields fed to a sub-call / creation (the log series is pinned). -/
  substateIn : Nat → Ethereum.Substate
  /-- Whether a failing ABI decoding of dynamic data fails at the decoder's memory allocation
      (`Panic(0x41)`) rather than at a bounds check (empty revert data): it depends on the free
      memory pointer, which the semantics does not model. -/
  allocPanic : Nat → Bool := fun _ => false

structure Machine where
  evm : EVM.State
  heap : Heap
  /-- The immutables of the running contract (`imm_<name>` locals): the values its constructor
      deployed, which solc embeds in the runtime code.  Empty while the constructor runs; it keeps
      them in its frames instead. -/
  immutables : Store := ∅
  tick : Nat := 0

structure Frame where
  /-- The contract whose code is executing (`super` / `using for` scope). -/
  here : Ident
  locals : Store
  /-- Return slots, in declaration order (unnamed ones are `#ret<i>`). -/
  retVars : List Ident
  unchecked : Bool := false
  /-- Remaining modifier chain and function body, run by `_;`. -/
  chain : List ModifierInvocation := []
  body : Block := []
  /-- Scopes suspended while a modifier body runs: the contract, locals and hidden bindings to
      return to. -/
  outer : List (Ident × Store × List (Ident × Local)) := []
  /-- Bindings hidden by a declaration of the same name in an inner block, newest first. -/
  hidden : List (Ident × Local) := []

inductive ExecResult where
  | normal (fr : Frame) (m : Machine)
  | returned (fr : Frame) (m : Machine)
  | break (fr : Frame) (m : Machine)
  | continue (fr : Frame) (m : Machine)
  | reverted (data : ByteArray)

/-- Result of evaluating something that yields an `α` and may update the frame and machine. -/
inductive Res (α : Type) where
  | ok (a : α) (fr : Frame) (m : Machine)
  | reverted (data : ByteArray)

abbrev ExprResult := Res Value

inductive LValue where
  | local (name : Ident)
  | storage (er : Solm.EvaledStorageRef) (ty : Ty)
  | memField (obj : Nat) (field : Ident)
  | memIndex (obj : Nat) (i : Nat)

/-- Outcome of running a function: the return values and the machine, or a revert. -/
inductive FnResult where
  | ok (vs : List Value) (m : Machine)
  | reverted (data : ByteArray)

namespace Frame

def get? (fr : Frame) (x : Ident) : Option Local := fr.locals.get? x

/-- Declare `x`.  A binding of the same name (from an enclosing block) is hidden until the block
    is left. -/
def bind (fr : Frame) (x : Ident) (ty : Ty) (loc : Option DataLoc) (v : Value) : Frame :=
  { fr with
      locals := fr.locals.insert x { ty := ty, loc := loc, val := v }
      hidden := match fr.locals.get? x with
        | some l => (x, l) :: fr.hidden
        | none => fr.hidden }

def setVal (fr : Frame) (x : Ident) (v : Value) : Frame :=
  match fr.locals.get? x with
  | some l => { fr with locals := fr.locals.insert x { l with val := v } }
  | none => fr

/-- Make hidden bindings visible again (the oldest of a name wins). -/
def restore (hs : List (Ident × Local)) (s : Store) : Store :=
  hs.foldl (fun s p => s.insert p.1 p.2) s

/-- Leave a block entered from `fr`: names declared inside are dropped, the bindings they hid come
    back, the others keep their new values. -/
def exitScope (fr fr' : Frame) : Frame :=
  let n := fr'.hidden.length - fr.hidden.length
  { fr' with
      locals := (restore (fr'.hidden.take n) fr'.locals).filter fun k _ => fr.locals.contains k
      hidden := fr'.hidden.drop n }

/-- The function scope, as `return` sees it: every hidden binding is visible again. -/
def unwind (fr : Frame) : Frame :=
  { fr with locals := restore fr.hidden fr.locals, hidden := [] }

end Frame

def retName (i : Nat) (p : Param) : Ident := p.name.getD s!"#ret{i}"

/-- The machine `Ξ` starts from (identical to `solmExec`'s initial state). -/
def initEvm (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : EVM.State :=
  { (default : EVM.State) with
      accountMap := σ
      σ₀ := σ₀
      executionEnv := I
      substate := A
      machineState.gasAvailable := .ofUInt256 g }

def Machine.this (m : Machine) : EVM.Address := m.evm.executionEnv.codeOwner

def Machine.pushLog (m : Machine) (le : Ethereum.LogEntry) : Machine :=
  { m with evm := { m.evm with substate := { m.evm.substate with
      logSeries := m.evm.substate.logSeries.push le } } }

end Solidity
