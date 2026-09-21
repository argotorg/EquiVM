import Solidity.Semantics.Exec
import Refinement.Result

/-!
# Message dispatch and constructor execution

`solidityExec` is the entry point of a message call: selector match over the dispatch table
(including generated getters), the non-payable check (`msg.value == 0`, empty revert data), ABI
decoding of the arguments (`ABI.DecodeMode.modern`), the function run, and the ABI return
convention.  Empty calldata goes to `receive` (else `fallback`); an unmatched selector to
`fallback`.  `solidityCtorExec` runs the state-variable initializers and the constructor chain
base-first (legacy code generator order), collecting the immutables assigned along the way.
-/

namespace Solidity

open ABI

/-- The dispatch entry whose selector matches the first four calldata bytes. -/
def selectorDispatch (fc : FlatContract) (calldata : ByteArray) : Option DispatchEntry :=
  if calldata.size < 4 then none
  else
    let sel := calldata.extract 0 4
    fc.entries.find? fun e => selectorOf e.sigStr == sel

/-- ABI-decode the calldata arguments of `d` (positional). -/
def decodeArgs (cfg : Config) (env : TypeEnv) (d : FnDecl) (calldata : ByteArray) : Option (List ABIValue) := do
  let sig ← sigOf env d.name (d.params.map (·.ty))
  ABI.decodeCalldataValues? sig.paramTypes calldata cfg.abiDecodeMode

def returnAbiTys (env : TypeEnv) (d : FnDecl) : Option (List ABIType) :=
  d.returns.mapM fun p => abiTypeOf env p.ty

/-- Outcome of a message call: return values (as ABI values) and the machine, or a revert. -/
inductive TopResult where
  | returned (m : Machine) (vs : List ABIValue)
  | reverted (data : ByteArray)

/-- Whether any entry point accepts the calldata (selector, `receive`, or `fallback`). -/
def dispatches (fc : FlatContract) (calldata : ByteArray) : Bool :=
  (selectorDispatch fc calldata).isSome ||
    (calldata.size == 0 && fc.receive?.isSome) || fc.fallback?.isSome

def rootFrame (fc : FlatContract) : Frame := { here := fc.name, locals := ∅, retVars := [] }

def initMachine (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (h : Heap := {}) : Machine :=
  { evm := initEvm createdAccounts genesisBlockHeader blocks σ σ₀ g A I, heap := h, tick := 0 }

def payableOrNoValue (d : FnDecl) (I : Ethereum.ExecutionEnv) : Prop :=
  d.mutability = .payable ∨ I.weiValue = ⟨0⟩

/-- Convention for `fallback` output: raw bytes when it returns `bytes`, ABI-void otherwise. -/
def fallbackConvention (d : FnDecl) : Refinement.ReturnConvention :=
  match d.returns with
  | [{ ty := .bytes, .. }] => .rawBytes
  | _ => .abi []

def fallbackArgs (d : FnDecl) (calldata : ByteArray) (h : Heap) : Option (List Value × Heap) :=
  match d.params with
  | [] => some ([], h)
  | [{ ty := .bytes, .. }] => let (h', fid) := h.alloc (.bytes false calldata); some ([.memRef fid], h')
  | _ => none

variable (cfg : Config) (o : Oracle) (fc : FlatContract)

/-- Execution of one message call at fixed transaction inputs. -/
inductive solidityExec (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : TopResult → Refinement.ReturnConvention → Prop where
  | call :
      selectorDispatch fc I.calldata = some e → fc.fns[e.fn]? = some fn →
      payableOrNoValue fn.decl I → returnAbiTys fc.types fn.decl = some retTys →
      decodeArgs cfg fc.types fn.decl I.calldata = some svs →
      ofAbiList fc.types (fn.decl.params.map (·.ty)) svs {} = some (vs, h0) →
      CallFn cfg o fc (rootFrame fc) (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0) fn vs (.ok rets m') →
      rets.mapM (toAbi m'.heap fuelDefault) = some out →
      solidityExec createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.returned m' out) (.abi retTys)
  | callReverted :
      selectorDispatch fc I.calldata = some e → fc.fns[e.fn]? = some fn →
      payableOrNoValue fn.decl I → returnAbiTys fc.types fn.decl = some retTys →
      decodeArgs cfg fc.types fn.decl I.calldata = some svs →
      ofAbiList fc.types (fn.decl.params.map (·.ty)) svs {} = some (vs, h0) →
      CallFn cfg o fc (rootFrame fc) (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0) fn vs (.reverted d) →
      solidityExec createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted d) (.abi retTys)
  | nonPayable :
      selectorDispatch fc I.calldata = some e → fc.fns[e.fn]? = some fn →
      fn.decl.mutability ≠ .payable → I.weiValue ≠ ⟨0⟩ → returnAbiTys fc.types fn.decl = some retTys →
      solidityExec createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted ByteArray.empty) (.abi retTys)
  | receive :
      I.calldata.size = 0 → fc.receive? = some fid → fc.fns[fid]? = some fn →
      CallFn cfg o fc (rootFrame fc) (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I) fn [] (.ok rets m') →
      solidityExec createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.returned m' []) (.abi [])
  | receiveReverted :
      I.calldata.size = 0 → fc.receive? = some fid → fc.fns[fid]? = some fn →
      CallFn cfg o fc (rootFrame fc) (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I) fn [] (.reverted d) →
      solidityExec createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted d) (.abi [])
  | fallback :
      selectorDispatch fc I.calldata = none → (fc.receive? = none ∨ I.calldata.size ≠ 0) →
      fc.fallback? = some fid → fc.fns[fid]? = some fn → payableOrNoValue fn.decl I →
      fallbackArgs fn.decl I.calldata {} = some (vs, h0) →
      CallFn cfg o fc (rootFrame fc) (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0) fn vs (.ok rets m') →
      rets.mapM (toAbi m'.heap fuelDefault) = some out →
      solidityExec createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.returned m' out) (fallbackConvention fn.decl)
  | fallbackReverted :
      selectorDispatch fc I.calldata = none → (fc.receive? = none ∨ I.calldata.size ≠ 0) →
      fc.fallback? = some fid → fc.fns[fid]? = some fn → payableOrNoValue fn.decl I →
      fallbackArgs fn.decl I.calldata {} = some (vs, h0) →
      CallFn cfg o fc (rootFrame fc) (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0) fn vs (.reverted d) →
      solidityExec createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted d) (fallbackConvention fn.decl)
  | fallbackNonPayable :
      selectorDispatch fc I.calldata = none → (fc.receive? = none ∨ I.calldata.size ≠ 0) →
      fc.fallback? = some fid → fc.fns[fid]? = some fn → fn.decl.mutability ≠ .payable → I.weiValue ≠ ⟨0⟩ →
      solidityExec createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted ByteArray.empty) (fallbackConvention fn.decl)

/-! ## Constructors -/

/-- Outcome of construction: the machine and the immutables (`imm_<name>` locals), or a revert. -/
inductive CtorResult where
  | ok (m : Machine) (imms : Store)
  | reverted (data : ByteArray)

def immStore (fr : Frame) : Store := fr.locals.filter fun k _ => k.startsWith "imm_"

/-- All immutables zero-initialised (as `imm_<name>` locals). -/
def immZero (fc : FlatContract) : Option Store :=
  (fc.stateVars.filter (·.mutability == .immutable)).foldlM (fun st v => do
    let z ← zeroValue fc.types v.ty
    pure (st.insert (immName v.name) { ty := v.ty, val := z })) (∅ : Store)

def topCtor? (fc : FlatContract) : Option FnDef :=
  fc.fns.toList.find? fun f => f.declaredIn == fc.name && f.decl.kind == .ctor

def ctorPayable (fc : FlatContract) (I : Ethereum.ExecutionEnv) : Prop :=
  match topCtor? fc with
  | some f => f.decl.mutability = .payable ∨ I.weiValue = ⟨0⟩
  | none => I.weiValue = ⟨0⟩

/-- State variables with an inline initializer, base-first. -/
def initializers (fc : FlatContract) : List FlatVar :=
  fc.stateVars.filter fun v => v.init.isSome && v.mutability != .constant

/-- Run the inline initializers of the state variables (mutable ones into storage, immutables
    into their `imm_` locals). -/
inductive ExecInits : Frame → Machine → List FlatVar → Res Unit → Prop where
  | nil : ExecInits fr m [] (.ok () fr m)
  | storage : v.mutability = .mutable → v.init = some e → EvalExpr cfg o fc fr m e (.ok val fr1 m1) →
      assign cfg fc.types fr1 m1 (.storage ⟨v.key, []⟩ v.ty) val = some (.ok (fr2, m2)) →
      ExecInits fr2 m2 rest r → ExecInits fr m (v :: rest) r
  | immutable : v.mutability = .immutable → v.init = some e → EvalExpr cfg o fc fr m e (.ok val fr1 m1) →
      assign cfg fc.types fr1 m1 (.local (immName v.name)) val = some (.ok (fr2, m2)) →
      ExecInits fr2 m2 rest r → ExecInits fr m (v :: rest) r
  | revert : v.init = some e → EvalExpr cfg o fc fr m e (.reverted d) → ExecInits fr m (v :: rest) (.reverted d)
  | storagePanic : v.mutability = .mutable → v.init = some e → EvalExpr cfg o fc fr m e (.ok val fr1 m1) →
      assign cfg fc.types fr1 m1 (.storage ⟨v.key, []⟩ v.ty) val = some (.error p) → ExecInits fr m (v :: rest) (.reverted p.data)
  | immutablePanic : v.mutability = .immutable → v.init = some e → EvalExpr cfg o fc fr m e (.ok val fr1 m1) →
      assign cfg fc.types fr1 m1 (.local (immName v.name)) val = some (.error p) → ExecInits fr m (v :: rest) (.reverted p.data)

/-- Arguments of a constructor-chain step: the decoded arguments for the most-derived contract,
    the explicitly written base arguments (evaluated in the most-derived constructor's frame)
    otherwise. -/
inductive CtorArgs (frP : Frame) (topArgs : List Value) : Machine → CtorStep → Res (List Value) → Prop where
  | top : step.contract = fc.name → CtorArgs frP topArgs m step (.ok topArgs frP m)
  | none : step.contract ≠ fc.name → step.args = none → CtorArgs frP topArgs m step (.ok [] frP m)
  | some : step.contract ≠ fc.name → step.args = some (w, args) → argExprsAny args = some es →
      EvalExprs cfg o fc frP m es r → CtorArgs frP topArgs m step r

/-- The constructor chain, base-first; `imm_` locals are threaded from step to step. -/
inductive ExecCtorChain (frP : Frame) (topArgs : List Value) : Store → Machine → List CtorStep → CtorResult → Prop where
  | nil : ExecCtorChain frP topArgs imms m [] (.ok m imms)
  | skip : step.fn = none → ExecCtorChain frP topArgs imms m rest r → ExecCtorChain frP topArgs imms m (step :: rest) r
  | run : step.fn = some fid → fc.fns[fid]? = some fn → CtorArgs cfg o fc frP topArgs m step (.ok vs _ m1) →
      enterFn cfg fc.types fn.declaredIn fn.decl vs m1 imms = some (.ok (fr2, m2)) → fn.decl.body = some body →
      ExecChain cfg o fc { fr2 with chain := fn.decl.modifiers, body := body } m2 fn.decl.modifiers body res →
      finished res = some (fr4, m4) →
      ExecCtorChain frP topArgs (immStore fr4) m4 rest r → ExecCtorChain frP topArgs imms m (step :: rest) r
  | argsReverted : step.fn = some fid → fc.fns[fid]? = some fn → CtorArgs cfg o fc frP topArgs m step (.reverted d) →
      ExecCtorChain frP topArgs imms m (step :: rest) (.reverted d)
  | bodyReverted : step.fn = some fid → fc.fns[fid]? = some fn → CtorArgs cfg o fc frP topArgs m step (.ok vs _ m1) →
      enterFn cfg fc.types fn.declaredIn fn.decl vs m1 imms = some (.ok (fr2, m2)) → fn.decl.body = some body →
      ExecChain cfg o fc { fr2 with chain := fn.decl.modifiers, body := body } m2 fn.decl.modifiers body (.reverted d) →
      ExecCtorChain frP topArgs imms m (step :: rest) (.reverted d)
  | enterPanic : step.fn = some fid → fc.fns[fid]? = some fn → CtorArgs cfg o fc frP topArgs m step (.ok vs _ m1) →
      enterFn cfg fc.types fn.declaredIn fn.decl vs m1 imms = some (.error p) →
      ExecCtorChain frP topArgs imms m (step :: rest) (.reverted p.data)

/-- The frame in which base-constructor arguments are evaluated: the most-derived constructor's
    parameters over the zeroed immutables. -/
def ctorParamFrame (fc : FlatContract) (topArgs : List Value) (m : Machine) (imms : Store) : Op (Frame × Machine) :=
  match topCtor? fc with
  | some f => enterFn cfg fc.types fc.name f.decl topArgs m imms
  | none => pure ({ here := fc.name, locals := imms, retVars := [] }, m)

/-- Construction at fixed inputs: initializers (base-first), then the constructor chain. -/
inductive solidityCtorExec (args : List ABIValue)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : CtorResult → Prop where
  | run :
      ctorPayable fc I → immZero fc = some imms0 →
      ofAbiList fc.types ((topCtor? fc).map (·.decl.params.map (·.ty)) |>.getD []) args {} = some (topArgs, h0) →
      ctorParamFrame cfg fc topArgs (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0) imms0 = some (.ok (frP, m0)) →
      ExecInits cfg o fc frP m0 (initializers fc) (.ok () frP1 m1) →
      ExecCtorChain cfg o fc frP1 topArgs (immStore frP1) m1 fc.ctorChain r →
      solidityCtorExec args createdAccounts genesisBlockHeader blocks σ σ₀ g A I r
  | initsReverted :
      ctorPayable fc I → immZero fc = some imms0 →
      ofAbiList fc.types ((topCtor? fc).map (·.decl.params.map (·.ty)) |>.getD []) args {} = some (topArgs, h0) →
      ctorParamFrame cfg fc topArgs (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0) imms0 = some (.ok (frP, m0)) →
      ExecInits cfg o fc frP m0 (initializers fc) (.reverted d) →
      solidityCtorExec args createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted d)
  | paramPanic :
      ctorPayable fc I → immZero fc = some imms0 →
      ofAbiList fc.types ((topCtor? fc).map (·.decl.params.map (·.ty)) |>.getD []) args {} = some (topArgs, h0) →
      ctorParamFrame cfg fc topArgs (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0) imms0 = some (.error p) →
      solidityCtorExec args createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted p.data)
  | nonPayable :
      ¬ ctorPayable fc I →
      solidityCtorExec args createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted ByteArray.empty)

end Solidity
