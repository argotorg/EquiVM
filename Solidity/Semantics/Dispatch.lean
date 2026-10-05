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

/-- ABI-decode the calldata arguments of `d` (positional).  A `calldata` array or struct is
    decoded with its words unvalidated (`paramDecodeTys`): solc validates them when they are
    read. -/
def decodeArgs (cfg : Config) (env : TypeEnv) (d : FnDecl) (calldata : ByteArray) : Option (List ABIValue) := do
  let tys ← paramDecodeTys env d.params
  ABI.decodeCalldataValues? tys calldata cfg.abiDecodeMode

/-- The arguments of `d` as spec values: ABI decoding, then the typed reconstruction, which rejects
    what solc's decoder validates beyond the ABI types (an enum value out of range). -/
def decodeCallArgs (cfg : Config) (env : TypeEnv) (d : FnDecl) (calldata : ByteArray) : Option (List Value × Heap) :=
  (decodeArgs cfg env d calldata).bind fun svs => ofAbiParams env calldata d.params svs {}

/-- Whether solc decodes some argument of `d` into memory with a length-dependent allocation: a
    parameter of dynamic type that is not located in calldata (getter parameters carry no
    location and are decoded to memory).  Such a decoder reverts with `Panic(0x41)` when an
    encoded length exceeds the allocator's bound, before the calldata bounds are checked. -/
def hasDynamicMemoryParam (env : TypeEnv) (d : FnDecl) : Bool :=
  d.params.any fun p => p.loc != some .calldata && ((abiTypeOf env p.ty).map isDynamicABIType).getD false

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
      ofAbiParams fc.types I.calldata fn.decl.params svs {} = some (vs, h0) →
      CallFn cfg o fc (rootFrame fc) (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0) fn vs (.ok rets m') →
      rets.mapM (toAbi m'.heap fuelDefault) = some out →
      solidityExec createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.returned m' out) (.abi retTys)
  | callReverted :
      selectorDispatch fc I.calldata = some e → fc.fns[e.fn]? = some fn →
      payableOrNoValue fn.decl I → returnAbiTys fc.types fn.decl = some retTys →
      decodeArgs cfg fc.types fn.decl I.calldata = some svs →
      ofAbiParams fc.types I.calldata fn.decl.params svs {} = some (vs, h0) →
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

/-- The frame the initializers run in: the immutables, no constructor parameters. -/
def initRoot (fc : FlatContract) (imms : Store) : Frame := { here := fc.name, locals := imms, retVars := [] }

/-- Run the inline initializers of the state variables (mutable ones into storage, immutables
    into their `imm_` locals), each in the scope of the contract that declares the variable. -/
inductive ExecInits : Frame → Machine → List FlatVar → Res Unit → Prop where
  | nil : ExecInits fr m [] (.ok () fr m)
  | storage : v.mutability = .mutable → v.init = some e →
      EvalExpr cfg o fc { fr with here := v.declaredIn } m e (.ok val fr1 m1) →
      assign cfg fc.types fr1 m1 (.storage ⟨v.key, []⟩ v.ty) val = some (.ok (fr2, m2)) →
      ExecInits fr2 m2 rest r → ExecInits fr m (v :: rest) r
  | immutable : v.mutability = .immutable → v.init = some e →
      EvalExpr cfg o fc { fr with here := v.declaredIn } m e (.ok val fr1 m1) →
      assign cfg fc.types fr1 m1 (.local (immName v.name)) val = some (.ok (fr2, m2)) →
      ExecInits fr2 m2 rest r → ExecInits fr m (v :: rest) r
  | revert : v.init = some e → EvalExpr cfg o fc { fr with here := v.declaredIn } m e (.reverted d) →
      ExecInits fr m (v :: rest) (.reverted d)
  | storagePanic : v.mutability = .mutable → v.init = some e →
      EvalExpr cfg o fc { fr with here := v.declaredIn } m e (.ok val fr1 m1) →
      assign cfg fc.types fr1 m1 (.storage ⟨v.key, []⟩ v.ty) val = some (.error p) → ExecInits fr m (v :: rest) (.reverted p.data)
  | immutablePanic : v.mutability = .immutable → v.init = some e →
      EvalExpr cfg o fc { fr with here := v.declaredIn } m e (.ok val fr1 m1) →
      assign cfg fc.types fr1 m1 (.local (immName v.name)) val = some (.error p) → ExecInits fr m (v :: rest) (.reverted p.data)

/-- The frame in which the parameters of the constructor of `c` are visible (over the immutables):
    the arguments `c` writes for its bases are evaluated here. -/
def ctorFrame (fc : FlatContract) (c : Ident) (vals : List Value) (m : Machine) (imms : Store) : Op (Frame × Machine) :=
  match fc.fns.toList.find? fun f => f.declaredIn == c && f.decl.kind == .ctor with
  | some f => enterFn cfg fc.types c f.decl vals m imms
  | none => pure ({ here := c, locals := imms, retVars := [] }, m)

/-- Constructor arguments of one contract of the hierarchy: the decoded ones for the most-derived
    contract; the written ones otherwise, evaluated with the parameters of the constructor that
    wrote them (`tbl`: the arguments of the more derived contracts). -/
inductive CtorArgs (topArgs : List Value) (imms : Store) (tbl : List (Ident × List Value)) :
    Machine → CtorStep → Res (List Value) → Prop where
  | top : step.contract = fc.name → CtorArgs topArgs imms tbl m step (.ok topArgs (rootFrame fc) m)
  | none : step.contract ≠ fc.name → step.args = none → CtorArgs topArgs imms tbl m step (.ok [] (rootFrame fc) m)
  | some : step.contract ≠ fc.name → step.args = some (w, args) → tbl.lookup w = some wvs →
      ctorFrame cfg fc w wvs m imms = some (.ok (frW, mW)) →
      callArgs (fc.ctorParamss step.contract) args = some es →
      EvalExprs cfg o fc frW mW es r → CtorArgs topArgs imms tbl m step r
  | framePanic : step.contract ≠ fc.name → step.args = some (w, args) → tbl.lookup w = some wvs →
      ctorFrame cfg fc w wvs m imms = some (.error p) → CtorArgs topArgs imms tbl m step (.reverted p.data)

/-- The arguments of every constructor, the most derived contract first.  solc evaluates them all
    before any constructor body runs. -/
inductive CtorArgsAll (topArgs : List Value) (imms : Store) :
    List (Ident × List Value) → Machine → List CtorStep →
      Except ByteArray (List (Ident × List Value) × Machine) → Prop where
  | nil : CtorArgsAll topArgs imms tbl m [] (.ok (tbl, m))
  | cons : CtorArgs cfg o fc topArgs imms tbl m step (.ok vs fr' m1) →
      CtorArgsAll topArgs imms ((step.contract, vs) :: tbl) m1 rest r →
      CtorArgsAll topArgs imms tbl m (step :: rest) r
  | revert : CtorArgs cfg o fc topArgs imms tbl m step (.reverted d) →
      CtorArgsAll topArgs imms tbl m (step :: rest) (.error d)

/-- The constructor bodies, base-first, with the arguments `tbl`; `imm_` locals are threaded from
    step to step. -/
inductive ExecCtorChain (tbl : List (Ident × List Value)) : Store → Machine → List CtorStep → CtorResult → Prop where
  | nil : ExecCtorChain tbl imms m [] (.ok m imms)
  | skip : step.fn = none → ExecCtorChain tbl imms m rest r → ExecCtorChain tbl imms m (step :: rest) r
  | run : step.fn = some fid → fc.fns[fid]? = some fn → tbl.lookup step.contract = some vs →
      enterFn cfg fc.types fn.declaredIn fn.decl vs m imms = some (.ok (fr2, m2)) → fn.decl.body = some body →
      ExecChain cfg o fc { fr2 with chain := fn.decl.modifiers, body := body } m2 fn.decl.modifiers body res →
      finished res = some (fr4, m4) →
      ExecCtorChain tbl (immStore fr4) m4 rest r → ExecCtorChain tbl imms m (step :: rest) r
  | bodyReverted : step.fn = some fid → fc.fns[fid]? = some fn → tbl.lookup step.contract = some vs →
      enterFn cfg fc.types fn.declaredIn fn.decl vs m imms = some (.ok (fr2, m2)) → fn.decl.body = some body →
      ExecChain cfg o fc { fr2 with chain := fn.decl.modifiers, body := body } m2 fn.decl.modifiers body (.reverted d) →
      ExecCtorChain tbl imms m (step :: rest) (.reverted d)
  | enterPanic : step.fn = some fid → fc.fns[fid]? = some fn → tbl.lookup step.contract = some vs →
      enterFn cfg fc.types fn.declaredIn fn.decl vs m imms = some (.error p) →
      ExecCtorChain tbl imms m (step :: rest) (.reverted p.data)

/-- Construction at fixed inputs, in solc's (legacy) order: the initializers (base-first), the
    arguments of every constructor (most derived first), the constructor bodies (base-first). -/
inductive solidityCtorExec (args : List ABIValue)
    (createdAccounts : Batteries.RBSet Ethereum.AccountAddress compare)
    (genesisBlockHeader : Ethereum.BlockHeader) (blocks : Ethereum.ProcessedBlocks)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) : CtorResult → Prop where
  | run :
      ctorPayable fc I → immZero fc = some imms0 →
      ofAbiList fc.types ((topCtor? fc).map (·.decl.params.map (·.ty)) |>.getD []) args {} = some (topArgs, h0) →
      ExecInits cfg o fc (initRoot fc imms0) (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0)
        (initializers fc) (.ok () frI m1) →
      CtorArgsAll cfg o fc topArgs (immStore frI) [] m1 fc.ctorChain.reverse (.ok (tbl, m2)) →
      ExecCtorChain cfg o fc tbl (immStore frI) m2 fc.ctorChain r →
      solidityCtorExec args createdAccounts genesisBlockHeader blocks σ σ₀ g A I r
  | initsReverted :
      ctorPayable fc I → immZero fc = some imms0 →
      ofAbiList fc.types ((topCtor? fc).map (·.decl.params.map (·.ty)) |>.getD []) args {} = some (topArgs, h0) →
      ExecInits cfg o fc (initRoot fc imms0) (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0)
        (initializers fc) (.reverted d) →
      solidityCtorExec args createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted d)
  | argsReverted :
      ctorPayable fc I → immZero fc = some imms0 →
      ofAbiList fc.types ((topCtor? fc).map (·.decl.params.map (·.ty)) |>.getD []) args {} = some (topArgs, h0) →
      ExecInits cfg o fc (initRoot fc imms0) (initMachine createdAccounts genesisBlockHeader blocks σ σ₀ g A I h0)
        (initializers fc) (.ok () frI m1) →
      CtorArgsAll cfg o fc topArgs (immStore frI) [] m1 fc.ctorChain.reverse (.error d) →
      solidityCtorExec args createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted d)
  | nonPayable :
      ¬ ctorPayable fc I →
      solidityCtorExec args createdAccounts genesisBlockHeader blocks σ σ₀ g A I (.reverted ByteArray.empty)

end Solidity
