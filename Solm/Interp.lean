import Solm.Semantics

/-!
# Executable Solm semantics

A fuel-indexed interpreter for the statement layer of Solm, written rule by rule after the
relational big-step semantics of `Solm/Semantics/Exec.lean`.  Everything below statements
(`evalExpr?`, the storage backend, ABI coding, dispatch) is already a function and is reused as
is; this file only executes the judgments `ExecStmt`, `ExecForLoop`, `ExecBlock`, `ExecFuncBody`,
`solmExec`, and `solmCtorExec`.

**Design for the equivalence proof.**  Each match arm corresponds to one constructor of the
relation and is labelled with its name.  The result type is the relation's own `ExecResult`;
the two extra outcomes are `outOfFuel` (the budget ended before a result) and `stuck` (no rule
applies: an ill-formed program or configuration).  The intended statements are

* soundness: `execStmt fuel o ω cfg solm evm s = (.result r, ω') → ExecStmt cfg solm evm s r`
  (and likewise for blocks, loops, bodies, and the message-level judgments), under the
  assumption that the oracle's call results are `Θ`/`Lambda` results (`Oracle.Sound`), and
* completeness up to the oracle: every derivation is reached by some fuel and some oracle.

**Nondeterminism.**  The relation leaves three things open, and the interpreter resolves them
through an `Oracle`: the call gas and input substate of `callViaEVM.callMade` (the oracle
returns the call's result, which must be a `Θ` result for *some* gas and substate), the same
for `newViaEVM.created`, and the word of `letGas`.  Static mode (`perm = false`) has, for each
state-changing statement, both an ordinary rule and a `*Static` rule; the interpreter always
takes the static rule when it applies, which is what the EVM does (it halts at the first
forbidden opcode).
-/

namespace Solm.Interp

open ABI Ethereum Ethereum.EVM

/-! ## Oracles for the existentials of the relation -/

inductive CallKind where
  | call | staticcall | delegatecall
  deriving Repr, BEq, Inhabited, DecidableEq

/-- The arguments a message call is made with, in `callViaEVM` / `delegateCallViaEVM` terms. -/
structure CallRequest where
  kind : CallKind
  target : EVM.Address
  /-- transferred value (`0` for delegatecall) -/
  value : Int
  calldata : ByteArray
  /-- the permission bit the callee runs with -/
  calleePerm : Bool

/-- A call's result as the relation observes it: the success flag `z`, the final accounts `σ'`
    and substate `A'`, and the output `o` of `Θ`. -/
structure CallResult where
  success : Bool
  accounts : AccountMap
  substate : Substate
  output : ByteArray

structure CreateRequest where
  value : Int
  initCode : ByteArray
  salt : Option ByteArray

structure CreateResult where
  address : EVM.Address
  accounts : AccountMap
  substate : Substate
  success : Bool

/-- Witnesses for the relation's existentials.  `Ω` is the oracle's own state, for instance a
    cursor into a recorded EVM trace.  `call`/`create` are consulted only when the relational
    guard admits the call (`callMade` / `created`); `callNotMade`/`createNotMade` let a replaying
    oracle consume the corresponding EVM boundary.  An `.error` is a missing witness: the interpreter
    reports it as `stuck`. -/
structure Oracle (Ω : Type) where
  call : Ω → CallRequest → EVM.State → Except String (CallResult × Ω)
  callNotMade : Ω → CallRequest → Ω := fun ω _ => ω
  create : Ω → CreateRequest → EVM.State → Except String (CreateResult × Ω)
  createNotMade : Ω → CreateRequest → Ω := fun ω _ => ω
  /-- the word bound by `letGas` (`ExecStmt.letGas w`) -/
  gasLeft : Ω → EVM.State → EVM.Word × Ω

/-- The `Θ` invocation of `callViaEVM.callMade` / `delegateCallViaEVM.callMade` at a chosen call
    gas and input substate. -/
def thetaCall (gas : UInt256) (substate : Substate) (req : CallRequest) (evm : EVM.State) :
    CallResult :=
  let env := evm.executionEnv
  match req.kind with
  | .delegatecall =>
      let (σ', _, A', z, o) := Θ evm.accountMap evm.σ₀ substate env.source env.sender env.codeOwner
        (toExecute evm.accountMap req.target) gas (.ofNat env.gasPrice) ⟨0⟩ env.weiValue
        req.calldata (env.depth + 1) env.header env.blobVersionedHashes env.blocks env.perm
      ⟨z, σ', A', o⟩
  | _ =>
      let valueWord := EVM.wordOfInt req.value
      let (σ', _, A', z, o) := Θ evm.accountMap evm.σ₀ substate env.codeOwner env.sender req.target
        (toExecute evm.accountMap req.target) gas (.ofNat env.gasPrice) valueWord valueWord
        req.calldata (env.depth + 1) env.header env.blobVersionedHashes env.blocks req.calleePerm
      ⟨z, σ', A', o⟩

/-- The `Lambda` invocation of `newViaEVM.created` at a chosen gas and input substate (the
    creator's nonce is bumped first, as the `CREATE` opcode does). -/
def lambdaCreate (gas : UInt256) (substate : Substate) (req : CreateRequest) (evm : EVM.State) :
    CreateResult :=
  let env := evm.executionEnv
  let creator := evm.accountMap.get? env.codeOwner |>.getD default
  let σStar := evm.accountMap.insert env.codeOwner { creator with nonce := creator.nonce + ⟨1⟩ }
  let (addr, σ', _, A', z, _) := Lambda σStar evm.σ₀ substate env.codeOwner env.sender gas
    (.ofNat env.gasPrice) (EVM.wordOfInt req.value) req.initCode (env.depth + 1) req.salt
    env.header env.blobVersionedHashes env.blocks env.perm
  ⟨addr, σ', A', z⟩

/-- The stateless oracle: every call runs `Θ` with the fixed `gas` and the caller's current
    substate; `gasleft()` is the caller's gas counter.  Adequate for callees that do not inspect
    their gas. -/
def thetaOracle (gas : UInt256 := .ofNat 10000000) : Oracle Unit where
  call := fun _ req evm => .ok (thetaCall gas evm.substate req evm, ())
  create := fun _ req evm => .ok (lambdaCreate gas evm.substate req evm, ())
  gasLeft := fun _ evm => (evm.machineState.gasAvailable.toUInt256, ())

/-! ## Outcomes -/

/-- The interpreter's answer: a result of the relation, or one of the two ways the executable
    semantics can fail to produce one. -/
inductive Outcome where
  | result : ExecResult → Outcome
  | outOfFuel : Outcome
  /-- no rule of the relation applies (ill-formed program/configuration, or no oracle witness) -/
  | stuck : String → Outcome
  /-- the case needs a memory allocation beyond `allocationCap`, which the executable semantics
      does not materialise (the relation still defines the result) -/
  | unsupported : String → Outcome

def Outcome.describe : Outcome → String
  | .result (.returned _ _ none) => "returned (fallthrough)"
  | .result (.returned _ _ (some vs)) => s!"returned {vs.length} value(s)"
  | .result (.ok _ _) => "ok"
  | .result (.break _ _) => "break"
  | .result (.continue _ _) => "continue"
  | .result .reverted => "reverted"
  | .result .staticViolation => "staticViolation"
  | .outOfFuel => "out of fuel"
  | .stuck why => s!"stuck: {why}"
  | .unsupported why => s!"unsupported: {why}"

def stuckEval (what : String) : EvalError → Outcome
  | .unboundVariable => .stuck s!"{what}: unbound variable"
  | .typeError => .stuck s!"{what}: type error"
  | .storageError => .stuck s!"{what}: storage error"

/-! ## Call bridges (`Solm/Semantics/Calls.lean`, executable) -/

/-- The guard of `callViaEVM.callMade`: the sender can pay and the depth limit is not reached. -/
def callMadeGuard (evm : EVM.State) (value : Int) : Bool :=
  decide (EVM.wordOfInt value ≤ (evm.accountMap.get? evm.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance))
    ∧ evm.executionEnv.depth ≠ 1024)

/-- `callViaEVM evm target value calldata (z, evm', o) perm`, with the oracle choosing the
    `callMade` witness.  `none`: the oracle has no witness. -/
def callViaEVMRun (o : Oracle Ω) (ω : Ω) (evm : EVM.State) (target : EVM.Address) (value : Int)
    (calldata : ByteArray) (perm : Bool) : Except String ((Bool × EVM.State × ByteArray) × Ω) :=
  let req : CallRequest :=
    { kind := if perm then .call else .staticcall, target, value, calldata,
      calleePerm := perm && evm.executionEnv.perm }
  if callMadeGuard evm value then
    -- callViaEVM.callMade
    match o.call ω req evm with
    | .ok (r, ω') => .ok ((r.success, { evm with accountMap := r.accounts, substate := r.substate }, r.output), ω')
    | .error e => .error e
  else
    -- callViaEVM.callNotMade
    .ok ((false, { evm with substate := (evm.addAccessedAccount target).substate }, ByteArray.empty),
      o.callNotMade ω req)

/-- `delegateCallViaEVM evm target calldata (z, evm', o)`. -/
def delegateCallViaEVMRun (o : Oracle Ω) (ω : Ω) (evm : EVM.State) (target : EVM.Address)
    (calldata : ByteArray) : Except String ((Bool × EVM.State × ByteArray) × Ω) :=
  let req : CallRequest :=
    { kind := .delegatecall, target, value := 0, calldata, calleePerm := evm.executionEnv.perm }
  if evm.executionEnv.depth ≠ 1024 then
    -- delegateCallViaEVM.callMade
    match o.call ω req evm with
    | .ok (r, ω') => .ok ((r.success, { evm with accountMap := r.accounts, substate := r.substate }, r.output), ω')
    | .error e => .error e
  else
    -- delegateCallViaEVM.callNotMade
    .ok ((false, { evm with substate := (evm.addAccessedAccount target).substate }, ByteArray.empty),
      o.callNotMade ω req)

/-- `typedCallViaEVM`: ABI-encode, then `callViaEVM`.  `none` when the ABI table has no encoding
    (no rule applies) or the oracle has no witness. -/
def typedCallViaEVMRun (o : Oracle Ω) (ω : Ω) (cfg : Config) (evm : EVM.State) (target : EVM.Address)
    (name : Ident) (value : Int) (args : List Value) (perm : Bool) :
    Except String ((Bool × EVM.State × ByteArray) × Ω) :=
  match cfg.externalABI.encode? name args with
  | none => .error s!"the external-call ABI has no encoding for {name}"
  | some calldata => callViaEVMRun o ω evm target value calldata perm

/-- The guard `newCanCreate`. -/
def newCanCreateB (evm : EVM.State) (value : Int) (initCode : ByteArray) : Bool :=
  let creator := evm.accountMap.get? evm.executionEnv.codeOwner |>.getD default
  decide (EVM.wordOfInt value ≤ creator.balance) && decide (evm.executionEnv.depth ≠ 1024)
    && decide (creator.nonce.toNat < 2 ^ 64 - 1) && decide (initCode.size ≤ 49152)

/-- `newViaEVM cfg evm name value args salt (addr, evm', z)`. -/
def newViaEVMRun (o : Oracle Ω) (ω : Ω) (cfg : Config) (evm : EVM.State) (name : Ident) (value : Int)
    (args : List Value) (salt : Option ByteArray) : Except String ((EVM.Address × EVM.State × Bool) × Ω) :=
  match cfg.creationCode name args with
  | none => .error s!"the configuration has no creation code for {name}"
  | some initCode =>
    let req : CreateRequest := { value, initCode, salt }
    if newCanCreateB evm value initCode then
      -- newViaEVM.created
      match o.create ω req evm with
      | .ok (r, ω') => .ok ((r.address, { evm with accountMap := r.accounts, substate := r.substate }, r.success), ω')
      | .error e => .error e
    else
      -- newViaEVM.notCreated
      .ok ((EVM.address 0, evm, false), o.createNotMade ω req)

/-! ## Statements -/

/-- The result of a block that ends a function body (`ExecFuncBody`). -/
def funcBodyResult : ExecResult → ExecResult
  | .ok solm evm => .returned solm evm none           -- ExecFuncBody.execBlockOK
  | .break solm evm => .returned solm evm none        -- ExecFuncBody.execBlockBreak
  | .continue solm evm => .returned solm evm none     -- ExecFuncBody.execBlockContinue
  | r => r                                            -- execBlockRet / execBlockRevert / execBlockStatic

/-! ## Allocation guard

`evalExpr?` materialises `new T[](n)` and `new bytes(n)` as lists of `n` elements.  solc rejects
lengths of `2^64` and above with a panic and the EVM cannot pay for a fraction of that, so a
generated case may ask for an allocation no machine can perform.  Statements whose allocation
sizes evaluate beyond `allocationCap` end in `unsupported`. -/

def allocationCap : Nat := 2 ^ 20

/-- The size expressions of the allocations in an expression. -/
partial def allocationSizes : Expr → List Expr
  | .newBytes n => n :: allocationSizes n
  | .newArray _ n => n :: allocationSizes n
  | .tupleGet e _ | .field e _ | .inRange _ e | .cast e _ | .addrOf e | .unary _ e | .keccak256 e
  | .abiDecode _ e | .extCodeSize e | .blockhash e | .balanceOf e | .extCodeHash e => allocationSizes e
  | .structLit _ fields => fields.flatMap fun (_, e) => allocationSizes e
  | .arrayLit es | .tupleLit es | .abiEncodeCall _ es => es.flatMap allocationSizes
  | .abiEncodePacked es => es.flatMap fun (_, e) => allocationSizes e
  | .bytesSlice a b c | .ite a b c => allocationSizes a ++ allocationSizes b ++ allocationSizes c
  | .binary _ a b | .index a b | .extCodePrefix a b => allocationSizes a ++ allocationSizes b
  | .storage ref | .transient ref | .arrayLength _ ref => refExprs ref |>.flatMap allocationSizes
  | _ => []
where
  refExprs (ref : StorageRef) : List Expr :=
    ref.steps.filterMap fun | .mindex e | .aindex e => some e | .field _ => none

/-- The expressions a statement evaluates itself (nested blocks are checked when they run). -/
def stmtExprs : Stmt → List Expr
  | .letDecl _ _ e | .setImmutable _ e | .require e | .while e _ | .for _ e _ _ | .ite e _ _ => [e]
  | .letStorage _ ref | .pop ref | .delete ref => allocationSizes.refExprs ref
  | .assign _ ref e => e :: allocationSizes.refExprs ref
  | .new _ v args _ salt => v :: args ++ salt.toList
  | .internalCall _ args _ | .emit _ args => args
  | .externalCall tgt _ v args _ _ => tgt :: v :: args
  | .lowLevelCall tgt v cd _ _ _ => [tgt, v, cd]
  | .delegateCall tgt cd _ _ => [tgt, cd]
  | .checkedCall recv _ v args _ _ _ _ _ => recv :: v :: args
  | .return es => es
  | .push ref e? => allocationSizes.refExprs ref ++ e?.toList
  | .letGas _ | .break | .continue => []

/-- The first allocation of the statement whose size evaluates beyond `allocationCap`. -/
def oversizedAllocation (cfg : Config) (solm : Frame) (evm : EVM.State) (stmt : Stmt) : Option String :=
  (stmtExprs stmt).flatMap allocationSizes |>.findSome? fun n =>
    match evalExpr? cfg solm evm n with
    | .ok (.int k) => if k > allocationCap then some s!"allocation of {k} elements" else none
    | _ => none

mutual

/-- `ExecStmt cfg solm evm stmt result`, with `fuel` bounding the derivation height. -/
def execStmt (fuel : Nat) (o : Oracle Ω) (ω : Ω) (cfg : Config) (solm : Frame) (evm : EVM.State) :
    Stmt → Outcome × Ω
  | stmt =>
  match fuel with
  | 0 => (.outOfFuel, ω)
  | fuel + 1 =>
  match oversizedAllocation cfg solm evm stmt with
  | some why => (.unsupported why, ω)
  | none =>
  let perm := evm.executionEnv.perm
  match stmt with
  | .letDecl name _ expr =>
      match evalExpr? cfg solm evm expr with
      | .ok value => (.result (.ok { solm with locals := solm.locals.insert name value } evm), ω)  -- letDecl
      | .revert => (.result .reverted, ω)                                                           -- letDeclRevert
      | .error e => (stuckEval "letDecl" e, ω)
  | .letStorage name ref =>
      match resolveStorageRef? cfg solm evm ref with
      | .ok (er, ty) => (.result (.ok { solm with locals := solm.locals.insert name (.storageRef er ty) } evm), ω)  -- letStorage
      | .revert => (.result .reverted, ω)                                                           -- letStorageRevert
      | .error e => (stuckEval "letStorage" e, ω)
  | .letGas name =>
      let (w, ω') := o.gasLeft ω evm                                                                 -- letGas w
      (.result (.ok { solm with locals := solm.locals.insert name (.int (Int.ofNat w.toNat)) } evm), ω')
  | .assign origin slot expr =>
      match evalExpr? cfg solm evm expr with
      | .revert => (.result .reverted, ω)                                                           -- assignExprRevert
      | .error e => (stuckEval "assign" e, ω)
      | .ok value =>
          match assignStorageRef? cfg solm evm origin slot value with
          | .revert => (.result .reverted, ω)                                                       -- assignStoreRevert
          | .error e => (stuckEval "assign (store)" e, ω)
          | .ok (solm', evm') =>
              if (origin = .storage ∨ origin = .transient) ∧ perm = false then
                (.result .staticViolation, ω)                                                     -- assignStatic / assignTransientStatic
              else (.result (.ok solm' evm'), ω)                                                   -- assign
  | .push ref (some expr) =>
      match evalExpr? cfg solm evm expr with
      | .revert => (.result .reverted, ω)                                                           -- pushValExprRevert
      | .error e => (stuckEval "push" e, ω)
      | .ok value =>
          match pushArray? cfg solm evm ref (some value) with
          | .revert => (.result .reverted, ω)                                                       -- pushValStoreRevert
          | .error e => (stuckEval "push (store)" e, ω)
          | .ok evm' =>
              if perm = false then (.result .staticViolation, ω)                                   -- pushValStatic
              else (.result (.ok solm evm'), ω)                                                    -- pushVal
  | .push ref none =>
      match pushArray? cfg solm evm ref none with
      | .revert => (.result .reverted, ω)                                                           -- pushGrowRevert
      | .error e => (stuckEval "push" e, ω)
      | .ok evm' =>
          if perm = false then (.result .staticViolation, ω)                                       -- pushGrowStatic
          else (.result (.ok solm evm'), ω)                                                        -- pushGrow
  | .pop ref =>
      match popArray? cfg solm evm ref with
      | .revert => (.result .reverted, ω)                                                           -- popRevert
      | .error e => (stuckEval "pop" e, ω)
      | .ok evm' =>
          if perm = false then (.result .staticViolation, ω)                                       -- popStatic
          else (.result (.ok solm evm'), ω)                                                        -- pop
  | .delete ref =>
      match deleteStorage? cfg solm evm ref with
      | .revert => (.result .reverted, ω)                                                           -- deleteRevert
      | .error e => (stuckEval "delete" e, ω)
      | .ok evm' =>
          if perm = false then (.result .staticViolation, ω)                                       -- deleteStatic
          else (.result (.ok solm evm'), ω)                                                        -- delete
  | .require cond =>
      match evalExpr? cfg solm evm cond with
      | .ok (.bool true) => (.result (.ok solm evm), ω)                                             -- requireTrue
      | .ok (.bool false) => (.result .reverted, ω)                                                 -- requireFalse
      | .revert => (.result .reverted, ω)                                                           -- requireRevert
      | .ok _ => (.stuck "require: condition is not a bool", ω)
      | .error e => (stuckEval "require" e, ω)
  | .while cond body =>
      match evalExpr? cfg solm evm cond with
      | .ok (.bool false) => (.result (.ok solm evm), ω)                                            -- whileFalse
      | .revert => (.result .reverted, ω)                                                           -- whileCondRevert
      | .ok (.bool true) =>
          match execBlock fuel o ω cfg solm evm body with
          | (.result (.ok solm' evm'), ω') => execStmt fuel o ω' cfg solm' evm' (.while cond body)     -- whileTrue
          | (.result (.returned solm' evm' value), ω') => (.result (.returned solm' evm' value), ω')   -- whileReturn
          | (.result .reverted, ω') => (.result .reverted, ω')                                        -- whileRevert
          | (.result (.break solm' evm'), ω') => (.result (.ok solm' evm'), ω')                       -- whileBreak
          | (.result (.continue solm' evm'), ω') => execStmt fuel o ω' cfg solm' evm' (.while cond body)  -- whileContinue
          | (.result .staticViolation, ω') => (.result .staticViolation, ω')                          -- whileStatic
          | other => other
      | .ok _ => (.stuck "while: condition is not a bool", ω)
      | .error e => (stuckEval "while" e, ω)
  | .for init cond post body =>
      match execBlock fuel o ω cfg solm evm init with
      | (.result (.ok solm1 evm1), ω') => execForLoop fuel o ω' cfg solm1 evm1 cond post body         -- for
      | (.result (.returned solm1 evm1 value), ω') => (.result (.returned solm1 evm1 value), ω')      -- forInitReturn
      | (.result .reverted, ω') => (.result .reverted, ω')                                           -- forInitRevert
      | (.result .staticViolation, ω') => (.result .staticViolation, ω')                             -- forInitStatic
      | (.result _, ω') => (.stuck "for: break/continue in the initialiser", ω')
      | other => other
  | .ite cond thenB elseB =>
      match evalExpr? cfg solm evm cond with
      | .ok (.bool true) => execBlock fuel o ω cfg solm evm thenB                                     -- iteTrue
      | .ok (.bool false) => execBlock fuel o ω cfg solm evm elseB                                    -- iteFalse
      | .revert => (.result .reverted, ω)                                                           -- iteCondRevert
      | .ok _ => (.stuck "if: condition is not a bool", ω)
      | .error e => (stuckEval "if" e, ω)
  | .internalCall name args retVar =>
      match evalExprs? cfg solm evm args with
      | .revert => (.result .reverted, ω)                                                           -- internalCallArgsRevert
      | .error e => (stuckEval "internal call arguments" e, ω)
      | .ok argVals =>
          match lookupCallable? solm.contract name with
          | none => (.stuck s!"internal call: unknown callee {name}", ω)
          | some callee =>
              match bindParams? callee.params argVals with
              | none => (.stuck s!"internal call: arity mismatch for {name}", ω)
              | some locals =>
                  match execFuncBody fuel o ω cfg { solm with locals := locals } evm callee.body with
                  | (.result (.returned _ calleeEvm value), ω') =>
                      (.result (.ok (resumeAfterInternalCall solm retVar value) calleeEvm), ω')     -- internalCallReturn
                  | (.result .reverted, ω') => (.result .reverted, ω')                               -- internalCallRevert
                  | (.result .staticViolation, ω') => (.result .staticViolation, ω')                 -- internalCallStatic
                  | (.result _, ω') => (.stuck "internal call: body ended in a non-function result", ω')
                  | other => other
  | .externalCall receiver name eth args retVar perm' =>
      match evalExpr? cfg solm evm receiver with
      | .revert => (.result .reverted, ω)                                                           -- externalCallReceiverRevert
      | .error e => (stuckEval "external call receiver" e, ω)
      | .ok (.address target) =>
          match evalExpr? cfg solm evm eth with
          | .revert => (.result .reverted, ω)                                                       -- externalCallSendRevert
          | .error e => (stuckEval "external call value" e, ω)
          | .ok (.int sendVal) =>
              match evalExprs? cfg solm evm args with
              | .revert => (.result .reverted, ω)                                                   -- externalCallArgsRevert
              | .error e => (stuckEval "external call arguments" e, ω)
              | .ok argVals =>
                  if EVM.wordOfInt sendVal ≠ ⟨0⟩ ∧ perm = false then (.result .staticViolation, ω)  -- externalCallStatic
                  else
                    match typedCallViaEVMRun o ω cfg evm (EVM.address target) name sendVal argVals perm' with
                    | .error e => (.stuck s!"external call {name}: {e}", ω)
                    | .ok ((false, _, _), ω') => (.result .reverted, ω')                             -- externalCallFailure
                    | .ok ((true, evm', out), ω') =>
                        match cfg.externalABI.decode? name out with
                        | some value =>                                                              -- externalCallSuccess
                            (.result (.ok { solm with locals := solm.locals.insert retVar (collapseReturns value) } evm'), ω')
                        | none => (.result .reverted, ω')                                            -- externalCallReturnDecodeRevert
          | .ok _ => (.stuck "external call: value is not an integer", ω)
      | .ok _ => (.stuck "external call: receiver is not an address", ω)
  | .lowLevelCall receiver eth cdata okVar dataVar perm' =>
      match evalExpr? cfg solm evm receiver with
      | .revert => (.result .reverted, ω)                                                           -- lowLevelCallReceiverRevert
      | .error e => (stuckEval "call receiver" e, ω)
      | .ok (.address target) =>
          match evalExpr? cfg solm evm eth with
          | .revert => (.result .reverted, ω)                                                       -- lowLevelCallSendRevert
          | .error e => (stuckEval "call value" e, ω)
          | .ok (.int sendVal) =>
              match evalExpr? cfg solm evm cdata with
              | .revert => (.result .reverted, ω)                                                   -- lowLevelCallDataRevert
              | .error e => (stuckEval "call data" e, ω)
              | .ok (.bytes calldata) =>
                  if EVM.wordOfInt sendVal ≠ ⟨0⟩ ∧ perm = false then (.result .staticViolation, ω)  -- lowLevelCallStatic
                  else
                    match callViaEVMRun o ω evm (EVM.address target) sendVal calldata perm' with
                    | .error e => (.stuck s!"call: {e}", ω)
                    | .ok ((z, evm', out), ω') =>                                                   -- lowLevelCallSuccess / lowLevelCallFailure
                        (.result (.ok { solm with locals := (solm.locals.insert okVar (.bool z)).insert dataVar (.bytes out) } evm'), ω')
              | .ok _ => (.stuck "call: calldata is not bytes", ω)
          | .ok _ => (.stuck "call: value is not an integer", ω)
      | .ok _ => (.stuck "call: receiver is not an address", ω)
  | .delegateCall receiver cdata okVar dataVar =>
      match evalExpr? cfg solm evm receiver with
      | .revert => (.result .reverted, ω)                                                           -- delegateCallReceiverRevert
      | .error e => (stuckEval "delegatecall receiver" e, ω)
      | .ok (.address target) =>
          match evalExpr? cfg solm evm cdata with
          | .revert => (.result .reverted, ω)                                                       -- delegateCallDataRevert
          | .error e => (stuckEval "delegatecall data" e, ω)
          | .ok (.bytes calldata) =>
              match delegateCallViaEVMRun o ω evm (EVM.address target) calldata with
              | .error e => (.stuck s!"delegatecall: {e}", ω)
              | .ok ((z, evm', out), ω') =>                                                       -- delegateCallSuccess / delegateCallFailure
                  (.result (.ok { solm with locals := (solm.locals.insert okVar (.bool z)).insert dataVar (.bytes out) } evm'), ω')
          | .ok _ => (.stuck "delegatecall: calldata is not bytes", ω)
      | .ok _ => (.stuck "delegatecall: receiver is not an address", ω)
  | .checkedCall receiver name eth args retVar onSuccess errVar onFail perm' =>
      match evalExpr? cfg solm evm receiver with
      | .revert => (.result .reverted, ω)                                                           -- checkedCallReceiverRevert
      | .error e => (stuckEval "try receiver" e, ω)
      | .ok (.address target) =>
          match evalExpr? cfg solm evm eth with
          | .revert => (.result .reverted, ω)                                                       -- checkedCallSendRevert
          | .error e => (stuckEval "try value" e, ω)
          | .ok (.int sendVal) =>
              match evalExprs? cfg solm evm args with
              | .revert => (.result .reverted, ω)                                                   -- checkedCallArgsRevert
              | .error e => (stuckEval "try arguments" e, ω)
              | .ok argVals =>
                  if EVM.wordOfInt sendVal ≠ ⟨0⟩ ∧ perm = false then (.result .staticViolation, ω)  -- checkedCallStatic
                  else
                    match typedCallViaEVMRun o ω cfg evm (EVM.address target) name sendVal argVals perm' with
                    | .error e => (.stuck s!"try {name}: {e}", ω)
                    | .ok ((false, evm', out), ω') =>                                                -- checkedCallFail
                        execBlock fuel o ω' cfg { solm with locals := solm.locals.insert errVar (.bytes out) } evm' onFail
                    | .ok ((true, evm', out), ω') =>
                        match cfg.externalABI.decode? name out with
                        | some value =>                                                              -- checkedCallSuccess
                            execBlock fuel o ω' cfg
                              { solm with locals := solm.locals.insert retVar (collapseReturns value) } evm' onSuccess
                        | none => (.result .reverted, ω')                                            -- checkedCallReturnDecodeRevert
          | .ok _ => (.stuck "try: value is not an integer", ω)
      | .ok _ => (.stuck "try: receiver is not an address", ω)
  | .new name valExpr args retVar salt =>
      match evalExpr? cfg solm evm valExpr with
      | .revert => (.result .reverted, ω)                                                           -- newValueRevert
      | .error e => (stuckEval "new value" e, ω)
      | .ok (.int sendVal) =>
          match evalExprs? cfg solm evm args with
          | .revert => (.result .reverted, ω)                                                       -- newArgsRevert
          | .error e => (stuckEval "new arguments" e, ω)
          | .ok argVals =>
              match evalSalt? cfg solm evm salt with
              | .error e => (stuckEval "new salt" e, ω)
              | .revert => (.stuck "new: salt reverted (no rule)", ω)
              | .ok saltBytes =>
                  if perm = false then (.result .staticViolation, ω)                               -- newStatic
                  else
                    match newViaEVMRun o ω cfg evm name sendVal argVals saltBytes with
                    | .error e => (.stuck s!"new {name}: {e}", ω)
                    | .ok ((addr, evm', true), ω') =>                                                -- newSuccess
                        (.result (.ok { solm with locals := solm.locals.insert retVar (.address addr) } evm'), ω')
                    | .ok ((_, _, false), ω') => (.result .reverted, ω')                             -- newRevert
      | .ok _ => (.stuck "new: value is not an integer", ω)
  | .return exprs =>
      match evalExprs? cfg solm evm exprs with
      | .ok values => (.result (.returned solm evm (some values)), ω)                               -- return
      | .revert => (.result .reverted, ω)                                                           -- returnRevert
      | .error e => (stuckEval "return" e, ω)
  | .setImmutable name expr =>
      match evalExpr? cfg solm evm expr with
      | .revert => (.result .reverted, ω)                                                           -- setImmutableRevert
      | .error e => (stuckEval "immutable assignment" e, ω)
      | .ok value =>
          match immutableType? solm.contract name with
          | none => (.stuck s!"immutable assignment: {name} is not an immutable", ω)
          | some ty =>
              if elemValueFits ty value then                                                        -- setImmutable
                (.result (.ok { solm with immutables := solm.immutables.insert name value } evm), ω)
              else (.stuck s!"immutable assignment: value of {name} does not fit its type", ω)
  | .break => (.result (.break solm evm), ω)                                                        -- break
  | .continue => (.result (.continue solm evm), ω)                                                  -- continue
  | .emit _ args =>
      match evalExprs? cfg solm evm args with
      | .revert => (.result .reverted, ω)                                                           -- emitArgsRevert
      | .error e => (stuckEval "emit" e, ω)
      | .ok _ =>
          if perm = false then (.result .staticViolation, ω)                                       -- emitStatic
          else (.result (.ok solm evm), ω)                                                          -- emit

/-- `ExecForLoop cfg solm evm cond post body result`. -/
def execForLoop (fuel : Nat) (o : Oracle Ω) (ω : Ω) (cfg : Config) (solm : Frame) (evm : EVM.State)
    (cond : Expr) (post body : List Stmt) : Outcome × Ω :=
  match fuel with
  | 0 => (.outOfFuel, ω)
  | fuel + 1 =>
  match evalExpr? cfg solm evm cond with
  | .ok (.bool false) => (.result (.ok solm evm), ω)                                                -- falseDone
  | .revert => (.result .reverted, ω)                                                               -- condRevert
  | .ok (.bool true) =>
      match execBlock fuel o ω cfg solm evm body with
      | (.result (.returned solm' evm' value), ω') => (.result (.returned solm' evm' value), ω')       -- bodyReturn
      | (.result .reverted, ω') => (.result .reverted, ω')                                            -- bodyRevert
      | (.result (.break solm' evm'), ω') => (.result (.ok solm' evm'), ω')                           -- bodyBreak
      | (.result .staticViolation, ω') => (.result .staticViolation, ω')                              -- bodyStatic
      | (.result (.ok solm1 evm1), ω') | (.result (.continue solm1 evm1), ω') =>                      -- iterate / continueIter
          match execBlock fuel o ω' cfg solm1 evm1 post with
          | (.result (.ok solm2 evm2), ω'') => execForLoop fuel o ω'' cfg solm2 evm2 cond post body
          | (.result .reverted, ω'') => (.result .reverted, ω'')                                      -- iteratePostRevert / continuePostRevert
          | (.result .staticViolation, ω'') => (.result .staticViolation, ω'')                        -- iteratePostStatic / continuePostStatic
          | (.result _, ω'') => (.stuck "for: the update block did not fall through", ω'')
          | other => other
      | other => other
  | .ok _ => (.stuck "for: condition is not a bool", ω)
  | .error e => (stuckEval "for" e, ω)

/-- `ExecBlock cfg solm evm stmts result`. -/
def execBlock (fuel : Nat) (o : Oracle Ω) (ω : Ω) (cfg : Config) (solm : Frame) (evm : EVM.State) :
    List Stmt → Outcome × Ω
  | stmts =>
  match fuel with
  | 0 => (.outOfFuel, ω)
  | fuel + 1 =>
  match stmts with
  | [] => (.result (.ok solm evm), ω)                                                               -- nil
  | stmt :: rest =>
      match execStmt fuel o ω cfg solm evm stmt with
      | (.result (.ok solm' evm'), ω') => execBlock fuel o ω' cfg solm' evm' rest                     -- consNormal
      | (.result r, ω') => (.result r, ω')                                                            -- consReturn / consRevert / consBreak / consContinue / consStatic
      | other => other

/-- `ExecFuncBody cfg solm evm body result`. -/
def execFuncBody (fuel : Nat) (o : Oracle Ω) (ω : Ω) (cfg : Config) (solm : Frame) (evm : EVM.State)
    (body : List Stmt) : Outcome × Ω :=
  match fuel with
  | 0 => (.outOfFuel, ω)
  | fuel + 1 =>
  match execBlock fuel o ω cfg solm evm body with
  | (.result r, ω') => (.result (funcBodyResult r), ω')
  | other => other

end

/-! ## Message-level judgments -/

/-- The EVM state `solmExec`/`solmCtorExec` start from. -/
def initialState (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) : EVM.State :=
  { (default : EVM.State) with
      accountMap := σ, σ₀ := σ₀, executionEnv := I, substate := A,
      machineState.gasAvailable := .ofUInt256 g }

/-- The outcome of dispatching a message, mirroring `solmExec` and the rejection cases of
    `runtimeRefinementFor`. -/
inductive DispatchOutcome where
  | ran : Outcome → ReturnConvention → DispatchOutcome
  /-- `dispatchMsg = none`: no transition, receive, or fallback accepts the calldata -/
  | noDispatch : DispatchOutcome
  /-- the selector matched but the calldata does not decode -/
  | decodingFailed : DispatchOutcome
  /-- a receive/fallback with a shape `solmExec` has no rule for -/
  | malformed : String → DispatchOutcome

/-- `ExecTransitionBody`, executable. -/
def execTransitionBody (fuel : Nat) (o : Oracle Ω) (ω : Ω) (cfg : Config) (contract : ContractDecl)
    (evm : EVM.State) (locals : Store) (body : Body) (immutables : Store) : Outcome × Ω :=
  execFuncBody fuel o ω cfg { contract := contract, locals := locals, immutables := immutables } evm body

/-- `solmExec`, executable: dispatch, decode, run. -/
def solmExecRun (fuel : Nat) (o : Oracle Ω) (ω : Ω) (cfg : Config) (contract : ContractDecl)
    (immutables : Store) (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    DispatchOutcome × Ω :=
  let evm := initialState σ σ₀ g A I
  match selectorDispatchMsg contract I.calldata with
  | some transition =>                                                                               -- solmExec.intro
      match decodeCalldataWithMode cfg.abiDecodeMode (transition.params.map Param.name)
          (transitionSignature transition).paramTypes I.calldata with
      | some callargs =>
          let (r, ω') := execTransitionBody fuel o ω cfg contract evm callargs transition.body immutables
          (.ran r (.abi transition.returnType), ω')
      | none => (.decodingFailed, ω)
  | none =>
      match receiveDispatchMsg contract I.calldata with
      | some transition =>                                                                           -- solmExec.receive
          if transition.params.isEmpty && transition.returnType.isEmpty then
            let (r, ω') := execTransitionBody fuel o ω cfg contract evm ∅ transition.body immutables
            (.ran r (.abi []), ω')
          else (.malformed "receive with parameters or return values", ω)
      | none =>
          match contract.fallback with
          | some transition =>                                                                       -- solmExec.fallback
              match fallbackCallargs I.calldata transition.params, fallbackReturnConvention transition with
              | some callargs, some rc =>
                  let (r, ω') := execTransitionBody fuel o ω cfg contract evm callargs transition.body immutables
                  (.ran r rc, ω')
              | _, _ => (.malformed "fallback with an unsupported signature", ω)
          | none => (.noDispatch, ω)

/-- `solmCtorExec`, executable.  `none` when the argument count does not match. -/
def solmCtorExecRun (fuel : Nat) (o : Oracle Ω) (ω : Ω) (cfg : Config) (contract : ContractDecl)
    (args : List Value) (σ σ₀ : AccountMap) (g : UInt256) (A : Substate) (I : ExecutionEnv) :
    Option (Outcome × Ω) :=
  if args.length = contract.ctor.params.length then
    let evm := initialState σ σ₀ g A I
    let argsStore : Store := Std.HashMap.ofList (List.zip (contract.ctor.params.map Param.name) args)
    some (execTransitionBody fuel o ω cfg contract evm argsStore contract.ctor.body (initialImmutables contract))
  else none

end Solm.Interp
