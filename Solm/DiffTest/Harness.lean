import Solm.DiffTest.Trace
import Solm.DiffTest.Compare
import Solm.DiffTest.Gen

/-!
# Differential test harness

A `Target` is a specification together with its compiled bytecode.  For each generated case the
harness runs the bytecode with evmlean, replays its call boundaries into the executable Solm
semantics, and decides the relation's cases (`compareRuntime`, `compareConstructor`).

Case families, all derived deterministically from the seed:
* every transition with random valid arguments, with and without call value, in both permission
  modes, from empty, random, and deployed storage;
* mutated calldata (truncations, dirty words, inflated offsets, corrupted selectors) and calldata
  that selects nothing (fallback/receive paths);
* call sequences that continue from the EVM's own post-state;
* the constructor with random arguments.

Gas is the oracle: the EVM runs with a fixed budget, out-of-gas cases are inconclusive (the
relation's `outOfGas` case), and the interpreter's call witnesses and `gasleft()` words are the
ones the EVM used.
-/

namespace Solm.DiffTest

open ABI Ethereum Ethereum.EVM Solm.Interp

/-- A specification and its artifact. -/
structure Target where
  name : String
  contract : ContractDecl
  config : Config
  /-- the deployed runtime code (for immutables: the template patched with `immutables`) -/
  runtime : ByteArray
  immutables : Store := ∅
  /-- creation code without arguments; `none` disables constructor tests and deployment -/
  initcode : Option ByteArray := none
  /-- the code a successful constructor must return, as a function of its final immutables -/
  runtimeCodeOf : Option (Store → ByteArray) := none
  /-- take `runtime` (and `runtimeCodeOf`) from a run of the creation code without arguments: for
      a constructor that fixes the immutables itself when no patch layout is available -/
  deployedRuntime : Bool := false
  /-- extra accounts (addresses with code) for the external-call tests -/
  callees : List (EVM.Address × ByteArray) := []
  selfAddress : EVM.Address := EVM.address 0x1000
  callers : List EVM.Address := [EVM.address 0x2000, EVM.address 0x3000]
  gas : Nat := 3000000
  fuel : Nat := 100000
  /-- extra interesting words for the generators -/
  words : List Nat := []

/-- The target's actors and words, plus the literals its contract mentions. -/
def Target.pools (t : Target) : Pools :=
  { addresses := t.selfAddress :: t.callers ++ t.callees.map Prod.fst ++ [EVM.address 0], words := t.words }
    ++ Pools.ofValues (contractLiterals t.contract)

def Target.codeOf (t : Target) : Store → ByteArray :=
  t.runtimeCodeOf.getD fun _ => t.runtime

/-- The initial world: the contract at `selfAddress`, funded callers, the callee pool. -/
def Target.world (t : Target) (code : ByteArray := t.runtime) : AccountMap :=
  let σ : AccountMap := (∅ : AccountMap).insert t.selfAddress
    { (default : Account) with code := code, balance := UInt256.ofNat (10 ^ 18) }
  let σ := t.callers.foldl (fun σ a => σ.insert a { (default : Account) with balance := UInt256.ofNat (10 ^ 20) }) σ
  t.callees.foldl (fun σ (a, c) => σ.insert a { (default : Account) with code := c, balance := UInt256.ofNat (10 ^ 18) }) σ

/-- The environment of a message to the contract. -/
def Target.env (t : Target) (code : ByteArray) (caller : EVM.Address) (value : Nat) (calldata : ByteArray)
    (perm : Bool) (timestamp : Nat := 0) (number : Nat := 0) : ExecutionEnv :=
  let header := { (default : ExecutionEnv).header with timestamp := timestamp, number := number }
  { (default : ExecutionEnv) with
      codeOwner := t.selfAddress, source := caller, sender := caller, weiValue := UInt256.ofNat value,
      calldata := calldata, code := code, gasPrice := 1, perm := perm, header := header }

/-- The value transfer of the message: the caller pays, the contract receives (as `Θ` does before
    running the code). -/
def transferValue (σ : AccountMap) (caller self : EVM.Address) (value : Nat) : AccountMap :=
  if value = 0 || caller = self then σ else
    let pay := σ.get? caller |>.getD default
    if pay.balance.toNat < value then σ else
      let σ := σ.insert caller { pay with balance := pay.balance - UInt256.ofNat value }
      let recv := σ.get? self |>.getD default
      σ.insert self { recv with balance := recv.balance + UInt256.ofNat value }

/-- One differential case. -/
structure Case where
  label : String
  σ : AccountMap
  I : ExecutionEnv

structure Report where
  target : String
  /-- the transition the case targets (`constructor`, or `stray` for calldata selecting nothing) -/
  transition : String
  label : String
  verdict : Verdict
  calldata : ByteArray
  deriving Repr

structure Summary where
  cases : Nat := 0
  agree : Nat := 0
  /-- agreements on a successful execution (the cases that compare storage and return data) -/
  success : Nat := 0
  evmOutOfGas : Nat := 0
  inapplicable : Nat := 0
  unsupported : Nat := 0
  specOutOfFuel : Nat := 0
  stuck : Nat := 0
  disagree : Nat := 0
  failures : List Report := []
  /-- per transition: cases run and successful agreements -/
  byTransition : List (String × Nat × Nat) := []

def Verdict.isSuccess : Verdict → Bool
  | .agree how => how == "success" || how == "deployed"
  | _ => false

def Summary.add (s : Summary) (rep : Report) : Summary :=
  let hit := rep.verdict.isSuccess
  let s := { s with cases := s.cases + 1, byTransition := bump s.byTransition rep.transition hit }
  match rep.verdict with
  | .agree _ => { s with agree := s.agree + 1, success := if hit then s.success + 1 else s.success }
  | .evmOutOfGas => { s with evmOutOfGas := s.evmOutOfGas + 1 }
  | .inapplicable _ => { s with inapplicable := s.inapplicable + 1 }
  | .unsupported _ => { s with unsupported := s.unsupported + 1 }
  | .specOutOfFuel => { s with specOutOfFuel := s.specOutOfFuel + 1 }
  | .specStuck _ => { s with stuck := s.stuck + 1, failures := s.failures ++ [rep] }
  | .disagree _ => { s with disagree := s.disagree + 1, failures := s.failures ++ [rep] }
where
  bump : List (String × Nat × Nat) → String → Bool → List (String × Nat × Nat)
    | [], name, hit => [(name, 1, if hit then 1 else 0)]
    | (n, c, k) :: rest, name, hit =>
        if n == name then (n, c + 1, if hit then k + 1 else k) :: rest else (n, c, k) :: bump rest name hit

/-- `successful/cases` per transition: shows which paths the generated cases reach. -/
def Summary.coverage (s : Summary) : String :=
  String.intercalate ", " (s.byTransition.map fun (n, c, k) => s!"{n} {k}/{c}")

def Summary.describe (s : Summary) : String :=
  s!"{s.cases} cases: {s.agree} agree ({s.success} successful), {s.disagree} disagree, {s.stuck} stuck, " ++
  s!"{s.evmOutOfGas} EVM out of gas, {s.specOutOfFuel} spec out of fuel" ++
  (if s.inapplicable = 0 then "" else s!", {s.inapplicable} inapplicable") ++
  (if s.unsupported = 0 then "" else s!", {s.unsupported} unsupported (allocation cap)")

/-- The outcome of one runtime case: the verdict and the EVM's final account map on success. -/
structure Run where
  verdict : Verdict
  evmResult : EVMResult
  postState : Option AccountMap

/-- Run both sides on one case. -/
def runCase (t : Target) (c : Case) : Run :=
  let g : UInt256 := .ofNat t.gas
  let A : Substate := default
  let evm0 := initialState c.σ c.σ g A c.I
  let tr := runTrace evm0 (t.gas + 1)
  let evmRes := tr.xiResult
  let (spec, ω) := solmExecRun t.fuel replayOracle (Replay.ofTrace tr) t.config t.contract t.immutables
    c.σ c.σ g A c.I
  let verdict := compareRuntime evmRes spec
  -- A successful specification run must have consumed every EVM call boundary and matched each.
  let verdict :=
    match verdict with
    | .agree how =>
        if !ω.mismatches.isEmpty then .disagree (String.intercalate "; " ω.mismatches)
        else
          match spec with
          | .ran (.result (.returned ..)) _ =>
              if ω.boundaries.isEmpty then .agree how
              else .disagree s!"the EVM made {ω.boundaries.length} more call(s) than the spec"
          | _ => .agree how
    | v => v
  let post := match tr.result with
    | .ok (.success s _) => some s.accountMap
    | _ => none
  { verdict, evmResult := evmRes, postState := post }

/-- Run the constructor on both sides; on agreement return the deployed world. -/
def runConstructor (t : Target) (initcode : ByteArray) (args : List Value) (value : Nat) (deployer : EVM.Address) :
    Verdict × Option AccountMap :=
  match t.config.selfDeployment initcode args with
  | none => (.inapplicable "selfDeployment does not encode the constructor arguments", none)
  | some code =>
    let σ := t.world ByteArray.empty
    let I := t.env code deployer value ByteArray.empty true
    let g : UInt256 := .ofNat t.gas
    let A : Substate := default
    let evm0 := initialState σ σ g A I
    let tr := runTrace evm0 (t.gas + 1)
    let evmRes := tr.xiResult
    match solmCtorExecRun t.fuel replayOracle (Replay.ofTrace tr) t.config t.contract args σ σ g A I with
    | none => (.specStuck "constructor arity mismatch", none)
    | some (outcome, ω) =>
      let verdict := compareConstructor evmRes outcome t.codeOf
      let verdict := if ω.mismatches.isEmpty then verdict else .disagree (String.intercalate "; " ω.mismatches)
      match verdict, tr.result with
      | .agree how, .ok (.success s o) =>
          -- the deployed account carries the returned code
          let σ' := match s.accountMap.get? t.selfAddress with
            | some acc => s.accountMap.insert t.selfAddress { acc with code := o }
            | none => s.accountMap.insert t.selfAddress { (default : Account) with code := o }
          (.agree how, some σ')
      | v, _ => (v, none)

/-- `deployedRuntime`: the code the creation code returns, run once without arguments. -/
def Target.resolveRuntime (t : Target) : Target :=
  match t.deployedRuntime, t.initcode with
  | true, some initcode =>
      match t.config.selfDeployment initcode [] with
      | none => t
      | some code =>
          let σ := t.world ByteArray.empty
          let I := t.env code (t.callers.headD t.selfAddress) 0 ByteArray.empty true
          match (runTrace (initialState σ σ (.ofNat t.gas) default I) (t.gas + 1)).result with
          | .ok (.success _ o) => { t with runtime := o, runtimeCodeOf := some fun _ => o }
          | _ => t
  | _, _ => t

/-! ## Case generation -/

/-- Calldata that selects no transition: empty, short, or a random selector. -/
def genStrayCalldata (r : Rng) : ByteArray × Rng :=
  let (bucket, r) := r.nat 0 3
  match bucket with
  | 0 => (ByteArray.empty, r)
  | 1 => let (n, r) := r.nat 1 3; r.bytes n
  | 2 => r.bytes 4
  | _ => let (n, r) := r.nat 4 100; r.bytes n

structure GenState where
  rng : Rng
  σ : AccountMap

/-- One generated case for the transition `tr` (or stray calldata when `tr = none`). -/
def genCase (t : Target) (tr : Option TransitionDecl) (σ : AccountMap) (r : Rng) (label : String)
    (block : Option (Nat × Nat) := none) : Case × Rng :=
  let (caller, r) := r.pick (t.callers ++ [t.selfAddress]) t.selfAddress
  -- the caller is a likely actor (owner checks, balances): weight it in the pools
  let base := { t.pools with addresses := caller :: caller :: t.pools.addresses }
  let (args, cd, r) := match tr with
    | some tr =>
        match genCalldata base tr r with
        | (some (vs, cd), r) => (vs, cd, r)
        | (none, r) => let (cd, r) := genStrayCalldata r; ([], cd, r)
    | none => let (cd, r) := genStrayCalldata r; ([], cd, r)
  -- the storage pre-state is keyed by the case's actors and holds its amounts, so guards on the
  -- caller, on balances, and on deadlines can pass
  let actors := Pools.ofValues args
  let focus := (caller :: actors.addresses).eraseDups
  let amounts := actors.words.flatMap fun w => [w, w + 1, 2 * w, w / 2]
  let storePools : Pools :=
    { addresses := focus ++ focus ++ base.addresses, words := amounts ++ base.words,
      fixedBytes := actors.fixedBytes ++ base.fixedBytes, bytes := actors.bytes ++ base.bytes }
  let (randomStore, r) := r.chance 80
  let evm0 := initialState σ σ (.ofNat t.gas) default (t.env t.runtime caller 0 .empty true)
  let (evm, written, r) :=
    if randomStore then randomStorage t.config t.contract storePools evm0 r else (evm0, {}, r)
  let (timestamp, number, r) := match block with
    | some (ts, bn) => (ts, bn, r)
    | none => genBlock written storePools r
  let (doMutate, r) := r.chance 15
  let (cd, r) := if doMutate then mutate cd r else (cd, r)
  let payable := match tr with | some tr => !isNonPayable tr | none => true
  let (value, r) := genCallValue payable (written ++ storePools) r
  let (static, r) := r.chance 10
  let name := match tr with | some tr => transitionSigStr tr | none => "stray"
  let tags := (if doMutate then " mutated" else "") ++ (if static then " static" else "") ++
    (if value != 0 then s!" value={value}" else "") ++ (if timestamp != 0 then s!" time={timestamp}" else "")
  ({ label := s!"{label} {name}{tags}",
     σ := transferValue evm.accountMap caller t.selfAddress value,
     I := t.env t.runtime caller value cd (!static) timestamp number }, r)

def transitionName : Option TransitionDecl → String
  | some tr => transitionSigStr tr
  | none => "stray"

/-- Run `count` cases per transition from the seed, continuing sequences from the EVM's
    post-state, and the constructor cases.  Returns the summary. -/
def runTarget (t : Target) (seed : Nat) (count : Nat) (sequenceLength : Nat := 4) : Summary := Id.run do
  let t := t.resolveRuntime
  let mut r := Rng.ofSeed seed
  let mut summary : Summary := {}
  let mut deployed : Option AccountMap := none
  -- constructor
  match t.initcode with
  | none => pure ()
  | some initcode =>
      for i in [:max 1 (count / 2)] do
        let (args, r') := genValues t.pools (t.contract.ctor.params.map Param.ty) r
        r := r'
        let (value, r') := if i % 3 == 2 then r.nat 1 100 else (0, r)
        r := r'
        let (deployer, r') := r.pick t.callers t.selfAddress
        r := r'
        let (verdict, σ?) := runConstructor t initcode args value deployer
        summary := summary.add { target := t.name, transition := "constructor",
                                 label := s!"constructor #{i} value={value}", verdict,
                                 calldata := (t.config.selfDeployment initcode args).getD ByteArray.empty }
        if deployed.isNone then deployed := σ?
  let base := deployed.getD (t.world)
  -- independent cases per transition and stray calldata
  let transitions := t.contract.transitions.map some ++ [none, none]
  for tr in transitions do
    for i in [:count] do
      let (c, r') := genCase t tr base r s!"#{i}"
      r := r'
      let run := runCase t c
      summary := summary.add { target := t.name, transition := transitionName tr, label := c.label,
                               verdict := run.verdict, calldata := c.I.calldata }
  -- sequences from the deployed/base state
  for s in [:max 1 (count / 2)] do
    let mut σ := base
    let (ts, bn, r') := genBlock {} t.pools r
    r := r'
    for k in [:sequenceLength] do
      let (tr, r') := r.pick t.contract.transitions.toArray.toList default
      r := r'
      let (c, r') := genCase t (some tr) σ r s!"seq{s}.{k}" (some (ts, bn))
      r := r'
      let run := runCase t c
      summary := summary.add { target := t.name, transition := transitionName (some tr), label := c.label,
                               verdict := run.verdict, calldata := c.I.calldata }
      match run.postState with
      | some σ' => if run.verdict.isAgree then σ := σ'
      | none => pure ()
  return summary

/-! ## Callees -/

def push2 (n : Nat) : ByteArray := ⟨#[0x61, UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]⟩

/-- A callee that returns (or reverts with) exactly `out`; with `writes`, it first stores `1` at
    its slot `0`, so a successful call leaves a visible state change. -/
def callee (out : ByteArray) (reverts := false) (writes := false) : ByteArray :=
  let prelude : ByteArray := if writes then ⟨#[0x60, 1, 0x60, 0, 0x55]⟩ else .empty
  prelude ++ push2 out.size ++ push2 (prelude.size + 15) ++ ⟨#[0x60, 0, 0x39]⟩ ++
    push2 out.size ++ ⟨#[0x60, 0, if reverts then 0xfd else 0xf3]⟩ ++ out

def wordBytes (n : Nat) : ByteArray := (UInt256.ofNat n).toByteArray

/-- The standard callee pool: returns one word, returns nothing, reverts, returns zero, writes. -/
def standardCallees : List (EVM.Address × ByteArray) :=
  [ (EVM.address 0x5000, callee (wordBytes 1)),
    (EVM.address 0x5001, callee .empty),
    (EVM.address 0x5002, callee (wordBytes 1) (reverts := true)),
    (EVM.address 0x5003, callee (wordBytes 0)),
    (EVM.address 0x5004, callee (wordBytes 1) (writes := true)),
    (EVM.address 0x5005, callee (wordBytes 1 ++ wordBytes 2)) ]

/-! ## Reporting -/

def hex (b : ByteArray) : String := Ethereum.toHex b

def printFailures (s : Summary) (limit : Nat := 10) : IO Unit := do
  for rep in s.failures.take limit do
    IO.println s!"  - [{rep.target}] {rep.label}"
    IO.println s!"      calldata: 0x{hex rep.calldata}"
    IO.println s!"      {rep.verdict.describe}"
  if s.failures.length > limit then
    IO.println s!"  ... {s.failures.length - limit} more"

/-- Run every target; returns `true` when no case disagreed or got stuck. -/
def runTargets (targets : List Target) (seed : Nat := 2026) (count : Nat := 20) : IO Bool := do
  let mut ok := true
  for t in targets do
    let s := runTarget t seed count
    IO.println s!"{t.name}: {s.describe}"
    IO.println s!"  successful/cases: {s.coverage}"
    if !s.failures.isEmpty then
      ok := false
      printFailures s
  pure ok

end Solm.DiffTest
