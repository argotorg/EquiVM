import Solidity.Interp
import Solidity.Setup
import Solidity.Equiv

/-!
# Differential test harness

Runs the EVM (`Ξ`) on pinned bytecode and the interpreter on the corresponding Solidity spec
from the same pre-state, and compares the results with a boolean version of
`execResultsEquiv` / `ctorResultEquiv`: created accounts, the account map (exactly: both sides
erase zero slots through `Account.updateStorage`), the log series, and return / revert data.
-/

namespace Solidity.Test

open Ethereum

def hexOfBytes (b : ByteArray) : String :=
  String.join <| b.toList.map fun x =>
    let s := Nat.toDigits 16 x.toNat
    String.ofList (if s.length = 1 then '0' :: s else s)

def selectorOfSig (sig : String) : ByteArray := (ffi.KEC sig.toUTF8).extract 0 4

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

/-- Decode a hex string (fixtures). -/
def bytesOfHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.toArray
  let mut out := ByteArray.empty
  let mut i := 0
  while i + 1 < cs.size do
    out := out.push ((hexDigit cs[i]! * 16 + hexDigit cs[i+1]!).toUInt8)
    i := i + 2
  return out

def addr (n : Nat) : EVM.Address := .ofNat n

def word (n : Nat) : UInt256 := .ofNat n

def natOfBytes (b : ByteArray) : Nat := bytesToNatBE b.toList

/-- 32-byte big-endian word. -/
def wordBytes (n : Nat) : ByteArray :=
  ⟨((List.range 32).map fun i => ((n >>> (8 * (31 - i))) % 256).toUInt8).toArray⟩

/-- Fuel for the interpreter (one unit per evaluation step / loop iteration). -/
def interpFuel : Nat := 100000

/-- Gas is irrelevant to the spec; sub-calls get a fixed budget. -/
def testOracle : Oracle :=
  { gasleft := fun _ => ⟨0⟩, callGas := fun _ => .ofNat 1000000, substateIn := fun _ => default }

def account (balance : Nat := 0) (code : ByteArray := .empty) (nonce : Nat := 1)
    (storage : List (UInt256 × UInt256) := []) : Account :=
  { nonce := .ofNat nonce, balance := .ofNat balance, code := code,
    storage := storage.foldl (fun s (k, v) => if v == ⟨0⟩ then s else s.insert k v) ∅, tstorage := ∅ }

inductive Expect where
  | success | revert | any
  deriving Repr, BEq

structure Case where
  name : String := ""
  /-- Runtime code, or init code (without arguments) when `ctorArgs` is set. -/
  code : ByteArray := .empty
  this : EVM.Address := addr 0xC0FFEE
  sender : EVM.Address := addr 0xA11CE
  value : Nat := 0
  /-- Raw calldata, or an external call `(signature, arguments)` encoded by `runCase`. -/
  calldata : ByteArray := .empty
  call : Option (String × List ABI.ABIValue) := none
  /-- Other accounts (the contract itself is added by `pre`). -/
  accounts : List (EVM.Address × Account) := []
  /-- Storage of the contract under test: raw slots, and layout paths resolved by `runCase`. -/
  storage : List (UInt256 × UInt256) := []
  refs : List (Solm.EvaledStorageRef × Nat) := []
  balance : Nat := 0
  gas : Nat := 10000000
  header : BlockHeader := default
  /-- Constructor case: ABI arguments; the spec's returned code must be the runtime. -/
  ctorArgs : Option (List ABI.ABIValue × ByteArray) := none
  expect : Expect := .any
  /-- A documented mismatch (e.g. a hand-written pinned initcode); must still mismatch. -/
  known : Option String := none

def Case.pre (c : Case) : AccountMap :=
  let code := if c.ctorArgs.isSome then ByteArray.empty else c.code
  c.accounts.foldl (fun σ (a, acc) => σ.insert a acc)
    ((∅ : AccountMap).insert c.this (account c.balance code 1 c.storage)
      |>.insert c.sender (account (balance := 10 ^ 24) (nonce := 0)))

def Case.deployedCode (c : Case) (cfg : Config) : Option ByteArray :=
  match c.ctorArgs with
  | none => some c.code
  | some (args, _) => cfg.selfDeployment c.code args

def Case.env (c : Case) (code : ByteArray) : ExecutionEnv :=
  { codeOwner := c.this, sender := c.sender, source := c.sender, weiValue := .ofNat c.value,
    calldata := c.calldata, code := code, gasPrice := 0, header := c.header, depth := 0,
    perm := true, blobVersionedHashes := [] }

/-! ## Running both sides -/

def runEVM (c : Case) (code : ByteArray) : EVMResult :=
  Ethereum.EVM.Ξ ∅ default #[] c.pre c.pre (.ofNat c.gas) default (c.env code)

inductive SpecOutcome where
  | run (res : TopResult) (conv : Refinement.ReturnConvention)
  | ctor (res : CtorResult)
  | rejected
  | stuck

def runSpec (cfg : Config) (fc : FlatContract) (c : Case) (code : ByteArray) : SpecOutcome :=
  let I := c.env code
  match c.ctorArgs with
  | some (args, _) =>
    match (Interp.interpCtor cfg testOracle fc interpFuel args ∅ default #[] c.pre c.pre (.ofNat c.gas) default I).run with
    | some (.ok r) => .ctor r
    | some (.error d) => .ctor (.reverted d)
    | none => .stuck
  | none =>
    if Interp.specRejectsB cfg fc I then .rejected
    else match (Interp.interpExec cfg testOracle fc interpFuel ∅ default #[] c.pre c.pre (.ofNat c.gas) default I).run with
    | some (.ok (r, conv)) => .run r conv
    | some (.error d) => .run (.reverted d) .rawBytes
    | none => .stuck

/-! ## Comparison (boolean `execResultsEquiv` / `ctorResultEquiv`) -/

def accountEquivB (a b : Account) : Bool :=
  a.nonce == b.nonce && a.balance == b.balance && a.code == b.code &&
    a.storage.toList == b.storage.toList && a.tstorage.toList == b.tstorage.toList

def accountMapEquivB (σ τ : AccountMap) : Bool :=
  let xs := σ.toList
  let ys := τ.toList
  xs.length == ys.length && (xs.zip ys).all fun p => p.1.1 == p.2.1 && accountEquivB p.1.2 p.2.2

def returnDataEquivB (out : ByteArray) (vs : List ABI.ABIValue) : Refinement.ReturnConvention → Bool
  | .abi tys => ABI.encodeReturnValues? tys vs == some out
  | .rawBytes => match vs with
    | [.bytes b] => b == out
    | _ => false

structure Diff where
  msgs : List String := []

def Diff.ok (d : Diff) : Bool := d.msgs.isEmpty

def Diff.add (d : Diff) (b : Bool) (msg : String) : Diff :=
  if b then d else { msgs := d.msgs ++ [msg] }

def describeAccounts (σ : AccountMap) : String :=
  String.intercalate "; " <| σ.toList.map fun (a, acc) =>
    s!"{a.toNat}: n={acc.nonce.toNat} b={acc.balance.toNat} code={acc.code.size}B st={acc.storage.toList.map fun p => (p.1.toNat, p.2.toNat)}"

def describeLogs (ls : LogSeries) : String :=
  String.intercalate "; " <| ls.toList.map fun l =>
    s!"{l.address.toNat} topics={l.topics.toList.map (·.toNat)} data={hexOfBytes l.data}"

def compareStates (d : Diff) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
    (A' : Substate) (m : Machine) : Diff :=
  d.add (cA'.toList == m.evm.createdAccounts.toList) "created accounts differ"
    |>.add (accountMapEquivB σ' m.evm.accountMap)
        s!"accounts differ\n    evm:  {describeAccounts σ'}\n    spec: {describeAccounts m.evm.accountMap}"
    |>.add (A'.logSeries == m.evm.substate.logSeries)
        s!"logs differ\n    evm:  {describeLogs A'.logSeries}\n    spec: {describeLogs m.evm.substate.logSeries}"

def compareRun (r : EVMResult) (res : TopResult) (conv : Refinement.ReturnConvention) : Diff :=
  match r, res with
  | .ok (.success (cA', σ', _, A') out), .returned m vs =>
    compareStates {} cA' σ' A' m
      |>.add (returnDataEquivB out vs conv) s!"return data differ: evm={hexOfBytes out}"
  | .ok (.revert _ out), .reverted d =>
    Diff.add {} (out == d) s!"revert data differ\n    evm:  {hexOfBytes out}\n    spec: {hexOfBytes d}"
  | .ok (.success _ out), .reverted d =>
    { msgs := [s!"evm succeeded ({hexOfBytes out}) but spec reverted ({hexOfBytes d})"] }
  | .ok (.revert _ out), .returned _ _ =>
    { msgs := [s!"evm reverted ({hexOfBytes out}) but spec succeeded"] }
  | .error e, _ => { msgs := [s!"evm exception {repr e}"] }

def compareCtor (r : EVMResult) (res : CtorResult) (runtime : ByteArray) : Diff :=
  match r, res with
  | .ok (.success (cA', σ', _, A') out), .ok m _ =>
    compareStates {} cA' σ' A' m
      |>.add (out == runtime) s!"deployed code differs ({out.size} bytes vs {runtime.size})"
  | .ok (.revert _ out), .reverted d =>
    Diff.add {} (out == d) s!"revert data differ\n    evm:  {hexOfBytes out}\n    spec: {hexOfBytes d}"
  | .ok (.success _ _), .reverted d => { msgs := [s!"evm succeeded but spec reverted ({hexOfBytes d})"] }
  | .ok (.revert _ out), .ok _ _ => { msgs := [s!"evm reverted ({hexOfBytes out}) but spec succeeded"] }
  | .error e, _ => { msgs := [s!"evm exception {repr e}"] }

def checkExpect (c : Case) (r : EVMResult) : Diff :=
  match c.expect, r with
  | .any, _ => {}
  | .success, .ok (.success _ _) => {}
  | .revert, .ok (.revert _ _) => {}
  | e, _ => { msgs := [s!"expected {repr e}"] }

def Case.resolve (c : Case) (fc : FlatContract) (t : LayoutTable) : Option Case := do
  let calldata ← match c.call with
    | none => some c.calldata
    | some (sig, args) => do
      let e ← fc.entries.find? (·.sigStr == sig)
      ABI.encodeCallWithSelector? (selectorOfSig sig) e.sig.paramTypes args
  let storage ← c.refs.foldlM (init := c.storage) fun st (r, v) => do
    let loc ← layout t r default
    let packed := v <<< (8 * loc.offset.val)
    match st.find? (·.1 == loc.slot) with
    | some (_, w) => pure ((st.filter (·.1 != loc.slot)) ++ [(loc.slot, word (w.toNat ||| packed))])
    | none => pure (st ++ [(loc.slot, word packed)])
  pure { c with calldata := calldata, storage := storage }

/-- Compare both sides; the EVM runs first so that an out-of-gas run (e.g. an unbounded loop)
    never reaches the interpreter.  `skipOOG` treats out-of-gas as a pass (fuzzing). -/
def runCase (cfg : Config) (fc : FlatContract) (c₀ : Case) (skipOOG : Bool := false) : Diff :=
  match c₀.deployedCode cfg, fc.layoutTable?.bind (c₀.resolve fc) with
  | none, _ => { msgs := ["cannot build deployment code"] }
  | _, none => { msgs := ["cannot resolve the case (calldata or storage paths)"] }
  | some code, some c =>
    let r := runEVM c code
    let d := checkExpect c r
    match r with
    | .error .OutOfGass => if skipOOG then {} else d.add false "evm out of gas"
    | _ =>
      match r, runSpec cfg fc c code with
      | _, .stuck => d.add false "spec stuck"
      | .ok (.revert _ out), .rejected => d.add (out.isEmpty) s!"spec rejects but evm reverted with {hexOfBytes out}"
      | .ok (.success _ _), .rejected => d.add false "spec rejects but evm succeeded"
      | .error e, .rejected => d.add false s!"spec rejects but evm raised {repr e}"
      | _, .run res conv => { msgs := d.msgs ++ (compareRun r res conv).msgs }
      | _, .ctor res =>
        let runtime := (c.ctorArgs.map (·.2)).getD .empty
        { msgs := d.msgs ++ (compareCtor r res runtime).msgs }

/-- `runCase` on a task, giving up after `ms` milliseconds (a spec that fails to terminate). -/
def runCaseTimeout (cfg : Config) (fc : FlatContract) (c : Case) (skipOOG : Bool := false)
    (ms : Nat := 20000) : IO Diff := do
  let t := Task.spawn fun _ => runCase cfg fc c skipOOG
  let mut waited := 0
  while !(← IO.hasFinished t) && waited < ms do
    IO.sleep 5
    waited := waited + 5
  if ← IO.hasFinished t then pure t.get else pure { msgs := ["spec did not terminate"] }

structure Scenario where
  name : String
  program : Program
  target : Ident
  cases : List Case
  /-- Immutable values baked into the runtime code under test. -/
  immutables : List (Ident × Value) := []
  /-- Creation bytecodes of the contracts the spec deploys with `new`. -/
  creations : List (Ident × EVM.Bytes) := []

def runScenario (s : Scenario) : IO Bool := do
  match setup s.program s.target s.immutables s.creations with
  | .error e => IO.println s!"[{s.name}] setup failed: {e}"; return false
  | .ok (fc, cfg) =>
    let mut ok := true
    let mut known := 0
    for c in s.cases do
      let d ← runCaseTimeout cfg fc c
      match c.known with
      | some why =>
        if d.ok then
          ok := false
          IO.println s!"[{s.name}] {c.name}: FAILED (expected a known deviation: {why})"
        else
          known := known + 1
          IO.println s!"[{s.name}] {c.name}: known deviation ({why})"
      | none =>
        unless d.ok do
          ok := false
          IO.println s!"[{s.name}] {c.name}: FAILED"
          for m in d.msgs do IO.println s!"  - {m}"
    let tag := if known = 0 then "" else s!", {known} known"
    IO.println s!"[{s.name}] {s.cases.length} cases{tag}: {if ok then "OK" else "FAILURES"}"
    return ok

/-! ## Fuzzing: random mutations of the scenario cases -/

structure Rng where
  g : StdGen

def Rng.nat (r : Rng) (hi : Nat) : Nat × Rng :=
  let (n, g) := randNat r.g 0 hi
  (n, ⟨g⟩)

def Rng.pick {α} (r : Rng) (xs : List α) (dflt : α) : α × Rng :=
  let (i, r') := r.nat (xs.length - 1)
  (xs[i]?.getD dflt, r')

/-- A word from a palette of boundary values, small numbers and dirty addresses. -/
def Rng.word (r : Rng) : Nat × Rng :=
  let (k, r1) := r.nat 8
  match k with
  | 0 => (0, r1)
  | 1 => (1, r1)
  | 2 => r1.nat 1000
  | 3 => (2 ^ 256 - 1, r1)
  | 4 => (2 ^ 255, r1)
  | 5 => r1.nat 0xffff
  | 6 => let (a, r2) := r1.nat 0xffff; (2 ^ 160 + a, r2)
  | 7 => let (a, r2) := r1.nat (2 ^ 64); (a * 2 ^ 128, r2)
  | _ => r1.pick [0xA11CE, 0xB0B, 0xF00D, 0xBE, 0xC0FFEE] 0

/-- A value that fits a storage location (bools stay 0/1). -/
def Rng.fitting (r : Rng) (loc : Storage.StorageLoc) : Nat × Rng :=
  let (w, r1) := r.word
  match loc.type with
  | .bool => (w % 2, r1)
  | _ => (w % 2 ^ (8 * loc.size.val), r1)

def mutateCalldata (r : Rng) (fc : FlatContract) (cd : ByteArray) : ByteArray × Rng :=
  let (k, r1) := r.nat 9
  match k with
  | 0 => let (n, r2) := r1.nat cd.size; (cd.extract 0 n, r2)
  | 1 =>
    let (n, r2) := r1.nat 40
    let (b, r3) := r2.nat 255
    (cd ++ ⟨(List.replicate n b.toUInt8).toArray⟩, r3)
  | 2 | 3 | 4 =>
    if cd.size < 36 then (cd, r1) else
    let words := (cd.size - 4) / 32
    let (i, r2) := r1.nat (words - 1)
    let (w, r3) := r2.word
    (cd.extract 0 (4 + 32 * i) ++ wordBytes w ++ cd.extract (4 + 32 * (i + 1)) cd.size, r3)
  | 5 | 6 =>
    let (i, r2) := r1.nat (fc.entries.length - 1)
    match fc.entries[i]? with
    | none => (cd, r2)
    | some e =>
      let (n, r3) := r2.nat (e.sig.paramTypes.length + 1)
      (List.range n).foldl (fun (b, r) _ => let (w, r') := r.word; (b ++ wordBytes w, r'))
        (selectorOfSig e.sigStr, r3)
  | _ => (cd, r1)

/-- Mutate the environment (value, sender, timestamp, seeded storage) of a base case. -/
def mutateEnv (r : Rng) (t : LayoutTable) (c : Case) : Case × Rng :=
  let (kv, r1) := r.nat 4
  let (v, r2) := if kv == 0 then r1.nat 5 else (c.value, r1)
  let (ks, r3) := r2.nat 3
  let (snd, r4) := if ks == 0 then r3.pick [0, 0xB0B, 0xF00D, 0xA11CE] 0 else (c.sender.toNat, r3)
  let (kt, r5) := r4.nat 2
  let (ts, r6) := if kt == 0 then r5.pick [0, 500, 1000, 1500, 2000, 2 ^ 40] 0 else (c.header.timestamp, r5)
  let (refs, r7) := c.refs.foldl (fun (acc, r) (ref, v) =>
      let (k, r') := r.nat 2
      match k, layout t ref default with
      | 0, some loc => let (w, r'') := r'.fitting loc; (acc ++ [(ref, w)], r'')
      | _, _ => (acc ++ [(ref, v)], r')) ([], r6)
  ({ c with
      value := v, sender := addr snd, header := { c.header with timestamp := ts }, refs := refs,
      expect := .any, known := none }, r7)

def describeCase (c : Case) : String :=
  s!"sender={c.sender.toNat} value={c.value} ts={c.header.timestamp} calldata={hexOfBytes c.calldata} storage={c.storage.map fun p => (p.1.toNat, p.2.toNat)}"

/-- `n` random variants of each runtime case of `s`; out-of-gas EVM runs are skipped. -/
def fuzzScenario (s : Scenario) (seed n : Nat) : IO Bool := do
  match setup s.program s.target s.immutables s.creations with
  | .error e => IO.println s!"[{s.name}] setup failed: {e}"; return false
  | .ok (fc, cfg) =>
    let some t := fc.layoutTable? | IO.println s!"[{s.name}] no layout"; return false
    let bases := s.cases.filter (·.ctorArgs.isNone)
    let mut r : Rng := ⟨mkStdGen seed⟩
    let mut ok := true
    let mut ran := 0
    let mut succ := 0
    let mut rev := 0
    for c₀ in bases do
      for _ in List.range n do
        let (c₁, r1) := mutateEnv r t c₀
        r := r1
        let some c₂ := c₁.resolve fc t | continue
        let (cd, r2) := mutateCalldata r fc c₂.calldata
        r := r2
        let c := { c₂ with calldata := cd, call := none, refs := [] }
        ran := ran + 1
        match runEVM c c.code with
        | .ok (.success _ _) => succ := succ + 1
        | .ok (.revert _ _) => rev := rev + 1
        | _ => pure ()
        let d ← runCaseTimeout cfg fc c (skipOOG := true)
        unless d.ok do
          ok := false
          IO.println s!"[{s.name}] fuzz of {c₀.name}: FAILED\n  {describeCase c}"
          for m in d.msgs do IO.println s!"  - {m}"
    IO.println s!"[{s.name}] fuzz: {ran} cases ({succ} succeed, {rev} revert): {if ok then "OK" else "FAILURES"}"
    return ok

end Solidity.Test
