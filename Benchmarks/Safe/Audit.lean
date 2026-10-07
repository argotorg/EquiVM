import Benchmarks.Safe.AuditSupport
import Benchmarks.Safe.SpecSyntax

/-! Executable regression cases for the pinned Safe bytecode and the actual Solm AST. -/

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.Safe.Audit

def addressValue (n : Nat) : Value := .address (EVM.address n)
def wordBytes (n : Nat) : ByteArray := (UInt256.ofNat n).toByteArray
def hashValue (n : Nat := 0) : Value := .fixedBytes bytes32Width (wordBytes n).toList
def bytesValue (xs : List UInt8 := []) : Value := .bytes ⟨xs.toArray⟩

def calldataFor (t : TransitionDecl) (values : List Value) : ByteArray :=
  (encodeCallWithSelector? ((KEC (transitionSigStr t).toUTF8).extract 0 4)
    (t.params.map Param.ty) values).getD ByteArray.empty

def defaultInput : ABIType → Value
  | .bytes | .string => bytesValue []
  | .dynamicArray _ => .array []
  | .elem .address => addressValue 0
  | .elem .bool => .bool false
  | .elem (.bytes n) => .fixedBytes n (List.replicate (n.val + 1) 0)
  | _ => .int 0

def world (slots : List (UInt256 × UInt256) := [])
    (others : List (Nat × ByteArray) := []) : AccountMap :=
  let self : Account := { (default : Account) with
    balance := UInt256.ofNat 1000000000, code := safeBytecode,
    storage := slots.foldl (fun s (k, v) ↦ s.insert k v) ∅ }
  others.foldl (fun σ (a, code) ↦ σ.insert (EVM.address a)
    { (default : Account) with code, balance := UInt256.ofNat 1000 })
    ((∅ : AccountMap).insert (EVM.address 4096) self)

def state (input : ByteArray) (σ : AccountMap := world []) (caller : Nat := 4096)
    (perm : Bool := true) (value : Nat := 0) (depth : Nat := 0) : State :=
  { (default : State) with
    accountMap := σ, σ₀ := σ,
    executionEnv := { (default : ExecutionEnv) with
      codeOwner := EVM.address 4096, source := EVM.address caller, sender := EVM.address 8192,
      code := safeBytecode, calldata := input, perm, weiValue := UInt256.ofNat value,
      gasPrice := 3, depth := Fin.ofNat 1025 depth },
    machineState.gasAvailable := .ofUInt256 (UInt256.ofNat 5000000) }

def pair (k v : Nat) : UInt256 × UInt256 := (UInt256.ofNat k, UInt256.ofNat v)
def ownerSlot (a : Nat) : UInt256 := ownersSlot (.address (EVM.address a))
def moduleSlot (a : Nat) : UInt256 := modulesSlot (.address (EVM.address a))

def configuredSlots : List (UInt256 × UInt256) :=
  [pair 3 2, pair 4 1, pair 5 9, (ownerSlot 1, UInt256.ofNat 8192),
    (ownerSlot 8192, UInt256.ofNat 12288), (ownerSlot 12288, UInt256.ofNat 1),
    (moduleSlot 1, UInt256.ofNat 16384), (moduleSlot 16384, UInt256.ofNat 1)]

structure Case where
  name : String
  input : State
  expected : Option String := none
  constructor : Bool := false

def caseFor (name : String) (t : TransitionDecl) (values : List Value)
    (slots : List (UInt256 × UInt256) := configuredSlots)
    (others : List (Nat × ByteArray) := []) (caller : Nat := 4096)
    (expected : Option String := none) : Case :=
  { name, input := state (calldataFor t values) (world slots others) caller, expected }

-- A tiny callee that returns exactly the supplied bytes (also supports revert payloads).
def returning (out : ByteArray) (reverts : Bool := false) : ByteArray :=
  ⟨#[0x61, UInt8.ofNat (out.size / 256), UInt8.ofNat out.size,
      0x60, 0x0e, 0x5f, 0x39, 0x61, UInt8.ofNat (out.size / 256), UInt8.ofNat out.size,
      0x5f, if reverts then 0xfd else 0xf3, 0x00, 0x00]⟩ ++ out

def approvedSignature (owner : Nat) : ByteArray := wordBytes owner ++ wordBytes 0 ++ ⟨#[1]⟩

def execArgs (signature : ByteArray) (operation : Nat := 0) (price : Nat := 0)
    (token : Nat := 0) : List Value :=
  [addressValue 20480, .int 0, bytesValue [0xab, 0xcd], .int operation,
    .int 100000, .int 10, .int price, addressValue token, addressValue 0, .bytes signature]

def moduleArgs (operation : Nat := 0) : List Value :=
  [addressValue 20480, .int 0, bytesValue [0xab, 0xcd], .int operation]

def setupArgs : List Value :=
  [.array [addressValue 8192, addressValue 12288], .int 2, addressValue 0, bytesValue [],
    addressValue 0, addressValue 0, .int 0, addressValue 0]

def replaceWord (input : ByteArray) (offset value : Nat) : ByteArray :=
  input.extract 0 offset ++ wordBytes value ++ input.extract (offset + 32) input.size

def cases : List Case := Id.run do
  let mut cases : List Case := []
  -- Every selector, in both permission modes, with zero and nonzero call value.
  for t in transitions do
    for perm in [true, false] do
      for value in [0, 7] do
        let args := t.params.map (fun p ↦ defaultInput p.ty)
        cases := cases ++ [{
          name := s!"{transitionSigStr t}/perm={perm}/value={value}",
          input := state (calldataFor t args) (world configuredSlots) 4096 perm value }]
    -- Matched selectors with truncated argument heads must revert rather than fall back.
    if !t.params.isEmpty then
      cases := cases ++ [{
        name := s!"{transitionSigStr t}/short-head",
        input := state ((calldataFor t (t.params.map (fun p ↦ defaultInput p.ty))).extract 0 4),
        expected := some "revert" }]
    -- Reject dirty address/enum words, and check dynamic-head aliases and out-of-bounds offsets.
    for (param, index) in t.params.zipIdx do
      let input := calldataFor t (t.params.map (fun p ↦ defaultInput p.ty))
      let mutations := match param.ty with
        | .elem .address => [2 ^ 160, 2 ^ 256 - 1]
        | .elem (.int (.uint bits)) => if bits.val == 8 then [2, 256] else []
        | .bytes | .dynamicArray _ => [0, 1, 2 ^ 64, 2 ^ 256 - 1]
        | _ => []
      for value in mutations do
        cases := cases ++ [{
          name := s!"{transitionSigStr t}/arg={index}/word={value}",
          input := state (replaceWord input (4 + 32 * index) value) (world configuredSlots) }]
  for perm in [true, false] do
    cases := cases ++ [{
      name := s!"receive/perm={perm}", input := state ⟨#[]⟩ (world []) 8192 perm,
      expected := some (if perm then "success" else "staticViolation") }]
  for input in [⟨#[0xff]⟩, ⟨#[0xff, 0xff, 0xff]⟩, ⟨#[0xff, 0xff, 0xff, 0xff]⟩] do
    for handler in [0, 2 ^ 160, 20480, 2 ^ 160 + 20480] do
      cases := cases ++ [{
        name := s!"fallback/{input.size}/handler={handler}",
        input := state input (world [(fallbackHandlerSlot, UInt256.ofNat handler)]
          [(20480, returning ⟨#[0x11, 0x22, 0x33]⟩)]), expected := some "success" }]
  cases := cases ++ [
    {
      name := "fallback/handler-revert", input := state ⟨#[0xff]⟩
        (world [(fallbackHandlerSlot, UInt256.ofNat 20480)]
          [(20480, returning ⟨#[0x99]⟩ true)]), expected := some "revert" },
    caseFor "setup/initial" setupTransition setupArgs [] [] 8192 (some "success"),
    caseFor "getOwners/normal" getownersTransition [] configuredSlots [] 8192 (some "success"),
    caseFor "getOwners/allocation-panic" getownersTransition [] [pair 3 (2 ^ 64)] [] 8192
      (some "revert"),
    caseFor "getOwners/broken-list" getownersTransition [] [pair 3 0] [] 8192 (some "revert"),
    caseFor "pagination/one" getmodulespaginatedTransition [addressValue 1, .int 1]
      configuredSlots [] 8192 (some "success"),
    caseFor "pagination/empty" getmodulespaginatedTransition [addressValue 1, .int 3]
      [(moduleSlot 1, UInt256.ofNat 1)] [] 8192 (some "success"),
    caseFor "pagination/broken-zero" getmodulespaginatedTransition [addressValue 1, .int 3]
      [] [] 8192 (some "revert"),
    caseFor "pagination/allocation-panic" getmodulespaginatedTransition
      [addressValue 1, .int (2 ^ 64)] configuredSlots [] 8192 (some "revert"),
    caseFor "storage/wrap-slot" getstorageatTransition [.int maxUint256, .int 2]
      [pair (2 ^ 256 - 1) 17, pair 0 23] [] 8192 (some "success"),
    caseFor "storage/allocation-panic" getstorageatTransition [.int 0, .int (2 ^ 59)]
      [] [] 8192 (some "revert"),
    caseFor "storage/shift-wrap-OOG" getstorageatTransition [.int 0, .int (2 ^ 251)]
      [] [] 8192 (some "outOfGas")]
  -- Assembly slots must be fully overwritten, including arbitrary dirty high bits.
  for (t, slot) in [(setfallbackhandlerTransition, fallbackHandlerSlot),
      (setguardTransition, guardSlot), (setmoduleguardTransition, moduleGuardSlot)] do
    cases := cases ++ [caseFor s!"{t.name}/dirty-word" t [addressValue 0]
      [(slot, UInt256.ofNat (2 ^ 255 + 17))] [] 4096 (some "success")]
  let dirty := UInt256.ofNat (2 ^ 240)
  let dirtySlots := configuredSlots ++ [(ownerSlot 20480, dirty), (moduleSlot 20480, dirty)]
  cases := cases ++ [
    caseFor "owner/add-dirty-mapping" addownerwiththresholdTransition [addressValue 20480, .int 1]
      dirtySlots [] 4096 (some "success"),
    caseFor "owner/remove" removeownerTransition [addressValue 1, addressValue 8192, .int 1]
      configuredSlots [] 4096 (some "success"),
    caseFor "owner/swap" swapownerTransition
      [addressValue 1, addressValue 8192, addressValue 20480] dirtySlots [] 4096 (some "success"),
    caseFor "module/enable-dirty-mapping" enablemoduleTransition [addressValue 20480]
      dirtySlots [] 4096 (some "success"),
    caseFor "module/disable" disablemoduleTransition [addressValue 1, addressValue 16384]
      configuredSlots [] 4096 (some "success"),
    caseFor "owner/approve" approvehashTransition [hashValue 99]
      configuredSlots [] 8192 (some "success")]
  for operation in [0, 1, 2, 255] do
    for reverts in [false, true] do
      let target := [(20480, returning ⟨#[0x11, 0x22, 0x33]⟩ reverts)]
      for t in
          [exectransactionfrommoduleTransition, exectransactionfrommodulereturndataTransition] do
        cases := cases ++ [caseFor s!"{t.name}/op={operation}/revert={reverts}" t
          (moduleArgs operation) configuredSlots target 16384]
      cases := cases ++ [caseFor s!"exec/op={operation}/revert={reverts}" exectransactionTransition
        (execArgs (approvedSignature 8192) operation) configuredSlots target 8192]
  -- Token return sizes and truthiness differ from typed Solidity bool decoding.
  for out in [ByteArray.empty, wordBytes 0, wordBytes 1, wordBytes 2,
      ⟨#[0x01]⟩, wordBytes 1 ++ wordBytes 0] do
    cases := cases ++ [caseFor s!"exec/token-return={Ethereum.toHex out}" exectransactionTransition
      (execArgs (approvedSignature 8192) 0 2 24576) configuredSlots
      [(20480, returning ⟨#[]⟩), (24576, returning out)] 8192]
  cases := cases ++ [caseFor "exec/native-refund" exectransactionTransition
    (execArgs (approvedSignature 8192) 0 2) configuredSlots [(20480, returning ⟨#[]⟩)] 8192
    (some "success")]
  for size in [0, 1, 31, 32, 33, 64] do
    let result := ByteArray.mk (Array.replicate size 0xab)
    let guards := configuredSlots ++ [(guardSlot, UInt256.ofNat 24576),
      (moduleGuardSlot, UInt256.ofNat 24576)]
    let others := [(20480, returning ⟨#[0x11, 0x22]⟩), (24576, returning result)]
    cases := cases ++ [
      caseFor s!"exec/guard-return-size={size}" exectransactionTransition
        (execArgs (approvedSignature 8192)) guards others 8192,
      caseFor s!"module/guard-return-size={size}" exectransactionfrommodulereturndataTransition
        (moduleArgs 0) guards others 16384]
  -- Cached guard survives a delegatecall clearing its slot; the post-hook still runs.
  let clearGuard := ⟨#[0x5f, 0x7f]⟩ ++ moduleGuardSlot.toByteArray ++ ⟨#[0x55, 0x5f, 0x5f, 0xf3]⟩
  cases := cases ++ [caseFor "module/cached-guard" exectransactionfrommodulereturndataTransition
    (moduleArgs 1) (configuredSlots ++ [(moduleGuardSlot, UInt256.ofNat 24576)])
    [(20480, clearGuard), (24576, returning (wordBytes 37))] 16384 (some "success")]
  -- Guard ABI bool return decoding, including dirty words and short return data.
  for out in [wordBytes 0, wordBytes 1, wordBytes 2, ByteArray.empty, wordBytes 1 ++ wordBytes 7] do
    for t in [setguardTransition, setmoduleguardTransition] do
      cases := cases ++ [caseFor s!"{t.name}/return={Ethereum.toHex out}" t [addressValue 24576]
        configuredSlots [(24576, returning out)] 4096]
  -- ERC-1271 exact length and exact magic word, reverting validators, and hash approvals.
  let sig := wordBytes 24576 ++ wordBytes 65 ++ ⟨#[0]⟩ ++ wordBytes 3 ++ ⟨#[1, 2, 3]⟩
  let sigSlots := configuredSlots ++ [(ownerSlot 24576, UInt256.ofNat 1)]
  for out in [wordBytes (0x1626ba7e * 2 ^ 224), wordBytes 0, ⟨#[0x16, 0x26, 0xba, 0x7e]⟩,
      wordBytes (0x1626ba7e * 2 ^ 224) ++ wordBytes 0] do
    for reverts in [false, true] do
      cases := cases ++ [caseFor s!"signature/1271/{Ethereum.toHex out}/{reverts}"
        checksignaturesAddressBytes32BytesTransition [addressValue 8192, hashValue 0, .bytes sig]
        sigSlots [(24576, returning out reverts)] 8192]
  for n in [0, 1, 2, 3, 27, 28, 31, 32, 255] do
    let sig := wordBytes 8192 ++ wordBytes 0 ++ ⟨#[UInt8.ofNat n]⟩
    cases := cases ++ [caseFor s!"signature/v={n}"
      checknsignaturesAddressBytes32BytesUint256Transition
      [addressValue 8192, hashValue 0, .bytes sig, .int 1] configuredSlots [] 8192]
  let publicKey := wordBytes 123 ++ wordBytes 456
  let signer := EVM.address (Ethereum.uInt256OfByteArray (KEC publicKey)).toNat
  for wrongSigner in [false, true] do
    let claimed := if wrongSigner then 8192 else signer.val
    let sig := wordBytes claimed ++ wordBytes 65 ++ ⟨#[2]⟩ ++
      wordBytes 1 ++ wordBytes 2 ++ publicKey
    let slots := configuredSlots ++ [(ownerSlot signer.val, UInt256.ofNat 1)]
    for out in [ByteArray.empty, wordBytes 0, wordBytes 1, wordBytes 2,
        wordBytes 1 ++ wordBytes 0] do
      cases := cases ++ [caseFor s!"signature/p256/{wrongSigner}/{Ethereum.toHex out}"
        checknsignaturesAddressBytes32BytesUint256Transition
        [addressValue 8192, hashValue 0, .bytes sig, .int 1] slots
        [(256, returning out)] 8192]
  -- Threshold is loaded before external signature validation and list order is strict.
  let twice := approvedSignature 8192 ++ approvedSignature 8192
  cases := cases ++ [caseFor "signature/duplicate-owner"
    checknsignaturesAddressBytes32BytesUint256Transition
    [addressValue 8192, hashValue 0, .bytes twice, .int 2] configuredSlots [] 8192 (some "revert")]
  -- Reentrant delegatecall can change arbitrary storage. Return data is captured before guards.
  let writes : ByteArray := ⟨#[0x60, 0x63, 0x60, 0x05, 0x55, 0x5f, 0x5f, 0xf3]⟩
  cases := cases ++ [caseFor "module/delegate-storage" exectransactionfrommodulereturndataTransition
    (moduleArgs 1) configuredSlots [(20480, writes)] 16384 (some "success")]
  for depth in [0, 1024] do
    let c := caseFor s!"module/depth={depth}" exectransactionfrommoduleTransition
      (moduleArgs 0) configuredSlots [] 16384 (some "success")
    cases := cases ++ [{ c with input.executionEnv.depth := Fin.ofNat 1025 depth }]
  -- Static-mode module calls can reach LOG without executing any preceding SSTORE.
  for operation in [0, 1] do
    let c := caseFor s!"module/static-log/op={operation}" exectransactionfrommoduleTransition
      (moduleArgs operation) configuredSlots [(20480, returning ⟨#[]⟩)] 16384
      (some "staticViolation")
    cases := cases ++ [{ c with input.executionEnv.perm := false }]
  -- Insufficient balance is a false CALL result; nonzero-value CALL in static mode is a halt.
  let args := [addressValue 20480, .int (2 ^ 255), bytesValue [], .int 0]
  let c := caseFor "module/insufficient-balance" exectransactionfrommoduleTransition args
    configuredSlots [] 16384 (some "success")
  cases := cases ++ [c, { c with
    name := "module/static-value", expected := some "staticViolation",
    input.executionEnv.perm := false }]
  -- A proxy/delegated execution can have codeOwner.code different from ExecutionEnv.code.
  for delegated in [false, true] do
    let code : ByteArray := if delegated then ⟨#[0xef, 0x01, 0x00]⟩ else ⟨#[0xef, 0x01, 0x01]⟩
    let σ := world configuredSlots
    let self := (σ.get? (EVM.address 4096)).getD default
    let σ := σ.insert (EVM.address 4096) { self with code }
    cases := cases ++ [{
      name := s!"owner/self-delegated={delegated}",
      input := state (calldataFor addownerwiththresholdTransition [addressValue 4096, .int 1]) σ,
      expected := some (if delegated then "success" else "revert") }]
  cases := cases ++ [
    {
      name := "receive/value", input := state ⟨#[]⟩ (world []) 8192 true 7,
      expected := some "success" },
    {
      name := "fallback/value", input := state ⟨#[0xff]⟩ (world []) 8192 true 7,
      expected := some "revert" },
    caseFor "owner/count-underflow" removeownerTransition
      [addressValue 1, addressValue 8192, .int 1] (configuredSlots ++ [pair 3 0]) [] 4096
      (some "revert"),
    caseFor "owner/count-overflow" addownerwiththresholdTransition [addressValue 20480, .int 1]
      (configuredSlots ++ [pair 3 (2 ^ 256 - 1)]) [] 4096 (some "revert")]
  for value in [0, 1] do
    cases := cases ++ [{
      name := s!"constructor/value={value}", constructor := true,
      input := { state ⟨#[]⟩ (world [pair 4 77]) 8192 true value with
        executionEnv.code := safeCreationBytecode },
      expected := some (if value == 0 then "success" else "revert") }]
  return cases

def main : IO Unit := do
  let mut counts : List (String × Nat) := []
  let mut failures := []
  for c in cases do
    match check c.input c.constructor with
    | .error message => failures := failures ++ [s!"{c.name}: {message}"]
    | .ok result =>
      if c.expected.isSome && c.expected != some result then
        failures := failures ++ [s!"{c.name}: expected {c.expected.getD ""}, got {result}"]
      counts := (result, (counts.lookup result).getD 0 + 1) :: counts.filter (·.1 != result)
  for failure in failures do IO.println failure
  IO.println (s!"Safe differential audit: {cases.length} cases, outcomes {counts}, " ++
    s!"failures {failures.length}")
  if !failures.isEmpty then throw (IO.userError "Safe differential audit failed")

#eval main

end Benchmarks.Safe.Audit
