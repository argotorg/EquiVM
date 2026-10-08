import Solm.Semantics
import ABI.Encode

/-!
# Input generation

Deterministic, seed-driven generators for the differential tests: ABI values biased towards
boundaries and towards the words a case can refer to, calldata for a transition, calldata
mutations, and storage pre-states written through the specification's own storage backend and
keyed by the case's actors.
-/

namespace Solm.DiffTest

open ABI Ethereum

/-- A splittable pseudo-random generator (the standard library's `StdGen`). -/
structure Rng where
  gen : StdGen

def Rng.ofSeed (seed : Nat) : Rng := ⟨mkStdGen seed⟩

def Rng.nat (r : Rng) (lo hi : Nat) : Nat × Rng :=
  let (n, g) := randNat r.gen lo hi
  (n, ⟨g⟩)

/-- `true` with probability `percent`/100. -/
def Rng.chance (r : Rng) (percent : Nat) : Bool × Rng :=
  let (n, r) := r.nat 0 99
  (n < percent, r)

def Rng.pick (r : Rng) (xs : List α) (fallback : α) : α × Rng :=
  match xs with
  | [] => (fallback, r)
  | _ =>
    let (i, r) := r.nat 0 (xs.length - 1)
    (xs.getD i fallback, r)

def Rng.bytes (r : Rng) (len : Nat) : ByteArray × Rng := Id.run do
  let mut r := r
  let mut out : Array UInt8 := #[]
  for _ in [:len] do
    let (b, r') := r.nat 0 255
    r := r'
    out := out.push (UInt8.ofNat b)
  return (⟨out⟩, r)

/-- Draw `bits` random bits as a natural number (built from 32-bit chunks). -/
def Rng.bigNat (r : Rng) (bits : Nat) : Nat × Rng := Id.run do
  let mut r := r
  let mut acc := 0
  let mut remaining := bits
  while remaining > 0 do
    let take := min remaining 32
    let (chunk, r') := r.nat 0 (2 ^ take - 1)
    r := r'
    acc := acc * 2 ^ take + chunk
    remaining := remaining - take
  return (acc, r)

/-! ## Pools -/

/-- What the generators draw from: actors, interesting words, and byte constants.  Pools come
    from a target's actors, from the literals the contract mentions, from the arguments of the
    case being generated, and from the storage written for it. -/
structure Pools where
  addresses : List EVM.Address := []
  words : List Nat := []
  fixedBytes : List (Fin 32 × List UInt8) := []
  bytes : List ByteArray := []
  deriving Inhabited

instance : Append Pools where
  append a b := { addresses := a.addresses ++ b.addresses, words := a.words ++ b.words,
                  fixedBytes := a.fixedBytes ++ b.fixedBytes, bytes := a.bytes ++ b.bytes }

def Pools.dedup (p : Pools) : Pools :=
  { addresses := p.addresses.eraseDups, words := p.words.eraseDups,
    fixedBytes := p.fixedBytes.eraseDups, bytes := p.bytes.eraseDups }

/-- The pools some values contribute: their addresses, their non-negative integers, the last
    index of every array, and their byte constants. -/
partial def Pools.ofValues (vs : List Value) : Pools := vs.foldl (fun p v => p ++ ofValue v) {}
where
  ofValue : Value → Pools
    | .address a => { addresses := [a] }
    | .int i => if 0 ≤ i ∧ i < 2 ^ 256 then { words := [i.toNat] } else {}
    | .fixedBytes n bs => { fixedBytes := [(n, bs)] }
    | .bytes b => { bytes := [b] }
    | .array vs => (if vs.isEmpty then {} else { words := [vs.length - 1] }) ++ Pools.ofValues vs
    | .tuple vs => Pools.ofValues vs
    | .struct _ fields => Pools.ofValues (fields.map (·.2))
    | _ => {}

/-! ## The literal dictionary -/

mutual
/-- The literals an expression mentions. -/
partial def exprLiterals : Expr → List Value
  | .intLit i => [.int i]
  | .bytesLit b => [.bytes b]
  | .fixedBytesLit n bs => [.fixedBytes n bs]
  | .newBytes e | .newArray _ e | .tupleGet e _ | .field e _ | .inRange _ e | .cast e _ | .addrOf e
  | .unary _ e | .keccak256 e | .abiDecode _ e | .extCodeSize e | .blockhash e | .balanceOf e
  | .extCodeHash e => exprLiterals e
  | .structLit _ fields => fields.flatMap fun (_, e) => exprLiterals e
  | .arrayLit es | .tupleLit es | .abiEncodeCall _ es => es.flatMap exprLiterals
  | .abiEncodePacked es => es.flatMap fun (_, e) => exprLiterals e
  | .bytesSlice a b c | .ite a b c => exprLiterals a ++ exprLiterals b ++ exprLiterals c
  | .binary _ a b | .index a b | .extCodePrefix a b => exprLiterals a ++ exprLiterals b
  | .storage ref | .transient ref | .arrayLength _ ref => refLiterals ref
  | _ => []

partial def refLiterals (ref : StorageRef) : List Value :=
  ref.steps.flatMap fun
    | .mindex e | .aindex e => exprLiterals e
    | .field _ => []
end

/-- The literals a statement mentions. -/
partial def stmtLiterals : Stmt → List Value
  | .letDecl _ _ e | .setImmutable _ e | .require e => exprLiterals e
  | .letStorage _ ref | .pop ref | .delete ref => refLiterals ref
  | .assign _ ref e => refLiterals ref ++ exprLiterals e
  | .while c body => exprLiterals c ++ body.flatMap stmtLiterals
  | .for init c post body => exprLiterals c ++ (init ++ post ++ body).flatMap stmtLiterals
  | .ite c a b => exprLiterals c ++ (a ++ b).flatMap stmtLiterals
  | .new _ v args _ salt => exprLiterals v ++ args.flatMap exprLiterals ++ (salt.map exprLiterals).getD []
  | .internalCall _ args _ | .emit _ args => args.flatMap exprLiterals
  | .externalCall tgt _ v args _ _ => exprLiterals tgt ++ exprLiterals v ++ args.flatMap exprLiterals
  | .lowLevelCall tgt v cd _ _ _ => exprLiterals tgt ++ exprLiterals v ++ exprLiterals cd
  | .delegateCall tgt cd _ _ => exprLiterals tgt ++ exprLiterals cd
  | .checkedCall recv _ v args _ onOk _ onFail _ =>
      exprLiterals recv ++ exprLiterals v ++ args.flatMap exprLiterals ++ (onOk ++ onFail).flatMap stmtLiterals
  | .return es => es.flatMap exprLiterals
  | .push ref e? => refLiterals ref ++ (e?.map exprLiterals).getD []
  | .letGas _ | .break | .continue => []

/-- Every literal a contract mentions (the `bytes32` names of `file(what, …)`, magic numbers,
    selectors), including its constants' values. -/
def contractLiterals (c : ContractDecl) : List Value :=
  let bodies := c.ctor.body :: c.transitions.map (·.body) ++ c.functions.map (·.body) ++
    (c.receive.map (·.body)).toList ++ (c.fallback.map (·.body)).toList
  (bodies.flatMap (·.flatMap stmtLiterals) ++ c.constants.flatMap (exprLiterals ·.value)).eraseDups

/-! ## Values -/

def edgeNats (bits : Nat) : List Nat :=
  [0, 1, 2, 3, 2 ^ bits - 1, 2 ^ bits - 2, 2 ^ (bits - 1), 2 ^ (bits - 1) - 1, 2 ^ (bits / 2), 255, 256, 2 ^ 64,
   2 ^ 64 - 1, 2 ^ 128, 10 ^ 18].filter (· < 2 ^ bits) |>.eraseDups

/-- An unsigned integer of `bits` bits: flags and small counts, boundaries, small numbers, pool
    words (the amounts the case refers to), or uniform. -/
def genNat (pools : Pools) (bits : Nat) (r : Rng) : Nat × Rng :=
  let (bucket, r) := r.nat 0 9
  let words := pools.words.filter (· < 2 ^ bits)
  if bucket < 2 then r.pick [0, 1, 1, 2, 3] 0
  else if bucket < 4 then r.pick (edgeNats bits) 0
  else if bucket < 6 || (bucket < 8 && words.isEmpty) then r.nat 0 1000
  else if bucket < 8 then r.pick words 0
  else r.bigNat bits

/-- A signed integer of `bits` bits. -/
def genInt (pools : Pools) (bits : Nat) (r : Rng) : Int × Rng :=
  let (bucket, r) := r.nat 0 9
  let half := 2 ^ (bits - 1)
  if bucket < 3 then r.pick [(0 : Int), 1, -1, Int.ofNat half - 1, -(Int.ofNat half), 2, -2] 0
  else if bucket < 5 then
    let (n, r) := r.nat 0 1000
    let (neg, r) := r.chance 50
    (if neg then -(Int.ofNat n) else Int.ofNat n, r)
  else
    let (n, r) := genNat pools bits r
    (Int.ofNat n - Int.ofNat half, r)

def genAddress (pools : Pools) (r : Rng) : EVM.Address × Rng :=
  let (bucket, r) := r.nat 0 9
  if bucket < 7 then r.pick pools.addresses (EVM.address 0)
  else if bucket < 8 then (EVM.address 0, r)
  else
    let (n, r) := r.bigNat 160
    (EVM.address n, r)

mutual
/-- A value of an ABI type. -/
partial def genValue (pools : Pools) (ty : ABIType) (r : Rng) : Value × Rng :=
  match ty with
  | .elem .bool =>
      let (b, r) := r.chance 50
      (.bool b, r)
  | .elem .address =>
      let (a, r) := genAddress pools r
      (.address a, r)
  | .elem (.int (.uint bits)) =>
      let (n, r) := genNat pools bits.val r
      (.int (Int.ofNat n), r)
  | .elem (.int (.sint bits)) =>
      let (i, r) := genInt pools bits.val r
      (.int i, r)
  | .elem (.bytes n) =>
      let known := pools.fixedBytes.filter (·.1 == n) |>.map (·.2)
      let (usePool, r) := r.chance (if known.isEmpty then 0 else 50)
      if usePool then
        let (bs, r) := r.pick known []
        (.fixedBytes n bs, r)
      else
        let (bs, r) := r.bytes (n.val + 1)
        (.fixedBytes n bs.toList, r)
  | .elem _ => (.int 0, r)
  | .bytes | .string =>
      let (usePool, r) := r.chance (if pools.bytes.isEmpty then 0 else 30)
      if usePool then
        let (b, r) := r.pick pools.bytes .empty
        (.bytes b, r)
      else
        let (len, r) := r.pick [0, 1, 31, 32, 33, 64, 5, 100] 0
        let (bs, r) := r.bytes len
        (.bytes bs, r)
  | .array t n =>
      let (vs, r) := genValues pools (List.replicate n t) r
      (.array vs, r)
  | .dynamicArray t =>
      let (len, r) := r.pick [0, 1, 2, 3, 1, 0] 0
      let (vs, r) := genValues pools (List.replicate len t) r
      (.array vs, r)
  | .tuple ts =>
      let (vs, r) := genValues pools ts r
      (.tuple vs, r)

partial def genValues (pools : Pools) (tys : List ABIType) (r : Rng) : List Value × Rng :=
  match tys with
  | [] => ([], r)
  | t :: rest =>
      let (v, r) := genValue pools t r
      let (vs, r) := genValues pools rest r
      (v :: vs, r)
end

/-- A value of a storage type; `none` for mappings (written through keys instead).  Unsigned
    fields are often flags (`wards`, `live`, `voted`) or the amounts the case refers to. -/
partial def genStorageValue (pools : Pools) (structs : List StructDecl) (ty : StorageType) (r : Rng) :
    Option Value × Rng :=
  match ty with
  | .elem (.int (.uint bits)) =>
      let (bucket, r) := r.nat 0 19
      let words := pools.words.filter (· < 2 ^ bits.val)
      if bucket < 5 then (some (.int 1), r)
      else if bucket < 14 && !words.isEmpty then
        let (w, r) := r.pick words 0
        (some (.int w), r)
      else
        let (v, r) := genValue pools (.elem (.int (.uint bits))) r
        (some v, r)
  | .elem e => let (v, r) := genValue pools (.elem e) r; (some v, r)
  | .contract _ => let (a, r) := genAddress pools r; (some (.address a), r)
  | .mapping _ _ => (none, r)
  | .struct name fields => Id.run do
      let mut r := r
      let mut vs : List (Ident × Value) := []
      for (f, fty) in fields do
        let (v?, r') := genStorageValue pools structs fty r
        r := r'
        match v? with
        | some v => vs := vs ++ [(f, v)]
        | none => pure ()
      return (some (.struct name vs), r)
  | .tuple ts => Id.run do
      let mut r := r
      let mut vs : List Value := []
      for t in ts do
        let (v?, r') := genStorageValue pools structs t r
        r := r'
        vs := vs ++ [v?.getD (.int 0)]
      return (some (.tuple vs), r)
  | .array t n => Id.run do
      let mut r := r
      let mut vs : List Value := []
      for _ in [:n] do
        let (v?, r') := genStorageValue pools structs t r
        r := r'
        vs := vs ++ [v?.getD (.int 0)]
      return (some (.array vs), r)
  | .dynamicArray t => Id.run do
      -- long enough for the small indices the case refers to
      let (len, r0) := r.pick ([0, 1, 2, 3] ++ (pools.words.filter (· < 8)).map (· + 1)) 0
      let mut r := r0
      let mut vs : List Value := []
      for _ in [:len] do
        let (v?, r') := genStorageValue pools structs t r
        r := r'
        vs := vs ++ [v?.getD (.int 0)]
      return (some (.array vs), r)
  | .bytes | .string =>
      let (len, r) := r.pick [0, 1, 31, 32, 33, 70] 0
      let (bs, r) := r.bytes len
      (some (.bytes bs), r)

/-! ## Storage pre-states -/

/-- Candidate keys of a mapping over the case's actors: its addresses, its small words, the
    `bytesN` constants, both booleans. -/
def keyCandidates (pools : Pools) : ElemType → List Value
  | .address => pools.addresses.take 4 |>.map .address
  | .bool => [.bool true, .bool false]
  | .int (.uint _) => (pools.words.filter (· < 2 ^ 64)).take 3 |>.map fun w => .int w
  | .int (.sint _) => [.int 0, .int 1, .int (-1)]
  | .bytes n => (pools.fixedBytes.filter (·.1 == n)).take 3 |>.map fun (n, bs) => .fixedBytes n bs
  | _ => []

/-- The key tuples over the candidates (capped), each with the type they lead to. -/
partial def keyTuples (pools : Pools) (cap : Nat) :
    StorageType → List (List EvaledStorageRefStep × List Value × StorageType)
  | .mapping k v =>
      (keyCandidates pools k).flatMap (fun key =>
        match valueToKey? key with
        | some kv => (keyTuples pools cap v).map fun (steps, keys, ty) => (.mindex kv :: steps, key :: keys, ty)
        | none => []) |>.take cap
  | ty => [([], [], ty)]

/-- Storage pre-state: for every mapping, entries at the key tuples over the case's actors (each
    kept with probability `keep`%), then `randomWrites` random writes per variable, all through
    the specification's backends: persistent declarations through `storageBackend`, transient
    ones through `transientBackend` (a nonzero transient pre-state stands for earlier calls of
    the same transaction).  Writes a backend rejects are skipped.  Also returns the pools of the
    keys and values written. -/
partial def randomStorage (cfg : Config) (contract : ContractDecl) (pools : Pools) (evm : EVM.State)
    (r : Rng) (randomWrites : Nat := 2) (cap : Nat := 12) (keep : Nat := 85) :
    EVM.State × Pools × Rng := Id.run do
  let mut r := r
  let mut evm := evm
  let mut trail : List Value := []
  let keyPools := pools.dedup
  let decls := contract.storage.map ((·, cfg.storageBackend)) ++ contract.transient.map ((·, cfg.transientBackend))
  for (decl, backend) in decls do
    let mut targets : List (List EvaledStorageRefStep × List Value × StorageType) := []
    match decl.ty with
    | .mapping .. =>
        for tup in keyTuples keyPools cap decl.ty do
          let (kept, r') := r.chance keep
          r := r'
          if kept then targets := targets ++ [tup]
    | _ => pure ()
    for _ in [:randomWrites] do
      let (steps, keys, ty, r') := path pools decl.ty [] [] r
      r := r'
      targets := targets ++ [(steps, keys, ty)]
    for (steps, keys, ty) in targets do
      let (v?, r') := genStorageValue pools contract.structs ty r
      r := r'
      if let some v := v? then
        if let .ok evm' := backend.write { base := decl.name, steps := steps } ty v evm then
          evm := evm'
          trail := trail ++ keys ++ [v]
  let written := Pools.ofValues trail
  return (evm, { written with words := written.words ++ written.words.map (· / 2) }.dedup, r)
where
  /-- Walk through mappings with random keys until a non-mapping type is reached. -/
  path (pools : Pools) : StorageType → List EvaledStorageRefStep → List Value → Rng →
      List EvaledStorageRefStep × List Value × StorageType × Rng
    | .mapping k v, steps, keys, r =>
        let (key, r) := genValue pools (.elem k) r
        match valueToKey? key with
        | some kv => path pools v (steps ++ [.mindex kv]) (keys ++ [key]) r
        | none => (steps, keys, .mapping k v, r)
    | ty, steps, keys, r => (steps, keys, ty, r)

/-! ## Messages -/

/-- Whether the transition starts with the compiler's non-payable guard `require(msg.value == 0)`. -/
def isNonPayable (t : TransitionDecl) : Bool :=
  t.body.any fun
    | .require (.binary .eq (.env .callvalue) (.intLit 0))
    | .require (.binary .eq (.intLit 0) (.env .callvalue)) => true
    | _ => false

/-- The ETH sent with a call: none (almost always for a non-payable function); otherwise small,
    just above a pool word (to outbid), or up to one ether. -/
def genCallValue (payable : Bool) (pools : Pools) (r : Rng) : Nat × Rng :=
  let (zero, r) := r.chance (if payable then 40 else 90)
  let (bucket, r) := r.nat 0 2
  if zero then (0, r)
  else if bucket = 0 then r.nat 1 1000
  else if bucket = 1 then
    let (w, r) := r.pick (pools.words.filter (· < 10 ^ 20)) 0
    (w + 1, r)
  else r.nat 0 (10 ^ 18)

/-- Block timestamp and number: a word the pre-state holds (deadlines, `rho`), the genesis zero,
    small, or realistic. -/
def genBlock (written pools : Pools) (r : Rng) : Nat × Nat × Rng :=
  let (bucket, r) := r.nat 0 9
  let deadlines := (written.words ++ pools.words).filter (· < 2 ^ 64)
  let (ts, r) :=
    if bucket < 4 && !deadlines.isEmpty then r.pick deadlines 0
    else if bucket < 6 then (0, r)
    else if bucket < 8 then r.nat 0 10000
    else r.nat 1600000000 1800000000
  let (bn, r) := r.nat 0 20000000
  (ts, bn, r)

/-- Calldata for a transition: its selector and a random valid encoding of its parameters,
    returned together with the encoded values. -/
def genCalldata (pools : Pools) (t : TransitionDecl) (r : Rng) : Option (List Value × ByteArray) × Rng :=
  let types := (transitionSignature t).paramTypes
  let (values, r) := genValues pools types r
  let selector := (Ethereum.KEC (String.toByteArray (transitionSigStr t))).extract 0 4
  ((encodeCallWithSelector? selector types values).map (values, ·), r)

def replaceWord (input : ByteArray) (offset : Nat) (value : Nat) : ByteArray :=
  input.extract 0 offset ++ (UInt256.ofNat value).toByteArray ++ input.extract (offset + 32) input.size

/-- Mutate calldata the way a hostile caller would: truncate, dirty or inflate a word, append
    bytes, or corrupt the selector. -/
def mutate (cd : ByteArray) (r : Rng) : ByteArray × Rng :=
  let (bucket, r) := r.nat 0 5
  match bucket with
  | 0 =>
      let (cut, r) := r.nat 0 cd.size
      (cd.extract 0 cut, r)
  | 1 =>
      if cd.size < 36 then (cd, r) else
        let (word, r) := r.nat 0 ((cd.size - 4) / 32 - 1)
        -- dirty high bits and width boundaries; no small values, which would turn an address
        -- parameter into a precompile the EVM model cannot execute
        let (value, r) := r.pick [2 ^ 160, 2 ^ 160 + 1, 2 ^ 256 - 1, 2 ^ 255, 2 ^ 255 + 1, 2 ^ 64, 2 ^ 64 - 1, 2 ^ 32] 0
        (replaceWord cd (4 + 32 * word) value, r)
  | 2 =>
      let (extra, r) := r.pick [1, 31, 32, 64] 1
      let (bs, r) := r.bytes extra
      (cd ++ bs, r)
  | 3 =>
      if cd.size = 0 then (cd, r) else
        let (b, r) := r.nat 0 255
        (⟨cd.data.set! 0 (UInt8.ofNat b)⟩, r)
  | 4 => (cd.extract 0 (min 4 cd.size), r)
  | _ =>
      if cd.size < 36 then (cd, r) else
        let (word, r) := r.nat 0 ((cd.size - 4) / 32 - 1)
        let (value, r) := r.bigNat 256
        (replaceWord cd (4 + 32 * word) value, r)

end Solm.DiffTest
