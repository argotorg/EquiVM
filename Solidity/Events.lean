import Solidity.Elab
import Solidity.Value
import ABI.Encode

/-!
# Event logs

`emit E(args)` appends `LogEntry { address := this, topics, data }`: `topics[0]` is the keccak of
the canonical signature unless the event is anonymous; indexed value types are their 32-byte ABI
words; indexed dynamic types are hashed (raw contents for `bytes`/`string`, in-place encoding for
arrays and structs); the non-indexed arguments are ABI-encoded as the data.
-/

namespace Solidity

open ABI

/-- The 32-byte word of an indexed value-type argument (`bytesN` left-aligned, ints two's complement). -/
def topicWordOf : ABIValue → Option EVM.Word
  | .fixedBytes n bs =>
    if bs.length = n.val + 1 then some (.ofNat (Ethereum.fromBytesBigEndian bs * 2 ^ (8 * (31 - n.val)))) else none
  | v => ABI.valueToWord v

def hashWord (b : ByteArray) : EVM.Word := Ethereum.uInt256OfByteArray (ffi.KEC b)

/-- Topic of an indexed argument of ABI type `ty`. -/
def topicOf (ty : ABIType) (v : ABIValue) : Option EVM.Word :=
  match ty, v with
  | .elem _, v => topicWordOf v
  | .bytes, .bytes b => some (hashWord b)
  | .string, .bytes b => some (hashWord b)
  | .dynamicArray e, .array vs => (encodeABIArrayElems? e vs).map fun bs => hashWord bs.toByteArray
  | .array e _, .array vs => (encodeABIArrayElems? e vs).map fun bs => hashWord bs.toByteArray
  | .tuple tys, .tuple vs => (encodeABIValues? tys vs).map fun bs => hashWord bs.toByteArray
  | _, _ => none

/-- The log entry for `emit ev(args)` (arguments already in the `ABIValue` domain). -/
def mkLogEntry (this : EVM.Address) (ev : EventInfo) (args : List ABIValue) :
    Option Ethereum.LogEntry := do
  let params := ev.decl.params
  if params.length ≠ args.length ∨ ev.sig.paramTypes.length ≠ args.length then none
  let triples := (params.zip ev.sig.paramTypes).zip args
  let indexed := triples.filter fun ((p, _), _) => p.indexed
  let plain := triples.filter fun ((p, _), _) => !p.indexed
  let idxTopics ← indexed.mapM fun ((_, ty), v) => topicOf ty v
  let sigTopic := if ev.decl.anonymous then [] else [hashWord ev.sigStr.toUTF8]
  let data ← encodeABIValues? (plain.map fun ((_, ty), _) => ty) (plain.map (·.2))
  pure { address := this, topics := (sigTopic ++ idxTopics).toArray, data := data.toByteArray }

end Solidity
