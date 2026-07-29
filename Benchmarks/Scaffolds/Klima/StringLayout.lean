import Solm.SolidityLayout

/-!
# KlimaToken per-contract `bytes`/`string` storage read/write hook (solc 0.7.5, pre-0.8 total decode)

`_name` (slot 3) and `_symbol` (slot 4) are ordinary mutable compact `string` storage values: written
by the creation bytecode and read by the deployed runtime getters (`name()` reads slot 3 at
`runtime.hex` pc 1588–1671 with pure `AND`/`DIV` mask arithmetic, `symbol()` reads slot 4).  Both are
short (`"Klima DAO"` = 9 bytes, `"KLIMA"` = 5 bytes).

`Solm/SolidityLayout.lean`'s default compact-string decode (`solidityDecodeBytesLengthHeader`) is
0.8-style: it **reverts** when the slot header's short/long flag disagrees with the decoded length
magnitude.  solc **pre-0.8** (0.7.5 here, as for the 0.5.16 WETH9 benchmark) does no such
validation — it trusts the header, deriving the length purely from the flag
(`len = (h & (flag=0 ? 0xff : ~0)) / 2`) and choosing the inline-vs-keccak data form solely by
`len < 32`.  Over the arbitrary-`σ` quantification of the refinement theorem, the extra Solm revert
is a spec falsity, so the fix is a Klima-local `readValue?` that mirrors the Solidity getter but with
a **total** header decode.  This is the same hook shape as `Benchmarks/WETH9/StringLayout.lean`; it is
duplicated here to keep the benchmark self-contained.
-/

open Solm Ethereum

namespace Benchmarks.Klima

/-- Pre-0.8 compact-string length decode: identical to `solidityDecodeBytesLengthHeader` but
    **total** (no revert on flag/length disagreement).  Length is `(h & 0xff)/2` for the short flag
    and `h/2` for the long flag. -/
def klimaDecodeBytesLengthHeader (header : EVM.Word) : StorageReadResult Nat :=
  let flag := UInt256.land header ⟨1⟩
  let rawLen := UInt256.div header ⟨2⟩
  let lenWord := if flag = ⟨0⟩ then UInt256.land rawLen ⟨127⟩ else rawLen
  .ok lenWord.toNat

/-- Base data slot + decoded length for a `bytes`/`string` leaf, via the total decode. -/
def klimaBytesBaseSlotAndLength?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (evm : EVM.State) : StorageReadResult (EVM.Word × Nat) :=
  match layout { er with steps := er.steps ++ [.length] } evm with
  | some lenLoc =>
      match klimaDecodeBytesLengthHeader
          (EVM.storageLoad evm evm.executionEnv.codeOwner lenLoc.slot) with
      | .ok len => .ok (lenLoc.slot, len)
      | .revert => .revert
      | .error => .error
  | none => .error

/-- Read a `bytes`/`string` value: form chosen by `len < 32` (inline header bytes vs keccak data
    words).  Never reverts. -/
def klimaReadBytesValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (evm : EVM.State) : StorageReadResult Value :=
  match klimaBytesBaseSlotAndLength? layout er evm with
  | .ok (baseSlot, len) =>
      if len < 32 then
        let header := EVM.storageLoad evm evm.executionEnv.codeOwner baseSlot
        .ok (.bytes (header.toByteArray.extract 0 len))
      else
        let bytes := readSolidityBytesDataWordsFrom evm baseSlot 0
          (solidityBytesDataWordCount len)
        .ok (.bytes (bytes.extract 0 len))
  | .revert => .revert
  | .error => .error

/-- Klima `readValue?` hook: total compact-string read for `bytes`/`string`, `none` (fall through to
    `.layout`) for every scalar/structured leaf — so non-string reads are definitionally unchanged. -/
def klimaReadValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) :
    Option (StorageReadResult Value) :=
  match ty with
  | .bytes | .string => some (klimaReadBytesValue? layout er evm)
  | _ => none

/-- Write a `bytes`/`string` value the pre-0.8 way.  The short-value store clears `ceil(oldLen/32)`
    keccak-data words **unconditionally** (no ≥0.8 "old value was packed, skip the clear" guard).  The
    old length is read via the **total** decode.  Since `constructorEquivalence` quantifies over
    arbitrary σ, an old short nonempty header with a nonzero `keccak(slot)` word is a legal input where
    the guarded (≥0.8) default would leave that word intact while the runtime zeroes it.  The
    long-value branch is unexercised by Klima (both `name`/`symbol` are short) and mirrors the Solidity
    default. -/
def klimaWriteBytesValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (bytes : ByteArray) (evm : EVM.State) :
    StorageReadResult EVM.State :=
  match klimaBytesBaseSlotAndLength? layout er evm with
  | .ok (baseSlot, oldLen) =>
      if bytes.size < 32 then
        let evmClean := clearSolidityBytesDataWordsFrom evm baseSlot 0
          (solidityBytesDataWordCount oldLen)
        .ok <|
          EVM.storageStore evmClean evmClean.executionEnv.codeOwner baseSlot
            (solidityShortBytesWord bytes)
      else
        let oldPacked := checkBytesPacked baseSlot evm
        let newWords := solidityBytesDataWordCount bytes.size
        let oldWords := solidityBytesDataWordCount oldLen
        let evmClean :=
          if oldPacked then evm
          else clearSolidityBytesDataWordsFrom evm baseSlot newWords (oldWords - newWords)
        let evmData := writeSolidityBytesDataWordsFrom evmClean baseSlot bytes 0 newWords
        .ok <|
          EVM.storageStore evmData evmData.executionEnv.codeOwner baseSlot
            (solidityBytesHeaderWord bytes.size)
  | .revert => .revert
  | .error => .error

/-- Klima `writeValue?` hook: pre-0.8 string/bytes write for `bytes`/`string`, `none` for scalars
    (so non-string writes are definitionally unchanged). -/
def klimaWriteValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (ty : StorageType) (value : Value) (evm : EVM.State) :
    Option (StorageReadResult EVM.State) :=
  match ty, value with
  | .bytes, .bytes bytes => some (klimaWriteBytesValue? layout er bytes evm)
  | .string, .bytes bytes => some (klimaWriteBytesValue? layout er bytes evm)
  | _, _ => none

/-- Klima storage layout: the Solidity layout with the `bytes`/`string` **read** overridden to the
    total pre-0.8 decode and the `bytes`/`string` **write** overridden to the pre-0.8
    unconditional-clear store.  `.layout`, `clearValue?`, `readBytesLength` are inherited verbatim;
    scalar/mapping leaves are definitionally unchanged (both hooks return `none` for non-string
    types). -/
def klimaStorageLayout
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc) : StorageLayout :=
  { solidityStorageLayout layout with
    readValue? := klimaReadValue? layout
    writeValue? := klimaWriteValue? layout }

end Benchmarks.Klima
