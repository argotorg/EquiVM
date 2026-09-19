import Solm.SolidityLayout

/-!
# WETH9 per-contract `bytes`/`string` storage read hook (solc 0.5.16 total header decode)

`Solm/SolidityLayout.lean`'s default compact-string decode (`solidityDecodeBytesLengthHeader`) is
0.8-style: it **reverts** when the slot header's short/long flag disagrees with the decoded length
magnitude (short flag with len ≥ 32, or long flag with len < 32).  solc **0.5.16**'s deployed getter
does no such validation — it trusts the header, deriving the length purely from the flag
(`len = (h & (flag=0 ? 0xff : ~0)) / 2`) and choosing the inline-vs-keccak data form solely by
`len < 32`.  Over the arbitrary-`σ` quantification of the refinement theorem, the extra Solm revert
is a spec falsity: for e.g. header `0x40` the Solm getter reverts while the runtime returns 32 bytes.

Per the layout-hook design (`StorageLayout` fields are per-contract config; `SolidityLayout` is a
convenience default), the fix is a WETH9-local `readValue?` that mirrors the Solidity one but with a
**total** header decode.  The write/clear hooks are inherited unchanged — the only string writes are
the constructor's, onto fresh (zero) storage, where the default decode already yields `.ok 0` without
reverting.  `.layout` is inherited too, so every scalar/mapping leaf is definitionally unchanged.
-/

open Solm Ethereum

namespace Benchmarks.WETH9

/-- solc 0.5.16 compact-string length decode: identical to `solidityDecodeBytesLengthHeader` but
    **total** (no revert on flag/length disagreement).  Length is `bits[1..7]` for the short flag
    (`(h/2) & 127 = (h & 0xff)/2`) and `h/2` for the long flag — matching the runtime's mask
    arithmetic at `runtime.hex` 0x352–0x367. -/
def weth9DecodeBytesLengthHeader (header : EVM.Word) : StorageReadResult Nat :=
  let flag := UInt256.land header ⟨1⟩
  let rawLen := UInt256.div header ⟨2⟩
  let lenWord := if flag = ⟨0⟩ then UInt256.land rawLen ⟨127⟩ else rawLen
  .ok lenWord.toNat

/-- Base data slot + decoded length for a `bytes`/`string` leaf, via the total decode. -/
def weth9BytesBaseSlotAndLength?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (evm : EVM.State) : StorageReadResult (EVM.Word × Nat) :=
  match layout { er with steps := er.steps ++ [.length] } evm with
  | some lenLoc =>
      match weth9DecodeBytesLengthHeader
          (EVM.storageLoad evm evm.executionEnv.codeOwner lenLoc.slot) with
      | .ok len => .ok (lenLoc.slot, len)
      | .revert => .revert
      | .error => .error
  | none => .error

/-- Read a `bytes`/`string` value: form chosen by `len < 32` (inline header bytes vs keccak data
    words), matching the runtime's form branch at `runtime.hex` 0x388.  Never reverts. -/
def weth9ReadBytesValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (evm : EVM.State) : StorageReadResult Value :=
  match weth9BytesBaseSlotAndLength? layout er evm with
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

/-- WETH9 `readValue?` hook: total compact-string read for `bytes`/`string`, `none` (fall through to
    `.layout`) for every scalar/structured leaf — so non-string reads are definitionally unchanged. -/
def weth9ReadValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) :
    Option (StorageReadResult Value) :=
  match ty with
  | .bytes | .string => some (weth9ReadBytesValue? layout er evm)
  | _ => none

/-- Write a `bytes`/`string` value the solc-**0.5.16** way.  The short-value store clears
    `ceil(oldLen/32)` keccak-data words **unconditionally** — solc 0.5.16 has no ≥0.8 "old value was
    packed, skip the clear" guard (creation-bytecode clear loop: `creation.hex` pc 254–273, count from
    the old length at pc 152–161).  The old length is read via the **total** decode.  Since
    `constructorEquivalence` quantifies over arbitrary σ (not fresh storage), an old short nonempty
    header with a nonzero `keccak(slot)` word is a legal input where the guarded (≥0.8) default would
    leave that word intact while the runtime zeroes it.  The long-value branch is unexercised by WETH9
    (both `name`/`symbol` are short) and mirrors the Solidity default. -/
def weth9WriteBytesValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (bytes : ByteArray) (evm : EVM.State) :
    StorageReadResult EVM.State :=
  match weth9BytesBaseSlotAndLength? layout er evm with
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

/-- WETH9 `writeValue?` hook: 0.5.16 string/bytes write for `bytes`/`string`, `none` for scalars
    (so non-string writes are definitionally unchanged). -/
def weth9WriteValue?
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc)
    (er : EvaledStorageRef) (ty : StorageType) (value : Value) (evm : EVM.State) :
    Option (StorageReadResult EVM.State) :=
  match ty, value with
  | .bytes, .bytes bytes => some (weth9WriteBytesValue? layout er bytes evm)
  | .string, .bytes bytes => some (weth9WriteBytesValue? layout er bytes evm)
  | _, _ => none

/-- WETH9 storage layout: the Solidity layout with the `bytes`/`string` **read** overridden to the
    total 0.5.16 decode and the `bytes`/`string` **write** overridden to the 0.5.16 unconditional-clear
    store.  `.layout`, `clearValue?`, `readBytesLength` are inherited verbatim; `clearValue?` is never
    invoked (WETH9 deletes no strings).  Scalar/mapping leaves are definitionally unchanged (both hooks
    return `none` for non-string types). -/
def weth9StorageLayout
    (layout : EvaledStorageRef -> EVM.State -> Option StorageLoc) : StorageLayout :=
  { solidityStorageLayout layout with
    readValue? := weth9ReadValue? layout
    writeValue? := weth9WriteValue? layout }

/-! ## Totality checks: total decode never reverts; the default Solidity decode does -/

-- Well-formed short: length byte 26 = 13·2 → len 13.
example : weth9DecodeBytesLengthHeader ⟨26⟩ = .ok 13 := by rfl
-- Malformed A: short flag (bit0=0) but len 32 ≥ 32 (header 0x40) — Solidity decode reverts; total is `.ok`.
example : weth9DecodeBytesLengthHeader ⟨64⟩ = .ok 32 := by rfl
example : solidityDecodeBytesLengthHeader ⟨64⟩ = .revert := by rfl
-- Malformed B: long flag (bit0=1) but len 13 < 32 (header 27) — Solidity decode reverts; total is `.ok`.
example : weth9DecodeBytesLengthHeader ⟨27⟩ = .ok 13 := by rfl
example : solidityDecodeBytesLengthHeader ⟨27⟩ = .revert := by rfl

end Benchmarks.WETH9
