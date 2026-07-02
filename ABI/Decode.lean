import EVM.Types
import ABI.Types
import Solm.Value

namespace ABI

def solcMaxU64 : Nat := 18446744073709551615

def bytesToWord (bytes : List UInt8) : EVM.Word :=
  Ethereum.UInt256.ofNat <| Ethereum.fromByteArrayBigEndian <| ByteArray.mk bytes.toArray

def bytesToValues (bytes : List UInt8) : List Solm.Value :=
  bytes.map (λ b ↦ .int (Int.ofNat b.toNat))

def readBytes? (bytes : List UInt8) (offset size : Nat) : Option (List UInt8) :=
  let slice := (bytes.drop offset).take size
  if slice.length = size then some slice else none

def readWord? (bytes : List UInt8) (offset : Nat) : Option EVM.Word := do
  let wordBytes <- readBytes? bytes offset 32
  some (bytesToWord wordBytes)

def readNat? (bytes : List UInt8) (offset : Nat) : Option Nat := do
  let word <- readWord? bytes offset
  some word.val

def rawBoolWordValue (n : Nat) : Solm.Value :=
  .tuple [.unit, .int (Int.ofNat n)]

def decodeABIRawBoolArrayElems? (n : Nat) (bytes : List UInt8) (start : Nat) :
    Option (List Solm.Value × Nat) :=
  match n with
  | 0 => some ([], start)
  | n + 1 => do
      let word <- readNat? bytes start
      let (values, restEnd) <- decodeABIRawBoolArrayElems? n bytes (start + 32)
      some (rawBoolWordValue word :: values, restEnd)

def zeroPadding? (bytes : List UInt8) (offset size : Nat) : Option Unit := do
  let padding <- readBytes? bytes offset size
  if padding.all (· == 0) then some () else none

def decodeABIWord? (ty : ABIType) (word : EVM.Word) (mode : DecodeMode := DecodeMode.modern) :
    Option Solm.Value :=
  let n : Nat := word.val
  match ty with
  | .elem .bool =>
      match mode with
      | DecodeMode.modern =>
          if n = 0 then
            some (.bool false)
          else if n = 1 then
            some (.bool true)
          else
            none
      | DecodeMode.legacySolc05 =>
          if n = 0 then
            some (.bool false)
          else
            some (.bool true)
  | .elem .address =>
      match mode with
      | DecodeMode.modern =>
          if n < EVM.addressModulus then
            some (.address (Ethereum.AccountAddress.ofNat n))
          else
            none
      | DecodeMode.legacySolc05 =>
          some (.address (Ethereum.AccountAddress.ofNat n))
  | .elem (.int (.uint bits)) =>
      match mode with
      | DecodeMode.modern =>
          if bits.val = 0 then
            none
          else if n < EVM.twoPow bits.val then
            some (.int (Int.ofNat n))
          else
            none
      | DecodeMode.legacySolc05 =>
          -- solc's legacy ABI coder v1 cleans a narrow uintN by masking, not validating: e.g. the
          -- Dai (solc 0.6.12) permit wrapper reads its `uint8 v` param as `and(calldataload(…), 0xff)`
          -- with no revert.  `n % 2^256 = n` for uint256, so full-width decoding matches `modern`.
          some (.int (Int.ofNat (n % EVM.twoPow bits.val)))
  | .elem (.int (.sint bits)) =>
      -- Legacy `SIGNEXTEND` cleanup of narrow sintN is not modelled (no benchmark decodes a signed
      -- param); both modes validate here.
      if bits.val = 0 then
        none
      else
        let positiveLimit := EVM.twoPow (bits.val - 1)
        let negativeStart := EVM.wordModulus - positiveLimit
        if n < positiveLimit then
          some (.int (Int.ofNat n))
        else if negativeStart ≤ n then
          some (.int (Int.ofNat n - Int.ofNat EVM.wordModulus))
        else
          none
  | _ => none

mutual
  def decodeABIValue? (ty : ABIType) (bytes : List UInt8) (start : Nat)
      (mode : DecodeMode := DecodeMode.modern) :
      Option (Solm.Value × Nat) :=
    match ty with
    | .elem _ => do
        match ty with
        | .elem (.bytes n) => do
            let wordBytes <- readBytes? bytes start 32
            let size := n.val + 1
            zeroPadding? wordBytes size (32 - size)
            some (.fixedBytes n (wordBytes.take size), start + 32)
        | .elem .function => do
            let wordBytes <- readBytes? bytes start 32
            zeroPadding? wordBytes 24 8
            some (.array (bytesToValues (wordBytes.take 24)), start + 32)
        | _ => do
            let word <- readWord? bytes start
            let value <- decodeABIWord? ty word mode
            some (value, start + 32)
    | .array elemTy n =>
        if isDynamicABIType elemTy then do
          let (values, endOffset) <- decodeABIArrayDynamicElems? elemTy n bytes start mode
          some (.array values, endOffset)
        else do
          let elemSize <- staticABIEncodedSize? elemTy
          let (values, endOffset) <- decodeABIArrayStaticElems? elemTy n elemSize bytes start mode
          some (.array values, endOffset)
    | .tuple elemTys => do
        let headSize <- abiTupleHeadSize? elemTys
        let (values, endOffset) <-
          decodeABIValues? elemTys bytes start 0 headSize (start + headSize) mode
        some (.tuple values, endOffset)
    | .bytes => do
        let size <- readNat? bytes start
        if solcMaxU64 < size then
          none
        else
        let payloadStart := start + 32
        let payload <- readBytes? bytes payloadStart size
        let endOffset := payloadStart + paddedSize size
        some (.bytes (ByteArray.mk payload.toArray), endOffset)
    | .string => do
        let size <- readNat? bytes start
        if solcMaxU64 < size then
          none
        else
        let payloadStart := start + 32
        let payload <- readBytes? bytes payloadStart size
        let endOffset := payloadStart + paddedSize size
        zeroPadding? bytes (payloadStart + size) (paddedSize size - size)
        some (.bytes (ByteArray.mk payload.toArray), endOffset)
    | .dynamicArray elemTy => do
        let size <- readNat? bytes start
        if solcMaxU64 < size then
          none
        else
        let elemsStart := start + 32
        match elemTy with
        | .elem .bool => do
          let (values, endOffset) <- decodeABIRawBoolArrayElems? size bytes elemsStart
          some (.array values, endOffset)
        | elemTy' =>
        if isDynamicABIType elemTy' then do
          let (values, endOffset) <- decodeABIArrayDynamicElems? elemTy' size bytes elemsStart mode
          some (.array values, endOffset)
        else do
          let elemSize <- staticABIEncodedSize? elemTy'
          let (values, endOffset) <- decodeABIArrayStaticElems? elemTy' size elemSize bytes elemsStart mode
          some (.array values, endOffset)
  termination_by (sizeOf ty, 0, 0)

  def decodeABIArrayStaticElems? (ty : ABIType) (n elemSize : Nat)
      (bytes : List UInt8) (start : Nat) (mode : DecodeMode := DecodeMode.modern) :
      Option (List Solm.Value × Nat) :=
    match n with
    | 0 => some ([], start)
    | n + 1 => do
        let (value, endOffset) <- decodeABIValue? ty bytes start mode
        if endOffset = start + elemSize then
          let (values, restEnd) <- decodeABIArrayStaticElems? ty n elemSize bytes endOffset mode
          some (value :: values, restEnd)
        else
          none
  termination_by (sizeOf ty, n + 1, 1)

  def decodeABIArrayDynamicElems? (ty : ABIType) (n : Nat)
      (bytes : List UInt8) (base : Nat) (mode : DecodeMode := DecodeMode.modern) :
      Option (List Solm.Value × Nat) :=
    decodeABIArrayDynamicElemsFrom? ty n bytes base 0 (n * 32) (base + n * 32) mode
  termination_by (sizeOf ty, n + 1, 2)

  def decodeABIArrayDynamicElemsFrom? (ty : ABIType) (n : Nat)
      (bytes : List UInt8) (base headCursor headSize maxEnd : Nat)
      (mode : DecodeMode := DecodeMode.modern) : Option (List Solm.Value × Nat) :=
    match n with
    | 0 => some ([], maxEnd)
    | n + 1 => do
        let relativeOffset <- readNat? bytes (base + headCursor)
        if solcMaxU64 < relativeOffset then
          none
        else
          let (value, valueEnd) <- decodeABIValue? ty bytes (base + relativeOffset) mode
          let (values, restEnd) <-
            decodeABIArrayDynamicElemsFrom? ty n bytes base (headCursor + 32) headSize
              (max maxEnd valueEnd) mode
          some (value :: values, restEnd)
  termination_by (sizeOf ty, n + 1, 1)

  def decodeABIValues? (types : List ABIType) (bytes : List UInt8)
      (base headCursor headSize maxEnd : Nat) (mode : DecodeMode := DecodeMode.modern) :
      Option (List Solm.Value × Nat) :=
    match types with
    | [] => some ([], maxEnd)
    | ty :: restTypes => do
        if isDynamicABIType ty then do
          let relativeOffset <- readNat? bytes (base + headCursor)
          if solcMaxU64 < relativeOffset then
            none
          else
            let (value, valueEnd) <- decodeABIValue? ty bytes (base + relativeOffset) mode
            let (values, restEnd) <-
              decodeABIValues? restTypes bytes base (headCursor + 32) headSize
                (max maxEnd valueEnd) mode
            some (value :: values, restEnd)
        else do
          let tySize <- staticABIEncodedSize? ty
          let (value, valueEnd) <- decodeABIValue? ty bytes (base + headCursor) mode
          if valueEnd = base + headCursor + tySize then
            let (values, restEnd) <-
              decodeABIValues? restTypes bytes base (headCursor + tySize) headSize
                (max maxEnd valueEnd) mode
            some (value :: values, restEnd)
          else
            none
  termination_by (sizeOf types, 0, 0)

end

def solcTotalSizeDynamicGuard : List ABIType → Bool
  | [.string] => true
  | [.bytes] => true
  | _ => false

def decodeCalldata (names : List Solm.Ident) (types : List ABIType) (calldata : ByteArray)
    (mode : DecodeMode := DecodeMode.modern) : Option Solm.Store :=
  if calldata.toList.length < 4 then
    none
  else
    let argsArray := calldata.toList.drop 4
    -- Dynamic solc decoders use signed comparisons against the full `CALLDATASIZE`.
    -- If it is a negative signed word (`>= 2^255`), the generated decoder reverts before
    -- accepting any dynamic tail.
    if types.any isDynamicABIType = true ∧ 2 ^ 255 ≤ calldata.toList.length then
      none
    else
    -- Modern solc ABI decoders guard the argument region with a signed check,
    -- `SLT(calldatasize - 4, headSize)`, reverting when `calldatasize - 4` is a negative
    -- two's-complement word (i.e. `>= 2^255`). Legacy solc 0.5.x optimized wrappers use
    -- unsigned static length checks instead.
    match mode with
    | DecodeMode.modern =>
        if types.isEmpty = false ∧ 2 ^ 255 ≤ argsArray.length then
          none
        else if solcTotalSizeDynamicGuard types = true ∧ 2 ^ 255 ≤ calldata.toList.length then
          none
        else
          let decoded := decodeArgs names types argsArray ∅
          match decoded with
          | some (store, _) => some store
          | none => none
    | DecodeMode.legacySolc05 =>
        let decoded := decodeArgs names types argsArray ∅
        match decoded with
        | some (store, _) => some store
        | none => none
  where
    decodeArgs (names : List Solm.Ident) (types : List ABIType) (bytes : List UInt8) (store : Solm.Store) :
        Option (Solm.Store × Nat) :=
      match types with
      | [] =>
          match names with
          | [] => some (store, 0)
          | _ => none
      | _ => do
          let headSize <- abiTupleHeadSize? types
          if bytes.length < headSize then
            none
          else
            match decodeABIValues? types bytes 0 0 headSize headSize mode with
            | some (values, endOffset) => do
                let store <- insertValues names values store
                some (store, endOffset)
            | none => none

    insertValues (names : List Solm.Ident) (values : List Solm.Value) (store : Solm.Store) : Option Solm.Store :=
      match names, values with
      | [], [] => some store
      | name :: names, value :: values =>
          insertValues names values (store.insert name value)
      | _, _ => none

def decodeCalldataWithMode (mode : DecodeMode) (names : List Solm.Ident) (types : List ABIType)
    (calldata : ByteArray) :
    Option Solm.Store :=
  decodeCalldata names types calldata mode

def decodeReturnValues? (types : List ABIType) (returndata : ByteArray) :
    Option (List Solm.Value) :=
  let bytes := returndata.toList
  -- Modern solc's return decoder uses the same signed-size guard as calldata tuple decoders. A
  -- nonempty return tuple whose length word has the sign bit set follows the generated revert path.
  if types.isEmpty = false ∧ (2 : Nat) ^ 255 ≤ bytes.length then
    none
  else do
    let headSize <- abiTupleHeadSize? types
    let (values, _endOffset) <- decodeABIValues? types bytes 0 0 headSize headSize
    some values

def decodeReturnValuesWithMode? (mode : DecodeMode) (types : List ABIType) (returndata : ByteArray) :
    Option (List Solm.Value) :=
  match mode with
  | DecodeMode.modern => decodeReturnValues? types returndata
  | DecodeMode.legacySolc05 => do
      let bytes := returndata.toList
      let headSize <- abiTupleHeadSize? types
      let (values, _endOffset) <-
        decodeABIValues? types bytes 0 0 headSize headSize DecodeMode.legacySolc05
      some values

-- Decodes a single top-level value.  For a callee's multi-value return use `decodeReturnValues?` —
-- a `.tuple` type here is one tuple-typed output (ABI-wrapped, with a leading offset word), NOT a
-- flat multi-return.
def decodeReturnValue? (ty : ABIType) (returndata : ByteArray) : Option Solm.Value := do
  match decodeReturnValues? [ty] returndata with
  | some [value] => some value
  | _ => none

def decodeReturnValueWithMode? (mode : DecodeMode) (ty : ABIType) (returndata : ByteArray) :
    Option Solm.Value :=
  match mode with
  | DecodeMode.modern => decodeReturnValue? ty returndata
  | DecodeMode.legacySolc05 => do
      match ty with
      | .elem .bool =>
          if 2 ^ 255 ≤ returndata.size then
            none
          else
            match decodeReturnValuesWithMode? DecodeMode.legacySolc05 [ty] returndata with
            | some [value] => some value
            | _ => none
      | _ =>
          match decodeReturnValuesWithMode? DecodeMode.legacySolc05 [ty] returndata with
          | some [value] => some value
          | _ => none
