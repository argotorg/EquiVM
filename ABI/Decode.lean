import EVM.Types
import ABI.Types
import Act.Value

namespace ABI

def bytesToWord (bytes : List UInt8) : EVM.Word :=
  Ethereum.UInt256.ofNat <| Ethereum.fromByteArrayBigEndian <| ByteArray.mk bytes.toArray

def bytesToValues (bytes : List UInt8) : List Act.Value :=
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

def zeroPadding? (bytes : List UInt8) (offset size : Nat) : Option Unit := do
  let padding <- readBytes? bytes offset size
  if padding.all (· == 0) then some () else none

def decodeABIWord? (ty : ABIType) (word : EVM.Word) : Option Act.Value :=
  let n : Nat := word.val
  match ty with
  | .elem .bool =>
      if n = 0 then
        some (.bool false)
      else if n = 1 then
        some (.bool true)
      else
        none
  | .elem .address =>
      if n < EVM.addressModulus then
        some (.address (Ethereum.AccountAddress.ofNat n))
      else
        none
  | .elem (.int (.uint bits)) =>
      if bits.val = 0 then
        none
      else if n < EVM.twoPow bits.val then
        some (.int (Int.ofNat n))
      else
        none
  | .elem (.int (.sint bits)) =>
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
  def decodeABIValue? (ty : ABIType) (bytes : List UInt8) (start : Nat) :
      Option (Act.Value × Nat) :=
    match ty with
    | .elem _ => do
        match ty with
        | .elem (.bytes n) => do
            let wordBytes <- readBytes? bytes start 32
            let size := n.val + 1
            zeroPadding? wordBytes size (32 - size)
            some (.array (bytesToValues (wordBytes.take size)), start + 32)
        | .elem .function => do
            let wordBytes <- readBytes? bytes start 32
            zeroPadding? wordBytes 24 8
            some (.array (bytesToValues (wordBytes.take 24)), start + 32)
        | _ => do
            let word <- readWord? bytes start
            let value <- decodeABIWord? ty word
            some (value, start + 32)
    | .array elemTy n =>
        if isDynamicABIType elemTy then do
          let (values, endOffset) <- decodeABIArrayDynamicElems? elemTy n bytes start
          some (.array values, endOffset)
        else do
          let elemSize <- staticABIEncodedSize? elemTy
          let (values, endOffset) <- decodeABIArrayStaticElems? elemTy n elemSize bytes start
          some (.array values, endOffset)
    | .tuple elemTys => do
        let headSize <- abiTupleHeadSize? elemTys
        let (values, endOffset) <-
          decodeABIValues? elemTys bytes start 0 headSize (start + headSize)
        some (.array values, endOffset)
    | .bytes | .string => do
        let size <- readNat? bytes start
        let payloadStart := start + 32
        let payload <- readBytes? bytes payloadStart size
        let endOffset := payloadStart + paddedSize size
        zeroPadding? bytes (payloadStart + size) (paddedSize size - size)
        some (.array (bytesToValues payload), endOffset)
    | .dynamicArray elemTy => do
        let size <- readNat? bytes start
        let elemsStart := start + 32
        if isDynamicABIType elemTy then do
          let (values, endOffset) <- decodeABIArrayDynamicElems? elemTy size bytes elemsStart
          some (.array values, endOffset)
        else do
          let elemSize <- staticABIEncodedSize? elemTy
          let (values, endOffset) <- decodeABIArrayStaticElems? elemTy size elemSize bytes elemsStart
          some (.array values, endOffset)
  termination_by (sizeOf ty, 0, 0)

  def decodeABIArrayStaticElems? (ty : ABIType) (n elemSize : Nat)
      (bytes : List UInt8) (start : Nat) : Option (List Act.Value × Nat) :=
    match n with
    | 0 => some ([], start)
    | n + 1 => do
        let (value, endOffset) <- decodeABIValue? ty bytes start
        if endOffset = start + elemSize then
          let (values, restEnd) <- decodeABIArrayStaticElems? ty n elemSize bytes endOffset
          some (value :: values, restEnd)
        else
          none
  termination_by (sizeOf ty, n + 1, 1)

  def decodeABIArrayDynamicElems? (ty : ABIType) (n : Nat)
      (bytes : List UInt8) (base : Nat) : Option (List Act.Value × Nat) :=
    decodeABIArrayDynamicElemsFrom? ty n bytes base 0 (n * 32) (base + n * 32)
  termination_by (sizeOf ty, n + 1, 2)

  def decodeABIArrayDynamicElemsFrom? (ty : ABIType) (n : Nat)
      (bytes : List UInt8) (base headCursor headSize maxEnd : Nat) : Option (List Act.Value × Nat) :=
    match n with
    | 0 => some ([], maxEnd)
    | n + 1 => do
        let relativeOffset <- readNat? bytes (base + headCursor)
        if relativeOffset < headSize then
          none
        else
          let (value, valueEnd) <- decodeABIValue? ty bytes (base + relativeOffset)
          let (values, restEnd) <-
            decodeABIArrayDynamicElemsFrom? ty n bytes base (headCursor + 32) headSize
              (max maxEnd valueEnd)
          some (value :: values, restEnd)
  termination_by (sizeOf ty, n + 1, 1)

  def decodeABIValues? (types : List ABIType) (bytes : List UInt8)
      (base headCursor headSize maxEnd : Nat) : Option (List Act.Value × Nat) :=
    match types with
    | [] => some ([], maxEnd)
    | ty :: restTypes => do
        if isDynamicABIType ty then do
          let relativeOffset <- readNat? bytes (base + headCursor)
          if relativeOffset < headSize then
            none
          else
            let (value, valueEnd) <- decodeABIValue? ty bytes (base + relativeOffset)
            let (values, restEnd) <-
              decodeABIValues? restTypes bytes base (headCursor + 32) headSize
                (max maxEnd valueEnd)
            some (value :: values, restEnd)
        else do
          let tySize <- staticABIEncodedSize? ty
          let (value, valueEnd) <- decodeABIValue? ty bytes (base + headCursor)
          if valueEnd = base + headCursor + tySize then
            let (values, restEnd) <-
              decodeABIValues? restTypes bytes base (headCursor + tySize) headSize
                (max maxEnd valueEnd)
            some (value :: values, restEnd)
          else
            none
  termination_by (sizeOf types, 0, 0)

end

def decodeCalldata (names : List Act.Ident) (types : List ABIType) (calldata : ByteArray) : Option Act.Store :=
  if calldata.toList.length < 4 then
    none
  else
    let argsArray := calldata.toList.drop 4
    let decoded := decodeArgs names types argsArray ∅
    match decoded with
    | some (store, _) => some store
    | none => none
  where
    decodeArgs (names : List Act.Ident) (types : List ABIType) (bytes : List UInt8) (store : Act.Store) :
        Option (Act.Store × Nat) :=
      match types with
      | [] =>
          match names with
          | [] => some (store, 0)
          | _ => none
      | _ => do
          let headSize <- abiTupleHeadSize? types
          match decodeABIValues? types bytes 0 0 headSize headSize with
          | some (values, endOffset) => do
              let store <- insertValues names values store
              some (store, endOffset)
          | none => none

    insertValues (names : List Act.Ident) (values : List Act.Value) (store : Act.Store) : Option Act.Store :=
      match names, values with
      | [], [] => some store
      | name :: names, value :: values =>
          insertValues names values (store.insert name value)
      | _, _ => none
