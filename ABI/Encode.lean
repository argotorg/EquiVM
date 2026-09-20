import EVM.Types
import ABI.Types
import ABI.Value

/-! ABI encoding of `ABIValue`s: the standard (padded) encoding and `abi.encodePacked`. -/

namespace ABI

def natBytes (n : Nat) : List UInt8 :=
  (EVM.Word.ofNat n).toBytesBE

def zeroBytes (n : Nat) : List UInt8 :=
  List.replicate n 0

def padRightToWord (bytes : List UInt8) : List UInt8 :=
  bytes ++ zeroBytes (paddedSize bytes.length - bytes.length)

def valueToByte? : ABIValue → Option UInt8
  | .int i =>
      if 0 ≤ i ∧ i < 256 then
        some (UInt8.ofNat i.toNat)
      else
        none
  | _ => none

def valuesToBytes? : List ABIValue → Option (List UInt8)
  | [] => some []
  | value :: values => do
      let byte <- valueToByte? value
      let bytes <- valuesToBytes? values
      some (byte :: bytes)

def encodeABIWord? (ty : ABIType) (value : ABIValue) : Option EVM.Word :=
  match ty, value with
  | .elem .bool, .bool b =>
      some b.toUInt256
  | .elem .address, .address a =>
      some (EVM.word a)
  | .elem (.int (.uint bits)), .int i =>
      if bits.val = 0 then
        none
      else if 0 ≤ i ∧ i < Int.ofNat (EVM.twoPow bits.val) then
        some (EVM.word i.toNat)
      else
        none
  | .elem (.int (.sint bits)), .int i =>
      if bits.val = 0 then
        none
      else
        let positiveLimit := Int.ofNat (EVM.twoPow (bits.val - 1))
        if -positiveLimit ≤ i ∧ i < positiveLimit then
          some (EVM.wordOfInt i)
        else
          none
  | _, _ => none



mutual
  def encodeABIValue? (ty : ABIType) (value : ABIValue) : Option (List UInt8) :=
    match ty with
    | .elem elemTy =>
        match elemTy, value with
        | .bytes n, .fixedBytes m bytes =>
            let size := n.val + 1
            if m = n ∧ bytes.length = size then
              some (bytes ++ zeroBytes (32 - size))
            else
              none
        | .function, .array values => do
            let bytes <- valuesToBytes? values
            if bytes.length = 24 then
              some (bytes ++ zeroBytes 8)
            else
              none
        | _, _ => do
            let word <- encodeABIWord? (.elem elemTy) value
            some (word.toBytesBE)
    | .array elemTy n =>
        match value with
        | .array values =>
            if values.length = n then
              encodeABIArrayElems? elemTy values
            else
              none
        | _ => none
    | .tuple elemTys =>
        match value with
        | .tuple values => encodeABIValues? elemTys values
        | _ => none
    | .bytes =>
        match value with
        | .bytes bytes =>
            some (natBytes bytes.size ++ padRightToWord bytes.toList)
        | _ => none
    | .string =>
        match value with
        | .bytes bytes =>
            some (natBytes bytes.size ++ padRightToWord bytes.toList)
        | _ => none
    | .dynamicArray elemTy =>
        match value with
        | .array values => do
            let encodedElems <- encodeABIArrayElems? elemTy values
            some (natBytes values.length ++ encodedElems)
        | _ => none
  termination_by (sizeOf ty, 0, 0)

  def encodeABIArrayElems? (ty : ABIType) (values : List ABIValue) : Option (List UInt8) :=
    if isDynamicABIType ty then
      encodeABIDynamicArrayElemsFrom? ty values (values.length * 32) [] []
    else
      encodeABIStaticArrayElems? ty values
  termination_by (sizeOf ty, values.length + 1, 5)

  def encodeABIStaticArrayElems? (ty : ABIType) (values : List ABIValue) : Option (List UInt8) :=
    match values with
    | [] => some []
    | value :: rest => do
        let encoded <- encodeABIValue? ty value
        let encodedRest <- encodeABIStaticArrayElems? ty rest
        some (encoded ++ encodedRest)
  termination_by (sizeOf ty, values.length + 1, 4)

  def encodeABIDynamicArrayElemsFrom? (ty : ABIType) (values : List ABIValue)
      (headSize : Nat) (head tail : List UInt8) : Option (List UInt8) :=
    match values with
    | [] => some (head ++ tail)
    | value :: rest => do
        let encoded <- encodeABIValue? ty value
        let offset := headSize + tail.length
        encodeABIDynamicArrayElemsFrom? ty rest headSize
          (head ++ natBytes offset) (tail ++ encoded)
  termination_by (sizeOf ty, values.length + 1, 3)

  def encodeABIValues? (types : List ABIType) (values : List ABIValue) : Option (List UInt8) := do
    let headSize <- abiTupleHeadSize? types
    encodeABIValuesFrom? types values headSize [] []
  termination_by (sizeOf types, values.length + 1, 2)

  def encodeABIValuesFrom? (types : List ABIType) (values : List ABIValue)
      (headSize : Nat) (head tail : List UInt8) : Option (List UInt8) :=
    match types, values with
    | [], [] => some (head ++ tail)
    | ty :: restTypes, value :: restValues => do
        let encoded <- encodeABIValue? ty value
        if isDynamicABIType ty then
          let offset := headSize + tail.length
          encodeABIValuesFrom? restTypes restValues headSize
            (head ++ natBytes offset) (tail ++ encoded)
        else
          encodeABIValuesFrom? restTypes restValues headSize
            (head ++ encoded) tail
    | _, _ => none
  termination_by (sizeOf types, values.length + 1, 1)
decreasing_by
  all_goals simp_wf
  all_goals omega
end

def encodeReturnValues? (types : List ABIType) (values : List ABIValue) : Option ByteArray := do
  let bytes <- encodeABIValues? types values
  some (ByteArray.mk bytes.toArray)

def encodeReturnValue? (ty : ABIType) (value : ABIValue) : Option ByteArray :=
  encodeReturnValues? [ty] [value]

/-- ABI-encode call arguments and prefix them with a 4-byte selector. -/
def encodeCallWithSelector? (sel : ByteArray) (tys : List ABIType)
    (args : List ABIValue) : Option EVM.Bytes := do
  let payload <- encodeABIValues? tys args
  some (sel ++ payload.toByteArray)

/-- `abi.encodePacked` of an array: each element is a full 32-byte padded word, no length prefix
    (verified from solc 0.8.35 Yul IR — `add(pos, 0x20)` per element).  Elementary elements only
    (`encodeABIWord?` returns `none` for nested/dynamic element types). -/
def encodePackedArrayElems? (elemTy : ABIType) : List ABIValue → Option (List UInt8)
  | [] => some []
  | v :: vs => do
      let w <- encodeABIWord? elemTy v
      let rest <- encodePackedArrayElems? elemTy vs
      some (EVM.Word.toBytesBE w ++ rest)

/-- Packed ("non-padded") ABI encoding of a single value, per Solidity's `abi.encodePacked`: each
    value takes its natural byte width with no left/right padding and no length prefix — `uintN`/`intN`
    are `N/8` big-endian bytes, `bool` is one byte, `address` is its 20 bytes, `bytesN` is its `N`
    bytes, and dynamic `bytes` is its raw contents.  Only the cases needed by current specs are
    handled; anything else returns `none` rather than risk a silent mis-encoding. -/
def encodePackedValue? (ty : ABIType) (v : ABIValue) : Option (List UInt8) :=
  match ty, v with
  | .elem .bool, .bool b => some [if b then (1 : UInt8) else 0]
  | .array elemTy _, .array vs => encodePackedArrayElems? elemTy vs
  | .dynamicArray elemTy, .array vs => encodePackedArrayElems? elemTy vs
  | .elem .address, .address a => some ((EVM.word a).toBytesBE.drop 12)
  | .elem (.int (.uint bits)), .int _ => do
      let w <- encodeABIWord? ty v
      some (w.toBytesBE.drop (32 - bits.val / 8))
  | .elem (.int (.sint bits)), .int _ => do
      let w <- encodeABIWord? ty v
      some (w.toBytesBE.drop (32 - bits.val / 8))
  | .elem (.bytes n), .fixedBytes m bytes =>
      if m = n ∧ bytes.length = n.val + 1 then some bytes else none
  | .bytes, .bytes ba => some ba.toList
  | .string, .bytes ba => some ba.toList
  | _, _ => none

#guard encodePackedValue? (.dynamicArray (.elem (.int (.uint ⟨8, by decide⟩)))) (.array [.int 1, .int 2])
  = some (List.replicate 31 0 ++ [1] ++ List.replicate 31 0 ++ [2])
