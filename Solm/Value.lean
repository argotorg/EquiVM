import Std.Data.HashMap

import EVM.Types
import ABI.Types
import Solm.Syntax

namespace Solm

/- Runtime values for the first semantics pass. Mappings are finite maps here;
   open-world behavior and typed defaults can be refined later. -/
inductive Value where
  | int : Int -> Value
  | bool : Bool -> Value
  | address : EVM.Address -> Value
  | struct : Ident -> List (Ident × Value) -> Value
  | array : List Value -> Value /- arrays can be copied to memory, so we need array values -/
  | tuple : List Value -> Value
  /- Fixed-size `bytesN`, carrying the ABI type index and the bytes in Solidity order. -/
  | fixedBytes : Fin 32 -> List UInt8 -> Value
  /- dynamic `bytes` (arbitrary-length byte string), e.g. low-level `.call` calldata -/
  | bytes : ByteArray -> Value
  /- Internal-only local alias for Solidity `storage` variables. Not ABI-encodable or storable. -/
  | storageRef : EvaledStorageRef -> StorageType -> Value
  | unit : Value
  deriving Inhabited


/- Zoe: We need a way to represent references to mappings, arrays, and structs in storage -/

mutual
  private def Value.decEq : (a b : Value) -> Decidable (a = b)
    | .int x, .int y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .bool x, .bool y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .address x, .address y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .struct tag fields, .struct tag' fields' =>
        match (inferInstance : Decidable (tag = tag')), Value.decEqNamedList fields fields' with
        | isTrue htag, isTrue hfields => isTrue (by subst tag'; cases hfields; rfl)
        | isFalse htag, _ => isFalse (by intro h'; cases h'; exact htag rfl)
        | _, isFalse hfields => isFalse (by intro h'; cases h'; exact hfields rfl)
    | .array xs, .array ys =>
        match Value.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .tuple xs, .tuple ys =>
        match Value.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .fixedBytes n bs, .fixedBytes m bs' =>
        match (inferInstance : Decidable (n = m)), (inferInstance : Decidable (bs = bs')) with
        | isTrue hn, isTrue hbytes => isTrue (by cases hn; cases hbytes; rfl)
        | isFalse hn, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse hbytes => isFalse (by intro h; cases h; exact hbytes rfl)
    | .unit, .unit => isTrue rfl
    | .bytes x, .bytes y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .storageRef rx tx, .storageRef ry ty =>
        match (inferInstance : Decidable (rx = ry)), (inferInstance : Decidable (tx = ty)) with
        | isTrue hr, isTrue ht => isTrue (by cases hr; cases ht; rfl)
        | isFalse hr, _ => isFalse (by intro h; cases h; exact hr rfl)
        | _, isFalse ht => isFalse (by intro h; cases h; exact ht rfl)
    | .int _, .bool _ => isFalse (by intro h; cases h)
    | .int _, .address _ => isFalse (by intro h; cases h)
    | .int _, .struct _ _ => isFalse (by intro h; cases h)
    | .int _, .array _ => isFalse (by intro h; cases h)
    | .int _, .tuple _ => isFalse (by intro h; cases h)
    | .int _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .int _, .unit => isFalse (by intro h; cases h)
    | .bool _, .int _ => isFalse (by intro h; cases h)
    | .bool _, .address _ => isFalse (by intro h; cases h)
    | .bool _, .struct _ _ => isFalse (by intro h; cases h)
    | .bool _, .array _ => isFalse (by intro h; cases h)
    | .bool _, .tuple _ => isFalse (by intro h; cases h)
    | .bool _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .bool _, .unit => isFalse (by intro h; cases h)
    | .address _, .int _ => isFalse (by intro h; cases h)
    | .address _, .bool _ => isFalse (by intro h; cases h)
    | .address _, .struct _ _ => isFalse (by intro h; cases h)
    | .address _, .array _ => isFalse (by intro h; cases h)
    | .address _, .tuple _ => isFalse (by intro h; cases h)
    | .address _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .address _, .unit => isFalse (by intro h; cases h)
    | .struct _ _, .int _ => isFalse (by intro h; cases h)
    | .struct _ _, .bool _ => isFalse (by intro h; cases h)
    | .struct _ _, .address _ => isFalse (by intro h; cases h)
    | .struct _ _, .array _ => isFalse (by intro h; cases h)
    | .struct _ _, .tuple _ => isFalse (by intro h; cases h)
    | .struct _ _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .struct _ _, .unit => isFalse (by intro h; cases h)
    | .array _, .int _ => isFalse (by intro h; cases h)
    | .array _, .bool _ => isFalse (by intro h; cases h)
    | .array _, .address _ => isFalse (by intro h; cases h)
    | .array _, .struct _ _ => isFalse (by intro h; cases h)
    | .array _, .tuple _ => isFalse (by intro h; cases h)
    | .array _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .array _, .unit => isFalse (by intro h; cases h)
    | .tuple _, .int _ => isFalse (by intro h; cases h)
    | .tuple _, .bool _ => isFalse (by intro h; cases h)
    | .tuple _, .address _ => isFalse (by intro h; cases h)
    | .tuple _, .struct _ _ => isFalse (by intro h; cases h)
    | .tuple _, .array _ => isFalse (by intro h; cases h)
    | .tuple _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .tuple _, .unit => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .int _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .bool _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .address _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .struct _ _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .array _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .tuple _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .unit => isFalse (by intro h; cases h)
    | .unit, .int _ => isFalse (by intro h; cases h)
    | .unit, .bool _ => isFalse (by intro h; cases h)
    | .unit, .address _ => isFalse (by intro h; cases h)
    | .unit, .struct _ _ => isFalse (by intro h; cases h)
    | .unit, .array _ => isFalse (by intro h; cases h)
    | .unit, .tuple _ => isFalse (by intro h; cases h)
    | .unit, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .int _, .bytes _ => isFalse (by intro h; cases h)
    | .bool _, .bytes _ => isFalse (by intro h; cases h)
    | .address _, .bytes _ => isFalse (by intro h; cases h)
    | .struct _ _, .bytes _ => isFalse (by intro h; cases h)
    | .array _, .bytes _ => isFalse (by intro h; cases h)
    | .tuple _, .bytes _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .bytes _ => isFalse (by intro h; cases h)
    | .unit, .bytes _ => isFalse (by intro h; cases h)
    | .bytes _, .int _ => isFalse (by intro h; cases h)
    | .bytes _, .bool _ => isFalse (by intro h; cases h)
    | .bytes _, .address _ => isFalse (by intro h; cases h)
    | .bytes _, .struct _ _ => isFalse (by intro h; cases h)
    | .bytes _, .array _ => isFalse (by intro h; cases h)
    | .bytes _, .tuple _ => isFalse (by intro h; cases h)
    | .bytes _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .bytes _, .unit => isFalse (by intro h; cases h)
    | .storageRef _ _, .int _ => isFalse (by intro h; cases h)
    | .int _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .bool _ => isFalse (by intro h; cases h)
    | .bool _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .address _ => isFalse (by intro h; cases h)
    | .address _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .struct _ _ => isFalse (by intro h; cases h)
    | .struct _ _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .array _ => isFalse (by intro h; cases h)
    | .array _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .tuple _ => isFalse (by intro h; cases h)
    | .tuple _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .bytes _ => isFalse (by intro h; cases h)
    | .bytes _, .storageRef _ _ => isFalse (by intro h; cases h)
    | .storageRef _ _, .unit => isFalse (by intro h; cases h)
    | .unit, .storageRef _ _ => isFalse (by intro h; cases h)

  private def Value.decEqList : (as bs : List Value) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match Value.decEq a b, Value.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def Value.decEqNamedList :
      (as bs : List (Ident × Value)) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | (name, value) :: as, (name', value') :: bs =>
        match (inferInstance : Decidable (name = name')),
            Value.decEq value value', Value.decEqNamedList as bs with
        | isTrue hname, isTrue hvalue, isTrue hs =>
            isTrue (by subst name'; cases hvalue; cases hs; rfl)
        | isFalse hname, _, _ =>
            isFalse (by intro h; cases h; exact hname rfl)
        | _, isFalse hvalue, _ =>
            isFalse (by intro h; cases h; exact hvalue rfl)
        | _, _, isFalse hs =>
            isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def Value.decEqPairList :
      (as bs : List (Value × Value)) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | (key, value) :: as, (key', value') :: bs =>
        match Value.decEq key key', Value.decEq value value', Value.decEqPairList as bs with
        | isTrue hkey, isTrue hvalue, isTrue hs =>
            isTrue (by cases hkey; cases hvalue; cases hs; rfl)
        | isFalse hkey, _, _ =>
            isFalse (by intro h; cases h; exact hkey rfl)
        | _, isFalse hvalue, _ =>
            isFalse (by intro h; cases h; exact hvalue rfl)
        | _, _, isFalse hs =>
            isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Value :=
  Value.decEq

def valueToWord : Value -> Option EVM.Word
  | .int i => pure $ EVM.wordOfInt i
  | .unit => .none
  | .bool b => b.toUInt256
  | .address a => pure $ .ofNat $ a.toNat
  | .array _ => .none
  | .tuple _ => .none
  | .struct _ _ => .none
  | .bytes _ => .none
  | .fixedBytes n bs =>
      if bs.length = n.val + 1 then
        some (.ofNat (Ethereum.fromBytesBigEndian bs))
      else
        none
  | .storageRef _ _ => .none

def wordToElem (t : ABI.ElemType) (w : EVM.Word) : Value :=
  match t with
  | .int (.uint _) => .int (w.toNat)
  | .int (.sint bits) =>
      -- Sign-extend at the *declared* width, as solc's `SIGNEXTEND` on load.  The leading mask
      -- (`% 2^bits`) is load-bearing: under a nonzero `bitOffset` `storageLocLoad` shift-rights the
      -- slot word, so bits above the field can hold packed neighbours — the mask drops them.  For
      -- `bits = 256` this coincides with `EVM.signed` (see the `#guard` below).
      let m := w.toNat % EVM.twoPow bits.val
      .int (if m < EVM.twoPow (bits.val - 1) then (m : Int)
        else (m : Int) - (EVM.twoPow bits.val : Int))
  | .bool => if w.val == 0 then .bool false else .bool true
  | .address => .address (.ofNat $ w.toNat)
  | .bytes n => .fixedBytes n (w.toBytesBE.drop (32 - (n.val + 1)))
  -- TODO: implement
  | .function => panic! "TODO: wordToElem: implement function"
  | .fixed _ => panic! "TODO: wordToElem: implement fixed"

-- Packed signed loads sign-extend at the declared width; unsigned loads are unchanged; and at the
-- full width the signed arm still agrees with `EVM.signed` (here: `2^255 ↦ -2^255`).
#guard wordToElem (.int (.sint ⟨24, by decide⟩)) (EVM.Word.ofNat 0xFFFFFF) = .int (-1)
#guard wordToElem (.int (.sint ⟨24, by decide⟩)) (EVM.Word.ofNat 0x7FFFFF) = .int 8388607
#guard wordToElem (.int (.uint ⟨24, by decide⟩)) (EVM.Word.ofNat 0xFFFFFF) = .int 16777215
#guard wordToElem (.int (.sint ⟨256, by decide⟩)) (EVM.Word.ofNat (EVM.twoPow 255))
  = .int (EVM.signed (EVM.Word.ofNat (EVM.twoPow 255)))
#guard wordToElem (.int (.sint ⟨256, by decide⟩)) (EVM.Word.ofNat (EVM.twoPow 255))
  = .int (-(EVM.twoPow 255 : Int))

abbrev Store := Std.HashMap Ident Value
