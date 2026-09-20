import EVM.Types
import ABI.Types

/-!
# ABI values

The values the ABI encodes and decodes, shared by every spec language: each language converts its
own values to and from `ABIValue` at the ABI and storage boundaries.  `rawBool` is a decoder
artifact — solc leaves the elements of a calldata `bool[]` unvalidated until they are read, so the
decoder keeps the raw word.
-/

namespace ABI

inductive ABIValue where
  | int : Int → ABIValue
  | bool : Bool → ABIValue
  | address : EVM.Address → ABIValue
  /-- `bytesN`, carrying the type index `N - 1` and the `N` bytes in Solidity order. -/
  | fixedBytes : Fin 32 → List UInt8 → ABIValue
  /-- Dynamic `bytes` and `string`. -/
  | bytes : ByteArray → ABIValue
  | array : List ABIValue → ABIValue
  | tuple : List ABIValue → ABIValue
  /-- An unvalidated `bool` calldata word. -/
  | rawBool : Nat → ABIValue
  deriving Inhabited, Repr

mutual
  def ABIValue.decEq : (a b : ABIValue) → Decidable (a = b)
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
    | .fixedBytes n bs, .fixedBytes m bs' =>
        match (inferInstance : Decidable (n = m)), (inferInstance : Decidable (bs = bs')) with
        | isTrue hn, isTrue hb => isTrue (by cases hn; cases hb; rfl)
        | isFalse hn, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
    | .bytes x, .bytes y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .array xs, .array ys =>
        match ABIValue.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .tuple xs, .tuple ys =>
        match ABIValue.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .rawBool x, .rawBool y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .int _, .bool _ => isFalse (by intro h; cases h)
    | .int _, .address _ => isFalse (by intro h; cases h)
    | .int _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .int _, .bytes _ => isFalse (by intro h; cases h)
    | .int _, .array _ => isFalse (by intro h; cases h)
    | .int _, .tuple _ => isFalse (by intro h; cases h)
    | .int _, .rawBool _ => isFalse (by intro h; cases h)
    | .bool _, .int _ => isFalse (by intro h; cases h)
    | .bool _, .address _ => isFalse (by intro h; cases h)
    | .bool _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .bool _, .bytes _ => isFalse (by intro h; cases h)
    | .bool _, .array _ => isFalse (by intro h; cases h)
    | .bool _, .tuple _ => isFalse (by intro h; cases h)
    | .bool _, .rawBool _ => isFalse (by intro h; cases h)
    | .address _, .int _ => isFalse (by intro h; cases h)
    | .address _, .bool _ => isFalse (by intro h; cases h)
    | .address _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .address _, .bytes _ => isFalse (by intro h; cases h)
    | .address _, .array _ => isFalse (by intro h; cases h)
    | .address _, .tuple _ => isFalse (by intro h; cases h)
    | .address _, .rawBool _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .int _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .bool _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .address _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .bytes _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .array _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .tuple _ => isFalse (by intro h; cases h)
    | .fixedBytes _ _, .rawBool _ => isFalse (by intro h; cases h)
    | .bytes _, .int _ => isFalse (by intro h; cases h)
    | .bytes _, .bool _ => isFalse (by intro h; cases h)
    | .bytes _, .address _ => isFalse (by intro h; cases h)
    | .bytes _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .bytes _, .array _ => isFalse (by intro h; cases h)
    | .bytes _, .tuple _ => isFalse (by intro h; cases h)
    | .bytes _, .rawBool _ => isFalse (by intro h; cases h)
    | .array _, .int _ => isFalse (by intro h; cases h)
    | .array _, .bool _ => isFalse (by intro h; cases h)
    | .array _, .address _ => isFalse (by intro h; cases h)
    | .array _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .array _, .bytes _ => isFalse (by intro h; cases h)
    | .array _, .tuple _ => isFalse (by intro h; cases h)
    | .array _, .rawBool _ => isFalse (by intro h; cases h)
    | .tuple _, .int _ => isFalse (by intro h; cases h)
    | .tuple _, .bool _ => isFalse (by intro h; cases h)
    | .tuple _, .address _ => isFalse (by intro h; cases h)
    | .tuple _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .tuple _, .bytes _ => isFalse (by intro h; cases h)
    | .tuple _, .array _ => isFalse (by intro h; cases h)
    | .tuple _, .rawBool _ => isFalse (by intro h; cases h)
    | .rawBool _, .int _ => isFalse (by intro h; cases h)
    | .rawBool _, .bool _ => isFalse (by intro h; cases h)
    | .rawBool _, .address _ => isFalse (by intro h; cases h)
    | .rawBool _, .fixedBytes _ _ => isFalse (by intro h; cases h)
    | .rawBool _, .bytes _ => isFalse (by intro h; cases h)
    | .rawBool _, .array _ => isFalse (by intro h; cases h)
    | .rawBool _, .tuple _ => isFalse (by intro h; cases h)

  def ABIValue.decEqList : (as bs : List ABIValue) → Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match ABIValue.decEq a b, ABIValue.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq ABIValue := ABIValue.decEq

/-- The 32-byte word of a scalar value, as stored in a slot or used as a topic. -/
def valueToWord : ABIValue → Option EVM.Word
  | .int i => pure (EVM.wordOfInt i)
  | .bool b => b.toUInt256
  | .address a => pure (.ofNat a.toNat)
  | .fixedBytes n bs =>
      if bs.length = n.val + 1 then
        some (.ofNat (Ethereum.fromBytesBigEndian bs))
      else
        none
  | .bytes _ | .array _ | .tuple _ | .rawBool _ => none

/-- The scalar value of elementary type `t` held in the (already right-aligned) word `w`. -/
def wordToElem (t : ElemType) (w : EVM.Word) : ABIValue :=
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
  | .address => .address (.ofNat w.toNat)
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

/-- The zero value of an elementary ABI type (what a fell-through `return` yields). -/
def defaultValue? : ABIType → Option ABIValue
  | .elem .bool => some (.bool false)
  | .elem .address => some (.address (.ofNat 0))
  | .elem (.int _) => some (.int 0)
  | .elem (.bytes n) => some (.fixedBytes n (List.replicate (n.val + 1) 0))
  | _ => none

end ABI
