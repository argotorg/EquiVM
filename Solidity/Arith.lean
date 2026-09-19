import Solidity.Types

/-!
# Integer arithmetic and conversions (Solidity 0.8)

Checked arithmetic reverts with `Panic(0x11)`; `unchecked` blocks wrap; division and modulo by
zero always `Panic(0x12)`; shifts never check and take the left operand's type; `**` takes the
base's type.  Explicit conversions follow the 0.8 rules (one attribute at a time).
-/

namespace Solidity

open ABI

abbrev IntTy := ABI.IntType

namespace IntTy

def width : IntTy → Nat
  | .uint w => w.val
  | .sint w => w.val

def isSigned : IntTy → Bool
  | .uint _ => false
  | .sint _ => true

def min : IntTy → Int
  | .uint _ => 0
  | .sint w => -(2 ^ (w.val - 1) : Nat)

def max : IntTy → Int
  | .uint w => (2 ^ w.val : Nat) - 1
  | .sint w => (2 ^ (w.val - 1) : Nat) - 1

def inRange (t : IntTy) (i : Int) : Bool := t.min ≤ i && i ≤ t.max

/-- Two's-complement wrap into the type's range. -/
def wrap (t : IntTy) (i : Int) : Int :=
  let m : Int := 2 ^ t.width
  let r := i % m
  if t.isSigned && r ≥ 2 ^ (t.width - 1) then r - m else r

/-- The `width`-bit two's-complement word of `i`. -/
def toWord (t : IntTy) (i : Int) : Nat := (i % (2 ^ t.width : Nat)).toNat

def ofTy : Ty → Option IntTy
  | .uint w => some (.uint w)
  | .int w => some (.sint w)
  | _ => none

def toTy : IntTy → Ty
  | .uint w => .uint w
  | .sint w => .int w

end IntTy

def uint256Ty : IntTy := .uint ⟨256, by decide⟩

/-! ## Panics -/

inductive Panic where
  | generic | assertFail | overflow | divByZero | enumRange | storageBytes | popEmpty | outOfBounds
  | allocTooLarge | zeroInitFn
  deriving DecidableEq, Repr, Inhabited

def Panic.code : Panic → Nat
  | .generic => 0x00
  | .assertFail => 0x01
  | .overflow => 0x11
  | .divByZero => 0x12
  | .enumRange => 0x21
  | .storageBytes => 0x22
  | .popEmpty => 0x31
  | .outOfBounds => 0x32
  | .allocTooLarge => 0x41
  | .zeroInitFn => 0x51

/-! ## Arithmetic -/

/-- Range-check (checked mode) or wrap (unchecked) an exact result. -/
def settle (t : IntTy) (checked : Bool) (r : Int) : Except Panic Int :=
  if checked then (if t.inRange r then .ok r else .error .overflow) else .ok (t.wrap r)

def add (t : IntTy) (checked : Bool) (a b : Int) : Except Panic Int := settle t checked (a + b)
def sub (t : IntTy) (checked : Bool) (a b : Int) : Except Panic Int := settle t checked (a - b)
def mul (t : IntTy) (checked : Bool) (a b : Int) : Except Panic Int := settle t checked (a * b)

/-- Truncating division; `type(int).min / -1` overflows when checked and wraps otherwise. -/
def div (t : IntTy) (checked : Bool) (a b : Int) : Except Panic Int :=
  if b = 0 then .error .divByZero else settle t checked (Int.tdiv a b)

/-- Remainder with the sign of the dividend; never overflows. -/
def mod (_t : IntTy) (a b : Int) : Except Panic Int :=
  if b = 0 then .error .divByZero else .ok (Int.tmod a b)

def powModNat (base exp m : Nat) : Nat :=
  if exp = 0 then 1 % m
  else
    let h := powModNat (base * base % m) (exp / 2) m
    if exp % 2 = 1 then base * h % m else h
termination_by exp
decreasing_by omega

/-- `a ** b` in the base's type.  Exponents beyond the width can only fit for bases in
    `{-1, 0, 1}`; larger ones overflow (checked) or are computed modulo `2^width` (unchecked). -/
def exp (t : IntTy) (checked : Bool) (a : Int) (b : Nat) : Except Panic Int :=
  if a = 0 then .ok (if b = 0 then 1 else 0)
  else if a = 1 then .ok 1
  else if a = -1 then .ok (if b % 2 = 0 then 1 else -1)
  else if b ≥ t.width then
    if checked then .error .overflow
    else .ok (t.wrap (powModNat (t.toWord a) b (2 ^ t.width)))
  else settle t checked (a ^ b)

/-- Unary minus (signed types only). -/
def neg (t : IntTy) (checked : Bool) (a : Int) : Except Panic Int := settle t checked (-a)

/-- Shifts never check; the result has the left operand's type. -/
def shl (t : IntTy) (a : Int) (s : Nat) : Int :=
  if s ≥ t.width then 0 else t.wrap (a * 2 ^ s)

def shr (t : IntTy) (a : Int) (s : Nat) : Int :=
  if s ≥ t.width then (if a < 0 then -1 else 0) else a >>> s

def bitAnd (t : IntTy) (a b : Int) : Int := t.wrap (t.toWord a &&& t.toWord b)
def bitOr (t : IntTy) (a b : Int) : Int := t.wrap (t.toWord a ||| t.toWord b)
def bitXor (t : IntTy) (a b : Int) : Int := t.wrap (t.toWord a ^^^ t.toWord b)
def bitNot (t : IntTy) (a : Int) : Int := t.wrap ((2 ^ t.width - 1) - t.toWord a)

/-! ## Literals and implicit conversions -/

/-- Smallest integer type holding the literal (its "mobile type"). -/
def mobileType (i : Int) : Option IntTy :=
  let widths := (List.range 32).map fun k => 8 * (k + 1)
  widths.findSome? fun w =>
    match Ty.bitWidth? w with
    | none => none
    | some bw => if i ≥ 0 then (if i < 2 ^ w then some (.uint bw) else none)
      else (if -(2 ^ (w - 1) : Int) ≤ i then some (.sint bw) else none)

/-- Implicit integer conversion: widening within a sign, or unsigned to a strictly wider signed. -/
def implicitIntConv (src dst : IntTy) : Bool :=
  match src, dst with
  | .uint a, .uint b => a.val ≤ b.val
  | .sint a, .sint b => a.val ≤ b.val
  | .uint a, .sint b => a.val < b.val
  | .sint _, .uint _ => false

/-- The common type of two integer operands (each side implicitly convertible to it). -/
def commonIntType (a b : IntTy) : Option IntTy :=
  if implicitIntConv a b then some b else if implicitIntConv b a then some a else none

/-- Big-endian bytes of `n`, `len` bytes wide (truncating high bytes). -/
def natToBytesBE (n : Nat) (len : Nat) : List UInt8 :=
  (List.range len).reverse.map fun k => ((n / 256 ^ k) % 256).toUInt8

def bytesToNatBE (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => acc * 256 + b.toNat) 0

end Solidity
