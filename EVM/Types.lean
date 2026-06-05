import Ethereum.Semantics
import Ethereum.UInt256
import Ethereum.Wheels

namespace EVM

abbrev Word := Ethereum.UInt256
abbrev Byte := UInt8
abbrev Bytes := ByteArray
abbrev Address := Ethereum.AccountAddress
abbrev State := Ethereum.State

abbrev WordBytes := { b : List UInt8 // b.length = 32 }

def Word.ofNat : ℕ → Word := Ethereum.UInt256.ofNat 

def Word.toBytesLE (u : Word) : List UInt8 :=
  let b := Ethereum.toBytes' u.val
  b ++ List.replicate (32 - b.length) 0

def Word.toBytesBE (u : Word) : List UInt8 :=
  let b := Ethereum.toBytesBigEndian u.val
  List.replicate (32 - b.length) 0 ++ b

-- TODO: Define an analogue in evmlean and reuse proof
def Word.toBytesLEWithSizeProof (val : Word) : WordBytes :=
  let b := Ethereum.toBytes' val.val
  let pad := b ++ List.replicate (32 - b.length) 0
  ⟨pad,
    by
      simp [pad]
      have hb : b.length ≤ 32 := by
        have ha : (val.toNat : ℕ) < 2 ^ (8 * 32) := by
          simp [Ethereum.UInt256.size, Ethereum.UInt256.toNat]
        simpa [b, BE] using Ethereum.toBytes'_le (k := 32) ha
      have h32 : 32 < USize.size := by
        rcases System.Platform.numBits_eq with h | h <;> rw [USize.size, h] <;> norm_num
      have h32' : (OfNat.ofNat 32 : USize).toNat = 32 := by
        exact USize.toNat_ofNat_of_le_of_lt (n := 32) (i := 32) h32 le_rfl
      have hbsize : (OfNat.ofNat b.length : USize).toNat = b.length := by
        exact USize.toNat_ofNat_of_le_of_lt (n := 32) (i := b.length) h32 hb
      omega
    ⟩



-- these are not strictly EVM related; TODO MOVE
/-
  The following definitions mostly cover translation from
  Word/UInt256 to ℤ. Look for existing implementations in
  Lean stdlib at some point
-/

def twoPow (n : Nat) : Nat := 2 ^ n
def wordModulus : Nat := twoPow 256
def addressModulus : Nat := twoPow 160

abbrev UIntN (bits : Nat) := Fin (twoPow bits)
def uintN (bits n : Nat) : UIntN bits :=
  ⟨n % twoPow bits, Nat.mod_lt _ (by unfold twoPow; exact Nat.pow_pos (by decide : 0 < 2))⟩

def word (n : Nat) : Word := { val := uintN 256 n }
def address (n : Nat) : Address := uintN 160 n

def signBit : Nat := twoPow 255
def signed (w : Word) : Int :=
  let x := w.val
  if x < signBit then
    Int.ofNat x
  else
    Int.ofNat x - Int.ofNat wordModulus

def wordOfInt (i : Int) : Word :=
  if i < 0 then
    let r := i.natAbs % wordModulus
    if r = 0 then ⟨0⟩ else word (wordModulus - r)
  else
    word i.toNat

