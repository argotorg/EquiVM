import Ethereum.Semantics

/-!
# Trusted BLAKE2F model for bytecode experiments

The compression model in this file is copied from
`/home/lefteris/evm-semantics/EvmSemantics/Crypto/Blake2f.lean`.
The precompile wrapper mirrors `/home/lefteris/evm-semantics/EvmSemantics/EVM/Precompile.lean`
for `runBlake2f`.

These definitions are intentionally pure Lean and independent of Solm.  They are the target for
proving that the deployed replacement bytecode behaves like the `0x09` BLAKE2F precompile at the
caller-visible bytecode boundary.
-/

open Ethereum Ethereum.EVM

namespace Blake2f.Model

/-- BLAKE2b initialisation vector (`IV[0..7]`). Source:
`EvmSemantics/Crypto/Blake2f.lean`. -/
def IV : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b,
  0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f,
  0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

/-- BLAKE2b message-word permutation schedule. Source:
`EvmSemantics/Crypto/Blake2f.lean`. -/
def SIGMA : Array (Array Nat) := #[
  #[ 0,  1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12, 13, 14, 15],
  #[14, 10,  4,  8,  9, 15, 13,  6,  1, 12,  0,  2, 11,  7,  5,  3],
  #[11,  8, 12,  0,  5,  2, 15, 13, 10, 14,  3,  6,  7,  1,  9,  4],
  #[ 7,  9,  3,  1, 13, 12, 11, 14,  2,  6,  5, 10,  4,  0, 15,  8],
  #[ 9,  0,  5,  7,  2,  4, 10, 15, 14,  1, 11, 12,  6,  8,  3, 13],
  #[ 2, 12,  6, 10,  0, 11,  8,  3,  4, 13,  7,  5, 15, 14,  1,  9],
  #[12,  5,  1, 15, 14, 13,  4, 10,  0,  7,  6,  3,  9,  2,  8, 11],
  #[13, 11,  7, 14, 12,  1,  3,  9,  5,  0, 15,  4,  8,  6,  2, 10],
  #[ 6, 15, 14,  9, 11,  3,  0,  8, 12,  2, 13,  7,  1,  4, 10,  5],
  #[10,  2,  8,  4,  7,  6,  1,  5, 15, 11,  9, 14,  3, 12, 13,  0]]

/-- Right-rotate a 64-bit word by `n` bits. Source:
`EvmSemantics/Crypto/Blake2f.lean`. -/
@[inline] def rotr64 (x : UInt64) (n : UInt64) : UInt64 :=
  (x >>> n) ||| (x <<< (64 - n))

/-- BLAKE2b quarter-round `G`. Source: `EvmSemantics/Crypto/Blake2f.lean`. -/
def mixG (v : Array UInt64) (a b c d : Nat) (x y : UInt64) :
    Array UInt64 := Id.run do
  let mut v := v
  v := v.set! a (v[a]! + v[b]! + x)
  v := v.set! d (rotr64 (v[d]! ^^^ v[a]!) 32)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr64 (v[b]! ^^^ v[c]!) 24)
  v := v.set! a (v[a]! + v[b]! + y)
  v := v.set! d (rotr64 (v[d]! ^^^ v[a]!) 16)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotr64 (v[b]! ^^^ v[c]!) 63)
  return v

/-- BLAKE2b compression function `F`. Source: `EvmSemantics/Crypto/Blake2f.lean`. -/
def compress (rounds : Nat) (h m : Array UInt64) (t0 t1 : UInt64)
    (f : Bool) : Array UInt64 := Id.run do
  let mut v : Array UInt64 := Array.mkEmpty 16
  for i in [0:8] do v := v.push h[i]!
  for i in [0:8] do v := v.push IV[i]!
  v := v.set! 12 (v[12]! ^^^ t0)
  v := v.set! 13 (v[13]! ^^^ t1)
  if f then v := v.set! 14 (v[14]! ^^^ 0xffffffffffffffff)
  for r in [0:rounds] do
    let s := SIGMA[r % 10]!
    v := mixG v 0 4  8 12 m[s[0]!]!  m[s[1]!]!
    v := mixG v 1 5  9 13 m[s[2]!]!  m[s[3]!]!
    v := mixG v 2 6 10 14 m[s[4]!]!  m[s[5]!]!
    v := mixG v 3 7 11 15 m[s[6]!]!  m[s[7]!]!
    v := mixG v 0 5 10 15 m[s[8]!]!  m[s[9]!]!
    v := mixG v 1 6 11 12 m[s[10]!]! m[s[11]!]!
    v := mixG v 2 7  8 13 m[s[12]!]! m[s[13]!]!
    v := mixG v 3 4  9 14 m[s[14]!]! m[s[15]!]!
  let mut out : Array UInt64 := Array.mkEmpty 8
  for i in [0:8] do out := out.push (h[i]! ^^^ v[i]! ^^^ v[i + 8]!)
  return out

/-- Read 8 bytes from `bs` starting at `off` as little-endian `UInt64`. Source:
`EvmSemantics/Crypto/Blake2f.lean`. -/
def readLE64 (bs : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut w : UInt64 := 0
  for i in [0:8] do
    let b : UInt64 := if _ : off + i < bs.size then bs[off + i].toUInt64 else 0
    w := w ||| (b <<< UInt64.ofNat (8 * i))
  return w

/-- Append `w` as 8 little-endian bytes. Source:
`EvmSemantics/Crypto/Blake2f.lean`. -/
def writeLE64 (acc : ByteArray) (w : UInt64) : ByteArray := Id.run do
  let mut acc := acc
  for i in [0:8] do
    let shift : UInt64 := UInt64.ofNat (8 * i)
    acc := acc.push ((w >>> shift) &&& 0xff).toUInt8
  return acc

/-- Byte-level BLAKE2F output. Source: `EvmSemantics/Crypto/Blake2f.lean`. -/
def compressBytes (input : ByteArray) (rounds : Nat) : ByteArray := Id.run do
  let mut h : Array UInt64 := Array.mkEmpty 8
  for i in [0:8] do h := h.push (readLE64 input (4 + i * 8))
  let mut m : Array UInt64 := Array.mkEmpty 16
  for i in [0:16] do m := m.push (readLE64 input (68 + i * 8))
  let t0 := readLE64 input 196
  let t1 := readLE64 input 204
  let f := input[212]! == 1
  let out := compress rounds h m t0 t1 f
  let mut res : ByteArray := ByteArray.empty
  for i in [0:8] do res := writeLE64 res out[i]!
  return res

/-- Decode a big-endian byte array as a natural number. Source:
`EvmSemantics/Data/Bytes.lean`. -/
def bytesToBigEndianNat (bs : ByteArray) : Nat :=
  bs.toList.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Exact byte length of a valid EIP-152 BLAKE2F input. Source:
`EvmSemantics/EVM/Precompile.lean`. -/
@[inline] def inputLength : Nat := 213

/-- Parsed round count used both as model input and native precompile gas. Source behavior:
`runBlake2f` in `EvmSemantics/EVM/Precompile.lean`. -/
def rounds (input : ByteArray) : Nat :=
  bytesToBigEndianNat (input.extract 0 4)

/-- EIP-152 final-flag validity.  The native precompile accepts only `0` and `1`. -/
def validFinalFlag (input : ByteArray) : Prop :=
  input[212]! = 0 ∨ input[212]! = 1

/-- Valid BLAKE2F precompile input, excluding the forwarded-gas threshold. -/
def validInput (input : ByteArray) : Prop :=
  input.size = inputLength ∧ validFinalFlag input

/-- Pure output required on valid BLAKE2F inputs. -/
def output (input : ByteArray) : ByteArray :=
  compressBytes input (rounds input)

/-- Native BLAKE2F precompile gas.  The replacement bytecode will have a different bytecode gas
expression; this is still useful as the trusted semantic reference. -/
def nativeGasCost (input : ByteArray) : Nat :=
  rounds input

inductive Result where
  | success (output : ByteArray) (gasUsed : Nat)
  | outOfGas
  deriving Inhabited, DecidableEq

/-- Trusted native precompile wrapper, copied behavior from `runBlake2f`. -/
def run (input : ByteArray) (childGas : Nat) : Result :=
  if input.size ≠ inputLength then .outOfGas
  else
    let fFlag := input[212]!
    if fFlag != 0 && fFlag != 1 then .outOfGas
    else
      let cost := nativeGasCost input
      if cost ≤ childGas then .success (output input) cost
      else .outOfGas

theorem run_success_of_valid {input : ByteArray} {childGas : Nat}
    (hvalid : validInput input)
    (hgas : nativeGasCost input ≤ childGas) :
    run input childGas = .success (output input) (nativeGasCost input) := by
  unfold run validInput validFinalFlag at *
  rcases hvalid with ⟨hlen, hflag | hflag⟩
  · simp [hlen, hflag, nativeGasCost]
    simpa [nativeGasCost] using hgas
  · simp [hlen, hflag, nativeGasCost]
    simpa [nativeGasCost] using hgas

theorem run_outOfGas_of_invalid {input : ByteArray} {childGas : Nat}
    (hinvalid : ¬ validInput input) :
    run input childGas = .outOfGas := by
  unfold run validInput validFinalFlag at *
  by_cases hlen : input.size = inputLength
  · simp [hlen] at hinvalid ⊢
    have hflag : ¬ (input[212]! = 0 ∨ input[212]! = 1) := by
      intro h
      rcases h with h0 | h1
      · exact hinvalid.1 h0
      · exact hinvalid.2 h1
    by_cases h0 : input[212]! = 0
    · exact False.elim (hflag (Or.inl h0))
    · by_cases h1 : input[212]! = 1
      · exact False.elim (hflag (Or.inr h1))
      · simp [h0, h1]
  · simp [hlen]

end Blake2f.Model
