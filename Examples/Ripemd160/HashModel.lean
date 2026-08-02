import Solm.Value
import Mathlib.Data.Nat.Bitwise

/-!
# Pure RIPEMD-160 model

This model is the common invariant for the Solm source loops and the optimized EVM memory/stack
loops. Values in the compression state are represented as naturals reduced modulo `2^32`.
-/

namespace Ripemd160

namespace Model

def modulus32 : Nat := 2 ^ 32
def mask32 : Nat := modulus32 - 1

def u32 (x : Nat) : Nat := x % modulus32

def not32 (x : Nat) : Nat := mask32 ^^^ x

def rol32 (x s : Nat) : Nat :=
  ((x <<< s) ||| (x >>> (32 - s))) &&& mask32

def paddedLength (n : Nat) : Nat := ((n + 72) / 64) * 64

def bitLength (n : Nat) : Nat := (n * 8) % (2 ^ 64)

def paddedByte (data : ByteArray) (p : Nat) : Nat :=
  let n := data.size
  let padded := paddedLength n
  if h : p < n then
    (data[p]'h).toNat
  else if p = n then
    128
  else if padded - 8 ≤ p then
    (bitLength n >>> ((p - (padded - 8)) * 8)) &&& 255
  else
    0

theorem paddedByte_lt (data : ByteArray) (p : Nat) : paddedByte data p < 256 := by
  unfold paddedByte
  dsimp only
  split
  · simpa using UInt8.toNat_lt _
  · split
    · omega
    · split
      · exact lt_of_le_of_lt Nat.and_le_right (by norm_num)
      · omega

def blockWord (data : ByteArray) (block index : Nat) : Nat :=
  let p := block * 64 + index * 4
  (paddedByte data (p + 3) <<< 24 ||| paddedByte data (p + 2) <<< 16) |||
    (paddedByte data (p + 1) <<< 8 ||| paddedByte data p)

def leftWordRow : Nat → Nat
  | 0 => 0x0123456789abcdef
  | 1 => 0x74d1a6f3c0952eb8
  | 2 => 0x3ae49f812706db5c
  | 3 => 0x19ba08c4d37fe562
  | _ => 0x40597c2ae138b6fd

def leftRotationRow : Nat → Nat
  | 0 => 0xbefc5879bdef6798
  | 1 => 0x768db97f7cf9b7dc
  | 2 => 0xbd67e9dfe8d65c75
  | 3 => 0xbcefef989e56865c
  | _ => 0x9f5b68dc5cdeb856

def leftConstant : Nat → Nat
  | 0 => 0x00000000
  | 1 => 0x5a827999
  | 2 => 0x6ed9eba1
  | 3 => 0x8f1bbcdc
  | _ => 0xa953fd4e

def rightWordRow : Nat → Nat
  | 0 => 0x5e7092b4d6f81a3c
  | 1 => 0x6b370d5aef8c4912
  | 2 => 0xf5137e69b8c2a04d
  | 3 => 0x86413bf05c2d97ae
  | _ => 0xcfa4158762de039b

def rightRotationRow : Nat → Nat
  | 0 => 0x899bdff5778beec6
  | 1 => 0x9df7c89b77c76fdb
  | 2 => 0x97fb866ecd5edd75
  | 3 => 0xf58bee6e69c9c5f8
  | _ => 0x85c9c5e68d65fdbb

def rightConstant : Nat → Nat
  | 0 => 0x50a28be6
  | 1 => 0x5c4dd124
  | 2 => 0x6d703ef3
  | 3 => 0x7a6d76e9
  | _ => 0x00000000

def rowEntry (row index : Nat) : Nat := (row >>> (60 - index * 4)) &&& 15

def leftF (group b c d : Nat) : Nat :=
  match group with
  | 0 => (b ^^^ c ^^^ d) &&& mask32
  | 1 => ((b &&& c) ||| (not32 b &&& d)) &&& mask32
  | 2 => ((b ||| not32 c) ^^^ d) &&& mask32
  | 3 => ((b &&& d) ||| (c &&& not32 d)) &&& mask32
  | _ => (b ^^^ (c ||| not32 d)) &&& mask32

def rightF (group b c d : Nat) : Nat :=
  match group with
  | 0 => (b ^^^ (c ||| not32 d)) &&& mask32
  | 1 => ((b &&& d) ||| (c &&& not32 d)) &&& mask32
  | 2 => ((b ||| not32 c) ^^^ d) &&& mask32
  | 3 => ((b &&& c) ||| (not32 b &&& d)) &&& mask32
  | _ => (b ^^^ c ^^^ d) &&& mask32

structure LineState where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
deriving DecidableEq, Repr

structure ChainState where
  h0 : Nat
  h1 : Nat
  h2 : Nat
  h3 : Nat
  h4 : Nat
deriving DecidableEq, Repr

def leftRound (data : ByteArray) (block group round : Nat) (s : LineState) : LineState :=
  let ri := rowEntry (leftWordRow group) round
  let si := rowEntry (leftRotationRow group) round
  let sum := u32 (s.a + leftF group s.b s.c s.d + blockWord data block ri +
    leftConstant group)
  let next := u32 (rol32 sum si + s.e)
  { a := s.e, b := next, c := s.b, d := rol32 s.c 10, e := s.d }

def rightRound (data : ByteArray) (block group round : Nat) (s : LineState) : LineState :=
  let ri := rowEntry (rightWordRow group) round
  let si := rowEntry (rightRotationRow group) round
  let sum := u32 (s.a + rightF group s.b s.c s.d + blockWord data block ri +
    rightConstant group)
  let next := u32 (rol32 sum si + s.e)
  { a := s.e, b := next, c := s.b, d := rol32 s.c 10, e := s.d }

def leftGroup (data : ByteArray) (block group : Nat) : Nat → LineState → LineState
  | 0, s => s
  | round + 1, s => leftRound data block group round (leftGroup data block group round s)

def leftLine (data : ByteArray) (block : Nat) : Nat → LineState → LineState
  | 0, s => s
  | group + 1, s => leftGroup data block group 16 (leftLine data block group s)

def rightGroup (data : ByteArray) (block group : Nat) : Nat → LineState → LineState
  | 0, s => s
  | round + 1, s => rightRound data block group round (rightGroup data block group round s)

def rightLine (data : ByteArray) (block : Nat) : Nat → LineState → LineState
  | 0, s => s
  | group + 1, s => rightGroup data block group 16 (rightLine data block group s)

def lineOfChain (h : ChainState) : LineState :=
  { a := h.h0, b := h.h1, c := h.h2, d := h.h3, e := h.h4 }

def runLeft (data : ByteArray) (block : Nat) (h : ChainState) : LineState :=
  leftLine data block 5 (lineOfChain h)

def runRight (data : ByteArray) (block : Nat) (h : ChainState) : LineState :=
  rightLine data block 5 (lineOfChain h)

def compress (data : ByteArray) (block : Nat) (h : ChainState) : ChainState :=
  let l := runLeft data block h
  let r := runRight data block h
  { h0 := u32 (h.h1 + l.c + r.d)
    h1 := u32 (h.h2 + l.d + r.e)
    h2 := u32 (h.h3 + l.e + r.a)
    h3 := u32 (h.h4 + l.a + r.b)
    h4 := u32 (h.h0 + l.b + r.c) }

def initial : ChainState :=
  { h0 := 0x67452301
    h1 := 0xefcdab89
    h2 := 0x98badcfe
    h3 := 0x10325476
    h4 := 0xc3d2e1f0 }

def finalState (data : ByteArray) : ChainState :=
  (List.range (paddedLength data.size / 64)).foldl
    (fun h block => compress data block h) initial

def wordLE (w : Nat) : List UInt8 :=
  [UInt8.ofNat w, UInt8.ofNat (w >>> 8), UInt8.ofNat (w >>> 16), UInt8.ofNat (w >>> 24)]

def digestBytes (data : ByteArray) : List UInt8 :=
  let h := finalState data
  wordLE h.h0 ++ wordLE h.h1 ++ wordLE h.h2 ++ wordLE h.h3 ++ wordLE h.h4

def digest (data : ByteArray) : ByteArray :=
  (digestBytes data).toByteArray

def rawOutput (data : ByteArray) : ByteArray :=
  ⟨#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ ++ digest data

theorem digest_size (data : ByteArray) : (digest data).size = 20 := by
  simp [digest, digestBytes, wordLE]

theorem digestBytes_length (data : ByteArray) : (digestBytes data).length = 20 := by
  simp [digestBytes, wordLE]

theorem rawOutput_size (data : ByteArray) : (rawOutput data).size = 32 := by
  rw [rawOutput, ByteArray.size_append, digest_size]
  rfl

theorem empty_digest :
    digest ByteArray.empty =
      ⟨#[0x9c, 0x11, 0x85, 0xa5, 0xc5, 0xe9, 0xfc, 0x54, 0x61, 0x28,
          0x08, 0x97, 0x7e, 0xe8, 0xf5, 0x48, 0xb2, 0x25, 0x8d, 0x31]⟩ := by
  native_decide

theorem abc_digest :
    digest "abc".toByteArray =
      ⟨#[0x8e, 0xb2, 0x08, 0xf7, 0xe0, 0x5d, 0x98, 0x7a, 0x9b, 0x04,
          0x4a, 0x8e, 0x98, 0xc6, 0xb0, 0x87, 0xf1, 0x5a, 0x0b, 0xfc]⟩ := by
  native_decide

end Model

end Ripemd160
