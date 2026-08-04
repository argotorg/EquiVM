import Examples.Precompiles.Ripemd160.ParserPart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Ripemd160

theorem modelBlockWord_lt (data : ByteArray) (block index : Nat) :
    Model.blockWord data block index < 2 ^ 32 := by
  let p := block * 64 + index * 4
  have h0 : Model.paddedByte data p < 2 ^ 32 :=
    lt_trans (Model.paddedByte_lt data p) (by norm_num)
  have hb1 : Model.paddedByte data (p + 1) < 2 ^ 8 := by
    simpa using Model.paddedByte_lt data (p + 1)
  have hb2 : Model.paddedByte data (p + 2) < 2 ^ 8 := by
    simpa using Model.paddedByte_lt data (p + 2)
  have hb3 : Model.paddedByte data (p + 3) < 2 ^ 8 := by
    simpa using Model.paddedByte_lt data (p + 3)
  have h1 := Nat.shiftLeft_lt hb1 (m := 8)
  have h2 := Nat.shiftLeft_lt hb2 (m := 16)
  have h3 := Nat.shiftLeft_lt hb3 (m := 24)
  have h1' : Model.paddedByte data (p + 1) <<< 8 < 2 ^ 32 := by
    exact lt_trans h1 (by norm_num)
  have h2' : Model.paddedByte data (p + 2) <<< 16 < 2 ^ 32 := by
    exact lt_trans h2 (by norm_num)
  have h3' : Model.paddedByte data (p + 3) <<< 24 < 2 ^ 32 := by
    simpa using h3
  unfold Model.blockWord
  dsimp only
  exact Nat.or_lt_two_pow
    (Nat.or_lt_two_pow h3' h2') (Nat.or_lt_two_pow h1' h0)

theorem u256ShiftLeftOfNat (x n : Nat) (hx : x < UInt256.size) (hn : n < 256) :
    UInt256.shiftLeft (UInt256.ofNat x) (UInt256.ofNat n) =
      UInt256.ofNat (x <<< n) := by
  apply u256_inj
  rw [ushl_ofNat_toNat _ n hn, ulit_toNat' x hx]
  rfl

theorem u256LorOfNat (x y : Nat) (hx : x < UInt256.size)
    (hy : y < UInt256.size) :
    UInt256.lor (UInt256.ofNat x) (UInt256.ofNat y) =
      UInt256.ofNat (x ||| y) := by
  apply u256_inj
  rw [u256_lor_toNat, ulit_toNat' x hx, ulit_toNat' y hy]
  rfl

theorem byte_lt_uint {b : Nat} (hb : b < 256) : b < UInt256.size :=
  lt_trans hb (by decide)

theorem byte_shift_lt_uint {b shift : Nat} (hb : b < 256) (hs : shift ≤ 24) :
    b <<< shift < UInt256.size := by
  have hb8 : b < 2 ^ 8 := by simpa using hb
  have hshift := Nat.shiftLeft_lt hb8 (m := shift)
  have hexp : 8 + shift < 256 := by omega
  rw [UInt256.size]
  exact lt_trans hshift
    (Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) hexp)

theorem nat_or_lt_uint {a b : Nat} (ha : a < UInt256.size)
    (hb : b < UInt256.size) : a ||| b < UInt256.size := by
  have ha' : a < 2 ^ 256 := by simpa [UInt256.size] using ha
  have hb' : b < 2 ^ 256 := by simpa [UInt256.size] using hb
  have hor : a ||| b < 2 ^ 256 := Nat.or_lt_two_pow ha' hb'
  simpa [UInt256.size] using hor

theorem shiftedByteOrOfNat {b low shift : Nat}
    (hb : b < 256) (hlow : low < UInt256.size) (hshift : shift ≤ 24) :
    UInt256.lor
        (UInt256.shiftLeft (UInt256.ofNat b) (UInt256.ofNat shift))
        (UInt256.ofNat low) =
      UInt256.ofNat (b <<< shift ||| low) := by
  calc
    UInt256.lor
        (UInt256.shiftLeft (UInt256.ofNat b) (UInt256.ofNat shift))
        (UInt256.ofNat low) =
        UInt256.lor (UInt256.ofNat (b <<< shift)) (UInt256.ofNat low) :=
      congrArg (fun x => UInt256.lor x (UInt256.ofNat low))
        (u256ShiftLeftOfNat b shift (byte_lt_uint hb) (by omega))
    _ = UInt256.ofNat (b <<< shift ||| low) :=
      u256LorOfNat _ _ (byte_shift_lt_uint hb hshift) hlow

theorem assembleWordOfBytes {b0 b1 b2 b3 : Nat}
    (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256) (hb3 : b3 < 256) :
    UInt256.lor
        (UInt256.lor
          (UInt256.shiftLeft (UInt256.ofNat b3) (UInt256.ofNat 24))
          (UInt256.shiftLeft (UInt256.ofNat b2) (UInt256.ofNat 16)))
        (UInt256.lor
          (UInt256.shiftLeft (UInt256.ofNat b1) (UInt256.ofNat 8))
          (UInt256.ofNat b0)) =
      UInt256.ofNat ((b3 <<< 24 ||| b2 <<< 16) |||
        (b1 <<< 8 ||| b0)) := by
  have hb0u := byte_lt_uint hb0
  have hb1u := byte_lt_uint hb1
  have hb2u := byte_lt_uint hb2
  have hb3u := byte_lt_uint hb3
  rw [u256ShiftLeftOfNat _ 24 hb3u (by decide),
    u256ShiftLeftOfNat _ 16 hb2u (by decide),
    u256ShiftLeftOfNat _ 8 hb1u (by decide)]
  have h1 := byte_shift_lt_uint hb1 (by decide : 8 ≤ 24)
  have h2 := byte_shift_lt_uint hb2 (by decide : 16 ≤ 24)
  have h3 := byte_shift_lt_uint hb3 (by decide : 24 ≤ 24)
  have horLeft := nat_or_lt_uint h3 h2
  have horRight := nat_or_lt_uint h1 hb0u
  rw [u256LorOfNat _ _ h3 h2, u256LorOfNat _ _ h1 hb0u]
  rw [u256LorOfNat _ _ horLeft horRight]

/-
theorem assembleNatBytes (b0 b1 b2 b3 : Nat) :
    (b3 <<< 24 ||| b2 <<< 16) ||| (b1 <<< 8 ||| b0) =
      b0 ||| b1 <<< 8 ||| b2 <<< 16 ||| b3 <<< 24 := by
  ac_rfl
-/


end Ripemd160
