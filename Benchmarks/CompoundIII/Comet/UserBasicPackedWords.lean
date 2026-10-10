import Benchmarks.CompoundIII.Comet.PackedWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def userBasicLowWord (old principal index accrued : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 232))
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 168)))
      (UInt256.shiftLeft accrued (UInt256.ofNat 168)))
    (UInt256.lor
      (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 168))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)))
        (UInt256.shiftLeft index (UInt256.ofNat 104)))
      (UInt256.lor (UInt256.land principal
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1)))
        (UInt256.land old (UInt256.lnot
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 232))
            (UInt256.ofNat 1))))))

def userBasicAssetsWord (old assets : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.shiftLeft ⟨65535⟩ ⟨232⟩) (UInt256.shiftLeft assets ⟨232⟩))
    (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨65535⟩ ⟨232⟩)) old)

def userBasicReservedWord (old reserved : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.lnot ⟨2^248-1⟩) (UInt256.shiftLeft reserved ⟨248⟩))
    (UInt256.land ⟨2^248-1⟩ old)

theorem userBasicLowWord_bits (old principal index accrued : BitVec 256) :
    let a := old % BitVec.ofNat 256 (256^0) +
      BitVec.ofNat 256 (256^0) * (principal % BitVec.ofNat 256 (256^13)) +
      BitVec.ofNat 256 (256^13) * (old / BitVec.ofNat 256 (256^13))
    let b := a % BitVec.ofNat 256 (256^13) +
      BitVec.ofNat 256 (256^13) * (index % BitVec.ofNat 256 (256^8)) +
      BitVec.ofNat 256 (256^21) * (a / BitVec.ofNat 256 (256^21))
    b % BitVec.ofNat 256 (256^21) +
      BitVec.ofNat 256 (256^21) * (accrued % BitVec.ofNat 256 (256^8)) +
      BitVec.ofNat 256 (256^29) * (b / BitVec.ofNat 256 (256^29)) =
    ((BitVec.ofNat 256 (2^232-2^168)) &&& (accrued <<< 168)) |||
      (((BitVec.ofNat 256 (2^168-2^104)) &&& (index <<< 104)) |||
        ((principal &&& BitVec.ofNat 256 (2^104-1)) |||
          (old &&& (~~~BitVec.ofNat 256 (2^232-1))))) := by
  dsimp only
  bv_decide

theorem userBasicLowWord_packed (old principal index accrued : UInt256) :
    packedWriteWord (packedWriteWord (packedWriteWord old principal 0 13) index 13 8)
      accrued 21 8 = userBasicLowWord old principal index accrued := by
  let x : BitVec 256 := ⟨old.val⟩
  let p : BitVec 256 := ⟨principal.val⟩
  let i : BitVec 256 := ⟨index.val⟩
  let a : BitVec 256 := ⟨accrued.val⟩
  rw [packedWriteWord_bitvec x p 0 13 (by decide) (by decide) (by decide),
    packedWriteWord_bitvec _ i 13 8 (by decide) (by decide) (by decide),
    packedWriteWord_bitvec _ a 21 8 (by decide) (by decide) (by decide),
    userBasicLowWord_bits]
  simp only [userBasicLowWord, UInt256.land, UInt256.lor, UInt256.lnot,
    BitVec.toFin_and, BitVec.toFin_or, BitVec.toFin_not]
  rfl

theorem userBasicAssetsWord_packed (old assets : UInt256) :
    packedWriteWord old assets 29 2 = userBasicAssetsWord old assets := by
  let x : BitVec 256 := ⟨old.val⟩
  let y : BitVec 256 := ⟨assets.val⟩
  rw [packedWriteWord_bitvec x y 29 2 (by decide) (by decide) (by decide)]
  have hb : x % BitVec.ofNat 256 (256^29) +
      BitVec.ofNat 256 (256^29) * (y % BitVec.ofNat 256 (256^2)) +
      BitVec.ofNat 256 (256^31) * (x / BitVec.ofNat 256 (256^31)) =
      ((BitVec.ofNat 256 65535 <<< 232) &&& (y <<< 232)) |||
        ((~~~(BitVec.ofNat 256 65535 <<< 232)) &&& x) := by bv_decide
  rw [hb]
  simp only [userBasicAssetsWord, UInt256.land, UInt256.lor, UInt256.lnot,
    BitVec.toFin_and, BitVec.toFin_or, BitVec.toFin_not]
  rfl

theorem userBasicReservedWord_packed (old reserved : UInt256) :
    packedWriteWord old reserved 31 1 = userBasicReservedWord old reserved := by
  have hz : old.toNat / 256^(31+1) = 0 := Nat.div_eq_of_lt old.val.isLt
  let x : BitVec 256 := ⟨old.val⟩
  let y : BitVec 256 := ⟨reserved.val⟩
  unfold packedWriteWord
  rw [hz, Nat.mul_zero, Nat.add_zero]
  apply congrArg UInt256.mk
  change (BitVec.ofNat 256 (x.toNat % 256^31 + 256^31 * (y.toNat % 256^1))).toFin = _
  rw [BitVec.ofNat_add, BitVec.ofNat_mul, bitvecOfNatMod x _ (by decide),
    bitvecOfNatMod y _ (by decide)]
  have hb : x % BitVec.ofNat 256 (256^31) +
      BitVec.ofNat 256 (256^31) * (y % BitVec.ofNat 256 (256^1)) =
      ((~~~BitVec.ofNat 256 (2^248-1)) &&& (y <<< 248)) |||
        (BitVec.ofNat 256 (2^248-1) &&& x) := by bv_decide
  rw [hb]
  simp only [UInt256.land, UInt256.lnot,
    BitVec.toFin_and, BitVec.toFin_or, BitVec.toFin_not]
  rfl

end Benchmarks.CompoundIII.Comet
