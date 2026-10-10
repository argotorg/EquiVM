import Benchmarks.CompoundIII.Comet.CollateralStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: replace the upper uint128 while preserving the lower uint128.
def high128WriteWord (old data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land (UInt256.lnot ⟨2^128-1⟩) (UInt256.shiftLeft data ⟨128⟩))
    (UInt256.land ⟨2^128-1⟩ old)

theorem high128WriteWord_packed (old data : UInt256) :
    packedWriteWord old data 16 16 = high128WriteWord old data := by
  have hz : old.toNat / 256^(16+16) = 0 := Nat.div_eq_of_lt old.val.isLt
  let x : BitVec 256 := ⟨old.val⟩
  let y : BitVec 256 := ⟨data.val⟩
  unfold packedWriteWord
  rw [hz, Nat.mul_zero, Nat.add_zero]
  apply congrArg UInt256.mk
  change (BitVec.ofNat 256 (x.toNat % 256^16 + 256^16 * (y.toNat % 256^16))).toFin = _
  rw [BitVec.ofNat_add, BitVec.ofNat_mul, bitvecOfNatMod x _ (by decide),
    bitvecOfNatMod y _ (by decide)]
  have hb : x % BitVec.ofNat 256 (256^16) +
      BitVec.ofNat 256 (256^16) * (y % BitVec.ofNat 256 (256^16)) =
      ((~~~BitVec.ofNat 256 (2^128-1)) &&& (y <<< 128)) |||
        (BitVec.ofNat 256 (2^128-1) &&& x) := by bv_decide
  rw [hb]
  simp only [UInt256.land, UInt256.lnot,
    BitVec.toFin_and, BitVec.toFin_or, BitVec.toFin_not]
  rfl

theorem sourceState_high128Write {s0 I σ evm} (hs : SourceState s0 I σ evm)
    (slot data : UInt256) :
    SourceState s0 I
      (sstoreAccountMap I.codeOwner σ slot (high128WriteWord (solcSlotWordAt slot σ I) data))
      (storePackedWord evm slot data 16 16) := by
  have hw := hs.readModifyWrite slot (fun old ↦ packedWriteWord old data 16 16)
  change SourceState _ _ _ (storePackedWord evm slot data 16 16) at hw
  rw [high128WriteWord_packed] at hw
  exact hw

end Benchmarks.CompoundIII.Comet
