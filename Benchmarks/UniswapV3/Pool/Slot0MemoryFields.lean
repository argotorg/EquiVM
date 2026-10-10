import Benchmarks.UniswapV3.Pool.Slot0Memory
import Benchmarks.UniswapV3.Pool.FlashProtocolWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem Slot0Memory.load_price {mem : ByteArray} {p : UInt256} {σ : AccountMap} {I : ExecutionEnv}
    (hm : Slot0Memory mem p σ I) (hb : p.toNat + 224 < UInt256.size) :
    memLoad p mem = slot0FieldWord 0 20 σ I := by
  have h := WordArrayMemory.load hm 0 (by change 0 < 7; decide) hb
  have h0 : p + UInt256.ofNat 0 = p := u256_add_zero p
  simpa only [slot0StructWords, List.getElem_cons_zero, Nat.mul_zero, h0] using h

-- Preserve the original accessor name used by the position-update trace.
theorem Slot0Memory.load_sqrt {mem : ByteArray} {p : UInt256} {σ : AccountMap}
    {I : ExecutionEnv} (hm : Slot0Memory mem p σ I) (hb : p.toNat + 224 < UInt256.size) :
    memLoad p mem = slot0FieldWord 0 20 σ I := Slot0Memory.load_price hm hb

theorem Slot0Memory.load_cardinalityNext {mem : ByteArray} {p : UInt256} {σ : AccountMap}
    {I : ExecutionEnv} (hm : Slot0Memory mem p σ I) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 128) mem = slot0FieldWord 27 2 σ I := by
  have h := WordArrayMemory.load hm 4 (by change 4 < 7; decide) hb
  simpa only [slot0StructWords, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceMul] using h

theorem Slot0Memory.load_feeProtocol {mem : ByteArray} {p : UInt256} {σ : AccountMap}
    {I : ExecutionEnv} (hm : Slot0Memory mem p σ I) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 160) mem = slot0FieldWord 29 1 σ I := by
  have h := WordArrayMemory.load hm 5 (by change 5 < 7; decide) hb
  simpa only [slot0StructWords, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceMul] using h

theorem slot0Price_clean (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) (slot0FieldWord 0 20 σ I) =
      slot0FieldWord 0 20 σ I := by
  rw [u256_land_comm]
  exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide)
    (u256LandMaskToNatLtOfToNat (bits := 160) _ _ (by decide))

theorem slot0FeeProtocol_clean (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (UInt256.ofNat 255) (slot0FieldWord 29 1 σ I) =
      slot0FieldWord 29 1 σ I := by
  rw [u256_land_comm]
  exact u256LandMaskCleanOfToNat (bits := 8) _ _ (by decide)
    (u256LandMaskToNatLtOfToNat (bits := 8) _ _ (by decide))

theorem slot0FeeProtocol_mod16 (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.mod (slot0FieldWord 29 1 σ I) (UInt256.ofNat 16) =
      poolProtocolDivisor false σ I := by
  apply u256_inj
  rw [umod_toNat_of_ne_zero _ _ (by decide), poolProtocolDivisor_toNat]
  rfl

theorem slot0FeeProtocol_shr4 (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.shiftRight (slot0FieldWord 29 1 σ I) (UInt256.ofNat 4) =
      poolProtocolDivisor true σ I := by
  apply u256_inj
  rw [wordShiftRight_toNat _ _ (by decide), poolProtocolDivisor_toNat]
  rfl

end Benchmarks.UniswapV3.Pool
