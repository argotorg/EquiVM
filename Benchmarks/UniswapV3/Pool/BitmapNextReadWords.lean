import Benchmarks.UniswapV3.Pool.BitmapNextModel
import Benchmarks.UniswapV3.Pool.BitmapPositionLaws

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def bitmapNextMemory (mem : ByteArray) (compressed : Int) (lte : Bool) : ByteArray :=
  twoWordHashMem (EVM.wordOfInt (bitmapWordPos (bitmapNextPosition compressed lte))) ⟨6⟩ mem

theorem bitmapNextHash (mem : ByteArray) (compressed : Int) (lte : Bool) :
    keccakWord ⟨0⟩ ⟨64⟩ (bitmapNextMemory mem compressed lte) =
      bitmapSlot (bitmapWordPos (bitmapNextPosition compressed lte)) :=
  twoWordHashMem_solcMappingSlot_any _ _ _

theorem bitmapNextLeftMaskWord (compressed : Int) :
    UInt256.lnot (UInt256.ofNat 0) +
        (UInt256.shiftLeft (UInt256.ofNat 1)
          (UInt256.land (bitmapPositionBitRaw compressed) (UInt256.ofNat 255)) +
        UInt256.shiftLeft (UInt256.ofNat 1)
          (UInt256.land (bitmapPositionBitRaw compressed) (UInt256.ofNat 255))) =
      bitmapNextMask compressed true := by
  rw [bitmapPositionShift, ← u256_add_assoc,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, lnot_zero_add]
  rfl

theorem bitmapNextRightMaskWord (compressed : Int) :
    UInt256.lnot (UInt256.sub
      (UInt256.shiftLeft (UInt256.ofNat 1)
        (UInt256.land (UInt256.ofNat 255)
          (bitmapPositionBitRaw (bitmapNextPosition compressed false)))) (UInt256.ofNat 1)) =
      bitmapNextMask compressed false := by
  rw [u256_land_comm, bitmapPositionShift]
  rfl

def bitmapNextFlag (masked : UInt256) : UInt256 := if masked = ⟨0⟩ then ⟨0⟩ else ⟨1⟩

theorem bitmapNextFlag_isZero (masked : UInt256) :
    UInt256.isZero (UInt256.isZero masked) = bitmapNextFlag masked := by
  by_cases hz : masked = ⟨0⟩
  · rw [bitmapNextFlag, if_pos hz, hz]; rfl
  · rw [bitmapNextFlag, if_neg hz, isZero_eq_zero_of_ne hz]; rfl

theorem bitmapNextFlag_eq (masked : UInt256) :
    UInt256.isZero (UInt256.eq (UInt256.ofNat 0) masked) = bitmapNextFlag masked := by
  by_cases hz : masked = ⟨0⟩
  · rw [bitmapNextFlag, if_pos hz, hz]; rfl
  · rw [bitmapNextFlag, if_neg hz]
    have he : UInt256.eq (UInt256.ofNat 0) masked = ⟨0⟩ := by
      exact uInt256_eq_zero_of_ne (fun he ↦ hz (uInt256_eq_one_eq he).symm)
    rw [he]; rfl

end Benchmarks.UniswapV3.Pool
