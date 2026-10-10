import Benchmarks.UniswapV3.Pool.BitScanBounds
import Benchmarks.UniswapV3.Pool.WordComplements

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def bitLsbMask (bits : Nat) : UInt256 := UInt256.ofNat (2 ^ bits - 1)

def bitLsbLow (x : UInt256) (bits : Nat) : UInt256 := UInt256.land x (bitLsbMask bits)

def bitLsbStep (state : Nat × UInt256) (bits : Nat) : Nat × UInt256 :=
  if 0 < (bitLsbLow state.2 bits).toNat then (state.1 - bits, state.2)
  else (state.1, UInt256.shiftRight state.2 (UInt256.ofNat bits))

theorem bitLsbStep_bounds (state : Nat × UInt256) (bits : Nat) :
    (bitLsbStep state bits).1 ≤ state.1 ∧ state.1 ≤ (bitLsbStep state bits).1 + bits := by
  unfold bitLsbStep
  split <;> constructor <;> omega

theorem bitLsbFold_bounds (state : Nat × UInt256) (bits : List Nat) :
    (bits.foldl bitLsbStep state).1 ≤ state.1 ∧
      state.1 ≤ (bits.foldl bitLsbStep state).1 + bits.sum := by
  induction bits generalizing state with
  | nil => simp only [List.foldl_nil, List.sum_nil, Nat.add_zero, le_refl, and_self]
  | cons b bs ih =>
    have hs := bitLsbStep_bounds state b
    have ht := ih (bitLsbStep state b)
    simp only [List.foldl_cons, List.sum_cons]
    constructor <;> omega

def bitLsbPrefix (x : UInt256) : Nat × UInt256 :=
  (tickLogMsbBits.take 7).foldl bitLsbStep (255, x)

def bitLsbCount (x : UInt256) : Nat := (bitLsbStep (bitLsbPrefix x) 1).1

theorem bitLsbPrefix_bounds (x : UInt256) :
    1 ≤ (bitLsbPrefix x).1 ∧ (bitLsbPrefix x).1 < 256 := by
  have h := bitLsbFold_bounds (255, x) (tickLogMsbBits.take 7)
  change (bitLsbPrefix x).1 ≤ 255 ∧ 255 ≤ (bitLsbPrefix x).1 + 254 at h
  omega

theorem bitLsbCount_lt (x : UInt256) : bitLsbCount x < 256 :=
  lt_of_le_of_lt (bitLsbStep_bounds (bitLsbPrefix x) 1).1 (bitLsbPrefix_bounds x).2

-- LIBRARY CANDIDATE: complement-addition implements bounded natural subtraction.
theorem wordLnot_add_nat {n bits : Nat} (hpos : 0 < bits) (hle : bits ≤ n)
    (hn : n < UInt256.size) :
    UInt256.lnot (UInt256.ofNat (bits - 1)) + UInt256.ofNat n = UInt256.ofNat (n - bits) := by
  rw [u256_add_comm, wordAdd_lnot_eq_sub_addOne]
  have hb : UInt256.ofNat (bits - 1) + (⟨1⟩ : UInt256) = UInt256.ofNat bits := by
    rw [u256_add_comm, u256_one_add_ofNat, Nat.sub_add_cancel hpos]
  rw [hb]
  apply u256_inj
  rw [usub_ofNat_lit_toNat hle hn,
    UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) hn)]

end Benchmarks.UniswapV3.Pool
