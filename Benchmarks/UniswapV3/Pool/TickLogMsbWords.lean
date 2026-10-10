import Benchmarks.UniswapV3.Pool.TickLogMsbSource
import Benchmarks.UniswapV3.Pool.WordShiftBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def tickLogMsbAmount (r : UInt256) (bits : Nat) : Nat :=
  if decide (2 ^ bits ≤ r.toNat) then bits else 0

def tickLogMsbScan (ratio : UInt256) : Nat → UInt256
  | 0 => ratio
  | i + 1 => UInt256.shiftRight (tickLogMsbScan ratio i)
      (UInt256.ofNat (tickLogMsbAmount (tickLogMsbScan ratio i) (2 ^ (7 - i))))

def tickLogMsbPart (ratio : UInt256) (i : Nat) : UInt256 :=
  UInt256.ofNat (tickLogMsbAmount (tickLogMsbScan ratio i) (2 ^ (7 - i)))

def tickLogMsbCount (ratio : UInt256) : Nat :=
  tickLogMsbAmount (tickLogMsbScan ratio 0) 128 +
    tickLogMsbAmount (tickLogMsbScan ratio 1) 64 +
    tickLogMsbAmount (tickLogMsbScan ratio 2) 32 +
    tickLogMsbAmount (tickLogMsbScan ratio 3) 16 +
    tickLogMsbAmount (tickLogMsbScan ratio 4) 8 +
    tickLogMsbAmount (tickLogMsbScan ratio 5) 4 +
    tickLogMsbAmount (tickLogMsbScan ratio 6) 2 +
    tickLogMsbAmount (tickLogMsbScan ratio 7) 1

def tickLogMsbPack (a b c d e f g h : UInt256) : UInt256 :=
  UInt256.lor (UInt256.lor
    (UInt256.lor f (UInt256.lor (UInt256.lor d (UInt256.lor c (UInt256.lor b a))) e)) g) h

private theorem tickLogMsbPack_flags : ∀ a b c d e f g h : Bool,
    tickLogMsbPack (UInt256.ofNat (if a then 128 else 0))
      (UInt256.ofNat (if b then 64 else 0)) (UInt256.ofNat (if c then 32 else 0))
      (UInt256.ofNat (if d then 16 else 0)) (UInt256.ofNat (if e then 8 else 0))
      (UInt256.ofNat (if f then 4 else 0)) (UInt256.ofNat (if g then 2 else 0))
      (UInt256.ofNat (if h then 1 else 0)) =
        UInt256.ofNat ((if a then 128 else 0) + (if b then 64 else 0) +
          (if c then 32 else 0) + (if d then 16 else 0) + (if e then 8 else 0) +
          (if f then 4 else 0) + (if g then 2 else 0) + (if h then 1 else 0)) ∧
      (if a then 128 else 0) + (if b then 64 else 0) + (if c then 32 else 0) +
        (if d then 16 else 0) + (if e then 8 else 0) + (if f then 4 else 0) +
        (if g then 2 else 0) + (if h then 1 else 0) < 256 := by native_decide

theorem tickLogMsbPack_eq (ratio : UInt256) :
    tickLogMsbPack (tickLogMsbPart ratio 0) (tickLogMsbPart ratio 1) (tickLogMsbPart ratio 2)
      (tickLogMsbPart ratio 3) (tickLogMsbPart ratio 4) (tickLogMsbPart ratio 5)
      (tickLogMsbPart ratio 6) (tickLogMsbPart ratio 7) = UInt256.ofNat (tickLogMsbCount ratio) ∧
      tickLogMsbCount ratio < 256 := by
  exact tickLogMsbPack_flags (decide (2 ^ 128 ≤ (tickLogMsbScan ratio 0).toNat))
    (decide (2 ^ 64 ≤ (tickLogMsbScan ratio 1).toNat))
    (decide (2 ^ 32 ≤ (tickLogMsbScan ratio 2).toNat))
    (decide (2 ^ 16 ≤ (tickLogMsbScan ratio 3).toNat))
    (decide (2 ^ 8 ≤ (tickLogMsbScan ratio 4).toNat))
    (decide (2 ^ 4 ≤ (tickLogMsbScan ratio 5).toNat))
    (decide (2 ^ 2 ≤ (tickLogMsbScan ratio 6).toNat))
    (decide (2 ^ 1 ≤ (tickLogMsbScan ratio 7).toNat))

theorem tickLogMsbStep_eq (state : Nat × UInt256) (bits : Nat) :
    tickLogMsbStep state bits =
      (state.1 + tickLogMsbAmount state.2 bits,
        UInt256.shiftRight state.2 (UInt256.ofNat (tickLogMsbAmount state.2 bits))) := by
  by_cases h : 2 ^ bits ≤ state.2.toNat
  · simp only [tickLogMsbStep, tickLogMsbAmount, h, decide_true, ↓reduceIte]
  · simp only [tickLogMsbStep, tickLogMsbAmount, h, decide_false, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero, show UInt256.ofNat 0 = ⟨0⟩ from rfl, wordShiftRight_zero]

theorem tickLogMsb_eq (price : UInt256) :
    tickLogMsb price = (tickLogMsbCount (tickLogRatio price),
      tickLogMsbScan (tickLogRatio price) 8) := by
  simp only [tickLogMsb, tickLogMsbBits, List.foldl_cons, List.foldl_nil, tickLogMsbStep_eq,
    Nat.zero_add]
  rfl

theorem tickLogMsb_lt (price : UInt256) : (tickLogMsb price).1 < 256 := by
  rw [tickLogMsb_eq]
  exact (tickLogMsbPack_eq (tickLogRatio price)).2

theorem tickLogMsbChoice_eq (r : UInt256) (p : Nat) (hp : p < 8) :
    UInt256.shiftLeft (UInt256.gt r (UInt256.ofNat (2 ^ (2 ^ p) - 1))) (UInt256.ofNat p) =
      UInt256.ofNat (tickLogMsbAmount r (2 ^ p)) := by
  have hpword : (UInt256.ofNat p).toNat = p :=
    UInt256.toNat_ofNat_of_lt (by change p < 2 ^ 256; omega)
  have hb : 2 ^ p < 256 := Nat.pow_lt_pow_right (by decide) hp
  have hfit : 2 ^ p < UInt256.size := lt_trans hb (by decide)
  have hmask : (UInt256.ofNat (2 ^ (2 ^ p) - 1)).toNat = 2 ^ (2 ^ p) - 1 := by
    apply UInt256.toNat_ofNat_of_lt
    exact lt_trans (Nat.sub_lt (by positivity) (by decide))
      (Nat.pow_lt_pow_right (by decide) hb)
  have hpos : 0 < 2 ^ (2 ^ p) := by positivity
  have hone : UInt256.shiftLeft ⟨1⟩ (UInt256.ofNat p) = UInt256.ofNat (2 ^ p) := by
    apply u256_inj
    rw [shiftLeft_toNat_of_noOverflow _ _ (by rw [hpword]; omega)
      (by change 1 * 2 ^ (UInt256.ofNat p).toNat < UInt256.size; simpa [hpword] using hfit)]
    rw [UInt256.toNat_ofNat_of_lt hfit, hpword]
    exact Nat.one_mul _
  have hzero : UInt256.shiftLeft ⟨0⟩ (UInt256.ofNat p) = ⟨0⟩ := by
    apply u256_inj
    rw [shiftLeft_toNat_of_noOverflow _ _ (by rw [hpword]; omega)
      (by change 0 * 2 ^ (UInt256.ofNat p).toNat < UInt256.size; simp [UInt256.size])]
    exact Nat.zero_mul _
  by_cases h : 2 ^ (2 ^ p) ≤ r.toNat
  · rw [ugt_one (by rw [hmask]; omega), hone]
    simp only [tickLogMsbAmount, h, decide_true, ↓reduceIte]
  · rw [ugt_zero (by rw [hmask]; omega), hzero]
    simp only [tickLogMsbAmount, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem tickLogMsbChoiceLast_eq (r : UInt256) :
    UInt256.gt r ⟨1⟩ = UInt256.ofNat (tickLogMsbAmount r 1) := by
  by_cases h : 2 ^ 1 ≤ r.toNat
  · rw [ugt_one (by change 1 < r.toNat; omega)]
    simp only [tickLogMsbAmount, h, decide_true, ↓reduceIte]
    rfl
  · rw [ugt_zero (by change r.toNat ≤ 1; omega)]
    simp only [tickLogMsbAmount, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl

def tickLogNormalized (ratio : UInt256) (msb : Nat) : UInt256 :=
  if 128 ≤ msb then UInt256.shiftRight ratio (UInt256.sub (UInt256.ofNat msb) ⟨127⟩)
  else UInt256.shiftLeft ratio (UInt256.sub ⟨127⟩ (UInt256.ofNat msb))

end Benchmarks.UniswapV3.Pool
