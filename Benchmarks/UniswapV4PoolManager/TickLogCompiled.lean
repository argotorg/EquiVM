import Benchmarks.UniswapV4PoolManager.TickPriceWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: extracting the top bit directly into a lower bit position.
theorem wordTopBitShift (w : UInt256) {bit : Nat} (hb : bit ≤ 255) :
    UInt256.land (UInt256.ofNat (2^bit)) (UInt256.shiftRight w (UInt256.ofNat (255-bit))) =
      UInt256.shiftLeft (UInt256.shiftRight w (UInt256.ofNat 255)) (UInt256.ofNat bit) := by
  have hw : w.toNat < 2^256 := w.val.isLt
  have hpow : 2^bit < UInt256.size := by
    change 2^bit < 2^256
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  apply u256_inj
  rw [uland_toNat, UInt256.toNat_ofNat_of_lt hpow, wordShiftRightNat _ (by omega),
    wordShiftLeftNat _ (by omega), wordShiftRightNat _ (by decide), Nat.and_comm,
    Nat.and_two_pow, Nat.testBit_eq_decide_div_mod_eq, Nat.div_div_eq_div_mul,
    ← Nat.pow_add, Nat.sub_add_cancel hb]
  have hq : w.toNat / 2^255 < 2 := by omega
  by_cases hz : w.toNat / 2^255 = 0
  · simp only [hz, Nat.zero_mod, show ¬(0:Nat) = 1 by decide, decide_false,
      Bool.toNat_false, zero_mul]
  · have ho : w.toNat / 2^255 = 1 := by omega
    simp only [ho, show (1:Nat)%2 = 1 by decide, decide_true, Bool.toNat_true, one_mul,
      Nat.mod_eq_of_lt hpow]

theorem tickLogNext_compiled (r : UInt256) :
    UInt256.shiftRight (UInt256.shiftRight (UInt256.mul r r) (UInt256.ofNat 127))
      (UInt256.shiftRight (UInt256.mul r r) (UInt256.ofNat 255)) = tickLogNext r true := by
  rw [← tickLogFlag_compiled]
  rfl

theorem tickLogBit_compiled {bit : Nat} (hb : bit ≤ 255) (r : UInt256) :
    UInt256.land (UInt256.ofNat (2^bit))
      (UInt256.shiftRight (UInt256.mul r r) (UInt256.ofNat (255-bit))) =
    UInt256.shiftLeft (tickLogFlag r) (UInt256.ofNat bit) := by
  rw [wordTopBitShift _ hb, ← tickLogFlag_compiled]

-- LIBRARY CANDIDATE: modular subtraction implemented as addition of the negated word.
theorem wordAddNegSub (x y : UInt256) : x + UInt256.sub ⟨0⟩ y = UInt256.sub x y := by
  apply u256_inj
  change (x.val + ((0 : Fin UInt256.size)-y.val)).val = (x.val-y.val).val
  congr 1
  abel

theorem tickPriceLogStart_compiled (msb : UInt256) :
    UInt256.shiftLeft (UInt256.ofNat (2^256-128) + msb) (UInt256.ofNat 64) = tickPriceLogStart msb := by
  rw [u256_add_comm]
  change UInt256.shiftLeft (msb + UInt256.sub ⟨0⟩ (UInt256.ofNat 128)) (UInt256.ofNat 64) = _
  rw [wordAddNegSub]
  rfl

theorem tickPriceLowRaw_compiled (log2 : UInt256) :
    UInt256.sar (UInt256.ofNat 128)
      (tickPriceScaled log2 + UInt256.ofNat 115792089237316195423570985008687907853266581672683754907038987867812469392726) =
      tickPriceLowRaw log2 := by
  change UInt256.sar (UInt256.ofNat 128)
    (tickPriceScaled log2 + UInt256.sub ⟨0⟩ (UInt256.ofNat 3402992956809132418596140100660247210)) = _
  rw [wordAddNegSub]
  rfl

end Benchmarks.UniswapV4PoolManager
