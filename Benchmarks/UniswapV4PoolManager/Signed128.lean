import Benchmarks.UniswapV4PoolManager.SignedArithmetic

/-! Canonical int128 words and their sign extension. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: sign extension preserves a negative canonical int128 word.
theorem signextend128_of_high (w : UInt256) (hw : 2^256 - 2^127 ≤ w.toNat) :
    UInt256.signextend ⟨15⟩ w = w := by
  have hlt := w.val.isLt
  change w.toNat < 2^256 at hlt
  have hdiv : w.toNat / 2^127 = 2^129 - 1 := by omega
  change (if UInt256.land w ⟨2^127⟩ ≠ ⟨0⟩ then UInt256.lor w ⟨2^256 - 2^127⟩
    else UInt256.land w ⟨2^127 - 1⟩) = w
  have hn : UInt256.land w ⟨2^127⟩ ≠ ⟨0⟩ := by
    intro he
    have he' := congrArg UInt256.toNat he
    rw [uland_toNat] at he'
    change w.toNat &&& 2^127 = 0 at he'
    rw [Nat.and_two_pow, Nat.testBit_eq_decide_div_mod_eq, hdiv] at he'
    norm_num at he'
  rw [if_pos hn]
  have hm : w.toNat &&& (2^256 - 2^127) = 2^256 - 2^127 := by
    have he := natLandClearLow w.toNat 127 (by decide) hlt
    change w.toNat &&& (2^256 - 2^127) = (w.toNat / 2^127) * 2^127 at he
    rw [he, hdiv]
    decide
  have ho : w.toNat ||| (2^256 - 2^127) = w.toNat := by
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := congrArg (fun n : Nat => n.testBit i) hm
    dsimp only at hi
    rw [Nat.testBit_and] at hi
    rw [Nat.testBit_or]
    cases h0 : w.toNat.testBit i <;> cases h1 : (2^256 - 2^127).testBit i <;>
      simp_all
  apply u256_inj
  change (w.toNat ||| (2^256 - 2^127)) % 2^256 = w.toNat
  rw [ho, Nat.mod_eq_of_lt hlt]

-- LIBRARY CANDIDATE: encoding an int128 and extending its sign is idempotent.
theorem signextend128_wordOfInt {i : Int} (hlo : -(2^127 : Int) ≤ i) (hhi : i < 2^127) :
    UInt256.signextend ⟨15⟩ (EVM.wordOfInt i) = EVM.wordOfInt i := by
  by_cases hn : 0 ≤ i
  · apply signextend128_of_lt
    rw [wordOfInt_eq_mod]
    change (i % (2^256 : Int)).toNat % 2^256 < 2^127
    omega
  · apply signextend128_of_high
    rw [wordOfInt_eq_mod]
    change 2^256 - 2^127 ≤ (i % (2^256 : Int)).toNat % 2^256
    omega

end Benchmarks.UniswapV4PoolManager
