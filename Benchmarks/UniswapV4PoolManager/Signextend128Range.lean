import Benchmarks.UniswapV4PoolManager.Signed128Range

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: every sign-extended int128 word is in one of its two unsigned intervals.
theorem signextend128_range (w : UInt256) :
    (UInt256.signextend ⟨15⟩ w).toNat < 2^127 ∨
      2^256-2^127 ≤ (UInt256.signextend ⟨15⟩ w).toNat := by
  change (if UInt256.land w ⟨2^127⟩ ≠ ⟨0⟩ then UInt256.lor w ⟨2^256-2^127⟩
    else UInt256.land w ⟨2^127-1⟩).toNat < 2^127 ∨
      2^256-2^127 ≤ (if UInt256.land w ⟨2^127⟩ ≠ ⟨0⟩ then UInt256.lor w ⟨2^256-2^127⟩
        else UInt256.land w ⟨2^127-1⟩).toNat
  split
  · right
    rw [u256_lor_toNat_exact]
    exact Nat.right_le_or
  · left
    rw [uland_toNat]
    have hh : w.toNat &&& (2^127-1) ≤ 2^127-1 := Nat.and_le_right
    change w.toNat &&& (2^127-1) < 2^127
    omega

theorem signed128Fits_of_word_range {w : UInt256}
    (hr : w.toNat < 2^127 ∨ 2^256-2^127 ≤ w.toNat) :
    signedFits ⟨128, by decide⟩ (EVM.signed w) := by
  have hb := w.val.isLt
  change w.toNat < 2^256 at hb
  change -(2^127 : Int) ≤ (if w.toNat < 2^255 then (w.toNat : Int) else w.toNat - 2^256) ∧
    (if w.toNat < 2^255 then (w.toNat : Int) else w.toNat - 2^256) < 2^127
  split_ifs <;> constructor <;> omega

theorem signextend128_fixed_iff {n : Int} (hn : int256Fits n) :
    UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt n) = EVM.wordOfInt n ↔
      signedFits ⟨128, by decide⟩ n := by
  constructor
  · intro he
    have hr := signextend128_range (EVM.wordOfInt n)
    change (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt n)).toNat < 2^127 ∨
      2^256-2^127 ≤ (UInt256.signextend (UInt256.ofNat 15) (EVM.wordOfInt n)).toNat at hr
    rw [he] at hr
    have hf := signed128Fits_of_word_range hr
    rwa [signed_wordOfInt hn] at hf
  · intro hf
    exact signextend128_wordOfInt hf.1 hf.2

end Benchmarks.UniswapV4PoolManager
