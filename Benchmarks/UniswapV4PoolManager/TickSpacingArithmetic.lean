import Benchmarks.UniswapV4PoolManager.TickSpacingSource
import Benchmarks.UniswapV4PoolManager.SignedRemainderWords
import Benchmarks.UniswapV4PoolManager.WordIntegerArithmetic
import Benchmarks.UniswapV4PoolManager.WordSignedSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickSpacingWordCount (spacing : UInt256) : UInt256 :=
  UInt256.sub (UInt256.sdiv ⟨887272⟩ spacing)
    (UInt256.sub (UInt256.sdiv (EVM.wordOfInt (-887272)) spacing)
      (UInt256.slt (UInt256.smod (EVM.wordOfInt (-887272)) spacing) ⟨0⟩)) + ⟨1⟩
def tickSpacingWordLimit (spacing : UInt256) : UInt256 :=
  UInt256.land (UInt256.div ⟨2^128-1⟩ (tickSpacingWordCount spacing)) ⟨2^128-1⟩

theorem tickSpacingCount_encode (spacing : UInt256) :
    EVM.wordOfInt (tickSpacingMax (EVM.signed spacing)-tickSpacingMin (EVM.signed spacing)+1) =
      tickSpacingWordCount spacing := by
  by_cases hz : spacing = ⟨0⟩
  · subst spacing
    decide +kernel
  · have hs : EVM.signed spacing ≠ 0 := fun hs => hz ((signed_eq_zero_iff spacing).mp hs)
    have hpos : EVM.signed (⟨887272⟩ : UInt256) = 887272 := by decide +kernel
    have hneg : EVM.signed (EVM.wordOfInt (-887272)) = -887272 :=
      signed_wordOfInt (by constructor <;> decide)
    have hrem := tmod_int256_of_abs_lt (x := (-887272)) (EVM.signed spacing) (by decide)
    simp only [tickSpacingMax, tickSpacingMin, if_neg hs, tickSpacingWordCount,
      sdiv_signed, smod_signed, if_neg hz, hpos, hneg, slt_signed, signed_wordOfInt hrem]
    change EVM.wordOfInt ((887272 : Int).tdiv (EVM.signed spacing) -
      ((-887272 : Int).tdiv (EVM.signed spacing) - if (-887272 : Int).tmod (EVM.signed spacing) < 0 then 1 else 0)+1) =
      UInt256.sub (EVM.wordOfInt ((887272 : Int).tdiv (EVM.signed spacing)))
        (UInt256.sub (EVM.wordOfInt ((-887272 : Int).tdiv (EVM.signed spacing)))
          (UInt256.fromBool (decide ((-887272 : Int).tmod (EVM.signed spacing) < 0)))) + ⟨1⟩
    rw [wordOfIntAdd, wordOfIntSub, wordOfIntSub]
    by_cases hr : (-887272 : Int).tmod (EVM.signed spacing) < 0 <;>
      simp only [hr, if_true, if_false, decide_true, decide_false] <;> rfl

theorem tickSpacingWordCount_value (spacing : UInt256) :
    Int.ofNat (tickSpacingWordCount spacing).toNat = tickSpacingCount (EVM.signed spacing) := by
  rw [← tickSpacingCount_encode, wordOfIntResidue]
  rfl

theorem tickSpacingWordLimit_value (spacing : UInt256) :
    Int.ofNat (tickSpacingWordLimit spacing).toNat = tickSpacingLimit (EVM.signed spacing) := by
  rw [tickSpacingLimit, ← tickSpacingWordCount_value]
  by_cases hz : tickSpacingWordCount spacing = ⟨0⟩
  · rw [hz]
    change Int.ofNat (UInt256.land (UInt256.div ⟨2^128-1⟩ (tickSpacingWordCount spacing)) ⟨2^128-1⟩).toNat = _
    rw [hz]
    decide +kernel
  · have hn : (tickSpacingWordCount spacing).toNat ≠ 0 := fun he => hz (uint256_toNat_eq_zero he)
    rw [if_neg (by simpa only [Int.ofNat_eq_natCast, Int.natCast_eq_zero] using hn)]
    rw [tickSpacingWordLimit, ← normalizeUintWord ⟨128, by decide⟩ _ ⟨2^128-1⟩ rfl, udiv_toNat]
    congr 1

end Benchmarks.UniswapV4PoolManager
