import Benchmarks.UniswapV4PoolManager.WordSignedCast
import Benchmarks.UniswapV4PoolManager.SignedRemainderWords
import Benchmarks.UniswapV4PoolManager.NarrowWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def tickCompressInt (tick spacing : Int) : Int :=
  tick.tdiv spacing - if tick.tmod spacing < 0 then 1 else 0
def tickCompressValue (tick spacing : Int) : Int :=
  if spacing = 0 then 0 else normalizeInt (.sint ⟨24, by decide⟩) (tickCompressInt tick spacing)
def tickCompressRaw (tick spacing : UInt256) : UInt256 :=
  UInt256.sub (UInt256.sdiv tick spacing) (UInt256.slt (UInt256.smod tick spacing) ⟨0⟩)
def tickCompressWord (tick spacing : UInt256) : UInt256 :=
  UInt256.signextend (UInt256.ofNat 2) (tickCompressRaw tick spacing)

theorem tickCompressInt_encode {tick spacing : UInt256} (ht : (EVM.signed tick).natAbs < 2^255)
    (hs : spacing ≠ ⟨0⟩) :
    EVM.wordOfInt (tickCompressInt (EVM.signed tick) (EVM.signed spacing)) = tickCompressRaw tick spacing := by
  have hr := tmod_int256_of_abs_lt (EVM.signed spacing) ht
  simp only [tickCompressInt, tickCompressRaw, sdiv_signed, smod_signed, if_neg hs,
    slt_signed, signed_wordOfInt hr]
  change EVM.wordOfInt ((EVM.signed tick).tdiv (EVM.signed spacing) -
    if (EVM.signed tick).tmod (EVM.signed spacing) < 0 then 1 else 0) =
      UInt256.sub (EVM.wordOfInt ((EVM.signed tick).tdiv (EVM.signed spacing)))
        (UInt256.fromBool (decide ((EVM.signed tick).tmod (EVM.signed spacing) < 0)))
  rw [wordOfIntSub]
  by_cases hn : (EVM.signed tick).tmod (EVM.signed spacing) < 0 <;>
    simp only [hn, if_true, if_false, decide_true, decide_false] <;> rfl

theorem tickCompressWord_value {tick spacing : UInt256} (ht : (EVM.signed tick).natAbs < 2^255) :
    tickCompressValue (EVM.signed tick) (EVM.signed spacing) = EVM.signed (tickCompressWord tick spacing) := by
  by_cases hs : spacing = ⟨0⟩
  · subst spacing
    simp only [tickCompressValue, show EVM.signed (⟨0⟩ : UInt256) = 0 from rfl, if_true,
      tickCompressWord, tickCompressRaw, sdiv_signed, Int.tdiv_zero]
    rfl
  · have hsn : EVM.signed spacing ≠ 0 := fun he => hs ((signed_eq_zero_iff spacing).mp he)
    rw [tickCompressValue, if_neg hsn, normalizeSigned24Integer, tickCompressInt_encode ht hs]
    rfl

theorem tickCompressWord_canonical (tick spacing : UInt256) : int24Canonical (tickCompressWord tick spacing) :=
  signextend24_canonical _

end Benchmarks.UniswapV4PoolManager
