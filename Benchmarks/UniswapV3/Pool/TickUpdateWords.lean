import Benchmarks.UniswapV3.Pool.TickUpdateRawModel
import Benchmarks.UniswapV3.Pool.TickUpdateMaxTrace
import Benchmarks.UniswapV3.Pool.SignedWordZero

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a zero test on the encoding of a bounded signed integer.
theorem isZero_wordOfInt (i : Int) (hlo : -(2 ^ 255 : Int) ≤ i) (hhi : i < 2 ^ 255) :
    UInt256.isZero (EVM.wordOfInt i) = (decide (i = 0)).toUInt256 := by
  by_cases hz : i = 0
  · subst i
    rfl
  · rw [isZero_eq_zero_of_ne (fun h ↦ hz ((wordOfInt_zero_iff_signed i hlo hhi).mp h)),
      decide_eq_false hz]
    rfl

theorem tickUpdateGrossBefore_bounds (a : TickUpdateArgs) (evm : EVM.State) :
    0 ≤ tickUpdateGrossBefore a evm ∧ tickUpdateGrossBefore a evm < 2 ^ 128 := by
  constructor
  · exact Int.ofNat_nonneg _
  · change ((tickGrossWord evm.accountMap evm.executionEnv a.tick).toNat : Int) < 2 ^ 128
    exact_mod_cast tickGrossWord_lt evm.accountMap evm.executionEnv a.tick

theorem tickUpdateGrossAfter_bounds (a : TickUpdateArgs) (evm : EVM.State) :
    0 ≤ tickUpdateGrossAfter a evm ∧ tickUpdateGrossAfter a evm < 2 ^ 128 :=
  liquidityDeltaResult_bounds _ _

theorem tickUpdateGrossBefore_word (a : TickUpdateArgs) (evm : EVM.State) :
    EVM.wordOfInt (tickUpdateGrossBefore a evm) =
      tickGrossWord evm.accountMap evm.executionEnv a.tick := wordOfInt_ofNat_toNat _

theorem tickUpdateGrossAfter_toNat (a : TickUpdateArgs) (evm : EVM.State) :
    (EVM.wordOfInt (tickUpdateGrossAfter a evm)).toNat = (tickUpdateGrossAfter a evm).toNat := by
  have hb := tickUpdateGrossAfter_bounds a evm
  rw [wordOfInt_mod, Int.emod_eq_of_lt hb.1 (by omega)]

theorem tickUpdateGrossAfter_word_lt (a : TickUpdateArgs) (evm : EVM.State) :
    (EVM.wordOfInt (tickUpdateGrossAfter a evm)).toNat < 2 ^ 128 := by
  rw [tickUpdateGrossAfter_toNat]
  have hb := tickUpdateGrossAfter_bounds a evm
  omega

theorem tickUpdateFlipped_word (a : TickUpdateArgs) (evm : EVM.State) :
    UInt256.isZero (UInt256.eq
      (UInt256.isZero (UInt256.land (UInt256.sub
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))
        (tickGrossWord evm.accountMap evm.executionEnv a.tick)))
      (UInt256.isZero (UInt256.land (EVM.wordOfInt (tickUpdateGrossAfter a evm))
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
          (UInt256.ofNat 1))))) = (tickUpdateFlipped a evm).toUInt256 := by
  have hbclean : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (tickGrossWord evm.accountMap evm.executionEnv a.tick) =
      tickGrossWord evm.accountMap evm.executionEnv a.tick := uint128Word_clean (tickGrossWord_lt _ _ _)
  have haclean : UInt256.land (UInt256.ofNat (2 ^ 128 - 1))
      (EVM.wordOfInt (tickUpdateGrossAfter a evm)) = EVM.wordOfInt (tickUpdateGrossAfter a evm) :=
    uint128Word_clean (tickUpdateGrossAfter_word_lt a evm)
  rw [solcMask128, hbclean, u256_land_comm (EVM.wordOfInt (tickUpdateGrossAfter a evm)),
    haclean, ← tickUpdateGrossBefore_word a evm]
  have hb := tickUpdateGrossBefore_bounds a evm
  have ha := tickUpdateGrossAfter_bounds a evm
  rw [isZero_wordOfInt _ (by omega) (by omega), isZero_wordOfInt _ (by omega) (by omega)]
  unfold tickUpdateFlipped
  cases decide (tickUpdateGrossBefore a evm = 0) <;>
    cases decide (tickUpdateGrossAfter a evm = 0) <;> rfl

theorem tickUpdateCompare_word (a : TickUpdateArgs) (hfit : a.TraceFits) :
    UInt256.sgt (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.tick))
      (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.current)) =
      if a.current < a.tick then ⟨1⟩ else ⟨0⟩ := by
  rcases hfit with ⟨ht, hc, _⟩
  rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
    signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
    normalizeSint_eq_self ⟨24, by decide⟩ _ ht.1 ht.2,
    normalizeSint_eq_self ⟨24, by decide⟩ _ hc.1 hc.2, sgt_eq_slt_swap]
  exact slt_wordOfInt _ _ (by omega) (by omega) (by omega) (by omega)

end Benchmarks.UniswapV3.Pool
