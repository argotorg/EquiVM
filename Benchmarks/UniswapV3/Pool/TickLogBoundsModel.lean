import Benchmarks.UniswapV3.Pool.TickLogSeriesWords
import Benchmarks.UniswapV3.Pool.TickSqrtModel
import Benchmarks.UniswapV3.Pool.WordComplements
import Benchmarks.UniswapV3.Pool.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickLogScaledLog (log : UInt256) : UInt256 :=
  UInt256.mul log (UInt256.ofNat 255738958999603826347141)

def tickLogLowRaw (log : UInt256) : UInt256 :=
  UInt256.sar ⟨128⟩
    (UInt256.sub (tickLogScaledLog log) (UInt256.ofNat 3402992956809132418596140100660247210))

def tickLogHighRaw (log : UInt256) : UInt256 :=
  UInt256.sar ⟨128⟩
    (tickLogScaledLog log + UInt256.ofNat 291339464771989622907027621153398088495)

def tickLogTick (word : UInt256) : Int :=
  normalizeInt (.sint ⟨24, by decide⟩) (Int.ofNat word.toNat)

def tickLogLow (log : UInt256) : Int := tickLogTick (tickLogLowRaw log)

def tickLogHigh (log : UInt256) : Int := tickLogTick (tickLogHighRaw log)

def tickLogSafe (log : UInt256) : Prop :=
  tickLogLow log = tickLogHigh log ∨ (tickLogHigh log).natAbs ≤ 887272

instance (log : UInt256) : Decidable (tickLogSafe log) := inferInstanceAs (Decidable (_ ∨ _))

def tickLogChoiceRaw (log price : UInt256) : UInt256 :=
  if tickLogLow log = tickLogHigh log then tickLogLowRaw log else
    if (tickSqrtValue (tickLogHigh log)).toNat ≤ price.toNat then tickLogHighRaw log else tickLogLowRaw log

def tickLogChoice (log price : UInt256) : Int := tickLogTick (tickLogChoiceRaw log price)

theorem tickLogTick_bounds (word : UInt256) :
    -(2 ^ 23 : Int) ≤ tickLogTick word ∧ tickLogTick word < 2 ^ 23 :=
  normalizeSint_bounds _ _

theorem tickLogChoice_eq (log price : UInt256) :
    tickLogChoice log price =
      if tickLogLow log = tickLogHigh log then tickLogLow log else
        if (tickSqrtValue (tickLogHigh log)).toNat ≤ price.toNat then tickLogHigh log else tickLogLow log := by
  unfold tickLogChoice tickLogChoiceRaw
  split
  · rfl
  · split <;> rfl

theorem tickLogLowRaw_compiled (log : UInt256) :
    UInt256.sar (UInt256.ofNat 128)
      (tickLogScaledLog log + UInt256.lnot (UInt256.ofNat 3402992956809132418596140100660247209)) =
      tickLogLowRaw log := by
  rw [wordAdd_lnot_eq_sub_addOne,
    show UInt256.ofNat 3402992956809132418596140100660247209 + (⟨1⟩ : UInt256) =
      UInt256.ofNat 3402992956809132418596140100660247210 by decide]
  rfl

theorem tickLogSignextend (word : UInt256) :
    UInt256.signextend (UInt256.ofNat 2) word = EVM.wordOfInt (tickLogTick word) :=
  signextend_normalizeSint ⟨24, by decide⟩ _ _ (by decide) (by decide)

theorem tickLogSignextend_eq (a b : UInt256) :
    UInt256.signextend (UInt256.ofNat 2) a = UInt256.signextend (UInt256.ofNat 2) b ↔
      tickLogTick a = tickLogTick b := by
  rw [tickLogSignextend, tickLogSignextend]
  constructor
  · intro h
    have hab := tickLogTick_bounds a
    have hbb := tickLogTick_bounds b
    have ha := wordOfInt_signed_value (tickLogTick a) (by omega) (by omega)
    have hb := wordOfInt_signed_value (tickLogTick b) (by omega) (by omega)
    rw [h] at ha
    exact ha.trans hb.symm
  · exact congrArg EVM.wordOfInt

end Benchmarks.UniswapV3.Pool
