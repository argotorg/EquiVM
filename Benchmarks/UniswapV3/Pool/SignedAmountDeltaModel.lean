import Benchmarks.UniswapV3.Pool.AmountDeltaBounds
import Benchmarks.UniswapV3.Pool.LiquidityDeltaModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

structure SignedAmountDeltaArgs where
  sqrtA : UInt256
  sqrtB : UInt256
  liquidity : Int

def SignedAmountDeltaArgs.Fits (a : SignedAmountDeltaArgs) : Prop :=
  a.sqrtA.toNat < 2 ^ 160 ∧ a.sqrtB.toNat < 2 ^ 160 ∧
    -(2 ^ 127 : Int) ≤ a.liquidity ∧ a.liquidity < 2 ^ 127

def signedAmountDeltaMagnitude (a : SignedAmountDeltaArgs) : Int :=
  if a.liquidity < 0 then -a.liquidity else a.liquidity

def signedAmountDeltaUnsigned (a : SignedAmountDeltaArgs) : AmountDeltaArgs :=
  {sqrtA := a.sqrtA, sqrtB := a.sqrtB, liquidity := EVM.wordOfInt (signedAmountDeltaMagnitude a),
    roundUp := decide (0 ≤ a.liquidity)}

def signedAmountDeltaValid (second : Bool) (a : SignedAmountDeltaArgs) : Prop :=
  amountDeltaValid second (signedAmountDeltaUnsigned a)

noncomputable def signedAmountDeltaResult (second : Bool) (a : SignedAmountDeltaArgs) : Int :=
  if a.liquidity < 0 then -Int.ofNat (amountDeltaResult second (signedAmountDeltaUnsigned a)).toNat
  else Int.ofNat (amountDeltaResult second (signedAmountDeltaUnsigned a)).toNat

theorem signedAmountDeltaMagnitude_bounds (a : SignedAmountDeltaArgs) (hfit : a.Fits) :
    0 ≤ signedAmountDeltaMagnitude a ∧ signedAmountDeltaMagnitude a < 2 ^ 128 := by
  unfold signedAmountDeltaMagnitude
  split_ifs <;> obtain ⟨_, _, hlo, hhi⟩ := hfit <;> omega

theorem signedAmountDeltaUnsignedValue (a : SignedAmountDeltaArgs) (hfit : a.Fits) :
    Int.ofNat (signedAmountDeltaUnsigned a).liquidity.toNat = signedAmountDeltaMagnitude a := by
  obtain ⟨hlo, hhi⟩ := signedAmountDeltaMagnitude_bounds a hfit
  change Int.ofNat (EVM.wordOfInt (signedAmountDeltaMagnitude a)).toNat = _
  rw [wordOfInt_mod, Int.emod_eq_of_lt hlo (by omega)]
  exact Int.toNat_of_nonneg hlo

theorem signedAmountDeltaUnsignedFits (a : SignedAmountDeltaArgs) (hfit : a.Fits) :
    (signedAmountDeltaUnsigned a).Fits := by
  refine ⟨hfit.1, hfit.2.1, ?_⟩
  have hm := (signedAmountDeltaMagnitude_bounds a hfit).2
  rw [← signedAmountDeltaUnsignedValue a hfit] at hm
  change ((signedAmountDeltaUnsigned a).liquidity.toNat : Int) < (2 ^ 128 : Nat) at hm
  exact_mod_cast hm

theorem signedAmountDeltaNegativeCast (a : SignedAmountDeltaArgs) (hfit : a.Fits)
    (hn : a.liquidity < 0) :
    normalizeInt (.uint ⟨128, by decide⟩)
      (normalizeInt (.sint ⟨128, by decide⟩) (0 - a.liquidity)) =
      Int.ofNat (signedAmountDeltaUnsigned a).liquidity.toNat := by
  rw [normalizeUInt_sint, signedAmountDeltaUnsignedValue a hfit]
  have hm := signedAmountDeltaMagnitude_bounds a hfit
  simp only [signedAmountDeltaMagnitude, if_pos hn] at hm ⊢
  rw [zero_sub]
  exact normalizeInt_uint_eq_self ⟨128, by decide⟩ _ hm.1 hm.2

theorem signedAmountDeltaPositiveCast (a : SignedAmountDeltaArgs) (hfit : a.Fits)
    (hn : ¬a.liquidity < 0) :
    normalizeInt (.uint ⟨128, by decide⟩) a.liquidity =
      Int.ofNat (signedAmountDeltaUnsigned a).liquidity.toNat := by
  rw [signedAmountDeltaUnsignedValue a hfit]
  have hm := signedAmountDeltaMagnitude_bounds a hfit
  simp only [signedAmountDeltaMagnitude, if_neg hn] at hm ⊢
  exact normalizeInt_uint_eq_self ⟨128, by decide⟩ _ hm.1 hm.2

theorem signedAmountDeltaResult_bounds (second : Bool) (a : SignedAmountDeltaArgs)
    (hfit : a.Fits) (hv : signedAmountDeltaValid second a) :
    -(2 ^ 255 : Int) ≤ signedAmountDeltaResult second a ∧
      signedAmountDeltaResult second a < 2 ^ 255 := by
  have hb := amountDeltaResult_lt255 second (signedAmountDeltaUnsigned a)
    (signedAmountDeltaUnsignedFits a hfit) hv
  unfold signedAmountDeltaResult
  split_ifs <;> simp only [Int.ofNat_eq_natCast] <;> omega

def signedAmountDeltaFunction (second : Bool) : FunctionDecl :=
  contract.functions[if second then 32 else 31]!

def signedAmountDeltaName (second : Bool) : Ident :=
  if second then "SqrtPriceMath_getAmount1Delta" else "SqrtPriceMath_getAmount0Delta"

theorem signedAmountDeltaLookup (second : Bool) :
    lookupCallable? contract (signedAmountDeltaName second) =
      some (signedAmountDeltaFunction second).toCallable := by cases second <;> rfl

def signedAmountDeltaLocals (a : SignedAmountDeltaArgs) : Store :=
  let locals := (∅ : Store).insert "liquidity" (.int a.liquidity)
  let locals := locals.insert "sqrtRatioBX96" (.int (Int.ofNat a.sqrtB.toNat))
  locals.insert "sqrtRatioAX96" (.int (Int.ofNat a.sqrtA.toNat))

def signedAmountDeltaFrame (imms : Store) (a : SignedAmountDeltaArgs) : Frame :=
  {contract := contract, locals := signedAmountDeltaLocals a, immutables := imms}

theorem signedAmountDeltaBind (second : Bool) (a : SignedAmountDeltaArgs) :
    bindParams? (signedAmountDeltaFunction second).params
      [.int (Int.ofNat a.sqrtA.toNat), .int (Int.ofNat a.sqrtB.toNat), .int a.liquidity] =
      some (signedAmountDeltaLocals a) := by cases second <;> rfl

end Benchmarks.UniswapV3.Pool
