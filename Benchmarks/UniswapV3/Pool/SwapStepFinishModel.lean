import Benchmarks.UniswapV3.Pool.SwapStepAmountsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

noncomputable def swapStepCap (a : SwapStepArgs) : Bool :=
  !swapStepExactIn a && decide ((swapStepAbsRemaining a).toNat < (swapStepAmount a false).toNat)

noncomputable def swapStepOutput (a : SwapStepArgs) : UInt256 :=
  if swapStepCap a then swapStepAbsRemaining a else swapStepAmount a false

noncomputable def swapStepUnusedFee (a : SwapStepArgs) : Bool :=
  swapStepExactIn a && !swapStepMax a

noncomputable def swapStepFee (a : SwapStepArgs) : UInt256 :=
  if swapStepUnusedFee a then UInt256.sub (EVM.wordOfInt a.remaining) (swapStepAmount a true)
  else fullMathRoundResult (swapStepAmount a true) a.fee (swapStepComplement a)

noncomputable def swapStepFeeValid (a : SwapStepArgs) : Prop :=
  if swapStepUnusedFee a then True
  else fullMathRoundValid (swapStepAmount a true) a.fee (swapStepComplement a)

noncomputable def swapStepValid (a : SwapStepArgs) : Prop :=
  swapStepAmountsValid a ∧ swapStepFeeValid a

noncomputable def swapStepResults (a : SwapStepArgs) : List Value :=
  [.int (Int.ofNat (swapStepPrice a).toNat), .int (Int.ofNat (swapStepAmount a true).toNat),
   .int (Int.ofNat (swapStepOutput a).toNat), .int (Int.ofNat (swapStepFee a).toNat)]

noncomputable def swapStepCapFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  {contract := contract
   immutables := imms
   locals := if swapStepCap a then (swapStepAmountsFrame imms a).locals.insert "amountOut"
     (.int (Int.ofNat (swapStepOutput a).toNat)) else (swapStepAmountsFrame imms a).locals}

noncomputable def swapStepFeeCallFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  {swapStepCapFrame imms a with
    locals := (swapStepCapFrame imms a).locals.insert "__c17"
      (.int (Int.ofNat (fullMathRoundResult (swapStepAmount a true) a.fee
        (swapStepComplement a)).toNat))}

noncomputable def swapStepResultFrame (imms : Store) (a : SwapStepArgs) : Frame :=
  {contract := contract
   immutables := imms
   locals := (if swapStepUnusedFee a then (swapStepCapFrame imms a).locals
     else (swapStepFeeCallFrame imms a).locals).insert "feeAmount"
       (.int (Int.ofNat (swapStepFee a).toNat))}

end Benchmarks.UniswapV3.Pool
