import Benchmarks.UniswapV3.Pool.NextSqrt1Prefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextSqrt1CallName (a : NextSqrtArgs) : String :=
  if nextSqrt1Small a then "__c4" else if a.add then "__c0" else "__c5"

noncomputable def nextSqrt1CallFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt1ZeroFrame imms a with
    locals := (nextSqrt1ZeroFrame imms a).locals.insert (nextSqrt1CallName a)
      (.int (Int.ofNat (nextSqrt1Quotient a).toNat))}

def nextSqrt1FullCall (a : NextSqrtArgs) : Stmt :=
  .internalCall (if a.add then "FullMath_mulDiv" else "FullMath_mulDivRoundingUp")
    nextSqrt1FullArgs (nextSqrt1CallName a)

theorem nextSqrt1FullReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hsmall : ¬nextSqrt1Small a) (hv : nextSqrt1QuotientValid a) :
    ExecStmt config (nextSqrt1ZeroFrame imms a) evm (nextSqrt1FullCall a)
      (.ok (nextSqrt1CallFrame imms a) evm) := by
  cases ha : a.add
  · have hvalid : fullMathRoundValid a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity := by
      simpa only [nextSqrt1QuotientValid, if_neg hsmall, ha, Bool.false_eq_true, if_false] using hv
    have hc := internalCallFunctionReturn (callee := fullMathRoundFunction)
      (retVar := nextSqrt1CallName a)
      (locals := fullMathLocals a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity)
      (calleeSolm := fullMathRoundFinalFrame imms a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity)
      (value := some [.int (Int.ofNat
        (fullMathRoundResult a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity).toNat)])
      (evalNextSqrt1FullArgs imms evm a) fullMathRoundLookup
      (fullMathRoundBind _ _ _) (fullMathRoundReturns imms evm _ _ _ hvalid)
    simpa only [nextSqrt1FullCall, nextSqrt1CallFrame, nextSqrt1Quotient,
      if_neg hsmall, ha, Bool.false_eq_true, if_false] using hc
  · have hvalid : fullMathValid a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity := by
      simpa only [nextSqrt1QuotientValid, if_neg hsmall, ha, if_true] using hv
    have hc := internalCallFunctionReturn (callee := fullMathFunction)
      (retVar := nextSqrt1CallName a)
      (locals := fullMathLocals a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity)
      (calleeSolm := fullMathProductFrame imms a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity)
      (value := some [.int (Int.ofNat
        (fullMathResult a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity).toNat)])
      (evalNextSqrt1FullArgs imms evm a) fullMathLookup
      (fullMathBind _ _ _) (fullMathReturns imms evm _ _ _ hvalid)
    simpa only [nextSqrt1FullCall, nextSqrt1CallFrame, nextSqrt1Quotient,
      if_neg hsmall, ha, if_true] using hc

theorem nextSqrt1FullReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hsmall : ¬nextSqrt1Small a) (hv : ¬nextSqrt1QuotientValid a) :
    ExecStmt config (nextSqrt1ZeroFrame imms a) evm (nextSqrt1FullCall a) .reverted := by
  cases ha : a.add
  · have hvalid : ¬fullMathRoundValid a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity := by
      simpa only [nextSqrt1QuotientValid, if_neg hsmall, ha, Bool.false_eq_true, if_false] using hv
    have hc := internalCallFunctionRevert (callee := fullMathRoundFunction)
      (retVar := nextSqrt1CallName a)
      (locals := fullMathLocals a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity)
      (evalNextSqrt1FullArgs imms evm a) fullMathRoundLookup
      (fullMathRoundBind _ _ _) (fullMathRoundReverts imms evm _ _ _ hvalid)
    simpa only [nextSqrt1FullCall, ha, Bool.false_eq_true, if_false] using hc
  · have hvalid : ¬fullMathValid a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity := by
      simpa only [nextSqrt1QuotientValid, if_neg hsmall, ha, if_true] using hv
    have hc := internalCallFunctionRevert (callee := fullMathFunction)
      (retVar := nextSqrt1CallName a)
      (locals := fullMathLocals a.amount (UInt256.ofNat (2 ^ 96)) a.liquidity)
      (evalNextSqrt1FullArgs imms evm a) fullMathLookup
      (fullMathBind _ _ _) (fullMathReverts imms evm _ _ _ hvalid)
    simpa only [nextSqrt1FullCall, ha, if_true] using hc

theorem nextSqrt1UnsafeReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hsmall : nextSqrt1Small a) (ha : a.add = false) :
    ExecStmt config (nextSqrt1ZeroFrame imms a) evm
      (.internalCall "UnsafeMath_divRoundingUp" nextSqrt1UnsafeArgs "__c4")
      (.ok (nextSqrt1CallFrame imms a) evm) := by
  have hc := internalCallFunctionReturn (callee := unsafeDivRoundFunction) (retVar := "__c4")
    (locals := unsafeDivRoundLocals (nextSqrt1ScaledAmount a) a.liquidity)
    (calleeSolm := unsafeDivRoundFrame imms (nextSqrt1ScaledAmount a) a.liquidity)
    (value := some [.int (Int.ofNat
      (unsafeDivRoundResult (nextSqrt1ScaledAmount a) a.liquidity).toNat)])
    (evalNextSqrt1UnsafeArgs imms evm a) unsafeDivRoundLookup (unsafeDivRoundBind _ _)
    (unsafeDivRoundReturns imms evm _ _)
  simpa only [nextSqrt1CallFrame, nextSqrt1CallName, nextSqrt1Quotient,
    if_pos hsmall, ha, Bool.false_eq_true, if_false] using hc

end Benchmarks.UniswapV3.Pool
