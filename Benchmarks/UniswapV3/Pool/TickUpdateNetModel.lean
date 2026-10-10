import Benchmarks.UniswapV3.Pool.TickUpdateInitializeSource
import Benchmarks.UniswapV3.Pool.SafeSignedMathSource
import Benchmarks.UniswapV3.Pool.SafeCast128Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickUpdateNetBefore (a : TickUpdateArgs) (evm : EVM.State) : Int :=
  tickNetValue (tickUpdateGrossState a evm).accountMap (tickUpdateGrossState a evm).executionEnv a.tick

def tickUpdateNetResult (a : TickUpdateArgs) (evm : EVM.State) (subtract : Bool) : Int :=
  safeSignedMathResult subtract (tickUpdateNetBefore a evm) a.delta

theorem tickUpdateNetBefore_bounds (a : TickUpdateArgs) (evm : EVM.State) :
    -(2 ^ 127 : Int) ≤ tickUpdateNetBefore a evm ∧ tickUpdateNetBefore a evm < 2 ^ 127 :=
  tickNetValue_bounds _ _ _

theorem tickUpdateNetMathValid (a : TickUpdateArgs) (evm : EVM.State) (subtract : Bool)
    (hdlo : -(2 ^ 127 : Int) ≤ a.delta) (hdhi : a.delta < 2 ^ 127) :
    safeSignedMathValid subtract (tickUpdateNetBefore a evm) a.delta := by
  have hb := tickUpdateNetBefore_bounds a evm
  apply (safeSignedMathValid_iff subtract _ _ (by omega) (by omega) (by omega) (by omega)).2
  cases subtract <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

def tickUpdateMathRet (subtract : Bool) : Ident := if subtract then "__c1" else "__c3"

def tickUpdateCastRet (subtract : Bool) : Ident := if subtract then "__c2" else "__c4"

def tickUpdateNetStartFrame (imms : Store) (a : TickUpdateArgs) (evm : EVM.State) : Frame :=
  let locals := (tickUpdateFlippedFrame imms a evm).locals.insert "__cond5" (.int 0)
  {tickUpdateFlippedFrame imms a evm with locals := locals}

def tickUpdateMathFrame (imms : Store) (a : TickUpdateArgs) (evm : EVM.State)
    (subtract : Bool) : Frame :=
  let locals := (tickUpdateNetStartFrame imms a evm).locals.insert (tickUpdateMathRet subtract)
    (.int (tickUpdateNetResult a evm subtract))
  {tickUpdateNetStartFrame imms a evm with locals := locals}

def tickUpdateCastFrame (imms : Store) (a : TickUpdateArgs) (evm : EVM.State)
    (subtract : Bool) : Frame :=
  let locals := (tickUpdateMathFrame imms a evm subtract).locals.insert (tickUpdateCastRet subtract)
    (.int (tickUpdateNetResult a evm subtract))
  {tickUpdateMathFrame imms a evm subtract with locals := locals}

def tickUpdateNetReadyFrame (imms : Store) (a : TickUpdateArgs) (evm : EVM.State)
    (subtract : Bool) : Frame :=
  let locals := (tickUpdateCastFrame imms a evm subtract).locals.insert "__cond5"
    (.int (tickUpdateNetResult a evm subtract))
  {tickUpdateCastFrame imms a evm subtract with locals := locals}

def tickUpdateFinalState (a : TickUpdateArgs) (evm : EVM.State) : EVM.State :=
  tickLiquidityState (tickUpdateGrossState a evm) a.tick true
    (EVM.wordOfInt (tickUpdateNetResult a evm a.upper))

def tickUpdateNetArgs : List Expr :=
  [.cast (.storage ⟨"info", [.field "liquidityNet"]⟩) (.elem (.int (.sint ⟨256, by decide⟩))),
   .var "liquidityDelta"]

def tickUpdateNetBody (subtract : Bool) : List Stmt :=
  [.internalCall (if subtract then "LowGasSafeMath_sub" else "LowGasSafeMath_add_int256_int256")
     tickUpdateNetArgs (tickUpdateMathRet subtract),
   .internalCall "SafeCast_toInt128" [.var (tickUpdateMathRet subtract)] (tickUpdateCastRet subtract),
   .assign .localVar ⟨"__cond5", []⟩ (.var (tickUpdateCastRet subtract))]

end Benchmarks.UniswapV3.Pool
