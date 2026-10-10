import Benchmarks.UniswapV3.Pool.OracleObserveSingleSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveSingleInternalSource (caller : Frame) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity card : UInt256)
    (values : List Value) (args : List Expr) (retVar : Ident)
    (hf : caller.contract = contract)
    (he : evalExprs? config caller evm args =
      .ok [.int (Int.ofNat time.toNat), .int (Int.ofNat secondsAgo.toNat), .int tick,
        .int (Int.ofNat index.toNat), .int (Int.ofNat liquidity.toNat),
        .int (Int.ofNat card.toNat)])
    (hc : card.toNat < 2 ^ 16) (ht : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hrun : OracleObserveSingleRun time secondsAgo tick index liquidity card
      evm.accountMap evm.executionEnv values) :
    ExecStmt config caller evm (.internalCall "Oracle_observeSingle" args retVar)
      (.ok (resumeAfterInternalCall caller retVar (some values)) evm) := by
  have hframe : {caller with
      locals := oracleObserveSingleLocals time secondsAgo tick index liquidity card} =
      oracleObserveSingleFrame caller.immutables time secondsAgo tick index liquidity card := by
    cases caller
    simp_all only [oracleObserveSingleFrame]
  obtain ⟨out, hbody⟩ := oracleObserveSingleReturns caller.immutables evm time secondsAgo tick
    index liquidity card values hc ht hrun
  exact internalCallFunctionReturn (callee := oracleObserveSingleFunction) (calleeSolm := out)
    (value := some values) he (by rw [hf]; exact oracleObserveSingleLookup)
    (oracleObserveSingleBind _ _ _ _ _ _) (by rw [hframe]; exact hbody)

theorem oracleObserveSingleInternalReverts (caller : Frame) (evm : EVM.State)
    (time secondsAgo : UInt256) (tick : Int) (index liquidity card : UInt256)
    (args : List Expr) (retVar : Ident) (hf : caller.contract = contract)
    (he : evalExprs? config caller evm args =
      .ok [.int (Int.ofNat time.toNat), .int (Int.ofNat secondsAgo.toNat), .int tick,
        .int (Int.ofNat index.toNat), .int (Int.ofNat liquidity.toNat),
        .int (Int.ofNat card.toNat)])
    (hc : card.toNat < 2 ^ 16) (ht : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hfail : OracleObserveSingleFailure time secondsAgo tick index liquidity card
      evm.accountMap evm.executionEnv) :
    ExecStmt config caller evm (.internalCall "Oracle_observeSingle" args retVar) .reverted := by
  have hframe : {caller with
      locals := oracleObserveSingleLocals time secondsAgo tick index liquidity card} =
      oracleObserveSingleFrame caller.immutables time secondsAgo tick index liquidity card := by
    cases caller
    simp_all only [oracleObserveSingleFrame]
  exact internalCallFunctionRevert he (by rw [hf]; exact oracleObserveSingleLookup)
    (oracleObserveSingleBind _ _ _ _ _ _) (by
      rw [hframe]
      exact oracleObserveSingleReverts caller.immutables evm time secondsAgo tick index liquidity
        card hc ht hfail)

end Benchmarks.UniswapV3.Pool
