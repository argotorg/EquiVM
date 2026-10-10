import Benchmarks.UniswapV3.Pool.SnapshotInside

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem snapshotSourceReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hticks : validTicks lower upper)
    (hl : (tickOutside lower evm.accountMap evm.executionEnv).initialized = true)
    (hu : (tickOutside upper evm.accountMap evm.executionEnv).initialized = true)
    (hin : lower ≤ slot0TickValue evm.accountMap evm.executionEnv →
      slot0TickValue evm.accountMap evm.executionEnv < upper →
      (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat < 65535) :
    ∃ frame, ExecTransitionBody config contract evm (snapshotLocals lower upper) snapshotTransition.body
      (.returned frame evm (some (snapshotResult lower upper evm.accountMap evm.executionEnv).values))
      (immStore v) := by
  have hp := snapshotReadyPrefix v evm lower upper hwv hself hticks hl hu
  by_cases hbelow : slot0TickValue evm.accountMap evm.executionEnv < lower
  · refine ⟨snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv, ExecFuncBody.execBlockRet ?_⟩
    rw [← List.take_append_drop 35 snapshotTransition.body]
    apply execBlock_append_ok hp
    simp only [snapshotResult, if_pos hbelow]
    apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ (snapshotBelowReturns v evm lower upper))
    simpa only [hbelow, decide_true] using evalSnapshotLower v evm lower upper
  · by_cases habove : slot0TickValue evm.accountMap evm.executionEnv < upper
    · refine ⟨snapshotInsideFrame v lower upper evm.accountMap evm.executionEnv, ExecFuncBody.execBlockRet ?_⟩
      rw [← List.take_append_drop 35 snapshotTransition.body]
      apply execBlock_append_ok hp
      simp only [snapshotResult, if_neg hbelow, if_pos habove]
      refine ExecBlock.consReturn (ExecStmt.iteFalse ?_ ?_)
      · simpa only [hbelow, decide_false] using evalSnapshotLower v evm lower upper
      · apply ExecBlock.consReturn (ExecStmt.iteTrue ?_
          (snapshotInsideReturns v evm lower upper (hin (by omega) habove)))
        simpa only [habove, decide_true] using evalSnapshotUpper v evm lower upper
    · refine ⟨snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv, ExecFuncBody.execBlockRet ?_⟩
      rw [← List.take_append_drop 35 snapshotTransition.body]
      apply execBlock_append_ok hp
      simp only [snapshotResult, if_neg hbelow, if_neg habove]
      refine ExecBlock.consReturn (ExecStmt.iteFalse ?_ ?_)
      · simpa only [hbelow, decide_false] using evalSnapshotLower v evm lower upper
      · apply ExecBlock.consReturn (ExecStmt.iteFalse ?_ (snapshotAboveReturns v evm lower upper))
        simpa only [habove, decide_false] using evalSnapshotUpper v evm lower upper

theorem snapshotRevertsIndex (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hticks : validTicks lower upper)
    (hl : (tickOutside lower evm.accountMap evm.executionEnv).initialized = true)
    (hu : (tickOutside upper evm.accountMap evm.executionEnv).initialized = true)
    (hbelow : lower ≤ slot0TickValue evm.accountMap evm.executionEnv)
    (habove : slot0TickValue evm.accountMap evm.executionEnv < upper)
    (hin : ¬ (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat < 65535) :
    ExecTransitionBody config contract evm (snapshotLocals lower upper)
      snapshotTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 35 snapshotTransition.body]
  apply execBlock_append_ok (snapshotReadyPrefix v evm lower upper hwv hself hticks hl hu)
  refine ExecBlock.consRevert (ExecStmt.iteFalse ?_ ?_)
  · simpa only [show ¬ slot0TickValue evm.accountMap evm.executionEnv < lower by omega, decide_false]
      using evalSnapshotLower v evm lower upper
  · apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ (snapshotInsideReverts v evm lower upper hin))
    simpa only [habove, decide_true] using evalSnapshotUpper v evm lower upper

end Benchmarks.UniswapV3.Pool
