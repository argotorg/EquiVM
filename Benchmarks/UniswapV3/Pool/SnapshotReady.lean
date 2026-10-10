import Benchmarks.UniswapV3.Pool.SnapshotRead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def snapshotLowerFrame (v : UniswapV3PoolImmutables) (lower upper : Int)
    (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  snapshotLowerReadFrame (snapshotAliasesFrame v lower upper).locals (immStore v) (tickOutside lower σ I)
def snapshotBothFrame (v : UniswapV3PoolImmutables) (lower upper : Int)
    (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  snapshotUpperReadFrame (snapshotLowerFrame v lower upper σ I).locals (immStore v) (tickOutside upper σ I)
def snapshotReadyFrame (v : UniswapV3PoolImmutables) (lower upper : Int)
    (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { (snapshotBothFrame v lower upper σ I) with
    locals := (snapshotBothFrame v lower upper σ I).locals.insert "_slot0" (slot0StructValue σ I) }

theorem snapshotAliasesPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hticks : validTicks lower upper) :
    ExecBlock config (snapshotFrame v lower upper) evm (snapshotTransition.body.take 14)
      (.ok (snapshotAliasesFrame v lower upper) evm) := by
  change ExecBlock _ _ _ (snapshotTransition.body.take 6 ++ (snapshotTransition.body.drop 6).take 8) _
  exact execBlock_append_ok (snapshotCheckedPrefix v evm lower upper hwv hself hticks)
    (snapshotAliasPrefix v evm lower upper)

theorem snapshotLowerPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hticks : validTicks lower upper) :
    ExecBlock config (snapshotFrame v lower upper) evm (snapshotTransition.body.take 23)
      (.ok (snapshotLowerFrame v lower upper evm.accountMap evm.executionEnv) evm) := by
  change ExecBlock _ _ _ (snapshotTransition.body.take 14 ++ (snapshotTransition.body.drop 14).take 9) _
  apply execBlock_append_ok (snapshotAliasesPrefix v evm lower upper hwv hself hticks)
  exact snapshotLowerRead _ _ evm lower
    (by simp [snapshotLowerAliasFrame, Std.HashMap.getElem_insert])
    (by simp [snapshotLowerAliasFrame, snapshotZerosFrame, Std.HashMap.getElem_insert])
    (by simp [snapshotLowerAliasFrame, snapshotZerosFrame, Std.HashMap.getElem_insert])
    (by simp [snapshotLowerAliasFrame, snapshotZerosFrame, Std.HashMap.getElem_insert])

theorem snapshotRevertsLower (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hticks : validTicks lower upper)
    (hl : (tickOutside lower evm.accountMap evm.executionEnv).initialized = false) :
    ExecTransitionBody config contract evm (snapshotLocals lower upper)
      snapshotTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 23 snapshotTransition.body]
  apply execBlock_append_ok (snapshotLowerPrefix v evm lower upper hwv hself hticks)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hl] using evalSnapshotLowerInitialized
    (snapshotAliasesFrame v lower upper).locals (immStore v) evm
    (tickOutside lower evm.accountMap evm.executionEnv)

theorem snapshotBothPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hticks : validTicks lower upper)
    (hl : (tickOutside lower evm.accountMap evm.executionEnv).initialized = true) :
    ExecBlock config (snapshotFrame v lower upper) evm (snapshotTransition.body.take 33)
      (.ok (snapshotBothFrame v lower upper evm.accountMap evm.executionEnv) evm) := by
  change ExecBlock _ _ _ (snapshotTransition.body.take 23 ++ (snapshotTransition.body.drop 23).take 10) _
  apply execBlock_append_ok (snapshotLowerPrefix v evm lower upper hwv hself hticks)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hl] using evalSnapshotLowerInitialized
      (snapshotAliasesFrame v lower upper).locals (immStore v) evm
      (tickOutside lower evm.accountMap evm.executionEnv)
  exact snapshotUpperRead _ _ evm upper
    (by simp [snapshotAliasesFrame, Std.HashMap.getElem_insert])
    (by simp [snapshotAliasesFrame, snapshotLowerAliasFrame,
      snapshotZerosFrame, Std.HashMap.getElem_insert])
    (by simp [snapshotAliasesFrame, snapshotLowerAliasFrame,
      snapshotZerosFrame, Std.HashMap.getElem_insert])
    (by simp [snapshotAliasesFrame, snapshotLowerAliasFrame,
      snapshotZerosFrame, Std.HashMap.getElem_insert])

theorem snapshotRevertsUpper (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hticks : validTicks lower upper)
    (hl : (tickOutside lower evm.accountMap evm.executionEnv).initialized = true)
    (hu : (tickOutside upper evm.accountMap evm.executionEnv).initialized = false) :
    ExecTransitionBody config contract evm (snapshotLocals lower upper)
      snapshotTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 33 snapshotTransition.body]
  apply execBlock_append_ok (snapshotBothPrefix v evm lower upper hwv hself hticks hl)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hu] using evalSnapshotUpperInitialized
    (snapshotLowerFrame v lower upper evm.accountMap evm.executionEnv).locals (immStore v) evm
    (tickOutside upper evm.accountMap evm.executionEnv)

theorem snapshotReadyPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hticks : validTicks lower upper)
    (hl : (tickOutside lower evm.accountMap evm.executionEnv).initialized = true)
    (hu : (tickOutside upper evm.accountMap evm.executionEnv).initialized = true) :
    ExecBlock config (snapshotFrame v lower upper) evm (snapshotTransition.body.take 35)
      (.ok (snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv) evm) := by
  change ExecBlock _ _ _ (snapshotTransition.body.take 33 ++ (snapshotTransition.body.drop 33).take 2) _
  apply execBlock_append_ok (snapshotBothPrefix v evm lower upper hwv hself hticks hl)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hu] using evalSnapshotUpperInitialized
      (snapshotLowerFrame v lower upper evm.accountMap evm.executionEnv).locals (immStore v) evm
      (tickOutside upper evm.accountMap evm.executionEnv)
  refine ExecBlock.consNormal (solm' := snapshotReadyFrame v lower upper evm.accountMap evm.executionEnv)
    (evm' := evm) (ExecStmt.letDecl ?_) ExecBlock.nil
  exact evalSlot0Struct _ _ evm (by
    simp [snapshotLowerFrame, snapshotLowerReadFrame,
      snapshotAliasesFrame, snapshotLowerAliasFrame, snapshotZerosFrame, snapshotCheckedFrame,
      snapshotDelegateFrame, snapshotInitialFrame, snapshotLocals, checkTicksLocals])

end Benchmarks.UniswapV3.Pool
