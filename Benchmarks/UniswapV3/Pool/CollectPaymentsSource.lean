import Benchmarks.UniswapV3.Pool.CollectSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def collectSubtractStmt (second : Bool) : Stmt :=
  .assign .storage ⟨"position", [.field (positionOwedField second)]⟩
    (.cast (.binary .sub (.storage ⟨"position", [.field (positionOwedField second)]⟩)
      (.var (poolAmountName second))) (.elem (.int (.uint ⟨128, by decide⟩))))

def collectPaymentState (evm : EVM.State) (key : UInt256) (second : Bool) (amount : UInt256) : EVM.State :=
  storePositionOwed evm key second (UInt256.sub (positionOwedWord key second evm.accountMap evm.executionEnv) amount)

theorem collectSubtract (locals imms : Store) (evm : EVM.State)
    (key : UInt256) (second : Bool) (amount : UInt256)
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hposition : locals.get? "position" = some (positionAlias key)) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm (collectSubtractStmt second)
      (.ok {contract := contract, locals := locals, immutables := imms} (collectPaymentState evm key second amount)) := by
  have ha := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hget
  have hp := evalPositionOwed locals imms evm key second hposition
  have hstore (value : UInt256) :
      storePositionOwed evm key second (uint128Word value) = storePositionOwed evm key second value := by
    simp only [storePositionOwed, protocolFeeUpdateWord, uint128Word_clean (uint128Word_lt value)]
  simpa only [hstore] using ExecStmt.assign (evalExpr_uint128Sub hp ha)
    (assignPositionOwed locals imms evm key second
      (uint128Word (UInt256.sub (positionOwedWord key second evm.accountMap evm.executionEnv) amount)) hposition)

def collectTokenStmt (second : Bool) : Stmt :=
  .ite (.binary .gt (.var (poolAmountName second)) (.intLit 0))
    [collectSubtractStmt second, poolTransferStmt second] []

theorem collectTokenZero (locals imms : Store) (evm : EVM.State) (second : Bool)
    (hget : locals.get? (poolAmountName second) = some (.int 0)) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm (collectTokenStmt second)
      (.ok {contract := contract, locals := locals, immutables := imms} evm) := by
  apply ExecStmt.iteFalse ?_ ExecBlock.nil
  simpa using evalExpr_uint256_var_positive (cfg := config)
    (frame := {contract := contract, locals := locals, immutables := imms})
    evm (poolAmountName second) ⟨0⟩ hget

theorem collectTokenReturns (v : UniswapV3PoolImmutables) (locals : Store)
    (evm evm' : EVM.State) (key : UInt256) (second : Bool) (recipient : AccountAddress) (amount : UInt256)
    (calleeFrame : Frame)
    (hrecipient : locals.get? "recipient" = some (.address recipient))
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hposition : locals.get? "position" = some (positionAlias key)) (hpos : 0 < amount.toNat)
    (hcall : ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient amount)
      (collectPaymentState evm key second amount) safeTransferFunction.body (.returned calleeFrame evm' none)) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm (collectTokenStmt second)
      (.ok { contract := contract
             locals := locals.insert (poolTransferCallName second) .unit
             immutables := immStore v } evm') := by
  refine ExecStmt.iteTrue ?_ ?_
  · simpa only [hpos, decide_true] using evalExpr_uint256_var_positive (cfg := config)
      (frame := {contract := contract, locals := locals, immutables := immStore v})
      evm (poolAmountName second) amount hget
  refine ExecBlock.consNormal (collectSubtract locals (immStore v) evm key second amount hget hposition) ?_
  exact ExecBlock.consNormal (poolTransferReturns v locals _ evm' second recipient amount calleeFrame
    hrecipient hget hcall) ExecBlock.nil

theorem collectTokenReverts (v : UniswapV3PoolImmutables) (locals : Store)
    (evm : EVM.State) (key : UInt256) (second : Bool) (recipient : AccountAddress) (amount : UInt256)
    (hrecipient : locals.get? "recipient" = some (.address recipient))
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hposition : locals.get? "position" = some (positionAlias key)) (hpos : 0 < amount.toNat)
    (hcall : ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient amount)
      (collectPaymentState evm key second amount) safeTransferFunction.body .reverted) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (collectTokenStmt second) .reverted := by
  refine ExecStmt.iteTrue ?_ ?_
  · simpa only [hpos, decide_true] using evalExpr_uint256_var_positive (cfg := config)
      (frame := {contract := contract, locals := locals, immutables := immStore v})
      evm (poolAmountName second) amount hget
  refine ExecBlock.consNormal (collectSubtract locals (immStore v) evm key second amount hget hposition) ?_
  exact ExecBlock.consRevert (poolTransferReverts v locals _ second recipient amount hrecipient hget hcall)

structure CollectValues (locals : Store) (recipient : AccountAddress)
    (lower upper key amount0 amount1 : UInt256) : Prop where
  recipient : locals.get? "recipient" = some (.address recipient)
  lower : locals.get? "tickLower" = some (.int (positionTick lower))
  upper : locals.get? "tickUpper" = some (.int (positionTick upper))
  amount0 : locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat))
  amount1 : locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat))
  position : locals.get? "position" = some (positionAlias key)
  slot0 : locals.get? "slot0" = none

theorem CollectValues.amount {locals : Store} {recipient : AccountAddress} {lower upper key a0 a1 : UInt256}
    (h : CollectValues locals recipient lower upper key a0 a1) (second : Bool) :
    locals.get? (poolAmountName second) = some (.int (Int.ofNat (if second then a1 else a0).toNat)) := by
  cases second
  · exact h.amount0
  · exact h.amount1

theorem collectAmounts_values (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (lower upper req0 req1 key amount0 amount1 : UInt256) :
    CollectValues (collectAmountsFrame v recipient lower upper req0 req1 key amount0 amount1).locals
      recipient lower upper key amount0 amount1 := by
  constructor <;> simp [collectAmountsFrame, collectPositionFrame, collectKeyFrame, collectInitFrame,
    collectLocals, Std.HashMap.getElem_insert]

theorem collectPaid_values {locals : Store} {recipient : AccountAddress}
    {lower upper key amount0 amount1 : UInt256} (h : CollectValues locals recipient lower upper key amount0 amount1)
    (second : Bool) :
    CollectValues (locals.insert (poolTransferCallName second) .unit) recipient lower upper key amount0 amount1 := by
  obtain ⟨hr, hl, hu, h0, h1, hp, hs⟩ := h
  simp only [Std.HashMap.get?_eq_getElem?] at hr hl hu h0 h1 hp hs
  cases second <;> constructor <;> simp_all [poolTransferCallName, Std.HashMap.getElem?_insert]

theorem collectFinish (locals imms : Store) (evm : EVM.State) (recipient : AccountAddress)
    (lower upper key amount0 amount1 : UInt256) (h : CollectValues locals recipient lower upper key amount0 amount1) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm (collectTransition.body.drop 11)
      (.returned {contract := contract, locals := locals, immutables := imms} (storeSlot0Unlocked evm true)
        (some [.int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)])) := by
  have hr := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) h.recipient
  have hl := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) h.lower
  have hu := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) h.upper
  have h0 := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) h.amount0
  have h1 := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) h.amount1
  refine ExecBlock.consNormal (ExecStmt.emit (vals := [.address evm.executionEnv.source,
    .address recipient, .int (positionTick lower), .int (positionTick upper),
    .int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)]) ?_) ?_
  · simp only [evalExprs?, hr, hl, hu, h0, h1, evalExpr?, envValue, bind, EvalResult.bind, pure]
  refine ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure])
    (assignSlot0Unlocked evm locals imms true h.slot0)) ?_
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have h0' := evalExpr_var_get (cfg := config) (evm := storeSlot0Unlocked evm true)
    (frame := {contract := contract, locals := locals, immutables := imms}) h.amount0
  have h1' := evalExpr_var_get (cfg := config) (evm := storeSlot0Unlocked evm true)
    (frame := {contract := contract, locals := locals, immutables := imms}) h.amount1
  simp only [evalExprs?, h0', h1', bind, EvalResult.bind, pure]

theorem collectAmountsPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    let locked := storeSlot0Unlocked evm false
    let key := positionKey evm.executionEnv.source lower upper
    ExecBlock config (collectFrame v recipient lower upper req0 req1) evm (collectTransition.body.take 9)
      (.ok (collectAmountsFrame v recipient lower upper req0 req1 key
        (minWord req0 (positionOwedWord key false locked.accountMap locked.executionEnv))
        (minWord req1 (positionOwedWord key true locked.accountMap locked.executionEnv))) locked) := by
  change ExecBlock _ _ _ (collectTransition.body.take 7 ++ (collectTransition.body.drop 7).take 2) _
  exact execBlock_append_ok (collectPositionPrefix v evm recipient lower upper req0 req1 hwv hunlocked)
    (collectAmounts v _ recipient lower upper req0 req1 _)

theorem collectSourceReturn (v : UniswapV3PoolImmutables) (evm evm0 evm1 evm2 : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 key amount0 amount1 : UInt256)
    (locals0 locals1 locals2 : Store)
    (hprefix : ExecBlock config (collectFrame v recipient lower upper req0 req1) evm (collectTransition.body.take 9)
      (.ok {contract := contract, locals := locals0, immutables := immStore v} evm0))
    (hpay0 : ExecStmt config {contract := contract, locals := locals0, immutables := immStore v} evm0
      (collectTokenStmt false) (.ok {contract := contract, locals := locals1, immutables := immStore v} evm1))
    (hpay1 : ExecStmt config {contract := contract, locals := locals1, immutables := immStore v} evm1
      (collectTokenStmt true) (.ok {contract := contract, locals := locals2, immutables := immStore v} evm2))
    (hvalues : CollectValues locals2 recipient lower upper key amount0 amount1) :
    ExecTransitionBody config contract evm (collectLocals recipient lower upper req0 req1) collectTransition.body
      (.returned {contract := contract, locals := locals2, immutables := immStore v} (storeSlot0Unlocked evm2 true)
        (some [.int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 9 collectTransition.body]
  exact execBlock_append_ok hprefix (ExecBlock.consNormal hpay0 (ExecBlock.consNormal hpay1
    (collectFinish locals2 (immStore v) evm2 recipient lower upper key amount0 amount1 hvalues)))

theorem collectSourceRevert0 (v : UniswapV3PoolImmutables) (evm evm0 : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256) (frame : Frame)
    (hprefix : ExecBlock config (collectFrame v recipient lower upper req0 req1) evm
      (collectTransition.body.take 9) (.ok frame evm0))
    (hpay0 : ExecStmt config frame evm0 (collectTokenStmt false) .reverted) :
    ExecTransitionBody config contract evm (collectLocals recipient lower upper req0 req1)
      collectTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 9 collectTransition.body]
  exact execBlock_append_ok hprefix (ExecBlock.consRevert hpay0)

theorem collectSourceRevert1 (v : UniswapV3PoolImmutables) (evm evm0 evm1 : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256) (frame0 frame1 : Frame)
    (hprefix : ExecBlock config (collectFrame v recipient lower upper req0 req1) evm
      (collectTransition.body.take 9) (.ok frame0 evm0))
    (hpay0 : ExecStmt config frame0 evm0 (collectTokenStmt false) (.ok frame1 evm1))
    (hpay1 : ExecStmt config frame1 evm1 (collectTokenStmt true) .reverted) :
    ExecTransitionBody config contract evm (collectLocals recipient lower upper req0 req1)
      collectTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 9 collectTransition.body]
  exact execBlock_append_ok hprefix (ExecBlock.consNormal hpay0 (ExecBlock.consRevert hpay1))

end Benchmarks.UniswapV3.Pool
