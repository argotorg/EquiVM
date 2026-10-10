import Benchmarks.UniswapV3.Pool.CollectProtocolSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def collectProtocolAdjustedAmount (amount fee : UInt256) : UInt256 :=
  if amount = fee then uint128Word (UInt256.sub amount ⟨1⟩) else amount

def collectProtocolAdjustLocals (locals : Store) (second : Bool) (amount fee : UInt256) : Store :=
  if amount = fee then locals.insert (poolAmountName second)
    (.int (Int.ofNat (collectProtocolAdjustedAmount amount fee).toNat)) else locals

def collectProtocolAdjustStmt (second : Bool) : Stmt :=
  .ite (.binary .eq (.var (poolAmountName second)) (protocolFeesExpr second))
    [.assign .localVar ⟨poolAmountName second, []⟩
      (.cast (.binary .sub (.var (poolAmountName second)) (.intLit 1))
        (.elem (.int (.uint ⟨128, by decide⟩))))] []

theorem collectProtocolAdjust (locals imms : Store) (evm : EVM.State)
    (second : Bool) (amount : UInt256)
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hbase : locals.get? "protocolFees" = none) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (collectProtocolAdjustStmt second)
      (.ok { contract := contract
             locals := collectProtocolAdjustLocals locals second amount
               (protocolFeesWord second evm.accountMap evm.executionEnv)
             immutables := imms } evm) := by
  have ha := evalExpr_var_get (cfg := config) (evm := evm) (frame :=
    {contract := contract, locals := locals, immutables := imms}) hget
  have hf := evalProtocolFeesWord locals imms evm second hbase
  have he := evalExpr_word_eq ha hf
  by_cases h : amount = protocolFeesWord second evm.accountMap evm.executionEnv
  · unfold collectProtocolAdjustStmt collectProtocolAdjustLocals collectProtocolAdjustedAmount
    rw [if_pos h, if_pos h]
    apply ExecStmt.iteTrue (by simpa only [h, decide_true] using he)
    refine ExecBlock.consNormal (ExecStmt.assign ?_ (assignLocalVarBase_frame hget)) ExecBlock.nil
    exact evalExpr_uint128Sub ha (show evalExpr? config _ evm (.intLit 1) =
      .ok (.int (Int.ofNat (⟨1⟩ : UInt256).toNat)) from by simp only [evalExpr?, pure]; decide +kernel)
  · unfold collectProtocolAdjustStmt collectProtocolAdjustLocals
    rw [if_neg h]
    exact ExecStmt.iteFalse (by simpa only [h, decide_false] using he) ExecBlock.nil

theorem collectProtocolAdjust_get (locals : Store) (second : Bool) (amount fee : UInt256)
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat))) :
    (collectProtocolAdjustLocals locals second amount fee).get? (poolAmountName second) =
      some (.int (Int.ofNat (collectProtocolAdjustedAmount amount fee).toNat)) := by
  by_cases h : amount = fee
  · simp [collectProtocolAdjustLocals, h]
  · simpa only [collectProtocolAdjustLocals, collectProtocolAdjustedAmount, if_neg h] using hget

theorem collectProtocolAdjust_get_other (locals : Store) (second : Bool) (amount fee : UInt256)
    (name : Ident) (hne : name ≠ poolAmountName second) :
    (collectProtocolAdjustLocals locals second amount fee).get? name = locals.get? name := by
  by_cases h : amount = fee <;>
    simp [collectProtocolAdjustLocals, h, Std.HashMap.getElem?_insert, Ne.symm hne]

theorem storeProtocolFee_uint128Word (evm : EVM.State) (second : Bool) (value : UInt256) :
    storeProtocolFee evm second (uint128Word value) = storeProtocolFee evm second value := by
  simp only [storeProtocolFee, protocolFeeUpdateWord, uint128Word_clean (uint128Word_lt value)]

def collectProtocolSubtractStmt (second : Bool) : Stmt :=
  .assign .storage ⟨"protocolFees", [.field (protocolFeesField second)]⟩
    (.cast (.binary .sub (protocolFeesExpr second) (.var (poolAmountName second)))
      (.elem (.int (.uint ⟨128, by decide⟩))))

def collectProtocolFeeState (evm : EVM.State) (second : Bool) (amount : UInt256) : EVM.State :=
  storeProtocolFee evm second (UInt256.sub (protocolFeesWord second evm.accountMap evm.executionEnv) amount)

theorem collectProtocolSubtract (locals imms : Store) (evm : EVM.State)
    (second : Bool) (amount : UInt256)
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hbase : locals.get? "protocolFees" = none) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (collectProtocolSubtractStmt second)
      (.ok {contract := contract, locals := locals, immutables := imms}
        (collectProtocolFeeState evm second amount)) := by
  have ha := evalExpr_var_get (cfg := config) (evm := evm) (frame :=
    {contract := contract, locals := locals, immutables := imms}) hget
  have hf := evalProtocolFeesWord locals imms evm second hbase
  simpa only [storeProtocolFee_uint128Word] using
    ExecStmt.assign (evalExpr_uint128Sub hf ha)
      (assignProtocolFee evm locals imms second
        (uint128Word (UInt256.sub (protocolFeesWord second evm.accountMap evm.executionEnv) amount)) hbase)

def collectProtocolTokenStmt (second : Bool) : Stmt :=
  .ite (.binary .gt (.var (poolAmountName second)) (.intLit 0))
    [collectProtocolAdjustStmt second, collectProtocolSubtractStmt second,
      poolTransferStmt second] []

theorem collectProtocolPayPrefix (locals imms : Store) (evm : EVM.State)
    (second : Bool) (amount : UInt256)
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hbase : locals.get? "protocolFees" = none) :
    let fee := protocolFeesWord second evm.accountMap evm.executionEnv
    let amount' := collectProtocolAdjustedAmount amount fee
    let locals' := collectProtocolAdjustLocals locals second amount fee
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      [collectProtocolAdjustStmt second, collectProtocolSubtractStmt second]
      (.ok {contract := contract, locals := locals', immutables := imms}
        (collectProtocolFeeState evm second amount')) := by
  dsimp only
  apply ExecBlock.consNormal (collectProtocolAdjust locals imms evm second amount hget hbase)
  refine ExecBlock.consNormal (collectProtocolSubtract _ imms evm second _
    (collectProtocolAdjust_get locals second amount _ hget) ?_) ExecBlock.nil
  rw [collectProtocolAdjust_get_other locals second amount _ "protocolFees"
    (by cases second <;> decide)]
  exact hbase

theorem collectProtocolTokenZero (locals imms : Store) (evm : EVM.State) (second : Bool)
    (hget : locals.get? (poolAmountName second) = some (.int 0)) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (collectProtocolTokenStmt second)
      (.ok {contract := contract, locals := locals, immutables := imms} evm) := by
  apply ExecStmt.iteFalse ?_ ExecBlock.nil
  have ha := evalExpr_var_get (cfg := config) (evm := evm) (frame :=
    {contract := contract, locals := locals, immutables := imms}) hget
  simp only [evalExpr?, ha, bind, EvalResult.bind, evalBinaryOp?, pure]
  rfl

theorem collectProtocolTokenPositive (locals imms : Store) (evm : EVM.State)
    (second : Bool) (amount : UInt256)
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hpos : 0 < amount.toNat) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.binary .gt (.var (poolAmountName second)) (.intLit 0)) = .ok (.bool true) := by
  have ha := evalExpr_var_get (cfg := config) (evm := evm) (frame :=
    {contract := contract, locals := locals, immutables := imms}) hget
  simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, hpos, decide_true] using
    evalExpr_word_gt ha (show evalExpr? config _ evm (.intLit 0) =
      .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) from by simp only [evalExpr?, pure]; decide +kernel)

theorem collectProtocolTokenReturns (v : UniswapV3PoolImmutables) (locals : Store)
    (evm evm' : EVM.State) (second : Bool) (recipient : AccountAddress) (amount : UInt256)
    (calleeFrame : Frame)
    (hrecipient : locals.get? "recipient" = some (.address recipient))
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hbase : locals.get? "protocolFees" = none) (hpos : 0 < amount.toNat)
    (hcall : ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient
      (collectProtocolAdjustedAmount amount (protocolFeesWord second evm.accountMap evm.executionEnv)))
      (collectProtocolFeeState evm second
        (collectProtocolAdjustedAmount amount (protocolFeesWord second evm.accountMap evm.executionEnv)))
      safeTransferFunction.body (.returned calleeFrame evm' none)) :
    let locals' := collectProtocolAdjustLocals locals second amount
      (protocolFeesWord second evm.accountMap evm.executionEnv)
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (collectProtocolTokenStmt second)
      (.ok { contract := contract
             locals := locals'.insert (poolTransferCallName second) .unit
             immutables := immStore v } evm') := by
  dsimp only
  apply ExecStmt.iteTrue (collectProtocolTokenPositive locals (immStore v) evm second amount hget hpos)
  change ExecBlock _ _ _ ([collectProtocolAdjustStmt second, collectProtocolSubtractStmt second] ++
    [poolTransferStmt second]) _
  apply execBlock_append_ok (collectProtocolPayPrefix locals (immStore v) evm second amount hget hbase)
  refine ExecBlock.consNormal (poolTransferReturns v _ _ evm' second recipient _ calleeFrame
    ?_ (collectProtocolAdjust_get locals second amount _ hget) hcall) ExecBlock.nil
  rw [collectProtocolAdjust_get_other locals second amount _ "recipient"
    (by cases second <;> decide)]
  exact hrecipient

theorem collectProtocolTokenReverts (v : UniswapV3PoolImmutables) (locals : Store)
    (evm : EVM.State) (second : Bool) (recipient : AccountAddress) (amount : UInt256)
    (hrecipient : locals.get? "recipient" = some (.address recipient))
    (hget : locals.get? (poolAmountName second) = some (.int (Int.ofNat amount.toNat)))
    (hbase : locals.get? "protocolFees" = none) (hpos : 0 < amount.toNat)
    (hcall : ExecFuncBody config (safeTransferFrame (immStore v) (poolToken v second) recipient
      (collectProtocolAdjustedAmount amount (protocolFeesWord second evm.accountMap evm.executionEnv)))
      (collectProtocolFeeState evm second
        (collectProtocolAdjustedAmount amount (protocolFeesWord second evm.accountMap evm.executionEnv)))
      safeTransferFunction.body .reverted) :
    ExecStmt config {contract := contract, locals := locals, immutables := immStore v} evm
      (collectProtocolTokenStmt second) .reverted := by
  apply ExecStmt.iteTrue (collectProtocolTokenPositive locals (immStore v) evm second amount hget hpos)
  change ExecBlock _ _ _ ([collectProtocolAdjustStmt second, collectProtocolSubtractStmt second] ++
    [poolTransferStmt second]) _
  apply execBlock_append_ok (collectProtocolPayPrefix locals (immStore v) evm second amount hget hbase)
  refine ExecBlock.consRevert (poolTransferReverts v _ _ second recipient _
    ?_ (collectProtocolAdjust_get locals second amount _ hget) hcall)
  rw [collectProtocolAdjust_get_other locals second amount _ "recipient"
    (by cases second <;> decide)]
  exact hrecipient

structure CollectProtocolValues (locals : Store) (recipient : AccountAddress)
    (amount0 amount1 : UInt256) : Prop where
  recipient : locals.get? "recipient" = some (.address recipient)
  amount0 : locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat))
  amount1 : locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat))
  fees : locals.get? "protocolFees" = none
  slot0 : locals.get? "slot0" = none

theorem collectProtocolAmounts_values (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (req0 req1 : UInt256) (owner : AccountAddress) (amount0 amount1 : UInt256) :
    CollectProtocolValues (collectProtocolAmountsFrame v recipient req0 req1 owner amount0 amount1).locals
      recipient amount0 amount1 := by
  constructor <;> simp [collectProtocolAmountsFrame, collectProtocolOwnerFrame, collectProtocolInitFrame,
    collectProtocolLocals, Std.HashMap.getElem_insert]

def collectProtocolPaidLocals (locals : Store) (second : Bool) (amount fee : UInt256) : Store :=
  (collectProtocolAdjustLocals locals second amount fee).insert (poolTransferCallName second) .unit

theorem collectProtocolPaid_values {locals : Store} {recipient : AccountAddress}
    {amount0 amount1 : UInt256} (h : CollectProtocolValues locals recipient amount0 amount1)
    (second : Bool) (fee : UInt256) :
    CollectProtocolValues
      (collectProtocolPaidLocals locals second (if second then amount1 else amount0) fee)
      recipient (if second then amount0 else collectProtocolAdjustedAmount amount0 fee)
      (if second then collectProtocolAdjustedAmount amount1 fee else amount1) := by
  obtain ⟨hr, h0, h1, hf, hs⟩ := h
  simp only [Std.HashMap.get?_eq_getElem?] at hr h0 h1 hf hs
  cases second
  · by_cases heq : amount0 = fee <;> constructor <;>
      simp_all [collectProtocolPaidLocals, collectProtocolAdjustLocals, poolAmountName,
        poolTransferCallName, collectProtocolAdjustedAmount, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem_insert]
  · by_cases heq : amount1 = fee <;> constructor <;>
      simp_all [collectProtocolPaidLocals, collectProtocolAdjustLocals, poolAmountName,
        poolTransferCallName, collectProtocolAdjustedAmount, Std.HashMap.getElem?_insert,
        Std.HashMap.getElem_insert]

theorem collectProtocolFinish (locals imms : Store) (evm : EVM.State)
    (recipient : AccountAddress) (amount0 amount1 : UInt256)
    (h : CollectProtocolValues locals recipient amount0 amount1) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (collectProtocolTransition.body.drop 11)
      (.returned {contract := contract, locals := locals, immutables := imms}
        (storeSlot0Unlocked evm true)
        (some [.int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)])) := by
  have hr := evalExpr_var_get (cfg := config) (evm := evm) (frame :=
    {contract := contract, locals := locals, immutables := imms}) h.recipient
  have h0 := evalExpr_var_get (cfg := config) (evm := evm) (frame :=
    {contract := contract, locals := locals, immutables := imms}) h.amount0
  have h1 := evalExpr_var_get (cfg := config) (evm := evm) (frame :=
    {contract := contract, locals := locals, immutables := imms}) h.amount1
  refine ExecBlock.consNormal (ExecStmt.emit (vals := [.address evm.executionEnv.source,
    .address recipient, .int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)]) ?_) ?_
  · simp only [evalExprs?, hr, h0, h1, evalExpr?, envValue, bind, EvalResult.bind, pure]
  refine ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure])
    (assignSlot0Unlocked evm locals imms true h.slot0)) ?_
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have h0' := evalExpr_var_get (cfg := config) (evm := storeSlot0Unlocked evm true) (frame :=
    {contract := contract, locals := locals, immutables := imms}) h.amount0
  have h1' := evalExpr_var_get (cfg := config) (evm := storeSlot0Unlocked evm true) (frame :=
    {contract := contract, locals := locals, immutables := imms}) h.amount1
  simp only [evalExprs?, h0', h1', bind, EvalResult.bind, pure]

theorem collectProtocolOwnerAmountsPrefix (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (owner : AccountAddress) (calleeFrame : Frame)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hfactory : ExecFuncBody config
      {contract := contract, locals := ∅, immutables := immStore v}
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body
      (.returned calleeFrame evm' (some [.address owner])))
    (howner : evm'.executionEnv.source = owner) :
    ExecBlock config (collectProtocolFrame v recipient req0 req1) evm (collectProtocolTransition.body.take 9)
      (.ok (collectProtocolAmountsFrame v recipient req0 req1 owner
        (minWord req0 (protocolFeesWord false evm'.accountMap evm'.executionEnv))
        (minWord req1 (protocolFeesWord true evm'.accountMap evm'.executionEnv))) evm') := by
  change ExecBlock _ _ _ (collectProtocolTransition.body.take 7 ++
    (collectProtocolTransition.body.drop 7).take 2) _
  exact execBlock_append_ok
    (collectProtocolOwnerPrefix v evm evm' recipient req0 req1 owner calleeFrame hwv hunlocked hfactory howner)
    (collectProtocolAmounts v evm' recipient req0 req1 owner)

theorem collectProtocolSourceReturn (v : UniswapV3PoolImmutables) (evm evm0 evm1 evm2 : EVM.State)
    (recipient : AccountAddress) (req0 req1 amount0 amount1 : UInt256) (locals0 locals1 locals2 : Store)
    (hprefix : ExecBlock config (collectProtocolFrame v recipient req0 req1) evm
      (collectProtocolTransition.body.take 9)
      (.ok {contract := contract, locals := locals0, immutables := immStore v} evm0))
    (hpay0 : ExecStmt config {contract := contract, locals := locals0, immutables := immStore v} evm0
      (collectProtocolTokenStmt false)
      (.ok {contract := contract, locals := locals1, immutables := immStore v} evm1))
    (hpay1 : ExecStmt config {contract := contract, locals := locals1, immutables := immStore v} evm1
      (collectProtocolTokenStmt true)
      (.ok {contract := contract, locals := locals2, immutables := immStore v} evm2))
    (hvalues : CollectProtocolValues locals2 recipient amount0 amount1) :
    ExecTransitionBody config contract evm (collectProtocolLocals recipient req0 req1)
      collectProtocolTransition.body
      (.returned {contract := contract, locals := locals2, immutables := immStore v}
        (storeSlot0Unlocked evm2 true)
        (some [.int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 9 collectProtocolTransition.body]
  apply execBlock_append_ok hprefix
  exact ExecBlock.consNormal hpay0 (ExecBlock.consNormal hpay1
    (collectProtocolFinish locals2 (immStore v) evm2 recipient amount0 amount1 hvalues))

theorem collectProtocolSourceRevert0 (v : UniswapV3PoolImmutables) (evm evm0 : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (frame0 : Frame)
    (hprefix : ExecBlock config (collectProtocolFrame v recipient req0 req1) evm
      (collectProtocolTransition.body.take 9) (.ok frame0 evm0))
    (hpay0 : ExecStmt config frame0 evm0 (collectProtocolTokenStmt false) .reverted) :
    ExecTransitionBody config contract evm (collectProtocolLocals recipient req0 req1)
      collectProtocolTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 9 collectProtocolTransition.body]
  exact execBlock_append_ok hprefix (ExecBlock.consRevert hpay0)

theorem collectProtocolSourceRevert1 (v : UniswapV3PoolImmutables) (evm evm0 evm1 : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (frame0 frame1 : Frame)
    (hprefix : ExecBlock config (collectProtocolFrame v recipient req0 req1) evm
      (collectProtocolTransition.body.take 9) (.ok frame0 evm0))
    (hpay0 : ExecStmt config frame0 evm0 (collectProtocolTokenStmt false) (.ok frame1 evm1))
    (hpay1 : ExecStmt config frame1 evm1 (collectProtocolTokenStmt true) .reverted) :
    ExecTransitionBody config contract evm (collectProtocolLocals recipient req0 req1)
      collectProtocolTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 9 collectProtocolTransition.body]
  exact execBlock_append_ok hprefix (ExecBlock.consNormal hpay0 (ExecBlock.consRevert hpay1))

theorem collectProtocolAdjustedAmount_lt (amount fee : UInt256) (h : amount.toNat < 2 ^ 128) :
    (collectProtocolAdjustedAmount amount fee).toNat < 2 ^ 128 := by
  unfold collectProtocolAdjustedAmount
  split
  · exact uint128Word_lt _
  · exact h

theorem collectProtocolAdjustedAmount_eq_sub (amount fee : UInt256)
    (heq : amount = fee) (hpos : 0 < amount.toNat) (h : amount.toNat < 2 ^ 128) :
    collectProtocolAdjustedAmount amount fee = UInt256.sub amount ⟨1⟩ := by
  rw [collectProtocolAdjustedAmount, if_pos heq]
  apply uint128Word_clean
  rw [usub_toNat (show (⟨1⟩ : UInt256).toNat ≤ amount.toNat from by change 1 ≤ _; omega)]
  exact lt_of_le_of_lt (Nat.sub_le _ _) h

end Benchmarks.UniswapV3.Pool
