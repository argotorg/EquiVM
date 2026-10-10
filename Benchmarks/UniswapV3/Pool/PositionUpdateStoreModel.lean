import Benchmarks.UniswapV3.Pool.PositionUpdateModel
import Benchmarks.UniswapV3.Pool.PositionScalarStorage
import Benchmarks.UniswapV3.Pool.FlashProtocolWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def positionUpdateLiquidityState (a : PositionUpdateArgs) (evm : EVM.State) : EVM.State :=
  if a.delta = 0 then evm
  else positionLiquidityState evm a.key (EVM.wordOfInt (positionUpdateLiquidityNext a evm))

def positionUpdateGrowthState (a : PositionUpdateArgs) (evm : EVM.State) : EVM.State :=
  positionLastState (positionLastState (positionUpdateLiquidityState a evm) a.key false a.growth0)
    a.key true a.growth1

def positionUpdateOwedState (a : PositionUpdateArgs) (original current : EVM.State)
    (second : Bool) : EVM.State :=
  storePositionOwed current a.key second
    (positionOwedWord a.key second current.accountMap current.executionEnv +
      positionUpdateOwed a original second)

def positionUpdateHasFees (a : PositionUpdateArgs) (evm : EVM.State) : Bool :=
  decide (0 < (positionUpdateOwed a evm false).toNat) ||
    decide (0 < (positionUpdateOwed a evm true).toNat)

def positionUpdateFinalState (a : PositionUpdateArgs) (evm : EVM.State) : EVM.State :=
  let updated := positionUpdateGrowthState a evm
  if positionUpdateHasFees a evm then
    positionUpdateOwedState a evm (positionUpdateOwedState a evm updated false) true
  else updated

def positionUpdateOwedStmt (second : Bool) : Stmt :=
  .assign .storage ⟨"self", [.field (positionOwedField second)]⟩
    (.cast (.binary .add (.storage ⟨"self", [.field (positionOwedField second)]⟩)
      (.var (positionOwedField second))) (.elem (.int (.uint ⟨128, by decide⟩))))

theorem positionUpdateOwedSource (locals imms : Store) (original current : EVM.State)
    (a : PositionUpdateArgs) (second : Bool)
    (hself : locals.get? "self" = some (positionAlias a.key))
    (howed : locals.get? (positionOwedField second) =
      some (.int (Int.ofNat (positionUpdateOwed a original second).toNat))) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} current
      (positionUpdateOwedStmt second)
      (.ok {contract := contract, locals := locals, immutables := imms}
        (positionUpdateOwedState a original current second)) := by
  have hs := evalPositionAliasOwed locals imms current "self" a.key second hself
  have ho := evalExpr_var_get (cfg := config) (evm := current)
    (frame := {contract := contract, locals := locals, immutables := imms}) howed
  have he : evalExpr? config {contract := contract, locals := locals, immutables := imms} current
      (.cast (.binary .add (.storage ⟨"self", [.field (positionOwedField second)]⟩)
        (.var (positionOwedField second))) (.elem (.int (.uint ⟨128, by decide⟩)))) =
      .ok (.int (Int.ofNat (uint128Word
        (positionOwedWord a.key second current.accountMap current.executionEnv +
          positionUpdateOwed a original second)).toNat)) := by
    simp only [evalExpr?, hs, ho, bind, EvalResult.bind, castValue?, evalBinaryOp?,
      uint128_add_cast, EvalResult.ofOption]
  have hstore (value : UInt256) : storePositionOwed current a.key second (uint128Word value) =
      storePositionOwed current a.key second value := by
    simp only [storePositionOwed, protocolFeeUpdateWord, uint128Word_clean (uint128Word_lt value)]
  simpa only [positionUpdateOwedState, hstore] using ExecStmt.assign he
    (assignPositionAliasOwed locals imms current "self" a.key second
      (uint128Word (positionOwedWord a.key second current.accountMap current.executionEnv +
        positionUpdateOwed a original second)) hself)

theorem positionUpdateLiquidityState_executionEnv (a : PositionUpdateArgs) (evm : EVM.State) :
    (positionUpdateLiquidityState a evm).executionEnv = evm.executionEnv := by
  unfold positionUpdateLiquidityState
  split_ifs
  · rfl
  · exact positionLiquidityState_executionEnv _ _ _

theorem positionUpdateGrowthState_executionEnv (a : PositionUpdateArgs) (evm : EVM.State) :
    (positionUpdateGrowthState a evm).executionEnv = evm.executionEnv := by
  simp only [positionUpdateGrowthState, positionLastState_executionEnv,
    positionUpdateLiquidityState_executionEnv]

theorem positionUpdateOwedState_executionEnv (a : PositionUpdateArgs) (original current : EVM.State)
    (second : Bool) : (positionUpdateOwedState a original current second).executionEnv =
      current.executionEnv := storePositionOwed_executionEnv _ _ _ _

theorem positionUpdateFinalState_executionEnv (a : PositionUpdateArgs) (evm : EVM.State) :
    (positionUpdateFinalState a evm).executionEnv = evm.executionEnv := by
  unfold positionUpdateFinalState
  split_ifs <;> simp only [positionUpdateOwedState_executionEnv,
    positionUpdateGrowthState_executionEnv]

end Benchmarks.UniswapV3.Pool
