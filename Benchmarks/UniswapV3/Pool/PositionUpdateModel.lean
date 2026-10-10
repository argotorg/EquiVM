import Benchmarks.UniswapV3.Pool.PositionStruct
import Benchmarks.UniswapV3.Pool.LiquidityDeltaSource
import Benchmarks.UniswapV3.Pool.FullMathSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

structure PositionUpdateArgs where
  key : UInt256
  delta : Int
  growth0 : UInt256
  growth1 : UInt256

def PositionUpdateArgs.growth (a : PositionUpdateArgs) (second : Bool) : UInt256 :=
  if second then a.growth1 else a.growth0

def positionUpdateLiquidityWord (a : PositionUpdateArgs) (evm : EVM.State) : UInt256 :=
  positionFieldWord a.key 0 0 16 evm.accountMap evm.executionEnv

def positionUpdateLiquidityBefore (a : PositionUpdateArgs) (evm : EVM.State) : Int :=
  Int.ofNat (positionUpdateLiquidityWord a evm).toNat

def positionUpdateLiquidityNext (a : PositionUpdateArgs) (evm : EVM.State) : Int :=
  if a.delta = 0 then positionUpdateLiquidityBefore a evm
  else liquidityDeltaResult (positionUpdateLiquidityBefore a evm) a.delta

def positionUpdateLiquidityValid (a : PositionUpdateArgs) (evm : EVM.State) : Prop :=
  if a.delta = 0 then 0 < positionUpdateLiquidityBefore a evm
  else liquidityDeltaValid (positionUpdateLiquidityBefore a evm) a.delta

def positionUpdateFeeDelta (a : PositionUpdateArgs) (evm : EVM.State) (second : Bool) : UInt256 :=
  UInt256.sub (a.growth second)
    (positionFieldWord a.key (if second then 2 else 1) 0 32 evm.accountMap evm.executionEnv)

def positionUpdateFeeRaw (a : PositionUpdateArgs) (evm : EVM.State) (second : Bool) : UInt256 :=
  fullMathResult (positionUpdateFeeDelta a evm second) (positionUpdateLiquidityWord a evm)
    (UInt256.ofNat (2 ^ 128))

def positionUpdateOwed (a : PositionUpdateArgs) (evm : EVM.State) (second : Bool) : UInt256 :=
  uint128Word (positionUpdateFeeRaw a evm second)

theorem positionUpdateLiquidityWord_lt (a : PositionUpdateArgs) (evm : EVM.State) :
    (positionUpdateLiquidityWord a evm).toNat < 2 ^ 128 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

-- LIBRARY CANDIDATE: dividing a full product by at least one factor cannot overflow a word.
theorem fullMathValid_of_le_denominator (a b d : UInt256)
    (hd : 0 < d.toNat) (hb : b.toNat ≤ d.toNat) : fullMathValid a b d := by
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < UInt256.size)).2
  exact lt_of_le_of_lt (Nat.mul_le_mul_left a.toNat hb)
    (by simpa only [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right a.val.isLt hd)

theorem positionUpdateFeeValid (a : PositionUpdateArgs) (evm : EVM.State) (second : Bool) :
    fullMathValid (positionUpdateFeeDelta a evm second) (positionUpdateLiquidityWord a evm)
      (UInt256.ofNat (2 ^ 128)) :=
  fullMathValid_of_le_denominator _ _ _ (by decide)
    (by change (positionUpdateLiquidityWord a evm).toNat ≤ 2 ^ 128
        exact Nat.le_of_lt (positionUpdateLiquidityWord_lt a evm))

def positionUpdateFunction : FunctionDecl := contract.functions[45]!

theorem positionUpdateLookup : lookupCallable? contract "Position_update" =
    some positionUpdateFunction.toCallable := rfl

def positionUpdateLocals (a : PositionUpdateArgs) : Store :=
  let locals := (∅ : Store).insert "feeGrowthInside1X128" (.int (Int.ofNat a.growth1.toNat))
  let locals := locals.insert "feeGrowthInside0X128" (.int (Int.ofNat a.growth0.toNat))
  let locals := locals.insert "liquidityDelta" (.int a.delta)
  locals.insert "key" (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE a.key))

def positionUpdateFrame (imms : Store) (a : PositionUpdateArgs) : Frame :=
  {contract := contract, locals := positionUpdateLocals a, immutables := imms}

def positionUpdateAliasFrame (imms : Store) (a : PositionUpdateArgs) : Frame :=
  let locals := (positionUpdateLocals a).insert "self" (positionAlias a.key)
  {positionUpdateFrame imms a with locals := locals}

def positionUpdateSnapshotFrame (imms : Store) (a : PositionUpdateArgs) (evm : EVM.State) : Frame :=
  let locals := (positionUpdateAliasFrame imms a).locals.insert "_self"
    (positionStructValue a.key evm.accountMap evm.executionEnv)
  {positionUpdateAliasFrame imms a with locals := locals}

def positionUpdateZeroFrame (imms : Store) (a : PositionUpdateArgs) (evm : EVM.State) : Frame :=
  let locals := (positionUpdateSnapshotFrame imms a evm).locals.insert "liquidityNext" (.int 0)
  {positionUpdateSnapshotFrame imms a evm with locals := locals}

def positionUpdateAddFrame (imms : Store) (a : PositionUpdateArgs) (evm : EVM.State) : Frame :=
  let locals := (positionUpdateZeroFrame imms a evm).locals.insert "__c0"
    (.int (liquidityDeltaResult (positionUpdateLiquidityBefore a evm) a.delta))
  {positionUpdateZeroFrame imms a evm with locals := locals}

def positionUpdateLiquidityFrame (imms : Store) (a : PositionUpdateArgs) (evm : EVM.State) : Frame :=
  let frame := if a.delta = 0 then positionUpdateZeroFrame imms a evm
    else positionUpdateAddFrame imms a evm
  {frame with locals := frame.locals.insert "liquidityNext" (.int (positionUpdateLiquidityNext a evm))}

theorem positionUpdateBind (a : PositionUpdateArgs) :
    bindParams? positionUpdateFunction.params
      [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE a.key), .int a.delta,
       .int (Int.ofNat a.growth0.toNat), .int (Int.ofNat a.growth1.toNat)] =
      some (positionUpdateLocals a) := rfl

end Benchmarks.UniswapV3.Pool
