import Benchmarks.Midnight.LiquidateConversion
import Benchmarks.Midnight.HealthArithmeticTrace
import Benchmarks.Midnight.ZeroFloorSub

/-! The remaining collateral's recoverable debt, rounded down before the threshold check. -/

open Ethereum

namespace Benchmarks.Midnight

def liquidateRecoverable (collateral price lif : UInt256) : UInt256 :=
  mulDivDown (mulDivDown collateral price liquidatePriceScale) lifScale lif

def LiquidateRecoverableSafe (collateral price lif : UInt256) : Prop :=
  collateral.toNat * price.toNat < UInt256.size ∧
    (mulDivDown collateral price liquidatePriceScale).toNat * lifScale.toNat < UInt256.size ∧
    lif ≠ ⟨0⟩

end Benchmarks.Midnight
