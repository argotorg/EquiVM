import Benchmarks.Midnight.LiquidateScaleRoutines

/-! The two directions of liquidation's collateral/debt amount conversion. -/

open Ethereum

namespace Benchmarks.Midnight

def liquidateRepaidAmount (seized price lif : UInt256) : UInt256 :=
  mulDivUp (mulDivUp seized price liquidatePriceScale) lifScale lif

def liquidateSeizedAmount (repaid price lif : UInt256) : UInt256 :=
  mulDivDown (mulDivDown repaid lif lifScale) liquidatePriceScale price

def LiquidateSeizeSafe (seized price lif : UInt256) : Prop :=
  MulDivUpSafe seized price liquidatePriceScale ∧
    MulDivUpSafe (mulDivUp seized price liquidatePriceScale) lifScale lif

def LiquidateRepaySafe (repaid price lif : UInt256) : Prop :=
  repaid.toNat * lif.toNat < UInt256.size ∧
    (mulDivDown repaid lif lifScale).toNat * liquidatePriceScale.toNat < UInt256.size ∧ price ≠ ⟨0⟩

end Benchmarks.Midnight
