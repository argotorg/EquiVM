import Benchmarks.UniswapV3.Pool.OracleObserveExact

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleInterpolatedTick (before after : OracleObservation) (target : UInt256) : Int :=
  normalizeInt (.sint ⟨56, by decide⟩)
    (before.tickCumulative + normalizeInt (.sint ⟨56, by decide⟩)
      ((normalizeInt (.sint ⟨56, by decide⟩) (after.tickCumulative - before.tickCumulative)).tdiv
        (Int.ofNat (oracleDelta after.timestamp before.timestamp).toNat) *
        Int.ofNat (oracleDelta target before.timestamp).toNat))

def oracleInterpolatedSeconds (before after : OracleObservation) (target : UInt256) : Int :=
  normalizeInt (.uint ⟨160, by decide⟩)
    (Int.ofNat before.secondsPerLiquidity.toNat + normalizeInt (.uint ⟨160, by decide⟩)
      (normalizeInt (.uint ⟨256, by decide⟩)
        (normalizeInt (.uint ⟨256, by decide⟩)
          (normalizeInt (.uint ⟨160, by decide⟩)
            (Int.ofNat after.secondsPerLiquidity.toNat - Int.ofNat before.secondsPerLiquidity.toNat)) *
          Int.ofNat (oracleDelta target before.timestamp).toNat) /
        Int.ofNat (oracleDelta after.timestamp before.timestamp).toNat))

def oracleInterpolatedValues (before after : OracleObservation) (target : UInt256) : List Value :=
  [.int (oracleInterpolatedTick before after target),
    .int (oracleInterpolatedSeconds before after target)]

def oracleInterpolationTickExpr : Expr :=
  .cast (.binary .add (.field (.var "beforeOrAt") "tickCumulative")
    (.cast (.binary .mul
      (.binary .sdiv
        (.cast (.binary .sub (.field (.var "atOrAfter") "tickCumulative")
          (.field (.var "beforeOrAt") "tickCumulative")) (.elem (.int (.sint ⟨56, by decide⟩))))
        (.var "observationTimeDelta")) (.var "targetDelta"))
      (.elem (.int (.sint ⟨56, by decide⟩))))) (.elem (.int (.sint ⟨56, by decide⟩)))

def oracleInterpolationSecondsExpr : Expr :=
  .cast (.binary .add (.field (.var "beforeOrAt") "secondsPerLiquidityCumulativeX128")
    (.cast (.binary .div
      (.cast (.binary .mul
        (.cast (.cast (.binary .sub
          (.field (.var "atOrAfter") "secondsPerLiquidityCumulativeX128")
          (.field (.var "beforeOrAt") "secondsPerLiquidityCumulativeX128"))
            (.elem (.int (.uint ⟨160, by decide⟩)))) (.elem (.int (.uint ⟨256, by decide⟩))))
        (.var "targetDelta")) (.elem (.int (.uint ⟨256, by decide⟩))))
      (.var "observationTimeDelta")) (.elem (.int (.uint ⟨160, by decide⟩)))))
    (.elem (.int (.uint ⟨160, by decide⟩)))

def oracleInterpolationBlock : List Stmt :=
  [.letDecl "observationTimeDelta" (some (.elem (.int (.uint ⟨32, by decide⟩))))
    (.cast (.binary .sub (.field (.var "atOrAfter") "blockTimestamp")
      (.field (.var "beforeOrAt") "blockTimestamp")) (.elem (.int (.uint ⟨32, by decide⟩)))),
   .letDecl "targetDelta" (some (.elem (.int (.uint ⟨32, by decide⟩))))
    (.cast (.binary .sub (.var "target") (.field (.var "beforeOrAt") "blockTimestamp"))
      (.elem (.int (.uint ⟨32, by decide⟩)))),
   .return [oracleInterpolationTickExpr, oracleInterpolationSecondsExpr]]

theorem oracleInterpolationBranch : oracleObserveSingleFunction.body[7]! =
    .ite (.binary .eq (.var "target") (.field (.var "beforeOrAt") "blockTimestamp"))
      [.return [.field (.var "beforeOrAt") "tickCumulative",
        .field (.var "beforeOrAt") "secondsPerLiquidityCumulativeX128"]]
      [.ite (.binary .eq (.var "target") (.field (.var "atOrAfter") "blockTimestamp"))
        [.return [.field (.var "atOrAfter") "tickCumulative",
          .field (.var "atOrAfter") "secondsPerLiquidityCumulativeX128"]]
        oracleInterpolationBlock] := rfl

end Benchmarks.UniswapV3.Pool
