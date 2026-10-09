import Benchmarks.Morpho.MorphoBlue.LiquidateMathReach
import Benchmarks.Morpho.MorphoBlue.LiquidateScaleReach
import Benchmarks.Morpho.MorphoBlue.LiquidateLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateSeizedBody : List Stmt :=
  match liquidateTransition.body[17]! with | .ite _ yes _ => yes | _ => []
def liquidateSharesBody : List Stmt :=
  match liquidateTransition.body[17]! with | .ite _ _ no => no | _ => []

inductive LiquidateAmountRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (σ : AccountMap) (mem : ByteArray) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 17) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateAmountRefines v ee g s0 p account srcOff len data locals imms evm σ mem R
  | ok {seized' shares' locals' aw' out' k' C'} :
      ABlock config evm { contract := contract, locals := locals, immutables := imms }
        (liquidateTransition.body.drop 17) { contract := contract, locals := locals', immutables := imms }
        (liquidateTransition.body.drop 18) → LiquidateLocals p account seized' shares' data locals' →
      locals'.get? "__memory" = locals.get? "__memory" →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2057)
        (liquidateFinishMathTail p.id seized' shares' srcOff len R)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out' σ k' C' →
      LiquidateAmountRefines v ee g s0 p account srcOff len data locals imms evm σ mem R

end Benchmarks.Morpho.MorphoBlue
