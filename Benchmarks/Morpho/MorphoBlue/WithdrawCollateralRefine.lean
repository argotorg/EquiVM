import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralUpdates
import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralAccrueRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoWithdrawCollateralRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {out : ByteArray} {aw assets account receiver : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus)
    (hr : receiver.toNat < EVM.addressModulus)
    (hl : CollateralTransferLocals p assets account receiver locals) (hs : SourceState s0 ee σ evm)
    (hac : locals.get? "__accrued" = some (.bool (accrueActive p evm)))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5620)
      (withdrawCollateralGuardTail p.id assets account receiver []) (withdrawCollateralGuardMem p ee account) aw out σ k C) :
    VoidBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (withdrawCollateralTransition.body.drop 10) := by
  have hf := morphoWithdrawCollateralAccrueRefine p locals imms (by decide) hc hl hac hs h
  cases hf with
  | reverted he hr => exact .reverted he hr
  | static he hr => exact .static he hr
  | @ok locals1 evm1 σ1 mem1 fp1 a1 out1 k1 C1 ab1 hl1 hg1 hs1 hm1 hlo1 hsize1 hparams1 hz1 rd1 =>
    exact (morphoWithdrawCollateralUpdates p locals1 imms hc ha hr hl1 hs1 hm1
      (by omega) (by omega) hg1 hz1 hparams1 rd1).prepend ab1

end Benchmarks.Morpho.MorphoBlue
