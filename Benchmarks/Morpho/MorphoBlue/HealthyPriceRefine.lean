import Benchmarks.Morpho.MorphoBlue.HealthyPriceRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive HealthyPriceRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account price : UInt256) (imms : Store) (evm : EVM.State)
    (mem : ByteArray) (ret : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecFuncBody config (healthyPriceFrame p account price imms) evm healthyPriceFunction.body .reverted →
      RDrev (deployedRuntime v) g s0 → HealthyPriceRefines v ee g s0 p account price imms evm mem ret R
  | ok {frame' σ aw out k C} (z : Bool) :
      ExecFuncBody config (healthyPriceFrame p account price imms) evm healthyPriceFunction.body
        (.returned frame' evm (some [.bool z])) → SourceState s0 ee σ evm →
      RD (deployedRuntime v) ee g s0 ret ((if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: R)
        (healthyPriceMem p.id account mem) aw out σ k C →
      HealthyPriceRefines v ee g s0 p account price imms evm mem ret R

theorem morphoHealthyPriceRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw account price ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (imms : Store)
    (hstack : R.length + 32 ≤ 1024) (hc : account.toNat < EVM.addressModulus)
    (hs : SourceState s0 ee σ evm) (hparams : p.InMemory (UInt256.ofNat 128) mem) (hsize : 288 ≤ mem.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14189)
      ([UInt256.ofNat 128, p.id, account, price, ret] ++ R) mem aw out σ k C) :
    HealthyPriceRefines v ee g s0 p account price imms evm mem ret R := by
  rcases morphoHealthyPriceRoutines p hstack hc hparams hsize hvalid h with ⟨hbad, hrev⟩ | ⟨hgood, a1, k1, C1, rd1⟩
  · exact .reverted (morphoHealthyPriceBodyReverts p account price imms evm hc
      (by simpa only [hs.env, ← hs.accounts] using hbad)) hrev
  · have he := morphoHealthyPriceBodyOk p account price imms evm hc
      (by simpa only [hs.env, ← hs.accounts] using hgood)
    rw [hs.env, ← hs.accounts] at he
    exact .ok _ he hs rd1

end Benchmarks.Morpho.MorphoBlue
