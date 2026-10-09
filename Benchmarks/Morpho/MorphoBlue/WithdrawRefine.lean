import Benchmarks.Morpho.MorphoBlue.WithdrawUpdates
import Benchmarks.Morpho.MorphoBlue.WithdrawAccrueRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoWithdrawRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {out : ByteArray} {aw assets shares account receiver : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus)
    (hr : receiver.toNat < EVM.addressModulus)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm)
    (hac : locals.get? "__accrued" = some (.bool (accrueActive p evm)))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7641)
      (withdrawAccrueTail p.id assets shares account receiver []) (withdrawGuardMem p ee account) aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (withdrawTransition.body.drop 11) withdrawTransition.returnType := by
  have hf := morphoWithdrawAccrueRefine p locals imms (by decide) hc hl hac hs h
  cases hf with
  | reverted he hr => exact .reverted he hr
  | static he hr => exact .static he hr
  | @ok locals1 evm1 σ1 mem1 fp1 a1 out1 k1 C1 ab1 hl1 hg1 hs1 hm1 hlo1 hsize1 hparams1 hz1 rd1 =>
    have hmth := morphoWithdrawMathRefine p locals1 imms (by decide) hl1 hs1 rd1
    cases hmth with
    | reverted he hr => exact .reverted (ab1.run he) hr
    | @ok assets2 shares2 locals2 a2 k2 C2 out2 ab2 hl2 hg2 rd2 =>
      have hm2 := hm1.hash p.id (UInt256.ofNat 3)
      have hp2 := (heapAdvance_hash mem1 fp1 p.id (UInt256.ofNat 3)).preserves
      have hz2 : memLoad (UInt256.ofNat 96) (twoWordHashMem p.id (UInt256.ofNat 3) mem1) = UInt256.ofNat 0 := by
        rw [memoryPrefix_memLoad hp2 (UInt256.ofNat 96) (by decide)
          (by change 128 ≤ fp1.toNat; omega) (by change 128 ≤ mem1.size; omega)]
        exact hz1
      have ht2 : memLoad (UInt256.ofNat 128) (twoWordHashMem p.id (UInt256.ofNat 3) mem1) = p.loanToken := by
        rw [memoryPrefix_memLoad hp2 (UInt256.ofNat 128) (by decide)
          (by change 160 ≤ fp1.toNat; omega) (by change 160 ≤ mem1.size; omega)]
        simpa only [MarketParamsWords.word, Nat.reduceMul, u256_add_zero] using hparams1 ⟨0, by decide⟩
      exact ((morphoWithdrawUpdates p locals2 imms hc ha hr hl2 hs1 hm2
        (by have hh := hp2.size; omega) (by omega) (hg2.trans hg1) hz2 ht2 rd2).prepend (StateBlock.ofABlock ab2)).prepend ab1

end Benchmarks.Morpho.MorphoBlue
