import Benchmarks.Morpho.MorphoBlue.WithdrawMathReach
import Benchmarks.Morpho.MorphoBlue.MarketTransferMathSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive WithdrawMathRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account receiver : UInt256)
    (locals imms : Store) (evm : EVM.State) (σ : AccountMap) (mem : ByteArray) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (withdrawTransition.body.drop 13) .reverted → RDrev (deployedRuntime v) g s0 →
      WithdrawMathRefines v ee g s0 p account receiver locals imms evm σ mem R
  | ok {assets' shares' locals' aw' k' C' out'} :
      ABlock config evm { contract := contract, locals := locals, immutables := imms }
        (withdrawTransition.body.drop 13) { contract := contract, locals := locals', immutables := imms }
        (withdrawTransition.body.drop 14) → MarketTransferLocals p assets' shares' account receiver locals' →
      locals'.get? "__memory" = locals.get? "__memory" →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7737)
        (withdrawUpdateTail p.id assets' shares' account receiver R)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out' σ k' C' →
      WithdrawMathRefines v ee g s0 p account receiver locals imms evm σ mem R

theorem morphoWithdrawMathRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw assets shares account receiver : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords)
    (locals imms : Store) (hstack : R.length + 28 ≤ 1024)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 7651)
      (withdrawAccrueTail p.id assets shares account receiver R) mem aw out σ k C) :
    WithdrawMathRefines v ee g s0 p account receiver locals imms evm σ mem R := by
  by_cases hz : assets = ⟨0⟩
  · obtain ⟨a1, k1, C1, rd1⟩ := morphoWithdrawReachAssets p hstack hz h
    by_cases hf : AssetsDownFits shares (marketFieldWord σ ee p.id 0) (marketFieldWord σ ee p.id 1)
    swap
    · exact .reverted (ExecBlock.consRevert (marketTransferMath_assetsReverts (evm := evm) ⟨0, by decide⟩ ⟨1, by decide⟩ hl hz
        (by simpa only [hs.env, ← hs.accounts] using hf)))
        (morphoAssetsDownReverts (v := v) (by change R.length + 12 + 12 ≤ 1024; omega) hf rd1)
    obtain ⟨k2, C2, rd2⟩ := morphoAssetsDownOk (v := v) (by change R.length + 12 + 12 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
    have rd3 := morphoBlocks.morpho_block_8097 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 14 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    obtain ⟨locals', he, hl', hm⟩ := marketTransferMath_assetsOk (imms := imms) (evm := evm) ⟨0, by decide⟩ ⟨1, by decide⟩ hl hz
      (by simpa only [hs.env, ← hs.accounts] using hf)
    rw [hs.env, ← hs.accounts] at hl'
    exact .ok ⟨fun ht ↦ ExecBlock.consNormal he ht⟩ hl' hm rd3
  · obtain ⟨a1, k1, C1, rd1⟩ := morphoWithdrawReachShares p hstack hz h
    by_cases hf : SharesUpFits assets (marketFieldWord σ ee p.id 0) (marketFieldWord σ ee p.id 1)
    swap
    · exact .reverted (ExecBlock.consRevert (marketTransferMath_sharesReverts (evm := evm) ⟨0, by decide⟩ ⟨1, by decide⟩ hl hz
        (by simpa only [hs.env, ← hs.accounts] using hf)))
        (morphoSharesUpReverts (v := v) (by change R.length + 13 + 14 ≤ 1024; omega) hf rd1)
    obtain ⟨k2, C2, rd2⟩ := morphoSharesUpOk (v := v) (by change R.length + 13 + 14 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
    have rd3 := morphoBlocks.morpho_block_7735 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 12 ≤ 1024; omega) rd2
    obtain ⟨locals', he, hl', hm⟩ := marketTransferMath_sharesOk (imms := imms) (evm := evm) ⟨0, by decide⟩ ⟨1, by decide⟩ hl hz
      (by simpa only [hs.env, ← hs.accounts] using hf)
    rw [hs.env, ← hs.accounts] at hl'
    exact .ok ⟨fun ht ↦ ExecBlock.consNormal he ht⟩ hl' hm rd3

end Benchmarks.Morpho.MorphoBlue
