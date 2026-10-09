import Benchmarks.Morpho.MorphoBlue.BorrowMathReach
import Benchmarks.Morpho.MorphoBlue.MarketTransferMathSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive BorrowMathRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account receiver : UInt256)
    (locals imms : Store) (evm : EVM.State) (σ : AccountMap) (mem : ByteArray) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (borrowTransition.body.drop 13) .reverted → RDrev (deployedRuntime v) g s0 →
      BorrowMathRefines v ee g s0 p account receiver locals imms evm σ mem R
  | ok {assets' shares' locals' aw' k' C' out'} :
      ABlock config evm { contract := contract, locals := locals, immutables := imms }
        (borrowTransition.body.drop 13) { contract := contract, locals := locals', immutables := imms }
        (borrowTransition.body.drop 14) → MarketTransferLocals p assets' shares' account receiver locals' →
      locals'.get? "__memory" = locals.get? "__memory" →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8538)
        (borrowUpdateTail p.id assets' shares' account receiver R)
        (twoWordHashMem p.id (UInt256.ofNat 3) mem) aw' out' σ k' C' →
      BorrowMathRefines v ee g s0 p account receiver locals imms evm σ mem R

theorem morphoBorrowMathRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw assets shares account receiver : UInt256} {out mem : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords)
    (locals imms : Store) (hstack : R.length + 30 ≤ 1024)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8491)
      (borrowAccrueTail p.id assets shares account receiver R) mem aw out σ k C) :
    BorrowMathRefines v ee g s0 p account receiver locals imms evm σ mem R := by
  by_cases hz : assets = ⟨0⟩
  · obtain ⟨a1, k1, C1, rd1⟩ := morphoBorrowReachAssets p hstack hz h
    by_cases hf : AssetsDownFits shares (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
    swap
    · exact .reverted (ExecBlock.consRevert (marketTransferMath_assetsReverts (evm := evm) ⟨2, by decide⟩ ⟨3, by decide⟩ hl hz
        (by simpa only [hs.env, ← hs.accounts] using hf)))
        (morphoAssetsDownReverts (v := v) (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) hf rd1)
    obtain ⟨k2, C2, rd2⟩ := morphoAssetsDownOk (v := v) (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
    have rd3 := morphoBlocks.morpho_block_8973 (immWords := wordsOf (immStore v))
      (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    obtain ⟨locals', he, hl', hm⟩ := marketTransferMath_assetsOk (imms := imms) (evm := evm) ⟨2, by decide⟩ ⟨3, by decide⟩ hl hz
      (by simpa only [hs.env, ← hs.accounts] using hf)
    rw [hs.env, ← hs.accounts] at hl'
    exact .ok ⟨fun ht ↦ ExecBlock.consNormal he ht⟩ hl' hm rd3
  · obtain ⟨a1, k1, C1, rd1⟩ := morphoBorrowReachShares p hstack hz h
    by_cases hf : SharesUpFits assets (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
    swap
    · exact .reverted (ExecBlock.consRevert (marketTransferMath_sharesReverts (evm := evm) ⟨2, by decide⟩ ⟨3, by decide⟩ hl hz
        (by simpa only [hs.env, ← hs.accounts] using hf)))
        (morphoSharesUpReverts (v := v) (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) hf rd1)
    obtain ⟨k2, C2, rd2⟩ := morphoSharesUpOk (v := v) (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
    have rd3 := morphoBlocks.morpho_block_8534 (immWords := wordsOf (immStore v))
      (by simp only [borrowAccrueTail, List.length_append, List.length_cons, List.length_nil, List.append]; omega) rd2
    obtain ⟨locals', he, hl', hm⟩ := marketTransferMath_sharesOk (imms := imms) (evm := evm) ⟨2, by decide⟩ ⟨3, by decide⟩ hl hz
      (by simpa only [hs.env, ← hs.accounts] using hf)
    rw [hs.env, ← hs.accounts] at hl'
    exact .ok ⟨fun ht ↦ ExecBlock.consNormal he ht⟩ hl' hm rd3

end Benchmarks.Morpho.MorphoBlue
