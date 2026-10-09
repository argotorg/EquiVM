import Benchmarks.Morpho.MorphoBlue.LiquidateCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoLiquidatePrepareCall {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw fp id seized shares srcOff len : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 20 ≤ 1024)
    (hc : p.oracle.toNat < EVM.addressModulus) (hfree : memLoad (UInt256.ofNat 64) mem = fp)
    (horacle : memLoad (UInt256.ofNat 192) mem = p.oracle)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1470)
      (liquidateGuardTail id seized shares srcOff len R) mem aw out σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1545)
      ([gasArg, p.oracle, fp, UInt256.ofNat 4, fp, UInt256.ofNat 32, fp] ++
        liquidateGuardTail id seized shares srcOff len R)
      (writeWord mem fp.toNat oraclePriceSelectorWord) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_1470_packed (immWords := wordsOf (immStore v))
    (by change R.length + 15 ≤ 1024; omega) h
  dsimp only [morphoBlocks.morpho_block_1470_stack, morphoBlocks.morpho_block_1470_memory] at rd1
  change RD _ _ _ _ _
    ( _ :: UInt256.land (memLoad (UInt256.ofNat 192) mem) solcAddrMask :: memLoad (UInt256.ofNat 64) mem ::
      UInt256.ofNat 4 :: memLoad (UInt256.ofNat 64) mem :: UInt256.ofNat 32 ::
      memLoad (UInt256.ofNat 64) mem :: liquidateGuardTail id seized shares srcOff len R)
    (writeWord mem (memLoad (UInt256.ofNat 64) mem).toNat oraclePriceSelectorWord) _ _ _ _ _ at rd1
  rw [hfree, horacle, solcAddrMask_clean hc] at rd1
  exact ⟨_, a1, k1, C1, rd1⟩

end Benchmarks.Morpho.MorphoBlue
