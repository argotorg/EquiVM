import Benchmarks.Morpho.MorphoBlue.HealthyPriceReach
import Benchmarks.Morpho.MorphoBlue.OraclePriceABI
import Benchmarks.Morpho.MorphoBlue.HeapWordWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoHealthyGuard {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw id account ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hc : account.toNat < EVM.addressModulus)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13948)
      ([UInt256.ofNat 128, id, account, ret] ++ R) mem aw out σ k C) :
    if positionFieldWord σ ee id account 1 = ⟨0⟩ then
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret (UInt256.ofNat 1 :: R)
        (supplyPositionMem id account mem) aw' out σ k' C'
    else
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14029)
        ([solcAddrMask, UInt256.ofNat 128, id, account, UInt256.ofNat 32, ret, UInt256.ofNat 0] ++ R)
        (supplyPositionMem id account mem) aw' out σ k' C' := by
  have hh1 : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 2) mem) =
      solcMappingSlot ⟨2⟩ id := twoWordHashMem_solcMappingSlot_any _ _ _
  have hmem : morphoBlocks.morpho_block_13948_taken_memory (mem := mem) (x1 := id) (x2 := account) =
      supplyPositionMem id account mem := by
    change twoWordHashMem (UInt256.land account solcAddrMask)
      (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (twoWordHashMem id (UInt256.ofNat 2) mem))
      (twoWordHashMem id (UInt256.ofNat 2) mem) = _
    rw [solcAddrMask_clean hc, hh1]
    rfl
  have hword : UInt256.land (solcSlotWordAt (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (morphoBlocks.morpho_block_13948_taken_memory (mem := mem) (x1 := id) (x2 := account)) + UInt256.ofNat 1) σ ee)
      (UInt256.ofNat 340282366920938463463374607431768211455) = positionFieldWord σ ee id account 1 := by
    rw [hmem, supplyPositionMem_hash]
    rfl
  dsimp only [morphoBlocks.morpho_block_13948_taken_memory] at hword
  by_cases hz : positionFieldWord σ ee id account 1 = ⟨0⟩
  · rw [if_pos hz]
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13948_taken_packed (immWords := wordsOf (immStore v))
      (by change R.length + 11 ≤ 1024; omega)
      (by change UInt256.isZero (UInt256.land (solcSlotWordAt _ σ ee) _) ≠ _; rw [hword, hz]; decide)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    rw [hmem] at rd1
    exact ⟨a1, _, _, morphoBlocks.morpho_block_14178 (immWords := wordsOf (immStore v)) (by omega) hvalid rd1⟩
  · rw [if_neg hz]
    obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13948_fallthrough_packed (immWords := wordsOf (immStore v))
      (by change R.length + 11 ≤ 1024; omega)
      (by change UInt256.isZero (UInt256.land (solcSlotWordAt _ σ ee) _) = _; rw [hword]; exact isZero_eq_zero_of_ne hz) h
    change RD _ _ _ _ _
      ([solcAddrMask, UInt256.ofNat 128, id, account, UInt256.ofNat 32, ret, UInt256.ofNat 0] ++ R)
      (morphoBlocks.morpho_block_13948_taken_memory (mem := mem) (x1 := id) (x2 := account)) _ _ _ _ _ at rd1
    rw [hmem] at rd1
    exact ⟨a1, k1, C1, rd1⟩

theorem morphoHealthyPrepareCall {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw fp id account ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (hstack : R.length + 20 ≤ 1024)
    (hc : p.oracle.toNat < EVM.addressModulus) (hfree : memLoad (UInt256.ofNat 64) mem = fp)
    (horacle : memLoad (UInt256.ofNat 192) mem = p.oracle)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14029)
      ([solcAddrMask, UInt256.ofNat 128, id, account, UInt256.ofNat 32, ret, UInt256.ofNat 0] ++ R) mem aw out σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14082)
      ([gasArg, p.oracle, fp, UInt256.ofNat 4, fp, UInt256.ofNat 32,
        fp, UInt256.ofNat 128, id, account, UInt256.ofNat 32, ret, UInt256.ofNat 0] ++ R)
      (writeWord mem fp.toNat oraclePriceSelectorWord) aw' out σ k' C' := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_14029_packed (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 12 ≤ 1024; omega) h
  dsimp only [morphoBlocks.morpho_block_14029_stack, morphoBlocks.morpho_block_14029_memory] at rd1
  change RD _ _ _ _ _
    ( _ :: UInt256.land (memLoad (UInt256.ofNat 192) mem) solcAddrMask :: memLoad (UInt256.ofNat 64) mem ::
      UInt256.ofNat 4 :: memLoad (UInt256.ofNat 64) mem :: UInt256.ofNat 32 ::
      memLoad (UInt256.ofNat 64) mem :: UInt256.ofNat 128 :: id :: account :: UInt256.ofNat 32 :: ret :: UInt256.ofNat 0 :: R)
    (writeWord mem (memLoad (UInt256.ofNat 64) mem).toNat oraclePriceSelectorWord) _ _ _ _ _ at rd1
  rw [hfree, horacle, solcAddrMask_clean hc] at rd1
  exact ⟨_, a1, k1, C1, rd1⟩

end Benchmarks.Morpho.MorphoBlue
