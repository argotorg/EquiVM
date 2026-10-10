import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositArithmeticSource
import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsUpRoutines

/-! The conversion and checked accumulation following the max-deposit market reads. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem maxDepositArithmeticSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares sa ss ba bs cap total morpho len ret i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 18 ≤ 1024)
    (hcontract : frame.contract = contract)
    (hbalances : frame.locals.get? "__c2" =
      some (.tuple [uint256Value sa, uint256Value ss, uint256Value ba, uint256Value bs]))
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hcap : frame.locals.get? "supplyCap" = some (uint256Value cap))
    (htotal : frame.locals.get? "totalSuppliable" = some (uint256Value total))
    (rd : RD (deployedRuntime v) I g s0 ⟨14037⟩
      ([bs, ba, ss, sa, shares, ⟨14045⟩, cap, total, ⟨14057⟩, ⟨1⟩, morpho, len, ret, i] ++ R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm maxDepositArithmetic .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm maxDepositArithmetic
      (.ok (maxDepositArithmeticFrame frame shares sa ss cap total) evm) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨14059⟩
        ([i, ⟨1⟩, morpho, len, ret, total + maxDepositGap shares sa ss cap] ++ R)
        mem aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14037_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hfit : assetsUpFits shares sa ss
  · obtain ⟨k2, C2, h2⟩ := assetsUpReturn v
      (by simp only [List.append, List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    obtain ⟨k3, C3, h3⟩ := maxDepositZeroFloorSub v
      (by simp only [List.append, List.length_cons]; omega) h2
    by_cases hsum : total.toNat + (maxDepositGap shares sa ss cap).toNat < UInt256.size
    · obtain ⟨k4, C4, h4⟩ := checkedAddReturn v
        (by simp only [List.append, List.length_cons]; omega) hsum
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
      obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_14057_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega) h4
      refine .inr ⟨?_, aw5, k5, C5, h5⟩
      apply (maxDepositTotalsPrefix hbalances).run
      apply ExecBlock.consNormal (maxDepositConversionSource hcontract hshares hfit)
      apply ExecBlock.consNormal (maxDepositGapSource hcontract hcap)
      exact ExecBlock.consNormal (maxDepositSumSource htotal hsum) ExecBlock.nil
    · refine .inl ⟨?_, checkedAddRevert v
        (by simp only [List.append, List.length_cons]; omega) (Nat.le_of_not_gt hsum) h3⟩
      apply (maxDepositTotalsPrefix hbalances).run
      apply ExecBlock.consNormal (maxDepositConversionSource hcontract hshares hfit)
      apply ExecBlock.consNormal (maxDepositGapSource hcontract hcap)
      exact ExecBlock.consRevert (maxDepositSumReverts htotal (Nat.le_of_not_gt hsum))
  · refine .inl ⟨?_, assetsUpRevert v
      (by simp only [List.append, List.length_cons]; omega) hfit h1⟩
    apply (maxDepositTotalsPrefix hbalances).run
    exact ExecBlock.consRevert (maxDepositConversionReverts hcontract hshares hfit)

theorem maxDepositArithmeticFrame_total (frame : Frame) (shares sa ss cap total : UInt256) :
    (maxDepositArithmeticFrame frame shares sa ss cap total).locals.get? "totalSuppliable" =
      some (uint256Value (total + maxDepositGap shares sa ss cap)) := store_get_self _ _ _

theorem maxDepositArithmeticFrame_preserves (frame : Frame) (shares sa ss cap total : UInt256)
    (name : Ident) (h0 : ("totalSupplyAssets" == name) = false)
    (h1 : ("totalSupplyShares" == name) = false) (h2 : ("supplyAssets" == name) = false)
    (h3 : ("__c4" == name) = false) (h4 : ("totalSuppliable" == name) = false) :
    (maxDepositArithmeticFrame frame shares sa ss cap total).locals.get? name =
      frame.locals.get? name := by
  rw [maxDepositArithmeticFrame, store_get_ne _ _ h4, maxDepositGapFrame,
    store_get_ne _ _ h3, maxDepositAssetsFrame, store_get_ne _ _ h2,
    maxDepositTotalsFrame_preserves _ _ _ _ h0 h1]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
