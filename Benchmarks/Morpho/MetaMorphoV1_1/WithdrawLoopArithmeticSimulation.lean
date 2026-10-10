import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopArithmeticSource
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawableSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsDownRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_073

/-! Share conversion and the actual liquidity call within one withdrawal-loop iteration. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem withdrawLoopArithmeticSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr src shares sa ss ba bs : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 14 ≤ 1024)
    (hcontract : frame.contract = contract) (himms : frame.immutables = immStore v)
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hbalances : frame.locals.get? "__c2" =
      some (.tuple [uint256Value sa, uint256Value ss, uint256Value ba, uint256Value bs]))
    (hcursor : frame.locals.get? cursorName = some (uint256Value ptr))
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hhi : ptr.toNat < 2 ^ 64)
    (hload : memLoad src mem = UInt256.ofNat p.loanToken.toNat)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨16053⟩
      ([bs, ba, ss, sa, shares, ⟨16063⟩, src, ⟨16069⟩] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm withdrawLoopArithmetic .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (liquid cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      (∀ outcome, ExecBlock config (withdrawLoopLiquidFrame frame shares sa ss ba liquid cursor)
        evm' (withdrawLoopArithmetic.drop 7) outcome →
        ExecBlock config frame evm withdrawLoopArithmetic outcome) ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ cursor.toNat < 2 ^ 64 ∧
      cursor.toNat ≤ mem'.size ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16069⟩
        (liquid :: R) mem' aw' out evm'.accountMap k' C' := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract himms hp hshares hbalances hcursor
  subst c
  subst imms
  let frame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  have htotals := withdrawLoopTotalsPrefix (frame := frame) (evm := evm) hbalances
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16053_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hfit : assetsDownFits shares sa ss
  swap
  · exact .inl ⟨htotals.run (ExecBlock.consRevert
        (withdrawLoopConversionReverts rfl hshares hfit)),
      assetsDownRevert v (by simp only [List.append, List.length_cons]; omega) hfit h1⟩
  obtain ⟨k2, C2, h2⟩ := assetsDownReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_16063_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  have hargs := withdrawLoopLiquidityArgs (frame := frame) (evm := evm)
    (shares := shares) (sa := sa) (ss := ss) (ba := ba) hp hcursor
  rcases withdrawableSimulation v p (by simp only [List.append]; omega) hfree hlo hhi hload hs
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3 with
    ⟨hbad, hrev⟩ | ⟨evm1, final1, liquid, cursor, mem1, out1,
      hs1, hstore1, hsource1, hfree1, hlo1, hhi1, hmem1, _, _, hdone⟩
  · refine .inl ⟨htotals.run ?_, hrev⟩
    apply ExecBlock.consNormal (withdrawLoopConversionSource rfl hshares hfit)
    exact ExecBlock.consRevert
      (internalCallFunctionRevert (callee := allocatedWithdrawableFunction) hargs rfl rfl hbad)
  have hcall := internalCallFunctionReturn (retVar := slotsAndCursorName)
    (name := allocatedWithdrawableFunction.name)
    (callee := allocatedWithdrawableFunction) hargs rfl rfl hsource1
  refine .inr ⟨evm1, liquid, cursor, mem1, out1, hs1, hstore1, ?_,
    hfree1, hlo1, hhi1, hmem1, hdone⟩
  intro outcome htail
  apply htotals.run
  apply ExecBlock.consNormal (withdrawLoopConversionSource rfl hshares hfit)
  exact cursorCallPrefix (by decide) hcall htail

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
