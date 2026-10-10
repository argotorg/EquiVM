import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoop

/-! The full allocated withdrawal simulation, up to the caller's final subtraction. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def simulateWithdrawFrame (imms : Store) (assets ptr : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert cursorName (uint256Value ptr)).insert "assets"
      (uint256Value assets)
    immutables := imms }

def simulateWithdrawInitialFrame (imms : Store) (assets ptr : UInt256) : Frame :=
  { simulateWithdrawFrame imms assets ptr with
    locals := (simulateWithdrawFrame imms assets ptr).locals.insert "i" (uint256Value ⟨0⟩) }

theorem simulateWithdrawInitialLocals (v : MetaMorphoV1_1Immutables) (assets ptr : UInt256) :
    WithdrawLoopLocals v (simulateWithdrawInitialFrame (immStore v) assets ptr) ⟨0⟩ assets ptr := by
  constructor <;> simp [simulateWithdrawInitialFrame, simulateWithdrawFrame, cursorName,
    Std.HashMap.getElem_insert]

theorem simulateWithdrawFunctionSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr assets supply total : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 32 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨15935⟩ (assets :: supply :: total :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (simulateWithdrawFrame (immStore v) assets ptr) evm
      allocatedSimulateWithdrawFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (final : Frame) (remaining cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      ExecFuncBody config (simulateWithdrawFrame (immStore v) assets ptr) evm
        allocatedSimulateWithdrawFunction.body
        (.returned final evm' (some [uint256Value remaining, uint256Value cursor])) ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ 96 ≤ mem'.size ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12234⟩
        ([assets, remaining, ⟨12410⟩, total, supply] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15935_packed
    (immWords := wordsOf (immStore v)) (by omega) rd
  simp only [metaMorphoV1_1_block_15935_stack, wordsOf_immStore_MORPHO] at h1
  rcases withdrawLoopSimulation v (codeOwnerStorageWord I σ ⟨21⟩).toNat hstack
      (simulateWithdrawInitialLocals v assets ptr) hcalldata hfree hlo hmem hs rfl
      (by simp) h1 with
    ⟨hbad, hrev⟩ | ⟨evm', final, i', remaining, cursor, mem', out, hs', hstore, hl,
      hfree', hlo', hmem', hloop, hdone⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedSimulateWithdrawFunction_body]
    apply ExecBlock.consRevert (ExecStmt.for ?_ hbad)
    exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
      (by simp only [evalExpr?, pure]; rfl)) ExecBlock.nil
  · refine .inr ⟨evm', final, remaining, cursor, mem', out, hs', hstore,
      ExecFuncBody.execBlockRet ?_, hfree', hlo', hmem', hdone⟩
    rw [allocatedSimulateWithdrawFunction_body]
    apply ExecBlock.consNormal (ExecStmt.for ?_ hloop)
    · apply ExecBlock.consReturn (ExecStmt.return ?_)
      simp only [evalExprs?, evalExpr?, hl.assets, hl.cursor, EvalResult.ofOption,
        bind, EvalResult.bind, pure]
    · exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
        (by simp only [evalExpr?, pure]; rfl)) ExecBlock.nil

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
