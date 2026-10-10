import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositLoop

/-! Complete simulation of the allocated internal max-deposit function. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def allocatedMaxDepositFrame (imms : Store) (ptr : UInt256) : Frame :=
  { contract := contract
    locals := (∅ : Store).insert cursorName (uint256Value ptr)
    immutables := imms }

def maxDepositInitialFrame (imms : Store) (ptr : UInt256) : Frame :=
  { allocatedMaxDepositFrame imms ptr with
    locals := ((allocatedMaxDepositFrame imms ptr).locals.insert "totalSuppliable"
      (uint256Value ⟨0⟩)).insert "i" (uint256Value ⟨0⟩) }

theorem maxDepositInitialLocals (v : MetaMorphoV1_1Immutables) (ptr : UInt256) :
    MaxDepositLocals v (maxDepositInitialFrame (immStore v) ptr) ⟨0⟩ ⟨0⟩ ptr := by
  constructor
  · rfl
  · rfl
  · exact store_get_self _ _ _
  · rw [maxDepositInitialFrame, store_get_ne _ _ (by decide), store_get_self]
  · rw [maxDepositInitialFrame, store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), allocatedMaxDepositFrame, store_get_self]
  · rw [maxDepositInitialFrame, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      allocatedMaxDepositFrame, store_get_ne _ _ (by decide)]
    simp only [store_get_empty]
  · rw [maxDepositInitialFrame, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      allocatedMaxDepositFrame, store_get_ne _ _ (by decide)]
    simp only [store_get_empty]

theorem allocatedMaxDepositFunction_lookup :
    lookupCallable? contract allocatedMaxDepositFunction.name =
      some allocatedMaxDepositFunction.toCallable := by rfl

theorem maxDepositFunctionSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 31 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13894⟩ (ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (allocatedMaxDepositFrame (immStore v) ptr) evm
      allocatedMaxDepositFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (total cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      ExecFuncBody config (allocatedMaxDepositFrame (immStore v) ptr) evm
        allocatedMaxDepositFunction.body
        (.returned frame' evm' (some [uint256Value total, uint256Value cursor])) ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ 96 ≤ mem'.size ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (total :: R)
        mem' aw' out evm'.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_13894_packed
    (immWords := wordsOf (immStore v)) (by omega) rd
  simp only [metaMorphoV1_1_block_13894_stack, wordsOf_immStore_MORPHO] at h1
  rcases maxDepositLoopSimulation v (codeOwnerStorageWord I σ ⟨20⟩).toNat hstack
      (maxDepositInitialLocals v ptr) hcalldata hfree hlo hmem hs rfl (by simp) hret h1 with
    ⟨hbad, hrev⟩ | ⟨evm', frame', total, cursor, mem', out, hs', hlocals,
      hfree', hlo', hmem', hloop, hdone⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedMaxDepositFunction_body]
    apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
      (by simp only [evalExpr?, pure]; rfl))
    apply ExecBlock.consRevert (ExecStmt.for ?_ hbad)
    exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
      (by simp only [evalExpr?, pure]; rfl)) ExecBlock.nil
  · refine .inr ⟨evm', frame', total, cursor, mem', out, hs',
      ExecFuncBody.execBlockRet ?_, hfree', hlo', hmem', hdone⟩
    rw [allocatedMaxDepositFunction_body]
    apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
      (by simp only [evalExpr?, pure]; rfl))
    apply ExecBlock.consNormal (ExecStmt.for ?_ hloop)
    · apply ExecBlock.consReturn (ExecStmt.return ?_)
      simp only [evalExprs?, evalExpr?, hlocals.total, hlocals.cursor, EvalResult.ofOption,
        bind, EvalResult.bind, pure]
    · exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
        (by simp only [evalExpr?, pure]; rfl)) ExecBlock.nil

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
