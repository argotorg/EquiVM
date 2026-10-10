import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsLoop

/-! Initialization and the complete withdrawal-queue prefix of accrued fee calculation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def allocatedAccruedAssetsFrame (imms : Store) (ptr : UInt256) : Frame :=
  { contract := contract
    locals := (∅ : Store).insert cursorName (uint256Value ptr)
    immutables := imms }

def accruedAssetsZerosFrame (imms : Store) (ptr : UInt256) : Frame :=
  { allocatedAccruedAssetsFrame imms ptr with locals :=
    ((((allocatedAccruedAssetsFrame imms ptr).locals.insert "feeShares"
      (uint256Value ⟨0⟩)).insert "newTotalAssets" (uint256Value ⟨0⟩)).insert
      "newLostAssets" (uint256Value ⟨0⟩)).insert "realTotalAssets" (uint256Value ⟨0⟩) }

def accruedAssetsInitialFrame (imms : Store) (ptr : UInt256) : Frame :=
  { accruedAssetsZerosFrame imms ptr with locals :=
    (accruedAssetsZerosFrame imms ptr).locals.insert "i" (uint256Value ⟨0⟩) }

theorem accruedAssetsInitialLocals (v : MetaMorphoV1_1Immutables) (ptr : UInt256) :
    AccruedAssetsLocals v (accruedAssetsInitialFrame (immStore v) ptr) ⟨0⟩ ⟨0⟩ ptr := by
  constructor <;> simp [accruedAssetsInitialFrame, accruedAssetsZerosFrame,
    allocatedAccruedAssetsFrame, cursorName, Std.HashMap.getElem_insert]

structure AccruedAssetsTailLocals (v : MetaMorphoV1_1Immutables) (frame : Frame)
    (total ptr : UInt256) : Prop where
  contract : frame.contract = Benchmarks.Morpho.MetaMorphoV1_1.contract
  imms : frame.immutables = immStore v
  total : frame.locals.get? "realTotalAssets" = some (uint256Value total)
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)
  feeShares : frame.locals.get? "feeShares" = some (uint256Value ⟨0⟩)
  newTotal : frame.locals.get? "newTotalAssets" = some (uint256Value ⟨0⟩)
  newLost : frame.locals.get? "newLostAssets" = some (uint256Value ⟨0⟩)
  lastAssets : frame.locals.get? "lastTotalAssets" = none
  lostAssets : frame.locals.get? "lostAssets" = none
  fee : frame.locals.get? "fee" = none
  supply : frame.locals.get? "_totalSupply" = none

theorem accruedAssetsTailLocals {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {ptr ptr' i total : UInt256} (hl : AccruedAssetsLocals v frame i total ptr')
    (hp : AccruedAssetsPreserves (accruedAssetsInitialFrame (immStore v) ptr) frame) :
    AccruedAssetsTailLocals v frame total ptr' := by
  refine ⟨hl.contract, hl.imms, hl.total, hl.cursor, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [hp _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)] <;>
    simp [accruedAssetsInitialFrame, accruedAssetsZerosFrame,
      allocatedAccruedAssetsFrame, cursorName, Std.HashMap.getElem_insert]

theorem allocatedAccruedFeeAssetsFunction_loop :
    allocatedAccruedFeeAssetsFunction.body.drop 4 =
      .for [.letDecl "i" (some abiUInt256) (.intLit 0)] accruedAssetsCondition
        accruedAssetsPost accruedAssetsIteration ::
          allocatedAccruedFeeAssetsFunction.body.drop 5 := by
  conv_lhs => rw [allocatedAccruedFeeAssetsFunction_prefix]
  rfl

theorem accruedAssetsZerosSource (imms : Store) (ptr : UInt256) (evm : State) :
    ABlock config evm (allocatedAccruedAssetsFrame imms ptr)
      allocatedAccruedFeeAssetsFunction.body (accruedAssetsZerosFrame imms ptr)
      (allocatedAccruedFeeAssetsFunction.body.drop 4) := by
  refine ⟨fun h ↦ ?_⟩
  rw [allocatedAccruedFeeAssetsFunction_loop] at h
  rw [allocatedAccruedFeeAssetsFunction_prefix]
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl))
  exact h

theorem accruedAssetsInitSource (imms : Store) (ptr : UInt256) (evm : State) :
    ExecBlock config (accruedAssetsZerosFrame imms ptr) evm
      [.letDecl "i" (some abiUInt256) (.intLit 0)]
      (.ok (accruedAssetsInitialFrame imms ptr) evm) :=
  ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)) ExecBlock.nil

theorem accruedAssetsPrefixSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 35 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨12247⟩ (ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
      allocatedAccruedFeeAssetsFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (total ptr' : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      AccruedAssetsTailLocals v frame' total ptr' ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ 96 ≤ mem'.size ∧
      (∀ result, ExecBlock config frame' evm'
          (allocatedAccruedFeeAssetsFunction.body.drop 5) result →
        ExecBlock config (allocatedAccruedAssetsFrame (immStore v) ptr) evm
          allocatedAccruedFeeAssetsFunction.body result) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12296⟩
        ([UInt256.ofNat v.MORPHO.toNat, codeOwnerStorageWord I σ ⟨21⟩,
          codeOwnerStorageWord I σ ⟨21⟩, total, ret, ⟨0⟩] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12247_packed
    (immWords := wordsOf (immStore v)) (by omega) rd
  simp only [metaMorphoV1_1_block_12247_stack, wordsOf_immStore_MORPHO] at h1
  rcases accruedAssetsLoopSimulation v (codeOwnerStorageWord I σ ⟨21⟩).toNat
      (by simp only [List.length_cons]; omega) (accruedAssetsInitialLocals v ptr)
      hcalldata hfree hlo hmem hs rfl (by simp) h1 with
    ⟨hbad, hrev⟩ | ⟨evm', frame', total, ptr', mem', out, hs', hstore, hlocals, hpreserve,
      hfree', hlo', hmem', hloop, hdone⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    apply (accruedAssetsZerosSource (immStore v) ptr evm).run
    rw [allocatedAccruedFeeAssetsFunction_loop]
    exact ExecBlock.consRevert
      (ExecStmt.for (accruedAssetsInitSource (immStore v) ptr evm) hbad)
  · refine .inr ⟨evm', frame', total, ptr', mem', out, hs', hstore,
      accruedAssetsTailLocals hlocals hpreserve, hfree', hlo', hmem', ?_, hdone⟩
    intro result htail
    apply (accruedAssetsZerosSource (immStore v) ptr evm).run
    rw [allocatedAccruedFeeAssetsFunction_loop]
    exact ExecBlock.consNormal
      (ExecStmt.for (accruedAssetsInitSource (immStore v) ptr evm) hloop) htail

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
