import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsState
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsQueueRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsDecoded
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyAssetsSimulation

/-! One complete iteration of the accrued-assets loop. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem accruedAssetsIterationSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr total len i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 33 ≤ 1024)
    (hlocals : AccruedAssetsLocals v frame i total ptr)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm) (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨21⟩).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨12447⟩
      ([UInt256.ofNat v.MORPHO.toNat, len, i, total] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm accruedAssetsIteration .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (total' ptr' : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      AccruedAssetsLocals v frame' i total' ptr' ∧ AccruedAssetsPreserves frame frame' ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ 96 ≤ mem'.size ∧
      ExecBlock config frame evm accruedAssetsIteration (.ok frame' evm') ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12521⟩
        ([total', ⟨1⟩, UInt256.ofNat v.MORPHO.toNat, len, i] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  rcases frame with ⟨cc, locals, imms⟩
  have hc := hlocals.contract
  have himms := hlocals.imms
  dsimp only at hc himms
  subst cc
  subst imms
  let frame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  have hread := accruedAssetsQueueRead hlocals.contract hlocals.queue hlocals.index
    (by rw [hs.storageRead]; exact hbound)
  rw [hs.storageRead] at hread
  have hargs1 : evalExprs? config frame evm
      [.storage ⟨"withdrawQueue", [.aindex (.var "i")]⟩, .var cursorName] =
      .ok [wordBytes32Value (accruedAssetsIdWord I σ i), uint256Value ptr] := by
    dsimp only [frame]
    simp only [evalExprs?, hread, evalExpr?, hlocals.cursor, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
    rfl
  obtain ⟨aw1, k1, C1, h1⟩ := accruedAssetsQueueRoutine v (by omega) hbound rd
  rcases marketParamsAllocationSimulation v
      (by simp only [List.append, List.length_cons]; omega)
      ((accruedAssetsQueueMemory_free hmem).trans hfree) hlo
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hs h1 with
    ⟨hbad, hrev⟩ | ⟨evm1, final1, params, mem1, src, ptr1, aw2, k2, C2,
      hsource1, hs1, hstore1, hparams, hfree1, hlo1, hhi1, hmem1, hsrc, hspan, hfields, h2⟩
  · exact .inl ⟨ExecBlock.consRevert (marketParamsReaderRevert hargs1 hbad), hrev⟩
  have hcall1 := marketParamsReaderCall (ret := slotsAndCursorName) hargs1 hsource1
  let frame1 := cursorResultFrame frame "__c0" (marketParamsValue params) ptr1
  have hl1 := hlocals.reader "__c0" (marketParamsValue params) ptr1
    (by decide) (by decide) (by decide)
  have hparams1 : frame1.locals.get? "__c0" = some (marketParamsData params).value :=
    cursorResultFrame_value _ _ _ _ (by decide)
  have hcursor1 : frame1.locals.get? cursorName = some (uint256Value ptr1) :=
    cursorResultFrame_cursor _ _ _ _
  have hargs2 : evalExprs? config frame1 evm1
      [.immutable "MORPHO", .var "__c0", .env .this, .var cursorName] =
      .ok [.address v.MORPHO, (marketParamsData params).value, .address I.codeOwner,
        uint256Value ptr1] := by
    have hm : evalExpr? config frame1 evm1 (.immutable "MORPHO") = .ok (.address v.MORPHO) :=
      evalImmutable_MORPHO _ _ _ _ _
    have he : evalExpr? config frame1 evm1 (.env .this) = .ok (.address I.codeOwner) := by
      simp only [evalExpr?, envValue, hs1.env, pure]
    simp only [evalExprs?, hm, he, evalExpr?, hparams1, hcursor1, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  have haddr : AccountAddress.ofNat (UInt256.ofNat v.MORPHO.val).toNat = v.MORPHO := by
    rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le v.MORPHO.isLt (by decide))]
    exact accountAddress_ofNat_toNat v.MORPHO
  rcases supplyAssetsSimulation v (marketParamsData params)
      (by simp only [List.append, List.length_cons]; omega) hcalldata hfree1 hlo1 hmem1 hsrc hspan
      (marketParamsBytes_of_fields hparams (by omega) (by change _ < 2 ^ 256; omega) hfields)
      (marketParamsLoads_of_fields hparams hfields) hs1
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2 with
    ⟨hbad, hrev⟩ | ⟨evm2, final2, assets, ptr2, mem2, out2, hs2, hstore2, hsource2,
      hfree2, hlo2, hhi2, hmem2, aw3, k3, C3, h3⟩
  · simp only [Fin.toNat, haddr] at hbad
    refine .inl ⟨?_, hrev⟩
    apply cursorCallPrefix (by decide) hcall1
    exact ExecBlock.consRevert
      (internalCallFunctionRevert (callee := allocatedSupplyAssetsFunction) hargs2
        allocatedSupplyAssetsFunction_lookup rfl hbad)
  simp only [Fin.toNat, haddr] at hsource2
  have hcall2 := internalCallFunctionReturn (retVar := slotsAndCursorName)
    (callee := allocatedSupplyAssetsFunction) hargs2
    allocatedSupplyAssetsFunction_lookup rfl hsource2
  let frame2 := cursorResultFrame frame1 "__c1" (uint256Value assets) ptr2
  have hl2 := hl1.reader "__c1" (uint256Value assets) ptr2 (by decide) (by decide) (by decide)
  have ha2 : frame2.locals.get? "__c1" = some (uint256Value assets) :=
    cursorResultFrame_value _ _ _ _ (by decide)
  obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_12515_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
  by_cases hfit : total.toNat + assets.toNat < UInt256.size
  · obtain ⟨k5, C5, h5⟩ := checkedAddReturn v
      (by simp only [List.append, List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
    refine .inr ⟨evm2, accruedAssetsTotalFrame frame2 total assets, total + assets, ptr2,
      mem2, out2, hs2, accountStorageStateEq_trans hstore1 hstore2, hl2.sum assets,
      ?_, hfree2, hlo2, by omega, ?_, aw4, k5, C5, h5⟩
    · exact (accruedAssetsReaderPreserves frame "__c0" _ ptr1 (.inl rfl)).trans
        ((accruedAssetsReaderPreserves frame1 "__c1" _ ptr2 (.inr rfl)).trans
          (accruedAssetsSumPreserves frame2 total assets))
    · apply cursorCallPrefix (by decide) hcall1
      apply cursorCallPrefix (by decide) hcall2
      exact ExecBlock.consNormal (accruedAssetsSumSource hl2.total ha2 hfit) ExecBlock.nil
  · refine .inl ⟨?_, checkedAddRevert v (by simp only [List.append, List.length_cons]; omega)
      (Nat.le_of_not_gt hfit) h4⟩
    apply cursorCallPrefix (by decide) hcall1
    apply cursorCallPrefix (by decide) hcall2
    exact ExecBlock.consRevert (accruedAssetsSumReverts hl2.total ha2 (Nat.le_of_not_gt hfit))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
