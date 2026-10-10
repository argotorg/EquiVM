import Benchmarks.Morpho.MetaMorphoV1_1.SetCapReadersSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapFinishSimulation

/-! The enabled-market branch from its packed flag write through the queue event. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem setCapEnableSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params cap id ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 34 ≤ 1024)
    (hready : SetCapReady frame p id cap ptr) (himms : frame.immutables = immStore v)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hmem : ptr.toNat ≤ mem.size) (hparamslo : 96 ≤ params.toNat)
    (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hbytes : mem.readWithPadding params.toNat 160 = p.bytes)
    (hloads : MarketParamsLoads mem params p) (hs : SourceState s0 I σ evm)
    (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13658⟩
      ([params, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (setCapEnableBody.drop 3) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧ SetCapReady frame' p id cap cursor ∧
      ExecBlock config frame evm (setCapEnableBody.drop 3) (.ok frame' evm') ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨13576⟩
        ([id, cap, id, ret, solcMappingSlot ⟨13⟩ id] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  rcases frame with ⟨c, locals, imms⟩
  have hc := hready.contract
  dsimp only at hc himms
  subst c
  subst imms
  let frame : Frame := ⟨contract, locals, immStore v⟩
  let evm1 := setCapEnableState evm id
  let previous := codeOwnerStorageWord I (setCapEnableAccounts I σ id) ⟨22⟩
  let frame1 := setCapPreviousFrame frame previous
  have hs1 : SourceState s0 I (setCapEnableAccounts I σ id) evm1 :=
    setCapEnableState_source hs id
  have hready1 : SetCapReady frame1 p id cap ptr := hready.previous previous
  have hprevious :
      Solm.EVM.storageLoad (setCapEnableState evm id) evm.executionEnv.codeOwner ⟨22⟩ =
        previous := by
    simpa only [evm1, setCapEnableState_executionEnv] using hs1.storageRead ⟨22⟩
  have hprefix (result : ExecResult)
      (htail : ExecBlock config frame1 evm1 (setCapEnableBody.drop 5) result) :
      ExecBlock config frame evm (setCapEnableBody.drop 3) result := by
    apply setCapEnableAssignedPrefix hready
    rw [hprevious]
    exact htail
  have hargs : evalExprs? config frame1 evm1
      [.immutable "MORPHO", .var "marketParams", .env .this, .var cursorName] =
      .ok [.address v.MORPHO, p.value, .address I.codeOwner, uint256Value ptr] := by
    have hm : evalExpr? config frame1 evm1 (.immutable "MORPHO") =
        .ok (.address v.MORPHO) := evalImmutable_MORPHO _ _ _ _ _
    have he : evalExpr? config frame1 evm1 (.env .this) = .ok (.address I.codeOwner) := by
      simp only [evalExpr?, envValue, hs1.env, pure]
    simp only [evalExprs?, hm, he, evalExpr?, hready1.params, hready1.cursor,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
  obtain ⟨aw1, k1, C1, h1⟩ := setCapEnableRuntime v p (by omega) hbytes hperm rd
  rcases setCapSupplyAssetsSimulation v p hstack hcalldata hfree hlo hmem hparamslo
      hparams hbytes hloads hs1 h1 with
    ⟨hbad, hrev⟩ | ⟨evm2, final2, assets, ptr2, mem2, out2, hs2, _, hsource2,
      _, _, _, _, aw2, k2, C2, h2⟩
  · refine .inl ⟨hprefix _ ?_, hrev⟩
    exact ExecBlock.consRevert (internalCallFunctionRevert
      (callee := allocatedSupplyAssetsFunction) hargs allocatedSupplyAssetsFunction_lookup rfl hbad)
  have hcall := internalCallFunctionReturn (retVar := slotsAndCursorName)
    (callee := allocatedSupplyAssetsFunction) hargs allocatedSupplyAssetsFunction_lookup rfl hsource2
  let frame2 := cursorResultFrame frame1 "__c0" (uint256Value assets) ptr2
  have hready2 := hready1.reader assets ptr2
  have hp2 : frame2.locals.get? "previousTotalAssets" = some (uint256Value previous) := by
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact store_get_self _ _ _
  have ha2 : frame2.locals.get? "__c0" = some (uint256Value assets) :=
    cursorResultFrame_value _ _ _ _ (by decide)
  rcases setCapFinishSimulation v (by omega) hready2 hp2 ha2 hs2 hperm h2 with
    ⟨hbad, hrev⟩ | ⟨evm3, frame3, mem3, hs3, hready3, hsource3, aw3, k3, C3, h3⟩
  · refine .inl ⟨hprefix _ ?_, hrev⟩
    exact cursorCallPrefix (by decide) hcall hbad
  · refine .inr ⟨evm3, frame3, ptr2, mem3, out2, hs3, hready3, hprefix _ ?_,
      aw3, k3, C3, h3⟩
    exact cursorCallPrefix (by decide) hcall hsource3

end Benchmarks.Morpho.MetaMorphoV1_1
