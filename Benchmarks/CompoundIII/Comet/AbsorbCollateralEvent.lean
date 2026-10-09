import Benchmarks.CompoundIII.Comet.AbsorbEventsMemory
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_080

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbCollateralEvent : Stmt :=
  .emit "AbsorbCollateral"
    [.var "absorber", .var "account", .var "asset", .var "seizeAmount", .var "value"]

theorem absorbCollateralEvent_source (frame : Frame) (evm : State)
    (absorber account asset : AccountAddress) (seized value : UInt256)
    (ha : frame.locals.get? "absorber" = some (.address absorber))
    (hb : frame.locals.get? "account" = some (.address account))
    (hc : frame.locals.get? "asset" = some (.address asset))
    (hn : frame.locals.get? "seizeAmount" = some (.int seized.toNat))
    (hv : frame.locals.get? "value" = some (.int value.toNat)) :
    ExecStmt config frame evm absorbCollateralEvent (.ok frame evm) := by
  apply ExecStmt.emit (vals := [.address absorber, .address account, .address asset,
    .int seized.toNat, .int value.toNat])
  simp only [evalExprs?, evalExpr?, ha, hb, hc, hn, hv, EvalResult.ofOption, pure,
    bind, EvalResult.bind]

theorem absorbCollateralEvent_memory {mem : ByteArray} {free seized value : UInt256}
    (hf : memLoad ⟨64⟩ mem = free) (hb : free.toNat + 32 < UInt256.size)
    (hn : seized.toNat < 2^128) :
    cometWithExtendedAssetList_block_17811_memory (mem := mem) (x1 := seized) (x2 := value) =
      pairEventMem mem free seized value := by
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128)) (UInt256.ofNat 1))
      seized = seized := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (bits := 128) rfl hn
  have ha : (free + UInt256.ofNat 32).toNat = free.toNat + 32 :=
    addWord_toNat free ⟨32⟩ hb
  simp only [cometWithExtendedAssetList_block_17811_memory, hmask,
    show memLoad (UInt256.ofNat 64) mem = free from hf, pairEventMem, ha, Reasoning.Theory.writeWord]

theorem cometAbsorbCollateralEvent {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw free delta seized value absorber account asset i assets reserved old oldPrincipal price : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024) (hp : ee.perm = true)
    (hf : memLoad ⟨64⟩ mem = free) (hb : free.toNat + 32 < UInt256.size)
    (hn : seized.toNat < 2^128)
    (h : RD (deployedRuntime v) ee g s0 ⟨17811⟩
      (delta :: seized :: value :: absorber :: account :: i :: assets :: reserved :: old ::
        oldPrincipal :: price :: account :: asset :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨17567⟩
      (i :: assets :: reserved :: old :: oldPrincipal :: price :: account :: delta :: R)
      (pairEventMem mem free seized value) aw' rdata σ k' C' := by
  have hr := cometWithExtendedAssetList_block_17811 (immWords := wordsOf (immStore v))
    hstack hp (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  rw [absorbCollateralEvent_memory hf hb hn] at hr
  exact ⟨_, _, _, hr⟩

end Benchmarks.CompoundIII.Comet
