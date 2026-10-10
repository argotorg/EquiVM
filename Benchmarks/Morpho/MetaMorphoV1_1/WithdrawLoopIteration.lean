import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopReaders
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopArithmeticSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopRoutines

/-! One complete withdrawal simulation iteration, including its early-exit branch. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem withdrawLoopIterationSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr i original assets total supply len : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 32 ≤ 1024)
    (hlocals : WithdrawLoopLocals v frame i assets ptr)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm) (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨21⟩).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨15998⟩
      ([UInt256.ofNat v.MORPHO.toNat, i, original, assets, total, supply, len] ++ R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm withdrawLoopIteration .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (assets' ptr' : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      WithdrawLoopLocals v frame' i assets' ptr' ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ ptr'.toNat < 2 ^ 64 ∧
      ptr'.toNat ≤ mem'.size ∧
      ExecBlock config frame evm withdrawLoopIteration
        (if assets' = ⟨0⟩ then .break frame' evm' else .ok frame' evm') ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0
        (if assets' = ⟨0⟩ then ⟨16091⟩ else ⟨16083⟩)
        ([i, UInt256.ofNat v.MORPHO.toNat, original, assets', total, supply, len] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  have hread := accruedAssetsQueueRead hlocals.contract hlocals.queue hlocals.index
    (by rw [hs.storageRead]; exact hbound)
  rw [hs.storageRead] at hread
  let id := accruedAssetsIdWord I σ i
  let frame1 := { frame with locals := frame.locals.insert "id" (wordBytes32Value id) }
  have hl1 := hlocals.insert "id" (wordBytes32Value id)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨aw1, k1, C1, h1⟩ := withdrawLoopQueueRoutine v
    (by simp only [List.append, List.length_cons]; omega) hbound rd
  rcases withdrawLoopReadersSimulation (frame := frame1) v
      (by simp only [List.append, List.length_cons]; omega) hl1.contract hl1.imms
      (store_get_self _ _ _) hl1.cursor hcalldata
      ((accruedAssetsQueueMemory_free hmem).trans hfree) hlo hs h1 with
    ⟨hbad, hrev⟩ | ⟨evm1, src, ptr1, shares, ptr2, ptr3, sa, ss, ba, params, market,
      mem1, out1, hs1, hstore1, hsource1, hfree1, hlo1, hhi1, hmem1, hload1,
      aw2, k2, C2, h2⟩
  · exact .inl ⟨ExecBlock.consNormal (ExecStmt.letDecl hread)
      (hbad withdrawLoopArithmetic), hrev⟩
  let balances := marketUpdatedBalancesValue market sa ss ba
  let frame2 := withdrawLoopBalancesFrame frame1 params ptr1 shares ptr2 ptr3 balances
  have hlp := hl1.reader "marketParams" (marketParamsValue params) ptr1
    (by decide) (by decide) (by decide)
  have hls := hlp.reader "supplyShares" (uint256Value shares) ptr2
    (by decide) (by decide) (by decide)
  have hl2 := hls.reader "__c2" balances ptr3 (by decide) (by decide) (by decide)
  have hp2 : frame2.locals.get? "marketParams" = some (marketParamsData params).value := by
    dsimp only [frame2]
    rw [withdrawLoopBalancesFrame,
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide),
      withdrawLoopSharesFrame,
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact cursorResultFrame_value _ _ _ _ (by decide)
  have hshares2 : frame2.locals.get? "supplyShares" = some (uint256Value shares) := by
    dsimp only [frame2]
    rw [withdrawLoopBalancesFrame,
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact cursorResultFrame_value _ _ _ _ (by decide)
  have hbalances2 : frame2.locals.get? "__c2" = some balances :=
    cursorResultFrame_value _ _ _ _ (by decide)
  rcases withdrawLoopArithmeticSimulation (frame := frame2) v (marketParamsData params)
      (by simp only [List.append, List.length_cons]; omega) hl2.contract hl2.imms hp2 hshares2
      hbalances2 hl2.cursor hfree1 hlo1 hhi1 hload1 hs1 h2 with
    ⟨hbad, hrev⟩ | ⟨evm2, liquid, ptr4, mem2, out2, hs2, hstore2, hsource2,
      hfree2, hlo2, hhi2, hmem2, aw3, k3, C3, h3⟩
  · exact .inl ⟨ExecBlock.consNormal (ExecStmt.letDecl hread)
      (hsource1 _ _ hbad), hrev⟩
  let frame3 := withdrawLoopLiquidFrame frame2 shares sa ss ba liquid ptr4
  have hl3 := (hl2.converted shares sa ss ba).reader "__c4" (uint256Value liquid) ptr4
    (by decide) (by decide) (by decide)
  have hliquid : frame3.locals.get? "__c4" = some (uint256Value liquid) :=
    cursorResultFrame_value _ _ _ _ (by decide)
  have hremaining := withdrawLoopRemainingSource (frame := frame3) (evm := evm2)
    hl3.contract hl3.assets hliquid
  obtain ⟨aw4, k4, C4, h4⟩ := withdrawLoopRemainingRoutine v
    (by simp only [List.append, List.length_cons]; omega) h3
  exact .inr ⟨evm2, withdrawLoopRemainingFrame frame3 assets liquid,
    withdrawRemainingWord assets liquid, ptr4, mem2, out2, hs2,
    accountStorageStateEq_trans hstore1 hstore2, hl3.remaining liquid,
    hfree2, hlo2, hhi2, hmem2, ExecBlock.consNormal (ExecStmt.letDecl hread)
      (hsource1 _ _ (hsource2 _ hremaining)), aw4, k4, C4, h4⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
