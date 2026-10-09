import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralHealthGuard
import Benchmarks.Morpho.MorphoBlue.VoidBlockRefines
import Benchmarks.Morpho.MorphoBlue.SafeTransferFunctionRefine
import Benchmarks.Morpho.MorphoBlue.SafeTransferInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem collateralTransfer_args {p assets account receiver locals}
    (hl : CollateralTransferLocals p assets account receiver locals) (imms : Store) (evm : EVM.State) (ptr : UInt256)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat))) :
    evalExprs? config { contract := contract, locals := locals, immutables := imms } evm
      [.tupleGet (.var "marketParams") 1, .var "receiver", .var "assets", .var "__memory"] =
      .ok (safeTransferArgs false (AccountAddress.ofNat p.collateralToken.toNat)
        evm.executionEnv.source (AccountAddress.ofNat receiver.toNat) assets ptr.toNat) := by
  have ht : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.tupleGet (.var "marketParams") 1) = .ok (.address (AccountAddress.ofNat p.collateralToken.toNat)) := by
    simp only [evalExpr?, hl.evalParams, MarketParamsWords.value, tupleGetValue?,
      EvalResult.bind, EvalResult.ofOption, bind]
    rfl
  simp only [evalExprs?, ht, hl.evalAssets, hl.evalReceiver, evalExpr?, envValue, hget,
    EvalResult.ofOption, pure, bind, EvalResult.bind]
  rfl

theorem collateralTransferEmit {p assets account receiver locals}
    (hl : CollateralTransferLocals p assets account receiver locals) (imms : Store) (evm : EVM.State) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      withdrawCollateralTransition.body[17]!
      (.ok { contract := contract, locals := locals, immutables := imms } evm) := by
  apply ExecStmt.emit
  change evalExprs? config _ _ [.var "id", .env .caller, .var "onBehalf", .var "receiver", .var "assets"] = _
  simp only [evalExprs?, hl.evalId imms evm, hl.evalAccount imms evm, hl.evalReceiver imms evm,
    hl.evalAssets imms evm, evalExpr?, envValue, EvalResult.bind, bind, pure]
  rfl

theorem morphoWithdrawCollateralTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw fp assets account receiver : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (z : Bool) (hc : p.Canonical)
    (hr : receiver.toNat < EVM.addressModulus)
    (hl : CollateralTransferLocals p assets account receiver locals) (hs : SourceState s0 ee σ evm) (hp : ee.perm = true)
    (hm : MorphoHeap mem fp 320) (hsize : 192 ≤ mem.size) (hptr : 192 ≤ fp.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 64))))
    (hz : locals.get? "__c4" = some (.bool z))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 160) mem = p.collateralToken)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5693)
      ((if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: UInt256.ofNat 5701 ::
        withdrawCollateralHealthTail p.id assets account receiver []) mem aw out σ k C) :
    VoidBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (withdrawCollateralTransition.body.drop 16) := by
  have hez : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "__c4") = .ok (.bool z) := by simp only [evalExpr?, hz, EvalResult.ofOption]
  have hcheck := morphoWithdrawCollateralHealthCheck (v := v) z (by change 34 ≤ 1024; decide) hm
    (by have hh := hm.space; omega) h
  cases z
  · exact .reverted (ExecBlock.consRevert (ExecStmt.requireFalse hez)) hcheck
  obtain ⟨a1, k1, C1, rd1, hm1, had1⟩ := hcheck
  have ab : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
      (withdrawCollateralTransition.body.drop 16) { contract := contract, locals := locals, immutables := imms } evm
      (withdrawCollateralTransition.body.drop 18) :=
    (StateBlock.start.step (ExecStmt.requireTrue hez)).step (collateralTransferEmit hl imms evm)
  obtain ⟨hm2, hp2⟩ := hm1.twoWordEvent (by decide) (UInt256.ofNat ee.source.val) assets
  have hpref := had1.preserves.trans (hp2.mono (by rw [had1.cursor]; omega))
  let mem2 := twoWordEventMem (morphoHealthMem mem) (fp + UInt256.ofNat 64) (UInt256.ofNat ee.source.val) assets
  have hz1 : memLoad (UInt256.ofNat 96) mem2 = UInt256.ofNat 0 := by
    rw [memoryPrefix_memLoad hpref _ (by decide) (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)]
    exact hzero
  have ht1 : memLoad (UInt256.ofNat 160) mem2 = p.collateralToken := by
    rw [memoryPrefix_memLoad hpref (UInt256.ofNat 160) (by decide) hptr hsize]
    exact htoken
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_5701_packed (immWords := wordsOf (immStore v))
    (by change 14 ≤ 1024; decide) hp (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  dsimp only [morphoBlocks.morpho_block_5701_stack, morphoBlocks.morpho_block_5701_memory] at rd2
  rw [hm1.free] at rd2
  change RD _ _ _ _ _
    [UInt256.land (memLoad (UInt256.ofNat 160) mem2) solcAddrMask,
      receiver, assets, UInt256.ofNat 1211, UInt256.ofNat 0] mem2 _ _ _ _ _ at rd2
  rw [ht1, solcAddrMask_clean hc.2.1] at rd2
  let token := AccountAddress.ofNat p.collateralToken.toNat
  let recipient := AccountAddress.ofNat receiver.toNat
  have htword : UInt256.ofNat token.val = p.collateralToken := addressWord_eq_ofNat_address hc.2.1
  have hrword : UInt256.ofNat recipient.val = receiver := addressWord_eq_ofNat_address hr
  rw [← htword, ← hrword] at rd2
  have hget1 : locals.get? "__memory" = some (.int (Int.ofNat (fp + UInt256.ofNat 64).toNat)) := by
    rw [had1.cursor]; exact hget
  have he := collateralTransfer_args hl imms evm (fp + UInt256.ofNat 64) hget1
  rw [hs.env] at he
  have hf := morphoSafeTransferFunctionRefine (v := v) false token ee.source recipient imms
    (by decide) hs (hm2.weaken (by decide)) (by have hb := hpref.size; omega)
    (by rw [had1.cursor]; omega) hz1 (by rw [morphoPatchedValidJumps v]; jump_dest) rd2
  cases hf with
  | reverted hb hr =>
    exact .reverted (ab.reverts (morphoSafeTransferInternalRevert false token ee.source recipient
      assets (fp + UInt256.ofNat 64).toNat locals imms evm _ "__c5" he hb)) hr
  | @ok frame' evm' σ' mem' ptr' aw' rdata' k' C' hb hs' hm' hpref' hsize' hlower' hzero' rd =>
    have he' := morphoSafeTransferInternalOk false token ee.source recipient assets (fp + UInt256.ofNat 64).toNat
      locals imms evm evm' frame' _ _ "__c5" he hb
    have hr := morphoBlocks.morpho_block_1211 (immWords := wordsOf (immStore v)) (by decide) rd
    exact .ok (ab.run (ExecBlock.consNormal he' ExecBlock.nil)) hs'
      (by simpa only [show (UInt256.ofNat 0).toNat = 0 from rfl, byteArray_readWithPadding_zero] using hr)

end Benchmarks.Morpho.MorphoBlue
