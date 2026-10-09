import Benchmarks.Morpho.MorphoBlue.FlashLoanCallbackSource
import Benchmarks.Morpho.MorphoBlue.FlashLoanCallbackFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem flashLoanFirstTransfer_args {frame token assets data} (hi : FlashLoanInputs frame token assets data)
    (evm : EVM.State) : evalExprs? config frame evm
      [.var "token", .env .caller, .var "assets", .intLit 192] =
      .ok (safeTransferArgs false token evm.executionEnv.source evm.executionEnv.source assets 192) := by
  simp only [evalExprs?, evalExpr?, hi.token_eq, hi.assets_eq, envValue,
    EvalResult.ofOption, pure, bind, EvalResult.bind]
  rfl

theorem flashLoanSecondTransfer_args {frame token assets data} (hi : FlashLoanInputs frame token assets data)
    (evm : EVM.State) (cursor : Nat)
    (hm : frame.locals.get? "__c0" = some (.int (Int.ofNat cursor))) :
    evalExprs? config frame evm [.var "token", .env .caller, .env .this, .var "assets", .var "__c0"] =
      .ok (safeTransferArgs true token evm.executionEnv.source evm.executionEnv.codeOwner assets cursor) := by
  simp only [evalExprs?, evalExpr?, hi.token_eq, hi.assets_eq, hm, envValue,
    EvalResult.ofOption, pure, bind, EvalResult.bind]
  rfl

inductive FlashLoanRepayRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (frame : Frame) (evm : EVM.State) : Prop where
  | reverted : ExecBlock config frame evm (flashLoanTransition.body.drop 9) .reverted →
      RDrev (deployedRuntime v) g s0 → FlashLoanRepayRefines v ee g s0 frame evm
  | ok {frame' evm' σ'} : ExecBlock config frame evm (flashLoanTransition.body.drop 9) (.ok frame' evm') →
      SourceState s0 ee σ' evm' → RDret (deployedRuntime v) g s0 σ' ByteArray.empty →
      FlashLoanRepayRefines v ee g s0 frame evm

theorem morphoFlashLoanRepay {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw ptr assets : UInt256} {σ : AccountMap}
    {k C : Nat} (token : AccountAddress) (locals imms : Store)
    (hi : FlashLoanInputs { contract := contract, locals := locals, immutables := imms } token assets data)
    (hcur : locals.get? "__c0" = some (.int (Int.ofNat ptr.toNat)))
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem ptr 0)
    (hsize : 128 ≤ mem.size) (hlower : 128 ≤ ptr.toNat)
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 15033)
      [UInt256.ofNat token.val, UInt256.ofNat ee.source.val, UInt256.ofNat ee.codeOwner.val, assets,
        UInt256.ofNat 1211, UInt256.ofNat 0] mem aw out σ k C) :
    FlashLoanRepayRefines v ee g s0 { contract := contract, locals := locals, immutables := imms } evm := by
  have he := flashLoanSecondTransfer_args hi evm ptr.toNat hcur
  rw [hs.env] at he
  have hf := morphoSafeTransferFunctionRefine (v := v) true token ee.source ee.codeOwner imms
    (by decide) hs hm hsize hlower hzero (by rw [morphoPatchedValidJumps v]; jump_dest) h
  cases hf with
  | reverted hb hr =>
    exact .reverted (ExecBlock.consRevert (morphoSafeTransferInternalRevert true token ee.source ee.codeOwner
      assets ptr.toNat locals imms evm _ "__c2" he hb)) hr
  | @ok frame' evm' σ' mem' ptr' aw' rdata' k' C' hb hs' hm' hpref hsize' hlower' hzero' rd =>
    have he' := morphoSafeTransferInternalOk true token ee.source ee.codeOwner assets ptr.toNat
      locals imms evm evm' frame' _ _ "__c2" he hb
    have hr := morphoBlocks.morpho_block_1211 (immWords := wordsOf (immStore v)) (by decide) rd
    exact .ok (ExecBlock.consNormal he' ExecBlock.nil) hs'
      (by simpa only [show (UInt256.ofNat 0).toNat = 0 from rfl, byteArray_readWithPadding_zero] using hr)

end Benchmarks.Morpho.MorphoBlue
