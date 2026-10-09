import Benchmarks.Morpho.MorphoBlue.FlashLoanTail
import Benchmarks.Morpho.MorphoBlue.FlashLoanEnter
import Benchmarks.Morpho.MorphoBlue.FlashLoanStatic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive FlashLoanCallsRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (frame : Frame) (evm : EVM.State) : Prop where
  | reverted : ExecBlock config frame evm (flashLoanTransition.body.drop 5) .reverted →
      RDrev (deployedRuntime v) g s0 → FlashLoanCallsRefines v ee g s0 frame evm
  | ok {frame' evm' σ'} : ExecBlock config frame evm (flashLoanTransition.body.drop 5) (.ok frame' evm') →
      SourceState s0 ee σ' evm' → RDret (deployedRuntime v) g s0 σ' ByteArray.empty →
      FlashLoanCallsRefines v ee g s0 frame evm

theorem morphoFlashLoanCalls {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {out data : ByteArray} {aw srcOff len assets : UInt256} {σ : AccountMap}
    {k C : Nat} (token : AccountAddress) (locals imms : Store)
    (hi : FlashLoanInputs { contract := contract, locals := locals, immutables := imms } token assets data)
    (hs : SourceState s0 ee σ evm)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14666)
      [UInt256.ofNat token.val, UInt256.ofNat ee.source.val, assets, UInt256.ofNat 1113,
        srcOff, len, UInt256.ofNat 0, assets, UInt256.ofNat token.val, UInt256.ofNat 0]
      (flashLoanEnterMem assets) aw out σ k C) :
    FlashLoanCallsRefines v ee g s0 { contract := contract, locals := locals, immutables := imms } evm := by
  have hm := flashLoanEnterMem_facts assets
  have he := flashLoanFirstTransfer_args hi evm
  rw [hs.env] at he
  have hf := morphoSafeTransferFunctionRefine (v := v) false token ee.source ee.source imms
    (by simp) hs hm.1 (by rw [hm.2.1]; decide) (by decide) hm.2.2
    (by rw [morphoPatchedValidJumps v]; jump_dest) h
  cases hf with
  | reverted hb hr =>
    exact .reverted (ExecBlock.consRevert (morphoSafeTransferInternalRevert false token ee.source ee.source
      assets 192 locals imms evm _ "__c0" he hb)) hr
  | @ok frame' evm' σ' mem' ptr' aw' rdata' k' C' hb hs' hm' hpref hsize' hlower' hzero' rd =>
    have he' := morphoSafeTransferInternalOk false token ee.source ee.source assets 192
      locals imms evm evm' frame' _ _ "__c0" he hb
    have hi' := hi.insert "__c0" (.int (Int.ofNat ptr'.toNat)) (by decide) (by decide) (by decide)
    have ht := morphoFlashLoanTail token _ imms hi' (store_get_self _ _ _) hs' hm'
      hsize' hlower' hzero' hlen hsrc hdata hdataSize rd
    cases ht with
    | reverted heTail hr => exact .reverted (ExecBlock.consNormal he' heTail) hr
    | ok heTail hs' hr => exact .ok (ExecBlock.consNormal he' heTail) hs' hr

end Benchmarks.Morpho.MorphoBlue
