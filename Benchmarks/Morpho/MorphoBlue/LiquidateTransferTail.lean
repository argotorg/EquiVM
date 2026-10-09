import Benchmarks.Morpho.MorphoBlue.LiquidateCallbackReach
import Benchmarks.Morpho.MorphoBlue.LiquidateLoanTransfer
import Benchmarks.Morpho.MorphoBlue.WordBytesCallerBridge
import Benchmarks.Morpho.MorphoBlue.CallerCallbackSource
import Benchmarks.Morpho.MorphoBlue.LocalBytesGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem liquidateCallback_args {p assets seized shares account badAssets badShares data locals}
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals)
    (imms : Store) (evm : EVM.State) :
    evalExprs? config (callerCallbackFrame { contract := contract, locals := locals, immutables := imms }
      evm.executionEnv.source) evm [.var "repaidAssets", .var "data"] =
      .ok [.int (Int.ofNat assets.toNat), .bytes data] := by
  have hl1 := hl.insert "callback" (.address evm.executionEnv.source) (by decide) (by decide) (by decide)
  simp only [evalExprs?, evalExpr?, callerCallbackFrame, hl1.assets_eq, hl1.data_eq,
    EvalResult.ofOption, pure, bind, EvalResult.bind]

theorem morphoLiquidateTransferTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account badAssets badShares srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (hl : LiquidateEventLocals p account seized shares data assets badAssets badShares locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 0) (hsize : 192 ≤ mem.size) (hptr : 192 ≤ fp.toNat)
    (hget : locals.get? "__c21" = some (.int (Int.ofNat fp.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hloan : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2704)
      (liquidateTransferTail assets seized srcOff len []) mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (liquidateTransition.body.drop 33) liquidateTransition.returnType := by
  have hg := evalLocalBytesNonempty (cfg := config) (evm := evm)
    (frame := { contract := contract, locals := locals, immutables := imms }) hl.data_eq
  by_cases hz : len = UInt256.ofNat 0
  · have hn : ¬ 0 < data.size := by rw [hdataSize, hz]; decide
    rw [decide_eq_false hn] at hg
    have rd0 := morphoBlocks.morpho_block_2704_fallthrough (immWords := wordsOf (immStore v)) (by change 8 ≤ 1024; decide) hz h
    exact (morphoLiquidateLoanTransfer (v := v) p locals imms hc hl hs hm (by omega) (by omega) hget hzero hloan rd0).prepend
      (StateBlock.start.step (ExecStmt.iteFalse hg ExecBlock.nil))
  · have hn : 0 < data.size := by
      rw [hdataSize]
      exact Nat.pos_of_ne_zero (fun he ↦ hz (uint256_toNat_eq_zero he))
    rw [decide_eq_true hn] at hg
    have rd0 := morphoBlocks.morpho_block_2704_taken (immWords := wordsOf (immStore v)) (by change 8 ≤ 1024; decide) hz
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    by_cases hcode : extCodeSizeWord σ (UInt256.ofNat ee.source.val) = UInt256.ofNat 0
    · have hes : ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
          (callerCallbackBody "onMorphoLiquidate" [.var "repaidAssets", .var "data"] "__c22") .reverted :=
        callerCallbackSourceNoCode config _ evm "onMorphoLiquidate" [.var "repaidAssets", .var "data"] "__c22" []
          (by rw [← hs.accounts, hs.env]; exact hcode)
      exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue hg hes))
        (morphoLiquidateCallbackNoCode (v := v) (R := []) (by decide) hcode rd0)
    · have hcode' : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0 := by
        rw [← hs.accounts, hs.env]; exact hcode
      obtain ⟨gasArg, a1, k1, C1, rd1⟩ := morphoLiquidateCallbackPrepare (v := v) (R := []) (by decide) hm hlen hcode rd0
      have hdecode : decode (deployedRuntime v) (UInt256.ofNat 2836) = some (.CALL, none) := by
        immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
          (⟨2836⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
          morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)
      obtain ⟨evm1, σ1, z, result, k2, C2, hcall, hs1, rd2, hout⟩ := wordBytesCallerBridge
        config "onMorphoLiquidate" liquidateCallbackSelectorWord hm hs hlen hsrc hdata hdataSize
        (by rw [liquidateCallbackSelectorWord_bytes]; exact liquidateCallback_encode assets data)
        hdecode (by simp) rd1
      change RD _ _ _ _ (UInt256.ofNat 2837) _ _ _ _ _ _ _ at rd2
      cases z
      · have hes : ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
            (callerCallbackBody "onMorphoLiquidate" [.var "repaidAssets", .var "data"] "__c22") .reverted :=
          callerCallbackSourceFailure config _ evm evm1 "onMorphoLiquidate" [.var "repaidAssets", .var "data"] "__c22"
            [] _ result hcode' (liquidateCallback_args hl imms evm) hcall
        exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue hg hes))
          (morphoLiquidateCallbackFailure (v := v) (R := []) (by decide) (by change _ < 2 ^ 256; omega) rd2)
      · obtain ⟨hm2, hp⟩ := hm.wordBytesCallRestored liquidateCallbackSelectorWord assets ee.calldata srcOff.toNat len.toNat hsrc
        have hz2 : memLoad (UInt256.ofNat 96) (writeWord (liquidateCallbackMem ee mem fp assets srcOff len) 64 fp) =
            UInt256.ofNat 0 := by
          rw [liquidateCallbackMem, memoryPrefix_memLoad hp (UInt256.ofNat 96) (by decide)
            (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)]
          exact hzero
        have ht2 : memLoad (UInt256.ofNat 128) (writeWord (liquidateCallbackMem ee mem fp assets srcOff len) 64 fp) = p.loanToken := by
          rw [liquidateCallbackMem, memoryPrefix_memLoad hp (UInt256.ofNat 128) (by decide)
            (by change 160 ≤ fp.toNat; omega) (by change 160 ≤ mem.size; omega)]
          exact hloan
        obtain ⟨a3, k3, C3, rd3⟩ := morphoLiquidateCallbackSuccess (v := v) (R := []) (by decide) (by have hh := hm.space; omega) rd2
        have hl1 := (hl.insert "callback" (.address evm.executionEnv.source) (by decide) (by decide) (by decide)).insert
          "__c22" .unit (by decide) (by decide) (by decide)
        have hget1 : (callerCallbackCalledFrame { contract := contract, locals := locals, immutables := imms }
            evm.executionEnv.source "__c22").locals.get? "__c21" = some (.int (Int.ofNat fp.toNat)) := by
          simpa only [callerCallbackCalledFrame, callerCallbackFrame,
            store_get_ne (k := "__c22") (a := "__c21") _ _ (by decide),
            store_get_ne (k := "callback") (a := "__c21") _ _ (by decide)] using hget
        have hf := morphoLiquidateLoanTransfer (v := v) p _ imms hc hl1 hs1 hm2
          (by have hh := hp.size; omega) (by omega) hget1 hz2 ht2 rd3
        have hes : ExecBlock config { contract := contract, locals := locals, immutables := imms } evm
            (callerCallbackBody "onMorphoLiquidate" [.var "repaidAssets", .var "data"] "__c22")
            (.ok (callerCallbackCalledFrame { contract := contract, locals := locals, immutables := imms }
              evm.executionEnv.source "__c22") evm1) :=
          callerCallbackSourceSuccess config _ evm evm1 "onMorphoLiquidate" [.var "repaidAssets", .var "data"] "__c22"
            [] _ result hcode' (liquidateCallback_args hl imms evm) hcall rfl ExecBlock.nil
        exact hf.prepend (StateBlock.start.step (ExecStmt.iteTrue hg hes))

end Benchmarks.Morpho.MorphoBlue
