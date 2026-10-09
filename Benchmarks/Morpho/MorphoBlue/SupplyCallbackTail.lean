import Benchmarks.Morpho.MorphoBlue.WordBytesCallerBridge
import Benchmarks.Morpho.MorphoBlue.SupplyCallbackSource
import Benchmarks.Morpho.MorphoBlue.SupplyCallbackReach
import Benchmarks.Morpho.MorphoBlue.SupplyTransfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoSupplyCallbackTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw srcOff len assets shares account ptr : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem ptr 0) (hsize : 160 ≤ mem.size) (hptr : 160 ≤ ptr.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 128) mem = p.loanToken) (hn : 0 < data.size)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 4218)
      (supplyCallbackTail assets shares srcOff len []) mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm (supplyTransition.body.drop 18) supplyTransition.returnType := by
  have hg : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .gt (.arrayLength .localVar ⟨"data", []⟩) (.intLit 0)) = .ok (.bool true) := by
    rw [supplyDataGuard hl imms evm, decide_eq_true hn]
  by_cases hcode : extCodeSizeWord σ (UInt256.ofNat ee.source.val) = UInt256.ofNat 0
  · exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue hg
      (supplyCallback_noCode _ evm (by rw [← hs.accounts, hs.env]; exact hcode))))
      (morphoSupplyCallbackNoCode (R := []) (by decide) hcode h)
  · have hcode' : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0 := by
      rw [← hs.accounts, hs.env]; exact hcode
    obtain ⟨gasArg, a1, k1, C1, rd1⟩ := morphoSupplyCallbackPrepare (R := []) (by decide) hm hlen hcode h
    have hdecode : decode (deployedRuntime v) (UInt256.ofNat 4290) = some (.CALL, none) := by
      immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨4290⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)
    obtain ⟨evm1, σ1, z, result, k2, C2, hcall', hs1, rd2, hout⟩ := wordBytesCallerBridge
      config "onMorphoSupply" supplyCallbackSelectorWord hm hs hlen hsrc hdata hdataSize
      (by rw [supplyCallbackSelectorWord_bytes]; exact supplyCallback_encode assets data)
      hdecode (by simp) rd1
    change RD _ _ _ _ (UInt256.ofNat 4291) _ _ _ _ _ _ _ at rd2
    cases z
    · exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue hg
        (supplyCallback_failure hl imms evm evm1 result hcode' hcall')))
        (morphoSupplyCallbackFailure (R := []) (by decide)
          (by change _ < 2 ^ 256; omega) rd2)
    · obtain ⟨hm2, hp⟩ := hm.wordBytesCallRestored supplyCallbackSelectorWord assets
        ee.calldata srcOff.toNat len.toNat hsrc
      have hzero2 : memLoad (UInt256.ofNat 96)
          (writeWord (supplyCallbackMem ee mem ptr assets srcOff len) 64 ptr) =
          UInt256.ofNat 0 := by
        rw [supplyCallbackMem, memoryPrefix_memLoad hp (UInt256.ofNat 96) (by decide) (by change 128 ≤ ptr.toNat; omega) (by change 128 ≤ mem.size; omega)]
        exact hzero
      have htoken2 : memLoad (UInt256.ofNat 128)
          (writeWord (supplyCallbackMem ee mem ptr assets srcOff len) 64 ptr) =
          p.loanToken := by
        rw [supplyCallbackMem, memoryPrefix_memLoad hp (UInt256.ofNat 128) (by decide) hptr hsize]
        exact htoken
      obtain ⟨a3, k3, C3, rd3⟩ := morphoSupplyCallbackSuccess (R := []) (by decide) (by have hh := hm.space; omega) rd2
      have hl1 := (hl.insert "callback" (.address evm.executionEnv.source) (by decide) (by decide)).insert
        "__c7" .unit (by decide) (by decide)
      have hget1 : (callerCallbackCalledFrame { contract := contract, locals := locals, immutables := imms }
          evm.executionEnv.source "__c7").locals.get? "__memory" = some (.int (Int.ofNat ptr.toNat)) := by
        simpa only [callerCallbackCalledFrame, callerCallbackFrame, store_get_ne (k := "__c7") (a := "__memory") _ _ (by decide),
          store_get_ne (k := "callback") (a := "__memory") _ _ (by decide)] using hget
      have hf := morphoSupplyTransfer p _ imms hc hl1 hs1 hm2 (le_trans hsize hp.size) hptr hget1 hzero2 htoken2 rd3
      have hab : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
          (supplyTransition.body.drop 18)
          (callerCallbackCalledFrame { contract := contract, locals := locals, immutables := imms }
            evm.executionEnv.source "__c7") evm1 (supplyTransition.body.drop 19) :=
        StateBlock.start.step (ExecStmt.iteTrue hg (supplyCallback_success hl imms evm evm1 result hcode' hcall'))
      exact hf.prepend hab

end Benchmarks.Morpho.MorphoBlue
