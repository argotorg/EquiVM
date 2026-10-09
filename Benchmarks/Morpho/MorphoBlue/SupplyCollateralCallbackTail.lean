import Benchmarks.Morpho.MorphoBlue.SupplyCollateralCallbackSource
import Benchmarks.Morpho.MorphoBlue.SupplyCollateralCallbackReach
import Benchmarks.Morpho.MorphoBlue.SupplyCollateralTransfer

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoSupplyCollateralCallbackTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw srcOff len assets account : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (hl : SupplyCollateralLocals p assets account data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem (UInt256.ofNat 544) 0) (hsize : 192 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 160) mem = p.collateralToken) (hn : 0 < data.size)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10307)
      [srcOff, len, solcAddrMask, assets, UInt256.ofNat 0, UInt256.ofNat 128] mem aw out σ k C) :
    VoidBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm (supplyCollateralTransition.body.drop 10) := by
  have hg : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.binary .gt (.arrayLength .localVar ⟨"data", []⟩) (.intLit 0)) = .ok (.bool true) := by
    rw [supplyCollateralDataGuard hl imms evm, decide_eq_true hn]
  by_cases hcode : extCodeSizeWord σ (UInt256.ofNat ee.source.val) = UInt256.ofNat 0
  · exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue hg
      (supplyCollateralCallback_noCode _ evm (by rw [← hs.accounts, hs.env]; exact hcode))))
      (morphoSupplyCollateralCallbackNoCode (R := []) (by decide) hcode h)
  · have hcode' : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0 := by
      rw [← hs.accounts, hs.env]; exact hcode
    obtain ⟨gasArg, a1, k1, C1, rd1⟩ := morphoSupplyCollateralCallbackPrepare (R := []) (by decide) hm hlen hcode h
    have hbound := paddedSize_le_add31 len.toNat
    have hfit : 100 + paddedSize len.toNat < UInt256.size := by
      norm_num [solcMaxU64, UInt256.size] at hlen ⊢; omega
    have hcd := wordBytesCallMem_read supplyCollateralCallbackSelectorWord assets ee.calldata mem data
      srcOff.toNat 544 len.toNat hsrc (by have hh := hm.gap; exact hh) hdata hdataSize
    rw [supplyCollateralCallbackSelectorWord_bytes] at hcd
    have hdecode : decode (deployedRuntime v) (UInt256.ofNat 10379) = some (.CALL, none) := by
      immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨10379⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)
    have hsmall : (wordBytesCalldata supplyCollateralCallbackSelector assets data).size ≤ maxReturnDataSizeByGas := by
      simp only [wordBytesCalldata, ByteArray.size_append, wordBytesArguments_size, hdataSize]
      change 4 + (96 + paddedSize len.toNat) ≤ maxReturnDataSizeByGas
      norm_num [solcMaxU64, maxReturnDataSizeByGas, maxReturnDataWordsByGas] at hlen ⊢
      omega
    obtain ⟨evm1, σ1, z, result, k2, C2, hcall, hs1, rd2, hout⟩ := zeroValueCallBridge
      (calldata := wordBytesCalldata supplyCollateralCallbackSelector assets data) rd1 hs hdecode
      (by rw [UInt256.toNat_ofNat_of_lt hfit]; exact hcd) hsmall (by simp)
    have hmout : callOutputMem (supplyCollateralCallbackMem ee mem (UInt256.ofNat 544) assets srcOff len)
        result (UInt256.ofNat 544) (UInt256.ofNat 0) =
        supplyCollateralCallbackMem ee mem (UInt256.ofNat 544) assets srcOff len := callOutputMem_zero _ _ _
    change RD _ _ _ _ (UInt256.ofNat 10380) _ _ _ _ _ _ _ at rd2
    rw [hmout] at rd2
    have hcall' : typedCallViaEVM config evm evm.executionEnv.source "onMorphoSupplyCollateral" 0
        [.int (Int.ofNat assets.toNat), .bytes data] (z, evm1, result) := by
      refine ⟨_, supplyCollateralCallback_encode assets data, ?_⟩
      simpa only [accountAddress_roundtrip, hs.env] using hcall
    cases z
    · exact .reverted (ExecBlock.consRevert (ExecStmt.iteTrue hg
        (supplyCollateralCallback_failure hl imms evm evm1 result hcode' hcall')))
        (morphoSupplyCollateralCallbackFailure (R := []) (by decide)
          (by change _ < 2 ^ 256; omega) rd2)
    · have hm1 := hm.wordBytesCall supplyCollateralCallbackSelectorWord assets ee.calldata srcOff.toNat len.toNat hsrc
      have hp1 := wordBytesCallMem_prefix supplyCollateralCallbackSelectorWord assets ee.calldata mem
        srcOff.toNat 544 len.toNat hsrc (by have hh := hm.gap; exact hh)
      have hp := hp1.trans hm1.setFree.2
      have hm2 := hm1.setFree.1
      have hzero2 : memLoad (UInt256.ofNat 96)
          (writeWord (supplyCollateralCallbackMem ee mem (UInt256.ofNat 544) assets srcOff len) 64 (UInt256.ofNat 544)) =
          UInt256.ofNat 0 := by
        rw [supplyCollateralCallbackMem, memoryPrefix_memLoad hp (UInt256.ofNat 96) (by decide) (by decide) (by change 128 ≤ mem.size; omega)]
        exact hzero
      have htoken2 : memLoad (UInt256.ofNat 160)
          (writeWord (supplyCollateralCallbackMem ee mem (UInt256.ofNat 544) assets srcOff len) 64 (UInt256.ofNat 544)) =
          p.collateralToken := by
        rw [supplyCollateralCallbackMem, memoryPrefix_memLoad hp (UInt256.ofNat 160) (by decide) (by decide) hsize]
        exact htoken
      obtain ⟨a3, k3, C3, rd3⟩ := morphoSupplyCollateralCallbackSuccess (R := []) (by decide) (by decide) rd2
      have hl1 := (hl.insert "callback" (.address evm.executionEnv.source) (by decide) (by decide)).insert
        "__c2" .unit (by decide) (by decide)
      have hf := morphoSupplyCollateralTransfer p _ imms hc hl1 hs1 hm2 (le_trans hsize hp.size) hzero2 htoken2 rd3
      have hab : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
          (supplyCollateralTransition.body.drop 10)
          (callerCallbackCalledFrame { contract := contract, locals := locals, immutables := imms }
            evm.executionEnv.source "__c2") evm1 (supplyCollateralTransition.body.drop 11) :=
        StateBlock.start.step (ExecStmt.iteTrue hg (supplyCollateralCallback_success hl imms evm evm1 result hcode' hcall'))
      exact hf.prepend hab

end Benchmarks.Morpho.MorphoBlue
