import Benchmarks.Morpho.MorphoBlue.FlashLoanRepay

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive FlashLoanTailRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (frame : Frame) (evm : EVM.State) : Prop where
  | reverted : ExecBlock config frame evm (flashLoanTransition.body.drop 6) .reverted →
      RDrev (deployedRuntime v) g s0 → FlashLoanTailRefines v ee g s0 frame evm
  | ok {frame' evm' σ'} : ExecBlock config frame evm (flashLoanTransition.body.drop 6) (.ok frame' evm') →
      SourceState s0 ee σ' evm' → RDret (deployedRuntime v) g s0 σ' ByteArray.empty →
      FlashLoanTailRefines v ee g s0 frame evm

theorem morphoFlashLoanTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw ptr srcOff len assets : UInt256} {σ : AccountMap}
    {k C : Nat} (token : AccountAddress) (locals imms : Store)
    (hi : FlashLoanInputs { contract := contract, locals := locals, immutables := imms } token assets data)
    (hcur : locals.get? "__c0" = some (.int (Int.ofNat ptr.toNat)))
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem ptr 0)
    (hsize : 128 ≤ mem.size) (hlower : 128 ≤ ptr.toNat)
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1113)
      [srcOff, len, UInt256.ofNat 0, assets, UInt256.ofNat token.val, UInt256.ofNat 0] mem aw out σ k C) :
    FlashLoanTailRefines v ee g s0 { contract := contract, locals := locals, immutables := imms } evm := by
  by_cases hc : extCodeSizeWord σ (UInt256.ofNat ee.source.val) = UInt256.ofNat 0
  · exact .reverted (flashLoanCallbackSourceNoCode _ evm (by rw [← hs.accounts, hs.env]; exact hc))
      (morphoFlashLoanCallbackNoCode (R := []) (by decide) hc h)
  · have hc' : extCodeSizeWord evm.accountMap (UInt256.ofNat evm.executionEnv.source.val) ≠ UInt256.ofNat 0 := by
      rw [← hs.accounts, hs.env]; exact hc
    obtain ⟨gasArg, a1, k1, C1, rd1⟩ := morphoFlashLoanCallbackPrepare (R := []) (by decide) hm hlen hc h
    have hbound := paddedSize_le_add31 len.toNat
    have hfit : 100 + paddedSize len.toNat < UInt256.size := by
      norm_num [solcMaxU64, UInt256.size] at hlen ⊢; omega
    have hcd := wordBytesCallMem_read flashLoanCallbackSelectorWord assets ee.calldata mem data
      srcOff.toNat ptr.toNat len.toNat hsrc (by have hh := hm.gap; omega) hdata hdataSize
    rw [flashLoanCallbackSelectorWord_bytes] at hcd
    have hdecode : decode (deployedRuntime v) (UInt256.ofNat 1185) = some (.CALL, none) := by
      immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
        (⟨1185⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
        morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)
    have hsmall : (wordBytesCalldata flashLoanCallbackSelector assets data).size ≤ maxReturnDataSizeByGas := by
      simp only [wordBytesCalldata, ByteArray.size_append, wordBytesArguments_size, hdataSize]
      change 4 + (96 + paddedSize len.toNat) ≤ maxReturnDataSizeByGas
      norm_num [solcMaxU64, maxReturnDataSizeByGas, maxReturnDataWordsByGas] at hlen ⊢
      omega
    obtain ⟨evm1, σ1, z, result, k2, C2, hcall, hs1, rd2, hout⟩ := zeroValueCallBridge
      (calldata := wordBytesCalldata flashLoanCallbackSelector assets data) rd1 hs hdecode
      (by rw [UInt256.toNat_ofNat_of_lt hfit]; exact hcd) hsmall (by simp)
    have hmout : callOutputMem (flashLoanCallbackMem ee mem ptr assets srcOff len) result ptr (UInt256.ofNat 0) =
        flashLoanCallbackMem ee mem ptr assets srcOff len := callOutputMem_zero _ _ _
    change RD _ _ _ _ (UInt256.ofNat 1186) _ _ _ _ _ _ _ at rd2
    rw [hmout] at rd2
    have hcall' : typedCallViaEVM config evm evm.executionEnv.source "onMorphoFlashLoan" 0
        [.int (Int.ofNat assets.toNat), .bytes data] (z, evm1, result) := by
      refine ⟨_, flashLoanCallback_encode assets data, ?_⟩
      simpa only [accountAddress_roundtrip, hs.env] using hcall
    cases z
    · exact .reverted (flashLoanCallbackSourceFailure hi evm evm1 result hc' hcall')
        (morphoFlashLoanCallbackFailure (R := []) (by decide)
          (by change _ < 2 ^ 256; omega) rd2)
    · have hm1 := hm.wordBytesCall flashLoanCallbackSelectorWord assets ee.calldata srcOff.toNat len.toNat hsrc
      have hp1 := wordBytesCallMem_prefix flashLoanCallbackSelectorWord assets ee.calldata mem
        srcOff.toNat ptr.toNat len.toNat hsrc (by have hh := hm.gap; omega)
      have hp := hp1.trans hm1.setFree.2
      have hm2 := hm1.setFree.1
      have hzero2 : memLoad (UInt256.ofNat 96)
          (writeWord (flashLoanCallbackMem ee mem ptr assets srcOff len) 64 ptr) = UInt256.ofNat 0 := by
        rw [flashLoanCallbackMem, memoryPrefix_memLoad hp (UInt256.ofNat 96) (by decide) hlower hsize]
        exact hzero
      obtain ⟨a3, k3, C3, rd3⟩ := morphoFlashLoanCallbackSuccess (R := []) (by decide)
        (by have hh := hm.space; omega) rd2
      have hi1 := (hi.insert "callback" (.address evm.executionEnv.source) (by decide) (by decide) (by decide)).insert
        "__c1" .unit (by decide) (by decide) (by decide)
      have hcur1 : (flashLoanCalledFrame { contract := contract, locals := locals, immutables := imms }
          evm.executionEnv.source).locals.get? "__c0" = some (.int (Int.ofNat ptr.toNat)) := by
        simp only [flashLoanCalledFrame, flashLoanCallbackFrame,
          store_get_ne (k := "__c1") (a := "__c0") _ _ (by decide),
          store_get_ne (k := "callback") (a := "__c0") _ _ (by decide), hcur]
      have hf := morphoFlashLoanRepay token _ imms hi1 hcur1 hs1 hm2
        (le_trans hsize hp.size) hlower hzero2 rd3
      cases hf with
      | reverted he hr =>
        exact .reverted (flashLoanCallbackSourceSuccess hi evm evm1 result hc' hcall' he) hr
      | ok he hs' hr =>
        exact .ok (flashLoanCallbackSourceSuccess hi evm evm1 result hc' hcall' he) hs' hr


end Benchmarks.Morpho.MorphoBlue
