import Benchmarks.Morpho.MorphoBlue.SafeTransferPrepareCall
import Benchmarks.Morpho.MorphoBlue.SafeTransferPostCall
import Benchmarks.Morpho.MorphoBlue.ZeroValueCallBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive SafeTransferFunctionRefinesAt (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (isFrom : Bool) (token sender recipient : AccountAddress) (value : UInt256) (imms : Store)
    (evm : EVM.State) (mem : ByteArray) (ptr ret : UInt256) (lower : Nat) (R : List UInt256) : Prop where
  | reverted : ExecFuncBody config (safeTransferStart isFrom token sender recipient value ptr.toNat imms)
      evm (safeTransferFunctionFor isFrom).body .reverted → RDrev (deployedRuntime v) g s0 →
      SafeTransferFunctionRefinesAt v ee g s0 isFrom token sender recipient value imms evm mem ptr ret lower R
  | ok {frame' evm' σ' mem' ptr' aw' rdata' k' C'} :
      ExecFuncBody config (safeTransferStart isFrom token sender recipient value ptr.toNat imms)
        evm (safeTransferFunctionFor isFrom).body (.returned frame' evm' (some [.int (Int.ofNat ptr'.toNat)])) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' ptr' 0 → MemoryPrefix mem mem' ptr.toNat →
      128 ≤ mem'.size → lower ≤ ptr'.toNat → memLoad (UInt256.ofNat 96) mem' = UInt256.ofNat 0 →
      RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata' σ' k' C' →
      SafeTransferFunctionRefinesAt v ee g s0 isFrom token sender recipient value imms evm mem ptr ret lower R

theorem morphoSafeTransferFunctionRefineAt {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw ptr value ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (token sender recipient : AccountAddress) (imms : Store)
    (hstack : R.length + 21 ≤ 1024) (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem ptr 0)
    (hsize : 128 ≤ mem.size) (hlower : 128 ≤ ptr.toNat) (lower : Nat) (hbound : lower ≤ ptr.toNat)
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferEntryPC isFrom)
      (safeTransferEVMArgs isFrom token sender recipient value ++ ret :: R) mem aw out σ k C) :
    SafeTransferFunctionRefinesAt v ee g s0 isFrom token sender recipient value imms evm mem ptr ret lower R := by
  have hi := safeTransferStart_inputs isFrom token sender recipient value ptr.toNat imms
  by_cases hf : ptr.toNat + safeTransferInputAllocation isFrom < 2 ^ 64
  · by_cases hc : extCodeSizeWord σ (UInt256.ofNat token.val) = UInt256.ofNat 0
    · have hc' : extCodeSizeWord evm.accountMap (UInt256.ofNat token.val) = UInt256.ofNat 0 := by
        rw [← hs.accounts]; exact hc
      exact .reverted (safeTransferSource_noCode isFrom hi.memory_eq hf
        (safeTransferCodeGuard_false hi.prepared.token_eq hc'))
        (morphoTransferNoCode isFrom token sender recipient hstack hm hc h)
    · obtain ⟨ptr1, offset, mem1, gasArg, a1, k1, C1, rd1, hcd, hm1, hcur1, hpref1,
        hsize1, hlo1, hzero1⟩ := morphoTransferPrepareCall isFrom token sender recipient
          hstack hm hsize hlower hzero hc hf h
      have hc' : extCodeSizeWord evm.accountMap (UInt256.ofNat token.val) ≠ UInt256.ofNat 0 := by
        rw [← hs.accounts]; exact hc
      have hlen : (UInt256.ofNat (safeTransferCallSize isFrom)).toNat = safeTransferCallSize isFrom := by
        cases isFrom <;> decide
      have hdecode : decode (deployedRuntime v) (safeTransferCallPC isFrom) = some (.CALL, none) := by
        cases isFrom
        · immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
            (⟨14858⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
            morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)
        · immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
            (⟨15163⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
            morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)
      obtain ⟨evm', σ', z, result, k2, C2, hcall, hs', rd2, hresult⟩ := zeroValueCallBridge
        (calldata := safeTransferCalldata isFrom sender recipient value) rd1 hs hdecode
        (by rw [hlen]; exact hcd)
        (by rw [safeTransferCalldata_size]; cases isFrom <;> decide)
        (by change R.length + 2 + 1 ≤ 1024; omega)
      have hpc : safeTransferCallPC isFrom + ⟨1⟩ = safeTransferAfterCallPC isFrom := by
        cases isFrom <;> decide
      have hmout : callOutputMem mem1 result (UInt256.ofNat 0) (UInt256.ofNat 0) = mem1 :=
        callOutputMem_zero mem1 result (UInt256.ofNat 0)
      rw [hpc, hmout] at rd2
      have hcall' : callViaEVM evm token 0 (safeTransferCalldata isFrom sender recipient value)
          (z, evm', result) := by simpa only [accountAddress_roundtrip] using hcall
      have hsource := safeTransferSource_call hi.memory_eq hf
        (safeTransferCodeGuard_true hi.prepared.token_eq hc') hi.prepared.token_eq
        (hi.prepared.encode evm (encodeSafeTransfer isFrom sender recipient value)) hcall'
      obtain ⟨hmem', hout', hz'⟩ := safeTransferCalled_locals
        (safeTransferStart isFrom token sender recipient value ptr.toNat imms) isFrom ptr.toNat z result
      rw [← hcur1] at hmem'
      rcases morphoTransferPostCall (R := R) isFrom (by omega) hmem' hout' hz' hresult hm1 hsize1 hlo1 hzero1
          hvalid rd2 with hbad | ⟨frame', mem2, ptr2, a2, k3, C3, he, rd3, hm2, hpref2, hcur2⟩
      · exact .reverted (.execBlockRevert (hsource.run hbad.1)) hbad.2
      · rw [← hcur2] at he
        have hpref := hpref1.trans (hpref2.mono (by rw [hcur1]; omega))
        refine .ok (.execBlockRet (hsource.run he)) hs' hm2 hpref (le_trans hsize hpref.size)
          (by rw [hcur2, hcur1]; omega) ?_ rd3
        rw [memoryPrefix_memLoad hpref (UInt256.ofNat 96) (by decide) hlower hsize]
        exact hzero
  · exact .reverted (safeTransferSource_inputRevert isFrom hi.memory_eq (by omega))
      (morphoTransferInputOverflow isFrom token sender recipient hstack hm (by omega) h)

end Benchmarks.Morpho.MorphoBlue
