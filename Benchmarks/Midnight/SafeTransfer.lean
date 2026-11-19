import Benchmarks.Midnight.SafeTransferAfterCall
import Benchmarks.Midnight.ZeroValueCall
import Benchmarks.Midnight.TransferGas

/-! Safe-transfer refinement for callers whose pre-call heap lies below 2^62 bytes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem safeTransferSmallHeap (isFrom : Bool) (imms : Store)
    {I : ExecutionEnv} {g : UInt256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat}
    {token sender recipient : AccountAddress} {value : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hm : 128 ≤ mem.size) (hl : 128 ≤ ptr.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hptr : ptr.toNat + safeTransferCallAllocation isFrom ≤ 2 ^ 62)
    (hgas : midnightGasBound g) (hfork : I.fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I (Sat256.ofUInt256 g) s0 (safeTransferEntryPC isFrom)
      (safeTransferEntryStack isFrom token sender recipient value (ret :: R))
      mem aw rdata σ k C) :
    X (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted ∧
      RDrev midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (ptr' aw' : UInt256) (k' C' : Nat),
      ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
        (safeTransferFunctionFor isFrom).body
        (.returned (safeTransferCallFrame isFrom imms token sender recipient value true out) evm'
          none) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = ptr' ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat < 2 ^ 64 ∧
      RD midnightBytecode I (Sat256.ofUInt256 g) s0 ret R mem' aw' out σ' k' C' := by
  by_cases hc : extCodeSizeWord σ (UInt256.ofNat token.val) = ⟨0⟩
  · refine Or.inr (Or.inl ⟨?_, safeTransferRevertNoCode isFrom (by simp; omega) hc rd⟩)
    apply safeTransferRevertsCode
    rw [← hs.accounts, hc]
    rfl
  · have hfit : ptr.toNat + safeTransferCallAllocation isFrom < 2 ^ 64 := by omega
    have hadd : (ptr + UInt256.ofNat (safeTransferCallAllocation isFrom)).toNat =
        ptr.toNat + safeTransferCallAllocation isFrom :=
      uadd_word_ofNat_toNat ptr _ (by change _ < 2 ^ 256; omega)
    have hprop := safeTransferCallMem_properties isFrom sender recipient value mem ptr (by omega)
    have hprefix := safeTransferCallMem_prefix isFrom sender recipient value mem ptr
    obtain ⟨gasArg, aw1, k1, C1, rd1⟩ := safeTransferPrepareCall isFrom
      (by simp only [List.length_cons]; omega) (by omega) hfit hfree hc rd
    have hcd : (safeTransferCallMem isFrom sender recipient value mem ptr).readWithPadding
        (ptr + UInt256.ofNat 32).toNat (UInt256.ofNat (safeTransferCallSize isFrom)).toNat =
        safeTransferCalldata isFrom sender recipient value := by
      rw [uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)]
      have hsize : (UInt256.ofNat (safeTransferCallSize isFrom)).toNat =
          safeTransferCallSize isFrom := by cases isFrom <;> rfl
      rw [hsize]
      exact hprop.2.2.2
    have hsmall : (safeTransferCalldata isFrom sender recipient value).size ≤ 1024 := by
      rw [safeTransferCalldata_size]
      cases isFrom <;> decide
    rcases zeroValueCallBridge rd1 hs
        (by cases isFrom <;> native_decide) hcd
        (hsmall.trans (by decide)) hfork (by simp only [List.length_cons]; omega) with
      hoog | ⟨evm', σ', success, out, aw2, k2, C2, hcall, hs', rd2, hout, hcost⟩
    · exact Or.inl hoog
    have hcall' : callViaEVM evm token 0 (safeTransferCalldata isFrom sender recipient value)
        (success, evm', out) true := by simpa only [accountAddress_roundtrip] using hcall
    have hcost' : out.size ≤ 1024 ∨ memoryCost ((out.size + 31) / 32) ≤ g.toNat := by
      simpa only [max_eq_left hsmall] using hcost
    have hzero1 : memLoad (UInt256.ofNat 96)
        (safeTransferCallMem isFrom sender recipient value mem ptr) = ⟨0⟩ := by
      rw [hprefix.load (UInt256.ofNat 96) (by decide) (by exact hl) (by exact hm), hzero]
    have hcode : 0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat token.val)).toNat := by
      rw [← hs.accounts]
      have hn := (extCodeSizeWord σ (UInt256.ofNat token.val)).val.isLt
      have hz : (extCodeSizeWord σ (UInt256.ofNat token.val)).toNat ≠ 0 := by
        intro h
        apply hc
        exact u256_inj h
      omega
    rcases safeTransferAfterCall isFrom imms (by omega)
        (by rw [hprop.1]; omega) (by rw [hadd]; omega) hprop.2.1 hzero1
        (by rw [hadd]; omega) (by change out.size < 2 ^ 256; omega)
        (fun _ _ ↦ transferReturnDataFits (by rw [hadd]; exact hptr) hgas hcost')
        hcode hcall' hret rd2 with
      hrev | ⟨htrue, hbody, hprefix', hfree', hl', hb', aw3, k3, C3, rd3⟩
    · exact Or.inr (Or.inl hrev)
    · have hp : MemoryPrefix mem _ ptr.toNat :=
        hprefix.trans (hprefix'.mono (by rw [hadd]; omega))
      refine Or.inr (Or.inr ⟨evm', σ', out, _, _, aw3, k3, C3, hbody, hs', hp,
        hfree', ?_, ?_, hb', rd3⟩)
      · rw [hp.load (UInt256.ofNat 96) (by decide) hl hm, hzero]
      · rw [hadd] at hl'
        omega

end Benchmarks.Midnight
