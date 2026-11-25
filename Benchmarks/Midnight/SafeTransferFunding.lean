import Benchmarks.Midnight.SafeTransferOutputBudget
import Benchmarks.Midnight.ZeroValueCallForwarding
import Benchmarks.Midnight.SafeTransferPrepareFunding
import Benchmarks.Midnight.AggregateMemoryGas
import Benchmarks.Midnight.TransferGas

variable {fork : Ethereum.Fork}

/-! Safe-transfer refinement using the combined parent and child memory budget. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem safeTransferFundedPreserving (isFrom : Bool) (imms : Store) {credit : Nat}
    {I : ExecutionEnv} {g : UInt256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat}
    {token sender recipient : AccountAddress} {value : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hm : 128 ≤ mem.size) (hl : 128 ≤ ptr.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (ha0 : MemoryFunding credit mem aw C)
    (hcover : ptr.toNat ≤ 32 * aw.toNat) (halign : ptr.toNat % 32 = 0)
    (hcredit : 4 * ((ptr.toNat + safeTransferCallAllocation isFrom + 31) / 32) ≤
      credit + 999921)
    (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 (safeTransferEntryPC isFrom)
      (safeTransferEntryStack isFrom token sender recipient value (ret :: R))
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecFuncBody fork config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (ptr' aw' : UInt256) (k' C' : Nat),
      ExecFuncBody fork config (safeTransferFrame isFrom imms token sender recipient value) evm
        (safeTransferFunctionFor isFrom).body
        (.returned (safeTransferCallFrame isFrom imms token sender recipient value true out) evm'
          none) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = ptr' ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat < 2 ^ 64 ∧
      MemoryFunding (credit + transferOutputWork out) mem' aw' C' ∧
      ptr'.toNat ≤ 32 * aw'.toNat ∧ ptr'.toNat % 32 = 0 ∧
      4 * ((ptr'.toNat - ptr.toNat) / 32) ≤ transferOutputWork out ∧
      RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ret R mem' aw' out σ' k' C' := by
  rcases midnightMemoryPaid_headroom rd ha0.accounting.paid hgas hcover with hoog | hroom
  · exact Or.inl hoog
  have halloc : safeTransferCallAllocation isFrom ≤ 160 := by cases isFrom <;> decide
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
    obtain ⟨gasArg, aw1, k1, C1, ha1, rd1⟩ := safeTransferPrepareCall_funded isFrom
      (by simp only [List.length_cons]; omega) (by omega) hfit hfree hc ha0 rd
    have hpwords : (ptr.toNat + safeTransferCallAllocation isFrom + 31) / 32 ≤ aw1.toNat := by
      have hs := ha1.covered
      unfold MemoryCovered at hs
      rw [hprop.1] at hs
      cases isFrom <;>
        simp only [safeTransferCallAllocation, safeTransferCallSize, Bool.false_eq_true,
          if_false, if_true] at hs ⊢ <;> omega
    have hbudget : memoryCost ((ptr.toNat + safeTransferCallAllocation isFrom + 31) / 32) +
        4 * ((ptr.toNat + safeTransferCallAllocation isFrom + 31) / 32) ≤ C1 + 1000000 := by
      have hw := memoryCost_mono hpwords
      have he : memoryCost aw1.toNat = Cₘ aw1 := by
        rw [memoryCost_eq_Cₘ (words := aw1.toNat) aw1.val.isLt, u256_ofNat_toNat]
      rw [he] at hw
      have hp := ha1.paid
      omega
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
    rcases zeroValueCallCostBridge rd1 hs
        (by cases isFrom <;> native_decide) hcd
        (hsmall.trans (by decide)) hfork (by simp only [List.length_cons]; omega) with
      hoog | ⟨evm', σ', success, out, aw2, k2, C2, hcall, hs', rd2, hout, hcost, hcharge⟩
    · exact Or.inl hoog
    have hcall' : callViaEVM fork evm token 0 (safeTransferCalldata isFrom sender recipient value)
        (success, evm', out) true := by simpa only [accountAddress_roundtrip] using hcall
    have hcost' : out.size ≤ 1024 ∨
        C1 + 100 + forwardingMinimum (memoryCost ((out.size + 31) / 32)) ≤ g.toNat := by
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
    have hreturnfit : (ptr + UInt256.ofNat (safeTransferCallAllocation isFrom)).toNat +
        returnDataAllocation out.size < 2 ^ 64 := by
      rcases hcost' with hsmall | hcost
      · rw [hadd]
        unfold returnDataAllocation
        omega
      · exact aggregateReturnDataFits
          (parent := (ptr.toNat + safeTransferCallAllocation isFrom + 31) / 32)
          (by rw [hadd]; omega) hbudget
          (midnightGasBound_lt_capacityCutoff hgas) (by omega)
    rcases safeTransferAfterCallCharge isFrom imms (by omega)
        (by rw [hprop.1]; omega) (by rw [hadd]; omega) hprop.2.1 hzero1
        (by rw [hadd]; omega) (by change out.size < 2 ^ 256; omega)
        (fun _ _ ↦ hreturnfit)
        hcode hcall' hret rd2 with
      hrev | ⟨htrue, hbody, hprefix', hfree', hl', hb', aw3, k3, C3, hpost, hcover3, rd3⟩
    · exact Or.inr (Or.inl hrev)
    · rcases hcharge with hfalse | ⟨hC12, haw12, hpaid12, hpaidOut⟩
      · simp [htrue] at hfalse
      have hcovered2 := ha1.covered.mono haw12
      have hcovered3 := hcover3 hcovered2
      have hfund3 : MemoryFunding (credit + transferOutputWork out)
          (safeTransferOutputMem (safeTransferCallMem isFrom sender recipient value mem ptr) out
            (ptr + UInt256.ofNat (safeTransferCallAllocation isFrom))) aw3 C3 := by
        refine ⟨?_, hcovered3⟩
        have hp1 := ha1.paid
        have hp3 := hpost.paid
        unfold transferOutputWork
        by_cases hsmallOut : out.size ≤ 1024
        · rw [if_pos hsmallOut]
          omega
        · rw [if_neg hsmallOut]
          rcases hpaidOut with hsmallOut' | hpaidOut
          · have : out.size ≤ 1024 := by simpa only [max_eq_left hsmall] using hsmallOut'
            contradiction
          · omega
      have hnewalign : (ptr + UInt256.ofNat (safeTransferCallAllocation isFrom)).toNat % 32 = 0 := by
        rw [hadd]
        cases isFrom <;>
          simp only [safeTransferCallAllocation, Bool.false_eq_true, if_false, if_true] <;> omega
      have hnewcover : (ptr + UInt256.ofNat (safeTransferCallAllocation isFrom)).toNat ≤
          32 * aw3.toNat := by
        have hw := hpost.active_le
        rw [hadd]
        omega
      have hreturnfit' : (ptr + UInt256.ofNat (safeTransferCallAllocation isFrom)).toNat +
          returnDataAllocation out.size < UInt256.size := by change _ < 2 ^ 256; omega
      have houtputNat := safeTransferOutputPtr_toNat hreturnfit'
      have hp : MemoryPrefix mem _ ptr.toNat :=
        hprefix.trans (hprefix'.mono (by rw [hadd]; omega))
      refine Or.inr (Or.inr ⟨evm', σ', out, _, _, aw3, k3, C3, hbody, hs', hp,
        hfree', ?_, ?_, hb', hfund3, ?_, ?_, ?_, rd3⟩)
      · rw [hp.load (UInt256.ofNat 96) (by decide) hl hm, hzero]
      · rw [hadd] at hl'
        omega
      · exact safeTransferOutputPtr_covered (by rw [hprop.1]; omega) (by rw [hadd]; omega)
          hreturnfit' hnewalign hnewcover hcovered3
      · exact safeTransferOutputPtr_aligned hreturnfit' hnewalign
      · rw [houtputNat, hadd]
        have hw := transferOutputWork_growth out halloc
        omega

theorem safeTransferFunded (isFrom : Bool) (imms : Store) {credit : Nat}
    {I : ExecutionEnv} {g : UInt256} {s0 evm : State} {mem rdata : ByteArray}
    {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat}
    {token sender recipient : AccountAddress} {value : UInt256} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hm : 128 ≤ mem.size) (hl : 128 ≤ ptr.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (ha0 : MemoryFunding credit mem aw C)
    (hcover : ptr.toNat ≤ 32 * aw.toNat) (halign : ptr.toNat % 32 = 0)
    (hcredit : 4 * ((ptr.toNat + safeTransferCallAllocation isFrom + 31) / 32) ≤
      credit + 999921)
    (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hs : SourceState s0 I σ evm)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 (safeTransferEntryPC isFrom)
      (safeTransferEntryStack isFrom token sender recipient value (ret :: R))
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecFuncBody fork config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (out mem' : ByteArray) (ptr' aw' : UInt256) (k' C' : Nat),
      ExecFuncBody fork config (safeTransferFrame isFrom imms token sender recipient value) evm
        (safeTransferFunctionFor isFrom).body
        (.returned (safeTransferCallFrame isFrom imms token sender recipient value true out) evm'
          none) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' ptr.toNat ∧
      memLoad (UInt256.ofNat 64) mem' = ptr' ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      ptr.toNat ≤ ptr'.toNat ∧ ptr'.toNat < 2 ^ 64 ∧
      RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ret R mem' aw' out σ' k' C' := by
  rcases safeTransferFundedPreserving isFrom imms hstack hm hl hfree hzero ha0 hcover halign
      hcredit hgas hfork hs hret rd with hoog | hrev | hsuccess
  · exact Or.inl hoog
  · exact Or.inr (Or.inl hrev)
  · obtain ⟨evm', σ', out, mem', ptr', aw', k', C', hb, hs', hp, hf, hz, hl', hlt,
        _, _, _, _, rd'⟩ := hsuccess
    exact Or.inr (Or.inr ⟨evm', σ', out, mem', ptr', aw', k', C', hb, hs', hp, hf, hz, hl',
      hlt, rd'⟩)

end Benchmarks.Midnight
