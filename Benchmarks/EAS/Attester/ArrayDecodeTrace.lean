import Benchmarks.EAS.Attester.Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

/-- The three checks in the compiler's shared calldata-array view routine. -/
structure ArrayHeadChecks (cd : ByteArray) (head : UInt256) : Prop where
  header : UInt256.slt (head + UInt256.ofNat 31) (UInt256.ofNat cd.size) ≠ UInt256.ofNat 0
  length : UInt256.isZero (UInt256.gt (calldataWord cd head.toNat)
    (UInt256.ofNat 18446744073709551615)) ≠ UInt256.ofNat 0
  payload : UInt256.isZero (UInt256.gt
    ((head + UInt256.shiftLeft (calldataWord cd head.toNat) (UInt256.ofNat 5)) + UInt256.ofNat 32)
    (UInt256.ofNat cd.size)) ≠ UInt256.ofNat 0

/-- Shared by both outer arrays and by each nested-array access. -/
theorem attesterArrayView {words : String → UInt256} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw ret head : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) ee g s0 ⟨2406⟩
      (head :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (immutableLayout.runtime attesterBytecode words) 0).contains ret = true) :
    (¬ ArrayHeadChecks ee.calldata head ∧ RDrev (immutableLayout.runtime attesterBytecode words) g
        s0) ∨
      (ArrayHeadChecks ee.calldata head ∧ ∃ k' C',
        RD (immutableLayout.runtime attesterBytecode words) ee g s0 ret
          (calldataWord ee.calldata head.toNat :: (head + UInt256.ofNat 32) :: R)
          mem aw rdata σ k' C') := by
  by_cases hhead : UInt256.slt (head + UInt256.ofNat 31) (UInt256.ofNat ee.calldata.size) =
      UInt256.ofNat 0
  · left
    refine ⟨fun hc ↦ hc.header hhead, ?_⟩
    have h' := attesterRuntime_block_2406_fallthrough (by simp only [List.length_cons]; omega) hhead
        h
    exact attesterRuntime_block_2420
      (by simp only [attesterRuntime_block_2406_fallthrough_stack, List.length_cons]; omega) h'
  have h' := attesterRuntime_block_2406_taken (by simp only [List.length_cons]; omega) hhead
    (by rw [attesterRuntime_validJumps]; native_decide) h
  by_cases hlen : UInt256.isZero (UInt256.gt (calldataWord ee.calldata head.toNat)
      (UInt256.ofNat 18446744073709551615)) = UInt256.ofNat 0
  · left
    refine ⟨fun hc ↦ hc.length hlen, ?_⟩
    have h'' := attesterRuntime_block_2424_fallthrough
      (by simp only [List.length_cons]; omega) hlen h'
    exact attesterRuntime_block_2444
      (by simp only [attesterRuntime_block_2424_fallthrough_stack, List.length_cons]; omega) h''
  have h'' := attesterRuntime_block_2424_taken (by simp only [List.length_cons]; omega) hlen
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  by_cases hend : UInt256.isZero (UInt256.gt
      ((head + UInt256.shiftLeft (calldataWord ee.calldata head.toNat) (UInt256.ofNat 5)) +
          UInt256.ofNat 32)
      (UInt256.ofNat ee.calldata.size)) = UInt256.ofNat 0
  · left
    refine ⟨fun hc ↦ hc.payload hend, ?_⟩
    have h''' := attesterRuntime_block_2448_fallthrough
      (by simp only [List.length_cons]; omega) hend h''
    exact attesterRuntime_block_2471
      (by simp only [attesterRuntime_block_2448_fallthrough_stack, List.length_cons]; omega) h'''
  have h''' := attesterRuntime_block_2448_taken (by simp only [List.length_cons]; omega) hend
    (by rw [attesterRuntime_validJumps]; native_decide) h''
  have hret := attesterRuntime_block_2475 (by omega) hvalid h'''
  exact .inr ⟨⟨hhead, hlen, hend⟩, _, _, hret⟩

def arrayHead (cd : ByteArray) (offset : Nat) : UInt256 :=
  UInt256.ofNat 4 + calldataWord cd offset

structure MultiHeadChecks (cd : ByteArray) : Prop where
  tuple : UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) ⟨4⟩)
    (UInt256.ofNat 64)) ≠ UInt256.ofNat 0
  firstOffset : UInt256.isZero (UInt256.gt (calldataWord cd 4)
    (UInt256.ofNat 18446744073709551615)) ≠ UInt256.ofNat 0
  first : ArrayHeadChecks cd (arrayHead cd 4)
  secondOffset : UInt256.isZero (UInt256.gt (calldataWord cd 36)
    (UInt256.ofNat 18446744073709551615)) ≠ UInt256.ofNat 0
  second : ArrayHeadChecks cd (arrayHead cd 36)

theorem attesterMultiHeads {words : String → UInt256} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) ee g s0 ⟨2482⟩
      (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hstack : R.length + 18 ≤ 1024)
    (hvalid : (D_J (immutableLayout.runtime attesterBytecode words) 0).contains ret = true) :
    (¬ MultiHeadChecks ee.calldata ∧ RDrev (immutableLayout.runtime attesterBytecode words) g s0) ∨
      (MultiHeadChecks ee.calldata ∧ ∃ k' C',
        RD (immutableLayout.runtime attesterBytecode words) ee g s0 ret
          (calldataWord ee.calldata (arrayHead ee.calldata 36).toNat ::
            (arrayHead ee.calldata 36 + UInt256.ofNat 32) ::
            calldataWord ee.calldata (arrayHead ee.calldata 4).toNat ::
            (arrayHead ee.calldata 4 + UInt256.ofNat 32) :: R)
          mem aw rdata σ k' C') := by
  by_cases htuple : UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩)
      (UInt256.ofNat 64)) = UInt256.ofNat 0
  · left
    refine ⟨fun hc ↦ hc.tuple htuple, ?_⟩
    have h' := attesterRuntime_block_2482_fallthrough (by simp only [List.length_cons]; omega)
        htuple h
    exact attesterRuntime_block_2500
      (by simp only [attesterRuntime_block_2482_fallthrough_stack, List.length_cons]; omega) h'
  have h' := attesterRuntime_block_2482_taken (by simp only [List.length_cons]; omega) htuple
    (by rw [attesterRuntime_validJumps]; native_decide) h
  by_cases hoff0 : UInt256.isZero (UInt256.gt (calldataWord ee.calldata 4)
      (UInt256.ofNat 18446744073709551615)) = UInt256.ofNat 0
  · left
    refine ⟨fun hc ↦ hc.firstOffset hoff0, ?_⟩
    have h'' := attesterRuntime_block_2504_fallthrough (x4 := ⟨4⟩)
      (by simp only [List.length_cons]; omega) hoff0 h'
    exact attesterRuntime_block_2523
      (by simp only [attesterRuntime_block_2504_fallthrough_stack, List.length_cons]; omega) h''
  have h'' := attesterRuntime_block_2504_taken (x4 := ⟨4⟩) (by simp only [List.length_cons]; omega)
      hoff0
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  have hview := attesterRuntime_block_2527 (by simp only [List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) h''
  rcases attesterArrayView hview (by simp only [List.length_cons]; omega)
      (by rw [attesterRuntime_validJumps]; native_decide) with hrev | ⟨hfirst, k', C', hfirstRD⟩
  · exact .inl ⟨fun hc ↦ hrev.1 hc.first, hrev.2⟩
  by_cases hoff1 : UInt256.isZero (UInt256.gt (calldataWord ee.calldata 36)
      (UInt256.ofNat 18446744073709551615)) = UInt256.ofNat 0
  · left
    refine ⟨fun hc ↦ hc.secondOffset hoff1, ?_⟩
    have hsecond := attesterRuntime_block_2539_fallthrough (x7 := ⟨4⟩)
      (by simp only [List.length_cons]; omega)
      hoff1 hfirstRD
    exact attesterRuntime_block_2567
      (by simp only [attesterRuntime_block_2539_fallthrough_stack, List.length_cons]; omega) hsecond
  have hsecond := attesterRuntime_block_2539_taken (x7 := ⟨4⟩)
    (by simp only [List.length_cons]; omega)
    hoff1 (by rw [attesterRuntime_validJumps]; native_decide) hfirstRD
  have hview2 := attesterRuntime_block_2571 (by simp only [List.length_cons]; omega)
    (by rw [attesterRuntime_validJumps]; native_decide) hsecond
  rcases attesterArrayView hview2 (by simp only [List.length_cons]; omega)
      (by rw [attesterRuntime_validJumps]; native_decide) with hrev | ⟨hsecond, k'', C'', hsecondRD⟩
  · exact .inl ⟨fun hc ↦ hrev.1 hc.second, hrev.2⟩
  have hret := attesterRuntime_block_2583 (by omega) hvalid hsecondRD
  exact .inr ⟨⟨htuple, hoff0, hfirst, hoff1, hsecond⟩, _, _, hret⟩

end Benchmarks.EAS.Attester
