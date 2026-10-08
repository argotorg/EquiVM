import Benchmarks.EAS.Attester.ArrayDecodeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

def nestedHead (cd : ByteArray) (base entry : UInt256) : UInt256 :=
  base + calldataWord cd entry.toNat

def rowEntry (base : UInt256) (i : Nat) : UInt256 :=
  base + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat i)

def rowHead (cd : ByteArray) (base : UInt256) (i : Nat) : UInt256 :=
  nestedHead cd base (rowEntry base i)

def rowLength (cd : ByteArray) (base : UInt256) (i : Nat) : UInt256 :=
  calldataWord cd (rowHead cd base i).toNat

def rowData (cd : ByteArray) (base : UInt256) (i : Nat) : UInt256 :=
  UInt256.ofNat 32 + rowHead cd base i

structure NestedHeadChecks (cd : ByteArray) (base entry : UInt256) : Prop where
  header : UInt256.slt (calldataWord cd entry.toNat)
    (UInt256.sub (UInt256.ofNat cd.size) base + UInt256.ofNat (UInt256.size - 31)) ≠ UInt256.ofNat 0
  length : UInt256.isZero (UInt256.gt (calldataWord cd (nestedHead cd base entry).toNat)
    (UInt256.ofNat 18446744073709551615)) ≠ UInt256.ofNat 0
  payload : UInt256.isZero (UInt256.sgt (UInt256.ofNat 32 + nestedHead cd base entry)
    (UInt256.sub (UInt256.ofNat cd.size)
      (UInt256.shiftLeft (calldataWord cd (nestedHead cd base entry).toNat) (UInt256.ofNat 5)))) ≠
          UInt256.ofNat 0

theorem attesterNestedView {words : String → UInt256} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {mem rdata : ByteArray} {aw ret base entry : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) ee g s0 ⟨2790⟩
      (base :: entry :: ret :: R) mem aw rdata σ k C)
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (immutableLayout.runtime attesterBytecode words) 0).contains ret = true) :
    (¬ NestedHeadChecks ee.calldata base entry ∧
      RDrev (immutableLayout.runtime attesterBytecode words) g s0) ∨
      (NestedHeadChecks ee.calldata base entry ∧ ∃ k' C',
        RD (immutableLayout.runtime attesterBytecode words) ee g s0 ret
          (calldataWord ee.calldata (nestedHead ee.calldata base entry).toNat ::
            (UInt256.ofNat 32 + nestedHead ee.calldata base entry) :: R)
          mem aw rdata σ k' C') := by
  by_cases hhead : UInt256.slt (calldataWord ee.calldata entry.toNat)
      (UInt256.sub (UInt256.ofNat ee.calldata.size) base + UInt256.ofNat (UInt256.size - 31)) =
          UInt256.ofNat 0
  · left
    refine ⟨fun hc ↦ hc.header hhead, ?_⟩
    have h' := attesterRuntime_block_2790_fallthrough (x1 := entry)
      (by simp only [List.length_cons]; omega) hhead h
    exact attesterRuntime_block_2839
      (by simp only [attesterRuntime_block_2790_fallthrough_stack, List.length_cons]; omega) h'
  have h' := attesterRuntime_block_2790_taken (x1 := entry)
    (by simp only [List.length_cons]; omega) hhead
    (by rw [attesterRuntime_validJumps]; native_decide) h
  by_cases hlen : UInt256.isZero (UInt256.gt
      (calldataWord ee.calldata (nestedHead ee.calldata base entry).toNat)
      (UInt256.ofNat 18446744073709551615)) = UInt256.ofNat 0
  · left
    refine ⟨fun hc ↦ hc.length hlen, ?_⟩
    have h'' := attesterRuntime_block_2843_fallthrough (x3 := base)
      (x0 := calldataWord ee.calldata entry.toNat) (by simp only [List.length_cons]; omega) hlen h'
    exact attesterRuntime_block_2866
      (by simp only [attesterRuntime_block_2843_fallthrough_stack, List.length_cons]; omega) h''
  have h'' := attesterRuntime_block_2843_taken (x3 := base)
    (x0 := calldataWord ee.calldata entry.toNat) (by simp only [List.length_cons]; omega) hlen
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  by_cases hend : UInt256.isZero (UInt256.sgt (UInt256.ofNat 32 + nestedHead ee.calldata base entry)
      (UInt256.sub (UInt256.ofNat ee.calldata.size)
        (UInt256.shiftLeft (calldataWord ee.calldata (nestedHead ee.calldata base entry).toNat)
          (UInt256.ofNat 5)))) = UInt256.ofNat 0
  · left
    refine ⟨fun hc ↦ hc.payload hend, ?_⟩
    have h''' := attesterRuntime_block_2870_fallthrough (by simp only [List.length_cons]; omega)
        hend h''
    exact attesterRuntime_block_2890
      (by simp only [attesterRuntime_block_2870_fallthrough_stack, List.length_cons]; omega) h'''
  have h''' := attesterRuntime_block_2870_taken (by simp only [List.length_cons]; omega) hend
    (by rw [attesterRuntime_validJumps]; native_decide) h''
  have hret := attesterRuntime_block_2475 (by omega) hvalid h'''
  exact .inr ⟨⟨hhead, hlen, hend⟩, _, _, hret⟩

end Benchmarks.EAS.Attester
