import Benchmarks.Morpho.MorphoBlue.SafeTransferEncode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferEntryPC (isFrom : Bool) : UInt256 := UInt256.ofNat (if isFrom then 15033 else 14666)
def safeTransferEVMArgs (isFrom : Bool) (token sender recipient : AccountAddress) (value : UInt256) : List UInt256 :=
  [UInt256.ofNat token.val] ++ (if isFrom then [UInt256.ofNat sender.val] else []) ++
    [UInt256.ofNat recipient.val, value]
def safeTransferCodeCond (σ : AccountMap) (token : AccountAddress) : UInt256 :=
  UInt256.isZero (UInt256.isZero (extCodeSizeWord σ (UInt256.ofNat token.val)))

theorem safeTransferCodeCond_zero {σ : AccountMap} {token : AccountAddress}
    (h : extCodeSizeWord σ (UInt256.ofNat token.val) = UInt256.ofNat 0) :
    safeTransferCodeCond σ token = UInt256.ofNat 0 := by rw [safeTransferCodeCond, h]; rfl

theorem safeTransferCodeCond_ne {σ : AccountMap} {token : AccountAddress}
    (h : extCodeSizeWord σ (UInt256.ofNat token.val) ≠ UInt256.ofNat 0) :
    safeTransferCodeCond σ token ≠ UInt256.ofNat 0 := by
  rw [safeTransferCodeCond, isZero_eq_zero_of_ne h]; decide

theorem safeTransferEncodeStack_length (isFrom : Bool) (token sender recipient : AccountAddress)
    (value ret : UInt256) (R : List UInt256) :
    (safeTransferEncodeStack isFrom token sender recipient value ret R).length = R.length + 10 := by
  cases isFrom <;> simp [safeTransferEncodeStack, Nat.add_comm] <;> omega

theorem safeTransferInputAllocation_eq (isFrom : Bool) :
    safeTransferInputAllocation isFrom = 64 + safeTransferCallAllocation isFrom := by
  cases isFrom <;> rfl

theorem morphoTransferEntry {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw value ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (token sender recipient : AccountAddress)
    (hstack : R.length + 14 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferEntryPC isFrom)
      (safeTransferEVMArgs isFrom token sender recipient value ++ ret :: R) mem aw out σ k C) :
    ∃ a k C, RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14491)
      (UInt256.ofNat 585 :: safeTransferCodeCond σ token :: safeTransferEncodePC isFrom ::
        safeTransferEncodeStack isFrom token sender recipient value ret R) mem a out σ k C := by
  have ht : UInt256.land (UInt256.ofNat token.val)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat token.val :=
    addressWord_val_clean token
  cases isFrom
  · obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_14666_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 13 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [morphoBlocks.morpho_block_14666_stack] at rd
    rw [ht] at rd
    exact ⟨a, k, C, rd⟩
  · obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_15033_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 1 + 13 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [morphoBlocks.morpho_block_15033_stack] at rd
    rw [ht] at rd
    exact ⟨a, k, C, rd⟩

theorem morphoTransferNoCode {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr value ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (token sender recipient : AccountAddress)
    (hstack : R.length + 21 ≤ 1024) (hm : MorphoHeap mem ptr 0)
    (hc : extCodeSizeWord σ (UInt256.ofNat token.val) = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferEntryPC isFrom)
      (safeTransferEVMArgs isFrom token sender recipient value ++ ret :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a, k, C, rd⟩ := morphoTransferEntry isFrom token sender recipient (by omega) h
  exact morphoTransferCodeRevert (by rw [safeTransferEncodeStack_length]; omega) hm
    (Or.inr (safeTransferCodeCond_zero hc)) rd

theorem morphoTransferInputOverflow {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr value ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (token sender recipient : AccountAddress)
    (hstack : R.length + 21 ≤ 1024) (hm : MorphoHeap mem ptr 0)
    (hbad : 2 ^ 64 ≤ ptr.toNat + safeTransferInputAllocation isFrom)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferEntryPC isFrom)
      (safeTransferEVMArgs isFrom token sender recipient value ++ ret :: R) mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a0, k0, C0, rd0⟩ := morphoTransferEntry isFrom token sender recipient (by omega) h
  by_cases hf : ptr.toNat + 64 < 2 ^ 64
  · by_cases hc : extCodeSizeWord σ (UInt256.ofNat token.val) = UInt256.ofNat 0
    · exact morphoTransferCodeRevert (by rw [safeTransferEncodeStack_length]; omega) hm
        (Or.inr (safeTransferCodeCond_zero hc)) rd0
    · obtain ⟨a1, k1, C1, rd1⟩ := morphoTransferCodeOk
        (by rw [safeTransferEncodeStack_length]; omega) hm.free hf (safeTransferCodeCond_ne hc)
        (by cases isFrom <;> rw [morphoPatchedValidJumps v] <;> jump_dest) rd0
      have hm1 : MorphoHeap (safeTransferNoCodeMem mem) (ptr + UInt256.ofNat 64) 0 :=
        hm.errorMessage _ _ hf
      have hp := uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
      obtain ⟨a2, k2, C2, rd2⟩ := morphoTransferEncode isFrom token sender recipient (by omega)
        hm1.free (by have hs := hm1.space; change _ < 2 ^ 256; omega) rd1
      rw [List.append_assoc] at rd2
      apply morphoTransferAllocateOverflow (ptr := ptr + UInt256.ofNat 64)
        (ret := safeTransferBeforeCallPC isFrom)
        (R := [ptr + UInt256.ofNat 64, UInt256.ofNat 0, (ptr + UInt256.ofNat 64) + UInt256.ofNat 32,
          UInt256.ofNat token.val, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 15005, ret] ++ R)
        isFrom (by change R.length + 8 + 5 ≤ 1024; omega)
        (by rw [hp]; omega) ?_ rd2
      rw [safeTransferInputAllocation_eq] at hbad
      rw [hp]
      omega
  · exact morphoTransferCodeRevert (by rw [safeTransferEncodeStack_length]; omega) hm
      (Or.inl (by omega)) rd0

theorem morphoTransferCallReady {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (token : AccountAddress)
    (hstack : R.length + 9 ≤ 1024) (hlen : memLoad ptr mem = UInt256.ofNat (safeTransferCallSize isFrom))
    (h : RD (deployedRuntime v) ee g s0 (safeTransferBeforeCallPC isFrom)
      ([ptr, UInt256.ofNat 0, ptr + UInt256.ofNat 32, UInt256.ofNat token.val,
        UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 15005, ret] ++ R) mem aw out σ k C) :
    ∃ gasArg a k C, RD (deployedRuntime v) ee g s0 (safeTransferCallPC isFrom)
      ([gasArg, UInt256.ofNat token.val, UInt256.ofNat 0, ptr + UInt256.ofNat 32,
        UInt256.ofNat (safeTransferCallSize isFrom), UInt256.ofNat 0, UInt256.ofNat 0,
        UInt256.ofNat 15005, ret] ++ R) mem a out σ k C := by
  cases isFrom
  · obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_14854_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 5 ≤ 1024; omega) h
    dsimp only [morphoBlocks.morpho_block_14854_stack] at rd
    rw [hlen] at rd
    exact ⟨_, a, k, C, rd⟩
  · obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_15159_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 4 + 5 ≤ 1024; omega) h
    dsimp only [morphoBlocks.morpho_block_15159_stack] at rd
    rw [hlen] at rd
    exact ⟨_, a, k, C, rd⟩

end Benchmarks.Morpho.MorphoBlue
