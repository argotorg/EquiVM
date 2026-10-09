import Benchmarks.Morpho.MorphoBlue.SafeTransferMessages
import Benchmarks.Morpho.MorphoBlue.ReturnBoolDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferDecodePC (isFrom : Bool) : UInt256 := UInt256.ofNat (if isFrom then 15310 else 15007)
def safeTransferAfterDecodePC (isFrom : Bool) : UInt256 := UInt256.ofNat (if isFrom then 15329 else 15026)
def safeTransferBoolStatus (out : ByteArray) : UInt256 :=
  if out.size = 0 then UInt256.ofNat 1 else calldataWord out 0

-- LIBRARY CANDIDATE: length of a bytes payload expressed by its two memory endpoints.
theorem returnData_span (ptr len : UInt256) :
    UInt256.sub ((ptr + len) + UInt256.ofNat 32) (ptr + UInt256.ofNat 32) = len := by
  rw [u256_add_assoc, u256_add_comm len (UInt256.ofNat 32), ← u256_add_assoc,
    word_add_sub_left]

theorem morphoTransferBoolPrepare {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out rdata : ByteArray} {aw data : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool)
    (hb : out.size < 2 ^ 64) (hn : out.size ≠ 0)
    (hlen : memLoad data mem = UInt256.ofNat out.size) (hstack : R.length + 6 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferBoolPC isFrom)
      (data :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14642)
      ((data + UInt256.ofNat 32) :: ((data + UInt256.ofNat out.size) + UInt256.ofNat 32) ::
        safeTransferAfterDecodePC isFrom :: R) mem aw' rdata σ k' C' := by
  have hsize : out.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hnw : UInt256.ofNat out.size ≠ UInt256.ofNat 0 := by
    intro he; have he := congrArg UInt256.toNat he
    rw [UInt256.toNat_ofNat_of_lt hsize] at he
    exact hn he
  have hcond : UInt256.isZero (UInt256.isZero (memLoad data mem)) ≠ UInt256.ofNat 0 := by
    rw [hlen, isZero_eq_zero_of_ne hnw]; decide
  have hprep : ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (safeTransferDecodePC isFrom)
      (UInt256.ofNat out.size :: data :: UInt256.isZero (UInt256.ofNat out.size) :: R)
      mem aw' rdata σ k' C' := by
    cases isFrom
    · obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_14930_taken_packed
        (immWords := wordsOf (immStore v)) (by omega) hcond
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
      dsimp only [morphoBlocks.morpho_block_14930_taken_stack] at rd
      rw [hlen] at rd
      exact ⟨a, k, C, rd⟩
    · obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_15235_taken_packed
        (immWords := wordsOf (immStore v)) (by omega) hcond
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
      dsimp only [morphoBlocks.morpho_block_15235_taken_stack] at rd
      rw [hlen] at rd
      exact ⟨a, k, C, rd⟩
  obtain ⟨a, k, C, rd⟩ := hprep
  cases isFrom
  · exact morphoBlocks.morpho_block_15007_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd
  · exact morphoBlocks.morpho_block_15310_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd

theorem morphoTransferBoolRouteRevert {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out rdata : ByteArray} {aw data : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool)
    (hb : out.size < 2 ^ 64) (hn : out.size ≠ 0) (hv : ¬ BoolReturnValid out)
    (hlen : memLoad data mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (data + UInt256.ofNat 32) mem = calldataWord out 0)
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferBoolPC isFrom)
      (data :: R) mem aw rdata σ k C) :
    ABI.decodeReturnValue? abiBool out = none ∧ RDrev (deployedRuntime v) g s0 := by
  obtain ⟨a, k, C, rd⟩ := morphoTransferBoolPrepare isFrom hb hn hlen hstack h
  exact morphoReturnBoolDecodeRevert (by omega) hv (returnData_span _ _) hword (by omega) rd

theorem morphoTransferBoolRouteOk {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out rdata : ByteArray} {aw data : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool)
    (hb : out.size < 2 ^ 64) (hv : out.size = 0 ∨ BoolReturnValid out)
    (hlen : memLoad data mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (data + UInt256.ofNat 32) mem = calldataWord out 0)
    (hstack : R.length + 6 ≤ 1024)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferBoolPC isFrom)
      (data :: R) mem aw rdata σ k C) :
    ∃ a b aw' k' C', RD (deployedRuntime v) ee g s0 (safeTransferResultPC isFrom)
      (a :: b :: safeTransferBoolStatus out :: R) mem aw' rdata σ k' C' := by
  by_cases hn : out.size = 0
  · have hcond : UInt256.isZero (UInt256.isZero (memLoad data mem)) = UInt256.ofNat 0 := by
      rw [hlen, hn]; rfl
    cases isFrom
    · obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_14930_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by omega) hcond h
      dsimp only [morphoBlocks.morpho_block_14930_fallthrough_stack] at rd
      rw [hlen, hn] at rd
      exact ⟨UInt256.ofNat 0, data, a, k, C, by simpa only [safeTransferBoolStatus, if_pos hn] using rd⟩
    · obtain ⟨a, k, C, rd⟩ := morphoBlocks.morpho_block_15235_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by omega) hcond h
      dsimp only [morphoBlocks.morpho_block_15235_fallthrough_stack] at rd
      rw [hlen, hn] at rd
      exact ⟨UInt256.ofNat 0, data, a, k, C, by simpa only [safeTransferBoolStatus, if_pos hn] using rd⟩
  · obtain ⟨a, k, C, rd⟩ := morphoTransferBoolPrepare isFrom hb hn hlen hstack h
    have hv := hv.resolve_left hn
    obtain ⟨_, a1, k1, C1, rd1⟩ := morphoReturnBoolDecodeOk (by omega) hv
      (returnData_span _ _) (hword hv.1) (by omega)
      (by cases isFrom <;> rw [morphoPatchedValidJumps v] <;> jump_dest) rd
    have hout : safeTransferBoolStatus out = calldataWord out 0 := if_neg hn
    rw [← hout] at rd1
    cases isFrom
    · obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_15026_packed
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact ⟨_, _, a2, k2, C2, rd2⟩
    · obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_15329_packed
        (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact ⟨_, _, a2, k2, C2, rd2⟩

end Benchmarks.Morpho.MorphoBlue
