import Benchmarks.EAS.Attester.AttestTrace
import Benchmarks.EAS.Attester.AttestReturnMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attestAfterCallFailure {words : String → UInt256} {I g s0 σ k C mem aw out R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2128⟩
      (⟨0⟩ :: R) mem aw out σ k C) (hstack : R.length + 4 ≤ 1024) :
    RDrev (immutableLayout.runtime attesterBytecode words) g s0 := by
  have h' := attesterRuntime_block_2128_fallthrough (by omega) (by decide) h
  exact attesterRuntime_block_2135
    (by simpa only [attesterRuntime_block_2128_fallthrough_stack, List.length_cons] using hstack) h'

theorem attestReachDecodeReturn {words : String → UInt256} {I g s0 σ k C aw out sel schema input t}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2128⟩
      [⟨1⟩, ⟨804⟩, ⟨4050855399⟩, t, ⟨0⟩, input, schema, ⟨162⟩, sel]
      (attestOutputMemory schema input out) aw out σ k C) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3827⟩
      [⟨448⟩, ⟨448⟩ + UInt256.ofNat out.size, ⟨2180⟩, ⟨0⟩, input, schema, ⟨162⟩, sel]
      (attestDecodedMemory schema input out) aw' out σ k' C' := by
  have h' := attesterRuntime_block_2128_taken (by simp) (by decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  obtain ⟨aw', k', C', h''⟩ := attesterRuntime_block_2144_packed
    (by simp) (by rw [attesterRuntime_validJumps]; native_decide) h'
  simp only [attesterRuntime_block_2144_stack, attesterRuntime_block_2144_memory,
    attestOutputMemory_freePtr] at h''
  exact ⟨aw', k', C', h''⟩

theorem attestDecodeReturnShort {words : String → UInt256} {I g s0 σ k C aw out mem R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3827⟩
      (⟨448⟩ :: (⟨448⟩ + UInt256.ofNat out.size) :: R) mem aw out σ k C)
    (hstack : R.length + 6 ≤ 1024) (hshort : out.size < 32) :
    RDrev (immutableLayout.runtime attesterBytecode words) g s0 := by
  have hlen := solcReturnStaticLenCheckShort (base := 448) (words := 1) hshort
    (by decide) (by change 448 + out.size < 2 ^ 256; omega) (by decide)
  change UInt256.slt (UInt256.sub (⟨448⟩ + UInt256.ofNat out.size) ⟨448⟩) (UInt256.ofNat 32) = ⟨1⟩
      at hlen
  have h' := attesterRuntime_block_3827_fallthrough hstack (by rw [hlen]; rfl) h
  exact attesterRuntime_block_3841
    (by simp only [attesterRuntime_block_3827_fallthrough_stack, List.length_cons]; omega) h'

theorem attestDecodeReturn {words : String → UInt256} {I g s0 σ k C aw out sel schema input}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨3827⟩
      [⟨448⟩, ⟨448⟩ + UInt256.ofNat out.size, ⟨2180⟩, ⟨0⟩, input, schema, ⟨162⟩, sel]
      (attestDecodedMemory schema input out) aw out σ k C)
    (hlen : 32 ≤ out.size) (hhi : out.size < 2 ^ 255) :
    ∃ aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨162⟩
      [calldataWord out 0, sel] (attestDecodedMemory schema input out) aw' out σ k' C' := by
  have hcheck := solcReturnStaticLenCheckOk (base := 448) (words := 1) hlen hhi
    (by decide) (by change 448 + out.size < 2 ^ 256; omega)
  change UInt256.slt (UInt256.sub (⟨448⟩ + UInt256.ofNat out.size) ⟨448⟩) (UInt256.ofNat 32) = ⟨0⟩
      at hcheck
  have h' := attesterRuntime_block_3827_taken (by simp) (by rw [hcheck]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  obtain ⟨aw', k', C', h''⟩ := attesterRuntime_block_3845_packed (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  have hw := attestDecodedMemory_word (schema := schema) (input := input) hlen
  change memLoad ⟨448⟩ (attestDecodedMemory schema input out) = calldataWord out 0 at hw
  simp only [attesterRuntime_block_3845_stack, hw] at h''
  have h''' := attesterRuntime_block_2180 (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) h''
  exact ⟨_, _, _, h'''⟩

theorem attestReturnWord {words : String → UInt256} {I g s0 σ k C aw out mem R uid ptr}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨162⟩
      (uid :: R) mem aw out σ k C)
    (hstack : R.length + 3 ≤ 1024) (hsize : 96 ≤ mem.size)
    (hptr : memLoad (UInt256.ofNat 64) mem = ptr) (hlo : 96 ≤ ptr.toNat) :
    RDret (immutableLayout.runtime attesterBytecode words) g s0 σ uid.toByteArray := by
  have h' := attesterRuntime_block_162 hstack
    (by rw [attesterRuntime_validJumps]; native_decide) h
  have hret := attesterRuntime_block_134 hstack h'
  simp only [attesterRuntime_block_162_memory, hptr] at hret
  have hp : memLoad (UInt256.ofNat 64) (uid.toByteArray.write 0 mem ptr.toNat 32) = ptr := by
    rw [memLoad_write_disjoint mem ptr.toNat (UInt256.ofNat 64) uid hsize (.inl hlo), hptr]
  rw [hp] at hret
  have hsub : UInt256.sub (UInt256.ofNat 32 + ptr) ptr = UInt256.ofNat 32 := by
    rw [u256_add_comm, ← u256_ofNat_toNat ptr]
    exact usub_uadd_lit_cancel_mod ptr.val.isLt (by decide)
  rw [hsub] at hret
  change RDret _ _ _ _ ((Reasoning.Theory.writeWord mem ptr.toNat uid).readWithPadding ptr.toNat 32)
      at hret
  simpa only [writeWord_sparse_read_back] using hret

end Benchmarks.EAS.Attester
