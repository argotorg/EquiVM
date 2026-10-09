import Benchmarks.EAS.Attester.Dispatch
import Benchmarks.EAS.Attester.Decode
import Benchmarks.EAS.Attester.AttestMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attesterAttestDispatch {cd : ByteArray}
    (hsel : (attesterAttestSelBytes == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some attestTransition := by
  rw [dispatchMsg_eq_dispatchList contract cd, contract_transitions]
  simp only [dispatchList_cons, attestSelectorOf, hsel, if_true]

theorem attesterAttestReachDecode {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = immutableLayout.runtime attesterBytecode words)
    (hvalue : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hsel : (attesterAttestSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨2662⟩ [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨157⟩, ⟨162⟩, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  have hsz := calldata_size_ge_of_selIs I attesterAttestSelBytes rfl hsel
  have heq := byteArray_eq_of_beq hsel
  obtain ⟨k, C, rd54⟩ := attesterRuntimeReach54 hcode hvalue hsz hsize
    (by rw [← heq]; decide) (by rw [← heq]; decide)
  have rd143 := attesterRuntime_block_54_taken (by decide)
    (by change UInt256.eq ⟨0x72b9966d⟩ (solcSelectorWord I) ≠ ⟨0⟩
        rw [attesterAttestEvmSelector hsz, hsel]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) rd54
  have rd2662 := attesterRuntime_block_143 (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) rd143
  exact ⟨_, _, rd2662⟩

theorem attesterAttestReachBody {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    {k C : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨2662⟩ [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨157⟩, ⟨162⟩, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C)
    (hlen : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k' C', RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨1884⟩ [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨162⟩, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k' C' := by
  obtain ⟨k', C', rd157⟩ := attesterDecodeTwoWords h (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) hlen hhi hsize
  have rd1884 := attesterRuntime_block_157 (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) rd157
  exact ⟨_, _, rd1884⟩

theorem attestReachCall {words : String → UInt256} {I g s0 σ k C sel schema input}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨1884⟩
      [input, schema, ⟨162⟩, sel] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C) :
    ∃ gasArg aw k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2127⟩
      [gasArg, UInt256.land solcAddrMask (words "_eas"), ⟨0⟩, ⟨448⟩, ⟨356⟩, ⟨448⟩, ⟨32⟩,
        ⟨804⟩, ⟨4050855399⟩, UInt256.land solcAddrMask (words "_eas"),
        ⟨0⟩, input, schema, ⟨162⟩, sel]
      (attestMemory schema input) aw ByteArray.empty σ k' C' := by
  obtain ⟨aw, k, C, h⟩ := attesterRuntime_block_1884_packed (by simp) h
  simp only [attestMemory0_summary, attestMemory0_stack] at h
  have h := attesterRuntime_block_2052 (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  obtain ⟨aw, k, C, h⟩ := attesterRuntime_block_2057_packed (x0 := ⟨448⟩) (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  simp only [attestMemory1_summary, attestMemory1_stack] at h
  obtain ⟨aw, k, C, h⟩ := attesterRuntime_block_3782_packed (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  simp only [attestMemory2_summary, attestMemory2_stack] at h
  obtain ⟨aw, k, C, h⟩ := attesterRuntime_block_3109_packed (by simp) h
  simp only [attestMemory3_summary, attestMemory3_stack] at h
  have h := attesterRuntime_block_3202_fallthrough (by simp) (by decide) h
  obtain ⟨aw, k, C, h⟩ := attesterRuntime_block_3211_packed (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  simp only [attestMemory4_summary, attesterRuntime_block_3211_stack] at h
  have h := attesterRuntime_block_3202_taken (by simp) (by decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  obtain ⟨aw, k, C, h⟩ := attesterRuntime_block_3231_packed (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  simp only [attestMemory_summary, attesterRuntime_block_3231_stack] at h
  have h := attesterRuntime_block_3819 (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  obtain ⟨aw, k, C, h⟩ := attesterRuntime_block_2113_packed (x0 := ⟨804⟩) (by simp) h
  simp only [attesterRuntime_block_2113_stack, attestMemory_freePtr] at h
  exact ⟨_, aw, k, C, h⟩

end Benchmarks.EAS.Attester
