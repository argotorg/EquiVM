import Benchmarks.EAS.Attester.Dispatch
import Benchmarks.EAS.Attester.Decode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attesterRevokeDispatch {cd : ByteArray}
    (hsel : (attesterRevokeSelBytes == cd.extract 0 4) = true) :
    dispatchMsg contract cd = some revokeTransition := by
  have heq := byteArray_eq_of_beq hsel
  rw [dispatchMsg_eq_dispatchList contract cd, contract_transitions]
  simp only [dispatchList_cons, dispatchList_nil, attestSelectorOf, multiAttestSelectorOf,
    multiRevokeSelectorOf, revokeSelectorOf, ← heq]
  rfl

theorem attesterRevokeReachDecode {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = immutableLayout.runtime attesterBytecode words)
    (hvalue : I.weiValue = ⟨0⟩) (hsize : I.calldata.size < UInt256.size)
    (hsel : (attesterRevokeSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨2662⟩ [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨190⟩, ⟨100⟩, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  have hsz := calldata_size_ge_of_selIs I attesterRevokeSelBytes rfl hsel
  have heq := byteArray_eq_of_beq hsel
  obtain ⟨k, C, rd65⟩ := attesterRuntimeReach65 hcode hvalue hsz hsize
    (by rw [← heq]; decide) (by rw [← heq]; decide) (by rw [← heq]; decide)
  have rd176 := attesterRuntime_block_65_taken (by decide)
    (by change UInt256.eq ⟨0xc2664610⟩ (solcSelectorWord I) ≠ ⟨0⟩
        rw [attesterRevokeEvmSelector hsz, hsel]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) rd65
  have rd2662 := attesterRuntime_block_176 (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) rd176
  exact ⟨_, _, rd2662⟩

theorem attesterRevokeReachBody {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    {k C : Nat}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨2662⟩ [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨190⟩, ⟨100⟩, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C)
    (hlen : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k' C', RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨2187⟩ [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨100⟩, solcSelectorWord I]
      solcFreePtrMem ⟨3⟩ ByteArray.empty σ k' C' := by
  obtain ⟨k', C', rd190⟩ := attesterDecodeTwoWords h (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) hlen hhi hsize
  have rd2187 := attesterRuntime_block_190 (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) rd190
  exact ⟨_, _, rd2187⟩

end Benchmarks.EAS.Attester
