import Benchmarks.EAS.Attester.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem attesterRuntimeRevertValue {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = immutableLayout.runtime attesterBytecode words)
    (hvalue : I.weiValue ≠ ⟨0⟩) :
    RDrev (immutableLayout.runtime attesterBytecode words) g (initState σ σ₀ g A I) := by
  have rd0 := RD.initState (σ := σ) (σ₀ := σ₀) (g := g) (A := A) hcode
  have rd12 := attesterRuntime_block_0_fallthrough (by decide)
    (isZero_eq_zero_of_ne hvalue) rd0
  exact attesterRuntime_block_12 (by simp [attesterRuntime_block_0_fallthrough_stack]) rd12

theorem attesterRuntimeReachSelector {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = immutableLayout.runtime attesterBytecode words)
    (hvalue : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨26⟩ [] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  have rd0 := RD.initState (σ := σ) (σ₀ := σ₀) (g := g) (A := A) hcode
  have rd16 := attesterRuntime_block_0_taken (by decide) (by rw [hvalue]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) rd0
  have rd26 := attesterRuntime_block_16_fallthrough (by decide)
    (lt_four_eq_zero_of_ge hsz hsize) rd16
  exact ⟨_, _, rd26⟩

theorem attesterRuntimeRevertShort {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = immutableLayout.runtime attesterBytecode words)
    (hvalue : I.weiValue = ⟨0⟩) (hshort : I.calldata.size < 4) :
    RDrev (immutableLayout.runtime attesterBytecode words) g (initState σ σ₀ g A I) := by
  have rd0 := RD.initState (σ := σ) (σ₀ := σ₀) (g := g) (A := A) hcode
  have rd16 := attesterRuntime_block_0_taken (by decide) (by rw [hvalue]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) rd0
  have rd76 := attesterRuntime_block_16_taken (by decide) (lt_four_ne_zero_of_lt hshort)
    (by rw [attesterRuntime_validJumps]; native_decide) rd16
  exact attesterRuntime_block_76 (by decide) rd76

theorem attesterRuntimeReach43 {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = immutableLayout.runtime attesterBytecode words)
    (hvalue : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false) :
    ∃ k C, RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨43⟩ [solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨k, C, rd26⟩ := attesterRuntimeReachSelector hcode hvalue hsz hsize
  have rd43 := attesterRuntime_block_26_fallthrough (by decide)
    (by change UInt256.eq ⟨0x13fde550⟩ (solcSelectorWord I) = ⟨0⟩
        rw [attesterMultiRevokeEvmSelector hsz, hmultiRevoke]; rfl) rd26
  exact ⟨_, _, rd43⟩

theorem attesterRuntimeReach54 {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = immutableLayout.runtime attesterBytecode words)
    (hvalue : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false) :
    ∃ k C, RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨54⟩ [solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨k, C, rd43⟩ := attesterRuntimeReach43 hcode hvalue hsz hsize hmultiRevoke
  have rd54 := attesterRuntime_block_43_fallthrough (by decide)
    (by change UInt256.eq ⟨0x54e1db35⟩ (solcSelectorWord I) = ⟨0⟩
        rw [attesterMultiAttestEvmSelector hsz, hmultiAttest]; rfl) rd43
  exact ⟨_, _, rd54⟩

theorem attesterRuntimeReach65 {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = immutableLayout.runtime attesterBytecode words)
    (hvalue : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false) :
    ∃ k C, RD (immutableLayout.runtime attesterBytecode words) I g (initState σ σ₀ g A I)
      ⟨65⟩ [solcSelectorWord I] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C := by
  obtain ⟨k, C, rd54⟩ := attesterRuntimeReach54 hcode hvalue hsz hsize hmultiRevoke hmultiAttest
  have rd65 := attesterRuntime_block_54_fallthrough (by decide)
    (by change UInt256.eq ⟨0x72b9966d⟩ (solcSelectorWord I) = ⟨0⟩
        rw [attesterAttestEvmSelector hsz, hattest]; rfl) rd54
  exact ⟨_, _, rd65⟩

theorem attesterRuntimeRevertUnknown {words : String → UInt256} {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = immutableLayout.runtime attesterBytecode words)
    (hvalue : I.weiValue = ⟨0⟩) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hrevoke : (attesterRevokeSelBytes == I.calldata.extract 0 4) = false) :
    RDrev (immutableLayout.runtime attesterBytecode words) g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd65⟩ :=
    attesterRuntimeReach65 hcode hvalue hsz hsize hmultiRevoke hmultiAttest hattest
  have rd76 := attesterRuntime_block_65_fallthrough (by decide)
    (by change UInt256.eq ⟨0xc2664610⟩ (solcSelectorWord I) = ⟨0⟩
        rw [attesterRevokeEvmSelector hsz, hrevoke]; rfl) rd65
  exact attesterRuntime_block_76 (by simp) rd76

end Benchmarks.EAS.Attester
