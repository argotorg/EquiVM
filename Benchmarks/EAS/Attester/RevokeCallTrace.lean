import Benchmarks.EAS.Attester.RevokeTrace
import Benchmarks.EAS.Attester.RevokeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

theorem revokePrepare {words : String → UInt256} {I g s0 σ k C sel schema uid}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2187⟩
      [uid, schema, ⟨100⟩, sel] solcFreePtrMem ⟨3⟩ ByteArray.empty σ k C) :
    ∃ aw k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2321⟩
      [words "_eas", ⟨256⟩, uid, schema, ⟨100⟩, sel]
      (revokeMemory schema uid) aw ByteArray.empty σ k' C' := by
  obtain ⟨aw, k', C', h'⟩ := attesterRuntime_block_2187_packed (by simp) h
  exact ⟨aw, k', C', by simpa only [revokeMemory_stack, revokeMemory_summary] using h'⟩

theorem revokeNoCode {words : String → UInt256} {I g s0 σ k C sel schema uid aw}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2321⟩
      [words "_eas", ⟨256⟩, uid, schema, ⟨100⟩, sel]
      (revokeMemory schema uid) aw ByteArray.empty σ k C)
    (hzero : extCodeSizeWord σ (UInt256.land solcAddrMask (words "_eas")) = ⟨0⟩) :
    RDrev (immutableLayout.runtime attesterBytecode words) g s0 := by
  obtain ⟨k', C', h'⟩ := attesterRuntime_block_2321_fallthrough (by simp)
    (by change UInt256.isZero (UInt256.isZero
          (extCodeSizeWord σ (UInt256.land solcAddrMask (words "_eas")))) = ⟨0⟩
        rw [hzero]; rfl) h
  exact attesterRuntime_block_2374 (by simp [attesterRuntime_block_2321_fallthrough_stack]) h'

theorem revokeReachCall {words : String → UInt256} {I g s0 σ k C sel schema uid aw}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2321⟩
      [words "_eas", ⟨256⟩, uid, schema, ⟨100⟩, sel]
      (revokeMemory schema uid) aw ByteArray.empty σ k C)
    (hne : extCodeSizeWord σ (UInt256.land solcAddrMask (words "_eas")) ≠ ⟨0⟩) :
    ∃ gasArg aw' k' C', RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2381⟩
      [gasArg, UInt256.land solcAddrMask (words "_eas"), ⟨0⟩, ⟨256⟩, ⟨100⟩, ⟨256⟩, ⟨0⟩,
        ⟨356⟩, ⟨1183998567⟩, UInt256.land solcAddrMask (words "_eas"), uid, schema, ⟨100⟩, sel]
      (revokeMemory schema uid) aw' ByteArray.empty σ k' C' := by
  obtain ⟨k', C', h'⟩ := attesterRuntime_block_2321_taken (by simp)
    (by change UInt256.isZero (UInt256.isZero
          (extCodeSizeWord σ (UInt256.land solcAddrMask (words "_eas")))) ≠ ⟨0⟩
        rw [isZero_eq_zero_of_ne hne]; decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  simp only [attesterRuntime_block_2321_taken_stack, revokeMemory_freePtr] at h'
  have h'' := attesterRuntime_block_2378 (by simp) h'
  exact ⟨_, _, _, _, h''⟩

theorem revokeAfterCallFailure {words : String → UInt256} {I g s0 σ k C mem aw out R}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2382⟩
      (⟨0⟩ :: R) mem aw out σ k C) (hstack : R.length + 4 ≤ 1024) :
    RDrev (immutableLayout.runtime attesterBytecode words) g s0 := by
  have h' := attesterRuntime_block_2382_fallthrough (by omega) (by decide) h
  exact attesterRuntime_block_2389
    (by simpa only [attesterRuntime_block_2382_fallthrough_stack, List.length_cons] using hstack) h'

theorem revokeAfterCallSuccess {words : String → UInt256} {I g s0 σ k C mem aw out sel}
    {x0 x1 x2 x3 x4 : UInt256}
    (h : RD (immutableLayout.runtime attesterBytecode words) I g s0 ⟨2382⟩
      [⟨1⟩, x0, x1, x2, x3, x4, ⟨100⟩, sel] mem aw out σ k C) :
    RDret (immutableLayout.runtime attesterBytecode words) g s0 σ ByteArray.empty := by
  have h' := attesterRuntime_block_2382_taken (by simp) (by decide)
    (by rw [attesterRuntime_validJumps]; native_decide) h
  have h'' := attesterRuntime_block_2398 (by simp)
    (by rw [attesterRuntime_validJumps]; native_decide) h'
  exact attesterRuntime_block_100 (by simp [attesterRuntime_block_2398_stack]) h''

end Benchmarks.EAS.Attester
