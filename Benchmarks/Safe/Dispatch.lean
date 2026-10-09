import Benchmarks.Safe.Common
import Benchmarks.Safe.Blocks.Runtime_001
import Benchmarks.Safe.Blocks.Runtime_002
import Benchmarks.Safe.Blocks.Runtime_003
import Benchmarks.Safe.Blocks.Runtime_004

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeReachShort {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hshort : I.calldata.size < 4) :
    ∃ k C, RD safeBytecode I g (initState σ σ₀ g A I) ⟨475⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hlt : UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4) ≠
      UInt256.ofNat 0 := by
    rw [ult_one (by
      rw [ulit_toNat' _ (lt_size_of_lt256 (by omega))]
      exact hshort)]
    decide
  have h := safeRuntime_block_0_taken (by decide) hlt (by jump_dest)
    (RD.initState (σ := σ) (σ₀ := σ₀) (g := g) (A := A) hcode)
  exact ⟨_, _, h⟩

/-- First equality arm selected by Safe's binary selector search. -/
def safeSelectorStart (w : UInt256) : UInt256 :=
  if UInt256.gt ⟨0xaffed0e0⟩ w = ⟨0⟩ then
    if UInt256.gt ⟨0xe19a9dd9⟩ w = ⟨0⟩ then
      if UInt256.gt ⟨0xf698da25⟩ w = ⟨0⟩ then ⟨51⟩ else ⟨100⟩
    else if UInt256.gt ⟨0xd4d9bdcd⟩ w = ⟨0⟩ then ⟨160⟩ else ⟨209⟩
  else if UInt256.gt ⟨0x5624b25b⟩ w = ⟨0⟩ then
    if UInt256.gt ⟨0x6a761202⟩ w = ⟨0⟩ then ⟨280⟩ else ⟨329⟩
  else if UInt256.gt ⟨0x2d9ad53d⟩ w = ⟨0⟩ then ⟨389⟩ else ⟨438⟩

set_option maxRecDepth 100000 in
theorem safeReachSelectorGroup {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hlong : 4 ≤ I.calldata.size) :
    ∃ k C, RD safeBytecode I g (initState σ σ₀ g A I) (safeSelectorStart (selWord I))
      [selWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hlt : UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4) =
      UInt256.ofNat 0 := by
    apply ult_zero
    rw [ulit_toNat' _ hsize, ulit_toNat' _ (lt_size_of_lt256 (by decide))]
    omega
  have h13 := safeRuntime_block_0_fallthrough (by decide) hlt
    (RD.initState (σ := σ) (σ₀ := σ₀) (g := g) (A := A) hcode)
  unfold safeSelectorStart
  by_cases hroot : UInt256.gt ⟨0xaffed0e0⟩ (selWord I) = ⟨0⟩
  · rw [if_pos hroot]
    have h29 := safeRuntime_block_13_fallthrough (by decide) hroot h13
    by_cases hhigh : UInt256.gt ⟨0xe19a9dd9⟩ (selWord I) = ⟨0⟩
    · rw [if_pos hhigh]
      have h40 := safeRuntime_block_29_fallthrough (by decide) hhigh h29
      by_cases hlast : UInt256.gt ⟨0xf698da25⟩ (selWord I) = ⟨0⟩
      · rw [if_pos hlast]
        exact ⟨_, _, safeRuntime_block_40_fallthrough (by decide) hlast h40⟩
      · rw [if_neg hlast]
        have h99 := safeRuntime_block_40_taken (by decide) hlast (by jump_dest) h40
        exact ⟨_, _, RD.jumpdest h99 (by native_decide) (by simp)⟩
    · rw [if_neg hhigh]
      have h148 := safeRuntime_block_29_taken (by decide) hhigh (by jump_dest) h29
      by_cases hlast : UInt256.gt ⟨0xd4d9bdcd⟩ (selWord I) = ⟨0⟩
      · rw [if_pos hlast]
        exact ⟨_, _, safeRuntime_block_148_fallthrough (by decide) hlast h148⟩
      · rw [if_neg hlast]
        have h208 := safeRuntime_block_148_taken (by decide) hlast (by jump_dest) h148
        exact ⟨_, _, RD.jumpdest h208 (by native_decide) (by simp)⟩
  · rw [if_neg hroot]
    have h257 := safeRuntime_block_13_taken (by decide) hroot (by jump_dest) h13
    by_cases hlow : UInt256.gt ⟨0x5624b25b⟩ (selWord I) = ⟨0⟩
    · rw [if_pos hlow]
      have h269 := safeRuntime_block_257_fallthrough (by decide) hlow h257
      by_cases hlast : UInt256.gt ⟨0x6a761202⟩ (selWord I) = ⟨0⟩
      · rw [if_pos hlast]
        exact ⟨_, _, safeRuntime_block_269_fallthrough (by decide) hlast h269⟩
      · rw [if_neg hlast]
        have h328 := safeRuntime_block_269_taken (by decide) hlast (by jump_dest) h269
        exact ⟨_, _, RD.jumpdest h328 (by native_decide) (by simp)⟩
    · rw [if_neg hlow]
      have h377 := safeRuntime_block_257_taken (by decide) hlow (by jump_dest) h257
      by_cases hlast : UInt256.gt ⟨0x2d9ad53d⟩ (selWord I) = ⟨0⟩
      · rw [if_pos hlast]
        exact ⟨_, _, safeRuntime_block_377_fallthrough (by decide) hlast h377⟩
      · rw [if_neg hlast]
        have h437 := safeRuntime_block_377_taken (by decide) hlast (by jump_dest) h377
        exact ⟨_, _, RD.jumpdest h437 (by native_decide) (by simp)⟩

/-- Finite certificate for the equality arms between a selector group and its body entry. -/
def safeDispatchCertificate (w : UInt256) (i : ℕ) (bodyPc : UInt256) : Prop :=
  (∀ j : Fin (i + 1), armWellFormed safeBytecode
    (nthArmPc safeBytecode (safeSelectorStart w) j)) ∧
  (∀ j : Fin i, UInt256.eq
    (armSelNat safeBytecode (nthArmPc safeBytecode (safeSelectorStart w) j)) w = ⟨0⟩) ∧
  UInt256.eq (armSelNat safeBytecode
    (nthArmPc safeBytecode (safeSelectorStart w) i)) w ≠ ⟨0⟩ ∧
  (D_J safeBytecode 0).contains bodyPc = true ∧
  armTgt safeBytecode (nthArmPc safeBytecode (safeSelectorStart w) i) = bodyPc

set_option synthInstance.maxSize 10000 in
instance (w : UInt256) (i : ℕ) (bodyPc : UInt256) :
    Decidable (safeDispatchCertificate w i bodyPc) := by
  unfold safeDispatchCertificate
  infer_instance

theorem safeReachEntry {σ σ₀ A I} {g : Sat256} (w : UInt256) (i : ℕ) (bodyPc : UInt256)
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hlong : 4 ≤ I.calldata.size) (hword : selWord I = w)
    (hcert : safeDispatchCertificate w i bodyPc) :
    ∃ k C, RD safeBytecode I g (initState σ σ₀ g A I) bodyPc
      [selWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, hgroup⟩ := safeReachSelectorGroup (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsize hlong
  rw [hword] at hgroup ⊢
  rcases hcert with ⟨hwf, hskip, htake, hjd, hbody⟩
  exact RD.dispatchTo bodyPc i hgroup
    (fun j hj ↦ hwf ⟨j, by omega⟩) (fun j hj ↦ hskip ⟨j, hj⟩)
    htake (by rw [hbody]; exact hjd) hbody (by decide)

end Benchmarks.Safe
