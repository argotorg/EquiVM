import Benchmarks.Safe.ViaIR.SelectorMiss
import Benchmarks.Safe.ViaIR.Blocks.Runtime_001
import Benchmarks.Safe.ViaIR.Blocks.Runtime_002
import Benchmarks.Safe.ViaIR.Blocks.Runtime_003
import Benchmarks.Safe.ViaIR.Blocks.Runtime_004

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000 in
theorem safeReachShort {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hshort : I.calldata.size < 4) :
    ∃ k C, RD fork safeBytecode I g (initState σ σ₀ g A I) ⟨14⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hlt : UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4) ≠
      UInt256.ofNat 0 := by
    rw [ult_one (by
      rw [ulit_toNat' _ (lt_size_of_lt256 (by omega))]
      exact hshort)]
    decide
  have h := safeRuntime_block_0_fallthrough (fork := fork) (by decide) (isZero_eq_zero_of_ne hlt)
    (RD.initState (fork := fork) (σ := σ) (σ₀ := σ₀) (g := g) (A := A) hcode)
  exact ⟨_, _, h⟩

/-- First equality arm of Safe's linear selector search. -/
def safeSelectorStart (_w : UInt256) : UInt256 := ⟨168⟩

set_option maxRecDepth 100000 in
theorem safeReachSelectorGroup {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hlong : 4 ≤ I.calldata.size) :
    ∃ k C, RD fork safeBytecode I g (initState σ σ₀ g A I) (safeSelectorStart (selWord I))
      [selWord I, ⟨0⟩] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hlt : UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 4) =
      UInt256.ofNat 0 := by
    apply ult_zero
    rw [ulit_toNat' _ hsize, ulit_toNat' _ (lt_size_of_lt256 (by decide))]
    omega
  have h161 := safeRuntime_block_0_taken (fork := fork) (by decide) (by rw [hlt]; decide) (by jump_dest)
    (RD.initState (fork := fork) (σ := σ) (σ₀ := σ₀) (g := g) (A := A) hcode)
  have h168 := evm_run h161 with [jumpdest, push0, push0, calldataload, push1 ⟨224⟩, shr]
  exact ⟨_, _, h168⟩

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
    ∃ k C, RD fork safeBytecode I g (initState σ σ₀ g A I) bodyPc
      [selWord I, ⟨0⟩] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, hgroup⟩ := safeReachSelectorGroup (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsize hlong
  rw [hword] at hgroup ⊢
  rcases hcert with ⟨hwf, hskip, htake, hjd, hbody⟩
  exact RD.dispatchTo bodyPc i hgroup
    (fun j hj ↦ hwf ⟨j, by omega⟩) (fun j hj ↦ hskip ⟨j, hj⟩)
    htake (by rw [hbody]; exact hjd) hbody (by decide)

set_option synthInstance.maxSize 10000 in
set_option maxRecDepth 100000 in
theorem safeReachSelectorEnd {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = safeBytecode) (hsize : I.calldata.size < UInt256.size)
    (hlong : 4 ≤ I.calldata.size)
    (hskip : ∀ j : Fin 30, UInt256.eq
      (armSelNat safeBytecode (nthArmPc safeBytecode ⟨168⟩ j)) (selWord I) = ⟨0⟩) :
    ∃ k C, RD fork safeBytecode I g (initState σ σ₀ g A I) ⟨498⟩
      [selWord I, ⟨0⟩] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hwf : ∀ j : Fin 30, armWellFormed safeBytecode
      (nthArmPc safeBytecode ⟨168⟩ j) := by native_decide
  obtain ⟨k, C, hgroup⟩ := safeReachSelectorGroup (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) hcode hsize hlong
  obtain ⟨k', C', hend⟩ := skipSelectorArms 30 hgroup
    (fun j hj ↦ hwf ⟨j, hj⟩) (fun j hj ↦ hskip ⟨j, hj⟩) (by decide)
  change RD fork safeBytecode I g (initState σ σ₀ g A I)
    (nthArmPc safeBytecode ⟨168⟩ 30) _ _ _ _ _ _ _ at hend
  rw [show nthArmPc safeBytecode ⟨168⟩ 30 = ⟨498⟩ from by native_decide] at hend
  exact ⟨k', C', hend⟩

end Benchmarks.Safe.ViaIR
