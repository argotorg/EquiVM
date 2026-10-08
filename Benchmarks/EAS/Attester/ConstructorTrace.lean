import Benchmarks.EAS.Attester.ConstructorMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.EAS.Attester.Immutables attesterCreationBlocks

namespace Benchmarks.EAS.Attester

theorem constructorNonpayableTrace {σ σ₀ A I} {g : Sat256} {tail : ByteArray}
    (hcode : I.code = attesterCreationBytecode ++ tail) (hv : I.weiValue ≠ ⟨0⟩) :
    RDrev (attesterCreationBytecode ++ tail) g (initState σ σ₀ g A I) := by
  have h0 := RD.initState (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  have h1 := attesterCreation_block_0_fallthrough (by simp) (isZero_eq_zero_of_ne hv) h0
  exact attesterCreation_block_11 (by simp [attesterCreation_block_0_fallthrough_stack]) h1

theorem constructorABI_summary (eas : AccountAddress) :
    attesterCreation_block_15_memory (tail := (UInt256.ofNat eas.val).toByteArray)
      (mem := constructorFreeMemory) = constructorABIMemory eas := by
  have hs : (attesterCreationBytecode ++ (UInt256.ofNat eas.val).toByteArray).size = 4089 :=
    constructorCode_size eas
  simp only [attesterCreation_block_15_memory, constructorFreeMemory_load, hs,
    show UInt256.sub (UInt256.ofNat 4089) (UInt256.ofNat 4057) = (⟨32⟩ : UInt256) from by decide,
    show (⟨160⟩ : UInt256) + ⟨32⟩ = ⟨192⟩ from by decide]
  change writeWord ((constructorCode eas).write 4057 constructorFreeMemory 160 32) 64 ⟨192⟩ = _
  rw [constructorCode_copyArg]
  rfl

theorem constructorReachBody {σ σ₀ A I} {g : Sat256} (eas : AccountAddress)
    (hcode : I.code = constructorCode eas) (hv : I.weiValue = ⟨0⟩) :
    ∃ aw k C, RD (constructorCode eas) I g (initState σ σ₀ g A I) ⟨44⟩
      [UInt256.ofNat eas.val] (constructorABIMemory eas) aw ByteArray.empty σ k C := by
  have h0 := RD.initState (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  obtain ⟨aw1, k1, C1, h1⟩ := attesterCreation_block_0_taken_packed
    (by simp) (by rw [hv]; decide) (by native_decide) h0
  change RD _ _ _ _ _ [I.weiValue] constructorFreeMemory _ _ _ _ _ at h1
  obtain ⟨aw2, k2, C2, h2⟩ := attesterCreation_block_15_packed
    (by simp) (by native_decide) h1
  have hs : (attesterCreationBytecode ++ (UInt256.ofNat eas.val).toByteArray).size = 4089 :=
    constructorCode_size eas
  simp only [attesterCreation_block_15_stack, constructorFreeMemory_load, hs,
    show UInt256.sub (UInt256.ofNat 4089) (UInt256.ofNat 4057) = (⟨32⟩ : UInt256) from by decide,
    show (⟨160⟩ : UInt256) + ⟨32⟩ = ⟨192⟩ from by decide, constructorABI_summary] at h2
  have h3 := attesterCreation_block_98_taken (by simp) (by decide) (by native_decide) h2
  simp only [attesterCreation_block_98_taken_stack] at h3
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by decide
  have hclean : UInt256.land (UInt256.ofNat eas.val) solcAddrMask = UInt256.ofNat eas.val := by
    rw [u256_land_comm, easWord_mask]
  have hload : memLoad (⟨160⟩ : UInt256) (constructorABIMemory eas) = UInt256.ofNat eas.val :=
    constructorABIMemory_load eas
  obtain ⟨aw4, k4, C4, h4⟩ := attesterCreation_block_115_taken_packed
    (by simp) (by rw [hload, hmask, hclean, uInt256_eq_self]; decide)
    (by native_decide) h3
  simp only [attesterCreation_block_115_taken_stack, hload] at h4
  obtain ⟨aw5, k5, C5, h5⟩ := attesterCreation_block_137_packed
    (by simp) (by native_decide) h4
  exact ⟨aw5, k5, C5, h5⟩

theorem constructorZeroTrace {σ σ₀ A I} {g : Sat256} (eas : AccountAddress)
    (hcode : I.code = constructorCode eas) (hv : I.weiValue = ⟨0⟩)
    (hz : eas = ⟨0, by decide⟩) :
    RDrev (constructorCode eas) g (initState σ σ₀ g A I) := by
  obtain ⟨aw, k, C, h⟩ := constructorReachBody (σ := σ) (σ₀ := σ₀) (A := A) (g := g) eas hcode hv
  have h1 := attesterCreation_block_44_fallthrough (by simp) (by rw [hz]; decide) h
  exact attesterCreation_block_58 (by simp) h1

theorem constructorSuccessTrace {σ σ₀ A I} {g : Sat256} (eas : AccountAddress)
    (hcode : I.code = constructorCode eas) (hv : I.weiValue = ⟨0⟩)
    (hz : eas ≠ ⟨0, by decide⟩) :
    RDret (constructorCode eas) g (initState σ σ₀ g A I) σ
      (deployedRuntime attesterBytecode (constructorFinalImms eas)) := by
  obtain ⟨aw, k, C, h⟩ := constructorReachBody (σ := σ) (σ₀ := σ₀) (A := A) (g := g) eas hcode hv
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = solcAddrMask := by decide
  have hne : UInt256.ofNat eas.val ≠ UInt256.ofNat 0 := by
    intro heq
    have hfit : eas.val < UInt256.size := by
      have hb := eas.isLt
      change eas.val < 2 ^ 160 at hb
      change _ < 2 ^ 256; omega
    have hnat := congrArg UInt256.toNat heq
    rw [ulit_toNat' _ hfit] at hnat
    exact hz (Fin.ext hnat)
  have h1 := attesterCreation_block_44_taken (by simp)
    (by rw [hmask, u256_land_comm, easWord_mask]; exact hne) (by native_decide) h
  obtain ⟨aw2, k2, C2, h2⟩ := attesterCreation_block_82_packed
    (by simp) (by native_decide) h1
  simp only [attesterCreation_block_82_stack, attesterCreation_block_82_memory, hmask,
    easWord_mask] at h2
  change RD _ _ _ _ _ [] (constructorMemory eas) _ _ _ _ _ at h2
  have hr := attesterCreation_block_144 (by simp) h2
  rw [constructorMemory_load] at hr
  simp only [ofNat_add_words, ulit_toNat' 192 (by decide), ulit_toNat' 0 (by decide),
    ulit_toNat' 3865 (by decide), ulit_toNat' 824 (by decide), ulit_toNat' 1719 (by decide),
    ulit_toNat' 1888 (by decide), ulit_toNat' 2289 (by decide), Nat.add_zero] at hr
  have hcopy : (attesterCreationBytecode ++ (UInt256.ofNat eas.val).toByteArray).write 192
      (constructorMemory eas) 0 3865 = attesterBytecode := constructorCode_copyRuntime eas
  rw [hcopy] at hr
  change RDret _ _ _ _ ((constructorPatchedMemory eas).readWithPadding 0 3865) at hr
  simpa only [constructorPatchedMemory_read] using hr

end Benchmarks.EAS.Attester
