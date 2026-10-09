import Benchmarks.Morpho.MorphoBlue.ConstructorReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

/-- Creation code refines the source constructor and returns the runtime with its computed domain separator. -/
theorem morphoConstructorCorrect :
    typedConstructorRefinement config morphoCreationBytecode contract (immutableLayout.deployed morphoBytecode) := by
  intro σ σ₀ g A I args deployedCode hdeploy hcode _hcalldata hperm
  obtain ⟨a, rfl, rfl⟩ := morphoConstructorDeployment hdeploy
  let w := UInt256.ofNat a.val
  have hc : w.toNat < EVM.addressModulus := addressWord_val_canonical a
  have rejects (hbad : I.weiValue ≠ ⟨0⟩ ∨ a = AccountAddress.ofNat 0)
      (hr : RDrev (morphoCreationBytecode ++ w.toByteArray) (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I)) :
      typedConstructorRefinementFor config contract [.address a] σ σ₀ g A I
        (immutableLayout.deployed morphoBytecode) := by
    rcases hr.xiResult hcode with hoog | ⟨g', o, hxi⟩
    · exact .outOfGas (by simpa using hoog)
    · exact .execution (by simpa using hxi)
        (morphoConstructorExec a (morphoConstructorSourceRejects a _ hbad))
        (.revert rfl rfl) True.intro
  by_cases hcv : I.weiValue = ⟨0⟩
  · obtain ⟨aw, k, C, rd⟩ := morphoConstructorReachOwner (σ := σ) (σ₀ := σ₀) (A := A)
      (g := .ofUInt256 g) w hcode hc hcv
    by_cases hzero : a = AccountAddress.ofNat 0
    · have hw : w = ⟨0⟩ := by simp only [w, hzero]; rfl
      rw [hw] at rd
      apply rejects (.inr hzero)
      rw [hw]
      exact morphoConstructorZeroOwnerReverts rd
    · have hw : w ≠ ⟨0⟩ := by
        intro heq
        apply hzero
        rw [← address_word_roundtrip a]
        change AccountAddress.ofNat w.toNat = _
        rw [heq]; rfl
      obtain ⟨aw1, k1, C1, rd1⟩ := morphoConstructorReachHash w hw rd
      have hr := morphoConstructorFinish w hc hperm rd1
      rw [constructorRuntimeFinal a I] at hr
      have ha : sstoreAccountMap I.codeOwner σ ⟨0⟩ (setAddressOffset0Word (solcSlotWordAt ⟨0⟩ σ I) w) =
          (morphoConstructorState (initState σ σ₀ (.ofUInt256 g) A I) a).accountMap := by
        rw [morphoConstructorState, storageStore_accountMap]
        rfl
      rcases hr with hoog | ⟨s, hX, hacc⟩
      · exact .outOfGas (Xi_error_of_X (g := g) (by rw [← hcode] at hoog; exact hoog))
      · have hxi := Xi_success_of_X (g := g) (by rw [← hcode] at hX; exact hX)
        rw [hacc] at hxi
        exact .execution hxi (morphoConstructorExec a (morphoConstructorSource a _ hcv hzero))
          (.success rfl rfl ha rfl) (morphoConstructorFinal_fit a I)
  · exact rejects (.inl hcv) (morphoConstructorValueReverts hcode hcv)

end Benchmarks.Morpho.MorphoBlue
