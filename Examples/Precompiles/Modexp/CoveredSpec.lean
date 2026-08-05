import Examples.Precompiles.Modexp.FastSpec
import Examples.Precompiles.Modexp.MontgomerySpec
import Examples.Precompiles.Modexp.BarrettSpec

/-!
# Combined direct bytecode spec for the ModExp cases proved so far

This file deliberately states only the covered region: the single-word path, the arbitrary-width
fast paths, the zero declared modulus-length exit, the positive one-word small-modulus-value exits,
the arbitrary-width one-limb odd-modulus Montgomery path, and the direct/normalized one-limb
even-modulus Barrett paths.  It is a consumer-facing wrapper over the branch-local `BytecodeSpec`
theorems; it does not assert full ModExp coverage.
-/

open Ethereum Ethereum.EVM Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def coveredAccepts (ctx : BytecodeContext) : Prop :=
  wordAccepts ctx ∨ wideFastAccepts ctx ∨
    wideZeroModulusLengthAccepts ctx ∨ wideSmallModulusValueAccepts ctx ∨
      wideMontgomeryWordAccepts ctx ∨ wideBarrettDirectWordAccepts ctx ∨
        wideBarrettNormalizedWordAccepts ctx

def coveredEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  (wordAccepts ctx ∧
      ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
        (wordGasCost ctx.executionEnv) result) ∨
  (wideFastAccepts ctx ∧
      ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
        (wideFastGas ctx.executionEnv) result) ∨
  (wideZeroModulusLengthAccepts ctx ∧
      ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
        (wideZeroModulusLengthTotalGas ctx.executionEnv) result) ∨
  (wideSmallModulusValueAccepts ctx ∧
      ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
        (wideSmallModulusValueTotalGas ctx.executionEnv) result) ∨
  (wideMontgomeryWordAccepts ctx ∧
      ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
        (wideMontgomeryWordTotalGas ctx.executionEnv) result) ∨
  (wideBarrettDirectWordAccepts ctx ∧
      ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
        (wideBarrettDirectWordTotalGas ctx.executionEnv) result) ∨
  (wideBarrettNormalizedWordAccepts ctx ∧
      ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
        (wideBarrettNormalizedWordTotalGas ctx.executionEnv) result)

theorem coveredBytecodeSpec :
    BytecodeSpec runtimeBytecode coveredAccepts coveredEnsures := by
  constructor
  intro ctx hcode haccepts
  rcases haccepts with hword | hrest
  · have hspec := wordBytecodeSpec.run ctx hcode hword
    exact Or.inl ⟨hword, hspec⟩
  · rcases hrest with hfast | hmont
    · have hspec := wideFastBytecodeSpec.run ctx hcode hfast
      exact Or.inr (Or.inl ⟨hfast, hspec⟩)
    · rcases hmont with hzero | hrest
      · have hspec := wideZeroModulusLengthBytecodeSpec.run ctx hcode hzero
        exact Or.inr (Or.inr (Or.inl ⟨hzero, hspec⟩))
      · rcases hrest with hsmall | hrest
        · have hspec := wideSmallModulusValueBytecodeSpec.run ctx hcode hsmall
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hsmall, hspec⟩)))
        · rcases hrest with hmont | hrest
          · have hspec := wideMontgomeryWordBytecodeSpec.run ctx hcode hmont
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hmont, hspec⟩))))
          · rcases hrest with hbarrett | hbarrettNorm
            · have hspec := wideBarrettDirectWordBytecodeSpec.run ctx hcode hbarrett
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hbarrett, hspec⟩)))))
            · have hspec := wideBarrettNormalizedWordBytecodeSpec.run ctx hcode hbarrettNorm
              exact Or.inr
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hbarrettNorm, hspec⟩)))))

end Modexp
