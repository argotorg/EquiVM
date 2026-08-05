import Examples.Precompiles.Modexp.CoveredSpec

/-!
# General ModExp bytecode-spec scaffold

This file separates the intended full ModExp bytecode contract from the region currently proved in
`CoveredSpec`.

`coveredBytecodeSpec` proves exact-gas functional correctness for the union of completed branches.
The theorem `modexpSomeExactGasSpec_of_coverage` records the remaining shape of the full proof:
if the completed branch predicates cover every accepted ModExp input, then the bytecode satisfies
the general functional spec with an exact gas threshold for the selected branch.

The theorem is intentionally conditional.  At the moment, `coveredAccepts` is not known to cover
all Osaka-valid inputs; multi-limb nontrivial backends remain to be proved.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The intended ModExp-level input side, independent of the current branch proof coverage. -/
def modexpAccepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧
  validOsaka ctx.executionEnv.calldata

/-- Functional correctness against the trusted model, retaining that the successful branch has
some exact bytecode gas threshold.  A later total proof should replace the existential with a
single executable gas selector covering every backend branch. -/
def modexpSomeExactGasEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ∃ gasCost : Nat,
    ExactGasPost ctx (Model.output ctx.executionEnv.calldata) gasCost result

/-- Inputs accepted by the covered branch-local specs are accepted by the intended ModExp input
predicate. -/
theorem coveredAccepts_modexpAccepts {ctx : BytecodeContext}
    (h : coveredAccepts ctx) : modexpAccepts ctx := by
  unfold coveredAccepts at h
  rcases h with hword | hrest
  · rcases hword with ⟨hvalue, hsized⟩
    rcases hsized with ⟨hb, he, hm⟩
    refine ⟨hvalue, ?_⟩
    unfold validOsaka
    exact ⟨by omega, by omega, by omega⟩
  · rcases hrest with hfast | hrest
    · rcases hfast with ⟨hvalue, _hcalldata, hvalid, _hwide, _hcond⟩
      exact ⟨hvalue, hvalid⟩
    · rcases hrest with hzero | hrest
      · rcases hzero with ⟨hvalue, _hcalldata, hvalid, _hwide, _hcond⟩
        exact ⟨hvalue, hvalid⟩
      · rcases hrest with hsmall | hrest
        · rcases hsmall with ⟨hvalue, _hcalldata, hvalid, _hwide, _hcond⟩
          exact ⟨hvalue, hvalid⟩
        · rcases hrest with hmont | hrest
          · rcases hmont with ⟨hvalue, _hcalldata, hvalid, _hwide, _hcond⟩
            exact ⟨hvalue, hvalid⟩
          · rcases hrest with hbarrett | hbarrettNorm
            · rcases hbarrett with ⟨hvalue, _hcalldata, hvalid, _hwide, _hcond⟩
              exact ⟨hvalue, hvalid⟩
            · rcases hbarrettNorm with ⟨hvalue, _hcalldata, hvalid, _hwide, _hcond⟩
              exact ⟨hvalue, hvalid⟩

/-- The current covered postcondition implies the general functional postcondition with an
existential exact gas threshold. -/
theorem coveredEnsures_modexpSomeExactGasEnsures {ctx : BytecodeContext}
    {result : BytecodeResult}
    (h : coveredEnsures ctx result) :
    modexpSomeExactGasEnsures ctx result := by
  unfold coveredEnsures at h
  unfold modexpSomeExactGasEnsures
  rcases h with hword | hrest
  · exact ⟨wordGasCost ctx.executionEnv, hword.2⟩
  · rcases hrest with hfast | hrest
    · exact ⟨wideFastGas ctx.executionEnv, hfast.2⟩
    · rcases hrest with hzero | hrest
      · exact ⟨wideZeroModulusLengthTotalGas ctx.executionEnv, hzero.2⟩
      · rcases hrest with hsmall | hrest
        · exact ⟨wideSmallModulusValueTotalGas ctx.executionEnv, hsmall.2⟩
        · rcases hrest with hmont | hrest
          · exact ⟨wideMontgomeryWordTotalGas ctx.executionEnv, hmont.2⟩
          · rcases hrest with hbarrett | hbarrettNorm
            · exact ⟨wideBarrettDirectWordTotalGas ctx.executionEnv, hbarrett.2⟩
            · exact ⟨wideBarrettNormalizedWordTotalGas ctx.executionEnv, hbarrettNorm.2⟩

/-- Directly package the already proved region as a ModExp functional spec. -/
theorem coveredBytecodeSomeExactGasSpec :
    BytecodeSpec runtimeBytecode coveredAccepts modexpSomeExactGasEnsures :=
  BytecodeSpec.mono coveredBytecodeSpec
    (by
      intro ctx result _haccepts hpost
      exact coveredEnsures_modexpSomeExactGasEnsures hpost)

/-- The mechanically explicit remaining obligation for a full ModExp functional spec. -/
def missingModexpCases (ctx : BytecodeContext) : Prop :=
  modexpAccepts ctx ∧ ¬ coveredAccepts ctx

/-- Word-sized accepted inputs are already covered. -/
theorem wordSized_coveredAccepts {ctx : BytecodeContext}
    (haccepts : modexpAccepts ctx)
    (hword : wordSized ctx.executionEnv.calldata) :
    coveredAccepts ctx := by
  exact Or.inl ⟨haccepts.1, hword⟩

/-- Wide fast-exit accepted inputs are already covered, provided the calldata-size side condition
required by the current wide proof is available. -/
theorem wideFast_coveredAccepts {ctx : BytecodeContext}
    (haccepts : modexpAccepts ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hwide : ¬ wordSized ctx.executionEnv.calldata)
    (hfast : wideFastCondition ctx.executionEnv.calldata) :
    coveredAccepts ctx := by
  exact Or.inr (Or.inl ⟨haccepts.1, hcalldata, haccepts.2, hwide, hfast⟩)

/-- Wide zero declared modulus-length inputs are already covered. -/
theorem wideZeroModulusLength_coveredAccepts {ctx : BytecodeContext}
    (haccepts : modexpAccepts ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hwide : ¬ wordSized ctx.executionEnv.calldata)
    (hcond : wideZeroModulusLengthCondition ctx.executionEnv) :
    coveredAccepts ctx := by
  exact Or.inr (Or.inr (Or.inl ⟨haccepts.1, hcalldata, haccepts.2, hwide, hcond⟩))

/-- Wide one-word small-modulus-value inputs are already covered. -/
theorem wideSmallModulusValue_coveredAccepts {ctx : BytecodeContext}
    (haccepts : modexpAccepts ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hwide : ¬ wordSized ctx.executionEnv.calldata)
    (hcond : wideSmallModulusValueCondition ctx.executionEnv) :
    coveredAccepts ctx := by
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨haccepts.1, hcalldata, haccepts.2, hwide, hcond⟩)))

/-- Wide one-word odd-modulus Montgomery inputs are already covered. -/
theorem wideMontgomeryWord_coveredAccepts {ctx : BytecodeContext}
    (haccepts : modexpAccepts ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hwide : ¬ wordSized ctx.executionEnv.calldata)
    (hcond : wideMontgomeryWordCondition ctx.executionEnv) :
    coveredAccepts ctx := by
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨haccepts.1, hcalldata, haccepts.2, hwide, hcond⟩))))

/-- Wide one-word even-modulus Barrett direct inputs are already covered. -/
theorem wideBarrettDirectWord_coveredAccepts {ctx : BytecodeContext}
    (haccepts : modexpAccepts ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hwide : ¬ wordSized ctx.executionEnv.calldata)
    (hcond : wideBarrettDirectWordCondition ctx.executionEnv) :
    coveredAccepts ctx := by
  exact Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨haccepts.1, hcalldata, haccepts.2, hwide, hcond⟩)))))

/-- Wide one-word even-modulus Barrett normalized inputs are already covered. -/
theorem wideBarrettNormalizedWord_coveredAccepts {ctx : BytecodeContext}
    (haccepts : modexpAccepts ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hwide : ¬ wordSized ctx.executionEnv.calldata)
    (hcond : wideBarrettNormalizedWordCondition ctx.executionEnv) :
    coveredAccepts ctx := by
  exact Or.inr
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨haccepts.1, hcalldata, haccepts.2, hwide, hcond⟩)))))

/-- Any missing case must be outside the all-single-word path. -/
theorem missing_not_wordSized {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx) :
    ¬ wordSized ctx.executionEnv.calldata := by
  intro hword
  exact hmissing.2 (wordSized_coveredAccepts hmissing.1 hword)

/-- Any bounded-calldata missing case must be outside the wide fast-exit paths. -/
theorem missing_not_wideFast {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64) :
    ¬ wideFastCondition ctx.executionEnv.calldata := by
  intro hfast
  exact hmissing.2
    (wideFast_coveredAccepts hmissing.1 hcalldata
      (missing_not_wordSized hmissing) hfast)

/-- Bounded-calldata missing cases cannot satisfy the completed zero declared modulus-length
predicate. -/
theorem missing_not_wideZeroModulusLength {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64) :
    ¬ wideZeroModulusLengthCondition ctx.executionEnv := by
  intro hcond
  exact hmissing.2
    (wideZeroModulusLength_coveredAccepts hmissing.1 hcalldata
      (missing_not_wordSized hmissing) hcond)

/-- Bounded-calldata missing cases cannot satisfy the completed small-modulus-value predicate. -/
theorem missing_not_wideSmallModulusValue {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64) :
    ¬ wideSmallModulusValueCondition ctx.executionEnv := by
  intro hcond
  exact hmissing.2
    (wideSmallModulusValue_coveredAccepts hmissing.1 hcalldata
      (missing_not_wordSized hmissing) hcond)

/-- Bounded-calldata missing cases cannot satisfy the completed Montgomery backend predicate. -/
theorem missing_not_wideMontgomeryWord {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64) :
    ¬ wideMontgomeryWordCondition ctx.executionEnv := by
  intro hcond
  exact hmissing.2
    (wideMontgomeryWord_coveredAccepts hmissing.1 hcalldata
      (missing_not_wordSized hmissing) hcond)

/-- Bounded-calldata missing cases cannot satisfy the completed Barrett-direct backend predicate. -/
theorem missing_not_wideBarrettDirectWord {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64) :
    ¬ wideBarrettDirectWordCondition ctx.executionEnv := by
  intro hcond
  exact hmissing.2
    (wideBarrettDirectWord_coveredAccepts hmissing.1 hcalldata
      (missing_not_wordSized hmissing) hcond)

/-- Bounded-calldata missing cases cannot satisfy the completed Barrett-normalized backend
predicate. -/
theorem missing_not_wideBarrettNormalizedWord {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64) :
    ¬ wideBarrettNormalizedWordCondition ctx.executionEnv := by
  intro hcond
  exact hmissing.2
    (wideBarrettNormalizedWord_coveredAccepts hmissing.1 hcalldata
      (missing_not_wordSized hmissing) hcond)

/-- The nontrivial wide backend region left after the proved word-sized and fast-exit paths. -/
def wideNontrivialInputs (ctx : BytecodeContext) : Prop :=
  modexpAccepts ctx ∧
  ctx.executionEnv.calldata.size < 2 ^ 64 ∧
  ¬ wordSized ctx.executionEnv.calldata ∧
  Model.bytesToNatPadded ctx.executionEnv.calldata
    (wideExponentOffset (lengths ctx.executionEnv.calldata).base)
    (lengths ctx.executionEnv.calldata).exponent ≠ 0 ∧
  1 < Model.bytesToNatPadded ctx.executionEnv.calldata 96
    (lengths ctx.executionEnv.calldata).base

def wideModulusNat (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  Model.bytesToNatPadded I.calldata (wideModulusOffset l.base l.exponent) l.modulus

def wideModulusParity (I : ExecutionEnv) : UInt256 :=
  let l := lengths I.calldata
  modulusLastByteParity
    (operandCopiedMemory I l.base l.exponent l.modulus)
    (operandModulusActiveWords l.base l.exponent l.modulus)
    l.base l.exponent l.modulus

def wideBarrettDirectSelector (I : ExecutionEnv) : Prop :=
  let l := lengths I.calldata
  l.modulus = 1 ∨
    UInt256.byteAt ⟨0⟩
      (wideLoadWord
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (UInt256.ofNat (operandModulusPtr l.base l.exponent + 32))) ≠ ⟨0⟩

def wideBarrettNormalizedFpFor (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  wideBarrettNormalizedFp l.base l.exponent l.modulus

def wideBarrettNormalizedLenForEnv (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  wideBarrettNormalizedLenFor I l.base l.exponent l.modulus

def wideBarrettNormalizedResultMemFor (I : ExecutionEnv) : ByteArray :=
  let l := lengths I.calldata
  barrettNormalizedResultMem
    (wideWordResultMemory I l.base l.exponent l.modulus)
    (wideWordResultWords l.base l.exponent l.modulus)
    (wideBarrettNormalizedFp l.base l.exponent l.modulus)
    (operandModulusPtr l.base l.exponent) l.modulus
    (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus)

def wideBarrettNormalizedResultAwFor (I : ExecutionEnv) : UInt256 :=
  let l := lengths I.calldata
  barrettNormalizedResultAw
    (wideWordResultMemory I l.base l.exponent l.modulus)
    (wideWordResultWords l.base l.exponent l.modulus)
    (wideBarrettNormalizedFp l.base l.exponent l.modulus)
    (operandModulusPtr l.base l.exponent) l.modulus
    (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus)

def wideBarrettNormalizedPayloadNat (I : ExecutionEnv) : Nat :=
  Model.bytesToNatPadded
    (wideBarrettNormalizedResultMemFor I)
    (wideBarrettNormalizedFpFor I + 32)
    (wideBarrettNormalizedLenForEnv I)

def wideBarrettNormalizedSkippedPrefixFor (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  barrettNormalizedOffset
    (wideWordResultMemory I l.base l.exponent l.modulus)
    (wideWordResultWords l.base l.exponent l.modulus)
    (operandModulusPtr l.base l.exponent) l.modulus - 32

def wideBarrettNormalizedWordFirstByteShape (I : ExecutionEnv) : Prop :=
  let l := lengths I.calldata
  wideBarrettNormalizedLenFor I l.base l.exponent l.modulus = 1 ∨
    UInt256.byteAt ⟨0⟩
      (wideLoadWord
        (barrettNormalizedResultMem
          (wideWordResultMemory I l.base l.exponent l.modulus)
          (wideWordResultWords l.base l.exponent l.modulus)
          (wideBarrettNormalizedFp l.base l.exponent l.modulus)
          (operandModulusPtr l.base l.exponent) l.modulus
          (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
        (barrettNormalizedResultAw
          (wideWordResultMemory I l.base l.exponent l.modulus)
          (wideWordResultWords l.base l.exponent l.modulus)
          (wideBarrettNormalizedFp l.base l.exponent l.modulus)
          (operandModulusPtr l.base l.exponent) l.modulus
          (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
        (UInt256.ofNat (wideBarrettNormalizedFp l.base l.exponent l.modulus + 32))) ≠ ⟨0⟩

def wideBarrettNormalizedMemoryBounds (I : ExecutionEnv) : Prop :=
  let fp := wideBarrettNormalizedFpFor I
  let n := wideBarrettNormalizedLenForEnv I
  let aw := wideBarrettNormalizedResultAwFor I
  fp + 32 + n + 32 < 2 ^ 64 ∧
  fp + 32 + n + 32 ≤ 32 * aw.toNat ∧
  32 * aw.toNat < UInt256.size

structure WideBarrettNormalizedWordModelFacts (I : ExecutionEnv) : Prop where
  hnonzero : wideBarrettNormalizedPayloadNat I ≠ 0
  hnotOne : wideBarrettNormalizedPayloadNat I ≠ 1
  hfirst :
    let l := lengths I.calldata
    wideBarrettNormalizedLenFor I l.base l.exponent l.modulus = 1 ∨
      UInt256.byteAt ⟨0⟩
        (wideLoadWord
          (barrettNormalizedResultMem
            (wideWordResultMemory I l.base l.exponent l.modulus)
            (wideWordResultWords l.base l.exponent l.modulus)
            (wideBarrettNormalizedFp l.base l.exponent l.modulus)
            (operandModulusPtr l.base l.exponent) l.modulus
            (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
          (barrettNormalizedResultAw
            (wideWordResultMemory I l.base l.exponent l.modulus)
            (wideWordResultWords l.base l.exponent l.modulus)
            (wideBarrettNormalizedFp l.base l.exponent l.modulus)
            (operandModulusPtr l.base l.exponent) l.modulus
            (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
          (UInt256.ofNat (wideBarrettNormalizedFp l.base l.exponent l.modulus + 32))) ≠ ⟨0⟩

structure WideBarrettNormalizedWordPayloadFacts (I : ExecutionEnv) : Prop where
  hpayload : wideBarrettNormalizedPayloadNat I = wideModulusNat I
  hfirst :
    let l := lengths I.calldata
    wideBarrettNormalizedLenFor I l.base l.exponent l.modulus = 1 ∨
      UInt256.byteAt ⟨0⟩
        (wideLoadWord
          (barrettNormalizedResultMem
            (wideWordResultMemory I l.base l.exponent l.modulus)
            (wideWordResultWords l.base l.exponent l.modulus)
            (wideBarrettNormalizedFp l.base l.exponent l.modulus)
            (operandModulusPtr l.base l.exponent) l.modulus
            (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
          (barrettNormalizedResultAw
            (wideWordResultMemory I l.base l.exponent l.modulus)
            (wideWordResultWords l.base l.exponent l.modulus)
            (wideBarrettNormalizedFp l.base l.exponent l.modulus)
            (operandModulusPtr l.base l.exponent) l.modulus
            (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
          (UInt256.ofNat (wideBarrettNormalizedFp l.base l.exponent l.modulus + 32))) ≠ ⟨0⟩

theorem wideBarrettNormalizedWordModelFacts_of_payload {ctx : BytecodeContext}
    (hmod : 1 < wideModulusNat ctx.executionEnv)
    (hpayload : WideBarrettNormalizedWordPayloadFacts ctx.executionEnv) :
    WideBarrettNormalizedWordModelFacts ctx.executionEnv := by
  refine ⟨?_, ?_, hpayload.hfirst⟩
  · intro hz
    rw [hpayload.hpayload] at hz
    omega
  · intro honePayload
    rw [hpayload.hpayload] at honePayload
    omega

structure WideBarrettNormalizedWordMemoryFacts (I : ExecutionEnv) : Prop where
  hzero :
    let l := lengths I.calldata
    memoryZeroResult
      (barrettNormalizedResultMem
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (wideBarrettNormalizedFp l.base l.exponent l.modulus)
        (operandModulusPtr l.base l.exponent) l.modulus
        (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
      (barrettNormalizedResultAw
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (wideBarrettNormalizedFp l.base l.exponent l.modulus)
        (operandModulusPtr l.base l.exponent) l.modulus
        (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
      (wideBarrettNormalizedFp l.base l.exponent l.modulus + 32)
      (wideBarrettNormalizedFp l.base l.exponent l.modulus + 32 +
        wideBarrettNormalizedLenFor I l.base l.exponent l.modulus) = 0
  hone :
    let l := lengths I.calldata
    memoryOneResult
      (barrettNormalizedResultMem
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (wideBarrettNormalizedFp l.base l.exponent l.modulus)
        (operandModulusPtr l.base l.exponent) l.modulus
        (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
      (barrettNormalizedResultAw
        (wideWordResultMemory I l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (wideBarrettNormalizedFp l.base l.exponent l.modulus)
        (operandModulusPtr l.base l.exponent) l.modulus
        (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
      (wideBarrettNormalizedFp l.base l.exponent l.modulus)
      (wideBarrettNormalizedLenFor I l.base l.exponent l.modulus) = 0
  hfirst :
    let l := lengths I.calldata
    wideBarrettNormalizedLenFor I l.base l.exponent l.modulus = 1 ∨
      UInt256.byteAt ⟨0⟩
        (wideLoadWord
          (barrettNormalizedResultMem
            (wideWordResultMemory I l.base l.exponent l.modulus)
            (wideWordResultWords l.base l.exponent l.modulus)
            (wideBarrettNormalizedFp l.base l.exponent l.modulus)
            (operandModulusPtr l.base l.exponent) l.modulus
            (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
          (barrettNormalizedResultAw
            (wideWordResultMemory I l.base l.exponent l.modulus)
            (wideWordResultWords l.base l.exponent l.modulus)
            (wideBarrettNormalizedFp l.base l.exponent l.modulus)
            (operandModulusPtr l.base l.exponent) l.modulus
            (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
          (UInt256.ofNat (wideBarrettNormalizedFp l.base l.exponent l.modulus + 32))) ≠ ⟨0⟩

theorem wideBarrettNormalizedWordMemoryFacts_of_model {I : ExecutionEnv}
    (hbounds : wideBarrettNormalizedMemoryBounds I)
    (hmodel : WideBarrettNormalizedWordModelFacts I) :
    WideBarrettNormalizedWordMemoryFacts I := by
  let fp := wideBarrettNormalizedFpFor I
  let n := wideBarrettNormalizedLenForEnv I
  let mem := wideBarrettNormalizedResultMemFor I
  let aw := wideBarrettNormalizedResultAwFor I
  rcases hbounds with ⟨hbound64, hactive, haw⟩
  refine ⟨?_, ?_, ?_⟩
  · have hzeroRef := memoryZeroResult_eq_reference
      (mem := mem) (aw := aw) (p := fp + 32) (end_ := fp + 32 + n)
      hbound64 hactive haw (by omega)
    have hwidth : fp + 32 + n - (fp + 32) = n := by omega
    have hne : Model.bytesToNatPadded mem (fp + 32) n ≠ 0 := by
      simpa [wideBarrettNormalizedPayloadNat, mem, fp, n] using hmodel.hnonzero
    change memoryZeroResult mem aw (fp + 32) (fp + 32 + n) = 0
    rw [hzeroRef]
    simp [memoryZeroReference, hwidth, hne]
  · have honeRef := memoryOneResult_eq_reference
      (mem := mem) (aw := aw) (ptr := fp) (len := n)
      hbound64 hactive haw
    have hne : Model.bytesToNatPadded mem (fp + 32) n ≠ 1 := by
      simpa [wideBarrettNormalizedPayloadNat, mem, fp, n] using hmodel.hnotOne
    change memoryOneResult mem aw fp n = 0
    rw [honeRef]
    simp [memoryOneReference, hne]
  · exact hmodel.hfirst

theorem wideBarrettNormalizedWordFacts_of_hnorm_memory {I : ExecutionEnv}
    (hnorm :
      let l := lengths I.calldata
      operandModulusPtr l.base l.exponent + 32 <
        barrettScanStop
          (wideWordResultMemory I l.base l.exponent l.modulus)
          (wideWordResultWords l.base l.exponent l.modulus)
          (operandModulusPtr l.base l.exponent) l.modulus)
    (hmem : WideBarrettNormalizedWordMemoryFacts I) :
    WideBarrettNormalizedWordFacts I where
  hnorm := hnorm
  hzero := hmem.hzero
  hone := hmem.hone
  hfirst := hmem.hfirst

/-- The one-word nontrivial backend shape, before splitting odd Montgomery from even Barrett. -/
def wideOneWordBackendInputs (ctx : BytecodeContext) : Prop :=
  wideNontrivialInputs ctx ∧
  0 < (lengths ctx.executionEnv.calldata).modulus ∧
  (lengths ctx.executionEnv.calldata).modulus ≤ 32 ∧
  1 < wideModulusNat ctx.executionEnv

/-- Remaining wide nontrivial region whose modulus byte length is larger than one EVM word. -/
def wideMultiLimbBackendInputs (ctx : BytecodeContext) : Prop :=
  wideNontrivialInputs ctx ∧
  32 < (lengths ctx.executionEnv.calldata).modulus

/-- The currently unproved wide nontrivial region after closing the one-word nontrivial backend,
the zero declared modulus-length exit, and the positive one-word small-modulus-value path. -/
def wideBackendResidualInputs (ctx : BytecodeContext) : Prop :=
  wideMultiLimbBackendInputs ctx

/-- Multi-limb residuals that dispatch to the odd-modulus Montgomery backend. -/
def wideMultiLimbOddMontgomeryInputs (ctx : BytecodeContext) : Prop :=
  wideMultiLimbBackendInputs ctx ∧
  wideModulusParity ctx.executionEnv = ⟨1⟩

/-- Multi-limb residuals that dispatch to the even-modulus Barrett backend. -/
def wideMultiLimbEvenBarrettInputs (ctx : BytecodeContext) : Prop :=
  wideMultiLimbBackendInputs ctx ∧
  wideModulusParity ctx.executionEnv = ⟨0⟩

theorem wideBarrettNormalizedWordModelFacts_of_oneWordPayload {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hpayload : WideBarrettNormalizedWordPayloadFacts ctx.executionEnv) :
    WideBarrettNormalizedWordModelFacts ctx.executionEnv := by
  exact wideBarrettNormalizedWordModelFacts_of_payload hone.2.2.2 hpayload

theorem wideBarrettNormalizedMemoryBounds_of_oneWordBackendInputs {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx) :
    wideBarrettNormalizedMemoryBounds ctx.executionEnv := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let baseSize := l.base
  let exponentSize := l.exponent
  let modulusSize := l.modulus
  rcases hone with ⟨hwideNontrivial, hmodPos, hmWord, _hmodNat⟩
  rcases hwideNontrivial with ⟨haccepts, _hcalldata, _hwide, _hexp, _hbase⟩
  have hvalid := haccepts.2
  unfold validOsaka at hvalid
  have hb : baseSize ≤ 1024 := by
    simpa [I, l, baseSize] using hvalid.1
  have he : exponentSize ≤ 1024 := by
    simpa [I, l, exponentSize] using hvalid.2.1
  have hm1024 : modulusSize ≤ 1024 := by
    have hm : (lengths I.calldata).modulus ≤ 1024 := hvalid.2.2
    simpa [I, l, modulusSize] using hm
  have hmodPosLocal : 0 < modulusSize := by
    simpa [I, l, modulusSize] using hmodPos
  have hmWordLocal : modulusSize ≤ 32 := by
    simpa [I, l, modulusSize] using hmWord
  let mem0 := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw0 := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let resultAw := barrettNormalizedResultAw mem0 aw0 fp p modulusSize resultFp
  have hstartLeEnd : barrettScanStart p ≤ barrettScanEnd p modulusSize := by
    unfold barrettScanStart barrettScanEnd
    omega
  have hstopBounds := barrettScanStopAt_bounds mem0 aw0
    (barrettScanEnd p modulusSize) (barrettScanStart p) hstartLeEnd
  have hstopLower : barrettScanStart p ≤ barrettScanStop mem0 aw0 p modulusSize := by
    simpa [barrettScanStop] using hstopBounds.1
  have hstopUpper : barrettScanStop mem0 aw0 p modulusSize ≤ barrettScanEnd p modulusSize := by
    simpa [barrettScanStop] using hstopBounds.2
  have hnEq : n = barrettNormalizedLen mem0 aw0 p modulusSize := by
    rfl
  have hnLeMod : n ≤ modulusSize := by
    dsimp [n]
    unfold wideBarrettNormalizedLenFor barrettNormalizedLen
    exact Nat.sub_le _ _
  have hnLe32 : n ≤ 32 := le_trans hnLeMod hmWordLocal
  have hfpCheckBound : fp + 32 + n + 32 < 2 ^ 64 := by
    dsimp [fp, n, wideBarrettNormalizedFp]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
      bytesAllocationSize
    omega
  let q := operandModulusWords baseSize exponentSize modulusSize +
    bytesAllocationWords modulusSize
  have haw0Eq : aw0 = UInt256.ofNat q := by
    dsimp [aw0, q]
    exact wideWordResultWords_eq hb he hm1024
  have hfpEq : fp = 32 * q := by
    dsimp [fp, wideBarrettNormalizedFp, q]
    rw [operandFreePtr_eq, bytesAllocationSize_eq_words]
    omega
  have hqBound : q + bytesAllocationWords n < UInt256.size := by
    apply lt_of_le_of_lt
      (show q + bytesAllocationWords n ≤ 76 by
        dsimp [q]
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hnewEq :
      newBytesWords aw0 fp n = UInt256.ofNat (q + bytesAllocationWords n) := by
    rw [haw0Eq, hfpEq]
    exact newBytesWords_aligned hqBound
  have hnewNat :
      (newBytesWords aw0 fp n).toNat = q + bytesAllocationWords n := by
    rw [hnewEq]
    exact UInt256.toNat_ofNat_of_lt hqBound
  have hnewActiveBytes :
      32 * (newBytesWords aw0 fp n).toNat = fp + bytesAllocationSize n := by
    rw [hnewNat, hfpEq, bytesAllocationSize_eq_words]
    omega
  have hoffsetLenEq :
      barrettNormalizedOffset mem0 aw0 p modulusSize + n = modulusSize + 32 := by
    let d := barrettScanStop mem0 aw0 p modulusSize - p
    have hoffsetEq : barrettNormalizedOffset mem0 aw0 p modulusSize = d := by
      rfl
    have hdGe : 32 ≤ d := by
      dsimp [d]
      unfold barrettScanStart at hstopLower
      omega
    have hdLe : d ≤ modulusSize + 31 := by
      dsimp [d]
      unfold barrettScanEnd at hstopUpper
      omega
    rw [hnEq]
    unfold barrettNormalizedLen
    rw [hoffsetEq]
    change d + (modulusSize - (d - 32)) = modulusSize + 32
    omega
  have hcopySourceActive :
      p + barrettNormalizedOffset mem0 aw0 p modulusSize + n ≤
        32 * (newBytesWords aw0 fp n).toNat := by
    rw [hnewActiveBytes]
    rw [show p + barrettNormalizedOffset mem0 aw0 p modulusSize + n =
        p + (modulusSize + 32) by omega]
    dsimp [fp, wideBarrettNormalizedFp, p]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hcopyDestActive :
      fp + 32 + n ≤ 32 * (newBytesWords aw0 fp n).toNat := by
    rw [hnewActiveBytes]
    unfold bytesAllocationSize
    omega
  have hcopyMaxActive :
      max (fp + 32) (p + barrettNormalizedOffset mem0 aw0 p modulusSize) + n ≤
        32 * (newBytesWords aw0 fp n).toNat := by
    rw [← Nat.add_max_add_right]
    exact max_le hcopyDestActive hcopySourceActive
  have hnormalizedAwEq :
      barrettNormalizedAw aw0 mem0 fp p modulusSize = newBytesWords aw0 fp n := by
    unfold barrettNormalizedAw barrettNormalizeCopyWords
    have hM :
        MachineState.M
            (newBytesWords aw0 fp (barrettNormalizedLen mem0 aw0 p modulusSize)).toNat
            (max (fp + 32) (p + barrettNormalizedOffset mem0 aw0 p modulusSize))
            (barrettNormalizedLen mem0 aw0 p modulusSize) =
          (newBytesWords aw0 fp (barrettNormalizedLen mem0 aw0 p modulusSize)).toNat := by
      simpa [← hnEq] using machineM_eq_of_access hcopyMaxActive
    rw [hM, u256_ofNat_toNat]
    rw [hnEq]
  have hnormalizedAwOfNat :
      barrettNormalizedAw aw0 mem0 fp p modulusSize =
        UInt256.ofNat (q + bytesAllocationWords n) := by
    rw [hnormalizedAwEq, hnewEq]
  let qn := q + bytesAllocationWords n
  have hresultFpEq : resultFp = fp + bytesAllocationSize n := by
    dsimp [resultFp, fp, n, wideBarrettNormalizedResultFp]
  have hresultFpWords : resultFp = 32 * qn := by
    dsimp [qn]
    rw [hresultFpEq, hfpEq, bytesAllocationSize_eq_words]
    omega
  have hqnBound : qn + bytesAllocationWords n < UInt256.size := by
    apply lt_of_le_of_lt
      (show qn + bytesAllocationWords n ≤ 78 by
        dsimp [qn, q]
        unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
        omega)
      (by decide)
  have hresultAwEq :
      resultAw = UInt256.ofNat (qn + bytesAllocationWords n) := by
    dsimp [resultAw]
    unfold barrettNormalizedResultAw
    rw [hnormalizedAwOfNat, hresultFpWords]
    exact newBytesWords_aligned hqnBound
  have hresultAwNat :
      resultAw.toNat = qn + bytesAllocationWords n := by
    rw [hresultAwEq]
    exact UInt256.toNat_ofNat_of_lt hqnBound
  have hresultActiveBytes :
      32 * resultAw.toNat = resultFp + bytesAllocationSize n := by
    rw [hresultAwNat, hresultFpWords, bytesAllocationSize_eq_words]
    omega
  have hchecksActive :
      fp + 32 + n + 32 ≤ 32 * resultAw.toNat := by
    rw [hresultActiveBytes, hresultFpEq]
    unfold bytesAllocationSize
    omega
  have hresultBound :
      resultFp + bytesAllocationSize n < 2 ^ 64 := by
    rw [hresultFpWords]
    dsimp [qn, q]
    unfold operandModulusWords operandExponentWords operandBaseWords bytesAllocationWords
      bytesAllocationSize
    omega
  have hchecksAw :
      32 * resultAw.toNat < UInt256.size := by
    rw [hresultActiveBytes]
    exact lt_trans hresultBound (by norm_num [UInt256.size])
  change fp + 32 + n + 32 < 2 ^ 64 ∧
    fp + 32 + n + 32 ≤ 32 * resultAw.toNat ∧
    32 * resultAw.toNat < UInt256.size
  exact ⟨hfpCheckBound, hchecksActive, hchecksAw⟩

/-- If the normalized result payload reads the significant suffix of the original one-word
modulus payload, and the skipped prefix decodes to zero, then the normalized payload Nat is exactly
the original trusted modulus Nat.  This factors the pure big-endian arithmetic out of the remaining
one-word Barrett-normalized payload proof. -/
theorem wideBarrettNormalizedPayloadNat_eq_wideModulusNat_of_read_prefix
    {ctx : BytecodeContext} (hone : wideOneWordBackendInputs ctx) {k : Nat}
    (hk :
      k + wideBarrettNormalizedLenForEnv ctx.executionEnv =
        (lengths ctx.executionEnv.calldata).modulus)
    (hread :
      (wideBarrettNormalizedResultMemFor ctx.executionEnv).readWithPadding
          (wideBarrettNormalizedFpFor ctx.executionEnv + 32)
          (wideBarrettNormalizedLenForEnv ctx.executionEnv) =
        (wideWordResultMemory ctx.executionEnv
          (lengths ctx.executionEnv.calldata).base
          (lengths ctx.executionEnv.calldata).exponent
          (lengths ctx.executionEnv.calldata).modulus).readWithPadding
            (operandModulusPtr
              (lengths ctx.executionEnv.calldata).base
              (lengths ctx.executionEnv.calldata).exponent + 32 + k)
            (wideBarrettNormalizedLenForEnv ctx.executionEnv))
    (hprefix :
      Model.bytesToNatPadded
        (wideWordResultMemory ctx.executionEnv
          (lengths ctx.executionEnv.calldata).base
          (lengths ctx.executionEnv.calldata).exponent
          (lengths ctx.executionEnv.calldata).modulus)
        (operandModulusPtr
          (lengths ctx.executionEnv.calldata).base
          (lengths ctx.executionEnv.calldata).exponent + 32) k = 0) :
    wideBarrettNormalizedPayloadNat ctx.executionEnv =
      wideModulusNat ctx.executionEnv := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let baseSize := l.base
  let exponentSize := l.exponent
  let modulusSize := l.modulus
  let mem0 := wideWordResultMemory I baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFpFor I
  let n := wideBarrettNormalizedLenForEnv I
  have hbounds := wideBarrettNormalizedMemoryBounds_of_oneWordBackendInputs hone
  rcases hone with ⟨hwideNontrivial, hmodPos, hmWord, _hmodNat⟩
  rcases hwideNontrivial with ⟨haccepts, _hcalldata, _hwide, _hexp, _hbase⟩
  have hvalid := haccepts.2
  unfold validOsaka at hvalid
  have hb : baseSize ≤ 1024 := by
    simpa [I, l, baseSize] using hvalid.1
  have he : exponentSize ≤ 1024 := by
    simpa [I, l, exponentSize] using hvalid.2.1
  have hmodPosLocal : 0 < modulusSize := by
    simpa [I, l, modulusSize] using hmodPos
  have hmWordLocal : modulusSize ≤ 32 := by
    simpa [I, l, modulusSize] using hmWord
  have hkLocal : k + n = modulusSize := by
    simpa [I, l, modulusSize, n] using hk
  have hnLe32 : n ≤ 32 := by omega
  have hn64 : n < 2 ^ 64 := by omega
  have hbounds64Local : fp + 32 + n + 32 < 2 ^ 64 := by
    simpa [I, fp, n] using hbounds.1
  have hfp64 : fp + 32 < 2 ^ 64 := by
    omega
  have hsource64 : p + 32 + k < 2 ^ 64 := by
    dsimp [p]
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hnormalizedBytes :
      Model.bytesToNatPadded
          (wideBarrettNormalizedResultMemFor I) (fp + 32) n =
        Model.bytesToNatPadded mem0 (p + 32 + k) n := by
    exact model_bytesToNatPadded_eq_of_readWithPadding
      hfp64 hsource64 hn64 (by simpa [I, l, baseSize, exponentSize, modulusSize,
        mem0, p, fp, n] using hread)
  have hsplit := model_bytesToNatPadded_split mem0 (p + 32) k n
  have hprefixLocal : Model.bytesToNatPadded mem0 (p + 32) k = 0 := by
    simpa [I, l, baseSize, exponentSize, modulusSize, mem0, p] using hprefix
  have horiginalMem :
      Model.bytesToNatPadded mem0 (p + 32) modulusSize =
        Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize := by
    simpa [I, l, baseSize, exponentSize, modulusSize, mem0, p] using
      wideWordResultModulus_toNat_eq_model I baseSize exponentSize modulusSize
        hb he hmodPosLocal (by omega)
  calc
    wideBarrettNormalizedPayloadNat I
        = Model.bytesToNatPadded (wideBarrettNormalizedResultMemFor I) (fp + 32) n := by
            rfl
    _ = Model.bytesToNatPadded mem0 (p + 32 + k) n := hnormalizedBytes
    _ = Model.bytesToNatPadded mem0 (p + 32) modulusSize := by
          rw [← hkLocal, hsplit]
          simp [hprefixLocal]
    _ = Model.bytesToNatPadded I.calldata (96 + baseSize + exponentSize) modulusSize :=
          horiginalMem
    _ = wideModulusNat I := by
          rfl

structure WideBarrettNormalizedWordReadFacts (I : ExecutionEnv) where
  k : Nat
  hk : k + wideBarrettNormalizedLenForEnv I = (lengths I.calldata).modulus
  hread :
    (wideBarrettNormalizedResultMemFor I).readWithPadding
        (wideBarrettNormalizedFpFor I + 32)
        (wideBarrettNormalizedLenForEnv I) =
      (wideWordResultMemory I
        (lengths I.calldata).base
        (lengths I.calldata).exponent
        (lengths I.calldata).modulus).readWithPadding
          (operandModulusPtr
            (lengths I.calldata).base
            (lengths I.calldata).exponent + 32 + k)
          (wideBarrettNormalizedLenForEnv I)
  hprefix :
    Model.bytesToNatPadded
      (wideWordResultMemory I
        (lengths I.calldata).base
        (lengths I.calldata).exponent
        (lengths I.calldata).modulus)
      (operandModulusPtr
        (lengths I.calldata).base
        (lengths I.calldata).exponent + 32) k = 0
  hfirst :
    let l := lengths I.calldata
    wideBarrettNormalizedLenFor I l.base l.exponent l.modulus = 1 ∨
      UInt256.byteAt ⟨0⟩
        (wideLoadWord
          (barrettNormalizedResultMem
            (wideWordResultMemory I l.base l.exponent l.modulus)
            (wideWordResultWords l.base l.exponent l.modulus)
            (wideBarrettNormalizedFp l.base l.exponent l.modulus)
            (operandModulusPtr l.base l.exponent) l.modulus
            (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
          (barrettNormalizedResultAw
            (wideWordResultMemory I l.base l.exponent l.modulus)
            (wideWordResultWords l.base l.exponent l.modulus)
            (wideBarrettNormalizedFp l.base l.exponent l.modulus)
            (operandModulusPtr l.base l.exponent) l.modulus
            (wideBarrettNormalizedResultFp I l.base l.exponent l.modulus))
          (UInt256.ofNat (wideBarrettNormalizedFp l.base l.exponent l.modulus + 32))) ≠ ⟨0⟩

theorem wideBarrettNormalizedWordPayloadFacts_of_readFacts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hfacts : WideBarrettNormalizedWordReadFacts ctx.executionEnv) :
    WideBarrettNormalizedWordPayloadFacts ctx.executionEnv := by
  refine ⟨?_, hfacts.hfirst⟩
  exact wideBarrettNormalizedPayloadNat_eq_wideModulusNat_of_read_prefix
    hone hfacts.hk hfacts.hread hfacts.hprefix

theorem wideBarrettNormalizedSkippedPrefix_add_len {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx) :
    wideBarrettNormalizedSkippedPrefixFor ctx.executionEnv +
      wideBarrettNormalizedLenForEnv ctx.executionEnv =
        (lengths ctx.executionEnv.calldata).modulus := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  rcases hone with ⟨_hwideNontrivial, hmodPos, _hmWord, _hmodNat⟩
  have hmodPosLocal : 0 < l.modulus := by
    simpa [I, l] using hmodPos
  simpa [wideBarrettNormalizedSkippedPrefixFor, wideBarrettNormalizedLenForEnv,
    wideBarrettNormalizedLenFor, I, l] using
    barrettNormalizedSkippedPrefix_add_len
      (wideWordResultMemory I l.base l.exponent l.modulus)
      (wideWordResultWords l.base l.exponent l.modulus)
      (operandModulusPtr l.base l.exponent) l.modulus hmodPosLocal

theorem wideBarrettNormalizedSkippedPrefix_zero {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx) :
    Model.bytesToNatPadded
      (wideWordResultMemory ctx.executionEnv
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent
        (lengths ctx.executionEnv.calldata).modulus)
      (operandModulusPtr
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent + 32)
      (wideBarrettNormalizedSkippedPrefixFor ctx.executionEnv) = 0 := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let baseSize := l.base
  let exponentSize := l.exponent
  let modulusSize := l.modulus
  let mem0 := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw0 := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let kprefix := wideBarrettNormalizedSkippedPrefixFor I
  rcases hone with ⟨hwideNontrivial, hmodPos, hmWord, _hmodNat⟩
  rcases hwideNontrivial with ⟨haccepts, _hcalldata, _hwide, _hexp, _hbase⟩
  have hvalid := haccepts.2
  unfold validOsaka at hvalid
  have hb : baseSize ≤ 1024 := by
    simpa [I, l, baseSize] using hvalid.1
  have he : exponentSize ≤ 1024 := by
    simpa [I, l, exponentSize] using hvalid.2.1
  have hm1024 : modulusSize ≤ 1024 := by
    have hm : (lengths I.calldata).modulus ≤ 1024 := hvalid.2.2
    simpa [I, l, modulusSize] using hm
  have hmodPosLocal : 0 < modulusSize := by
    simpa [I, l, modulusSize] using hmodPos
  have hmWordLocal : modulusSize ≤ 32 := by
    simpa [I, l, modulusSize] using hmWord
  have hstopBounds := barrettScanStopAt_bounds mem0 aw0
    (barrettScanEnd p modulusSize) (barrettScanStart p)
    (by
      unfold barrettScanStart barrettScanEnd
      omega)
  have hstopUpper :
      barrettScanStop mem0 aw0 p modulusSize ≤ barrettScanEnd p modulusSize := by
    simpa [barrettScanStop] using hstopBounds.2
  apply model_bytesToNatPadded_eq_zero_of_bytes
  intro i hi
  have hscanZero :
      barrettScanByteAt mem0 aw0 (p + 32 + i) = ⟨0⟩ := by
    have hbefore :
        p + 32 + i < barrettScanStop mem0 aw0 p modulusSize := by
      have hk :
          kprefix =
            barrettNormalizedOffset mem0 aw0 p modulusSize - 32 := by
        rfl
      have hiLocal : i < kprefix := by
        simpa [I, kprefix] using hi
      rw [hk] at hiLocal
      dsimp [barrettNormalizedOffset] at hiLocal
      omega
    simpa [barrettScanStop, barrettScanStart] using
      barrettScanStopAt_zero_before mem0 aw0
        (barrettScanEnd p modulusSize) (barrettScanStart p)
        (p + 32 + i)
        (by simp [barrettScanStart])
        (by simpa [barrettScanStop, barrettScanStart] using hbefore)
  have hbyteModel :
      (barrettScanByteAt mem0 aw0 (p + 32 + i)).toNat =
        Model.bytesToNatPadded mem0 (p + 32 + i) 1 := by
    have haddrLtEnd :
        p + 32 + i < p + modulusSize + 31 := by
      have hk :
          kprefix =
            barrettNormalizedOffset mem0 aw0 p modulusSize - 32 := by
        rfl
      have hiLocal : i < kprefix := by
        simpa [I, kprefix] using hi
      rw [hk] at hiLocal
      dsimp [barrettNormalizedOffset] at hiLocal
      have hltStop :
          p + 32 + i < barrettScanStop mem0 aw0 p modulusSize := by
        omega
      have hstopLeEnd :
          barrettScanStop mem0 aw0 p modulusSize ≤ p + modulusSize + 31 := by
        simpa [barrettScanEnd] using hstopUpper
      omega
    have haddrLtWord : p + 32 + i < UInt256.size := by
      have hsmall : p + 32 + i < 2368 := by
        dsimp [p] at haddrLtEnd ⊢
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at haddrLtEnd ⊢
        omega
      exact lt_of_lt_of_le hsmall (by decide)
    have haddrLt64 : p + 32 + i < 2 ^ 64 := by
      have hsmall : p + 32 + i < 2368 := by
        dsimp [p] at haddrLtEnd ⊢
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at haddrLtEnd ⊢
        omega
      exact lt_of_lt_of_le hsmall (by norm_num)
    apply barrettScanByteAt_toNat_eq_model
    · exact haddrLtWord
    · exact haddrLt64
    · intro hfrontier
      change (aw0 * ⟨32⟩).toNat ≤
          (UInt256.ofNat (p + 32 + i)).toNat at hfrontier
      rw [show (aw0 * ⟨32⟩).toNat =
          operandFreePtr baseSize exponentSize modulusSize +
            bytesAllocationSize modulusSize by
        dsimp [aw0]
        exact resultActiveBytes_toNat hb he hm1024] at hfrontier
      rw [UInt256.toNat_ofNat_of_lt haddrLtWord] at hfrontier
      have hword : 1 ≤ (modulusSize + 31) / 32 := by omega
      dsimp [p] at hfrontier
      unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
        bytesAllocationSize at hfrontier
      omega
  have hzNat : (barrettScanByteAt mem0 aw0 (p + 32 + i)).toNat = 0 := by
    rw [hscanZero]
    rfl
  simpa [I, l, baseSize, exponentSize, modulusSize, mem0, p, kprefix,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hbyteModel.symm.trans hzNat

theorem wideBarrettNormalizedResultMem_read_canonical_payload {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx) :
    (wideBarrettNormalizedResultMemFor ctx.executionEnv).readWithPadding
        (wideBarrettNormalizedFpFor ctx.executionEnv + 32)
        (wideBarrettNormalizedLenForEnv ctx.executionEnv) =
      (wideWordResultMemory ctx.executionEnv
        (lengths ctx.executionEnv.calldata).base
        (lengths ctx.executionEnv.calldata).exponent
        (lengths ctx.executionEnv.calldata).modulus).readWithPadding
          (operandModulusPtr
            (lengths ctx.executionEnv.calldata).base
            (lengths ctx.executionEnv.calldata).exponent + 32 +
              wideBarrettNormalizedSkippedPrefixFor ctx.executionEnv)
          (wideBarrettNormalizedLenForEnv ctx.executionEnv) := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let baseSize := l.base
  let exponentSize := l.exponent
  let modulusSize := l.modulus
  let mem0 := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw0 := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  rcases hone with ⟨hwideNontrivial, hmodPos, hmWord, _hmodNat⟩
  rcases hwideNontrivial with ⟨haccepts, _hcalldata, _hwide, _hexp, _hbase⟩
  have hvalid := haccepts.2
  unfold validOsaka at hvalid
  have hb : baseSize ≤ 1024 := by
    simpa [I, l, baseSize] using hvalid.1
  have he : exponentSize ≤ 1024 := by
    simpa [I, l, exponentSize] using hvalid.2.1
  have hm1024 : modulusSize ≤ 1024 := by
    have hm : (lengths I.calldata).modulus ≤ 1024 := hvalid.2.2
    simpa [I, l, modulusSize] using hm
  have hmodPosLocal : 0 < modulusSize := by
    simpa [I, l, modulusSize] using hmodPos
  have hmWordLocal : modulusSize ≤ 32 := by
    simpa [I, l, modulusSize] using hmWord
  have hstartLeEnd : barrettScanStart p ≤ barrettScanEnd p modulusSize := by
    unfold barrettScanStart barrettScanEnd
    omega
  have hstopBounds := barrettScanStopAt_bounds mem0 aw0
    (barrettScanEnd p modulusSize) (barrettScanStart p) hstartLeEnd
  have hstopLower : barrettScanStart p ≤ barrettScanStop mem0 aw0 p modulusSize := by
    simpa [barrettScanStop] using hstopBounds.1
  have hstopUpper : barrettScanStop mem0 aw0 p modulusSize ≤ barrettScanEnd p modulusSize := by
    simpa [barrettScanStop] using hstopBounds.2
  have hnEq : n = barrettNormalizedLen mem0 aw0 p modulusSize := by
    rfl
  have hoffsetGe : 32 ≤ barrettNormalizedOffset mem0 aw0 p modulusSize := by
    change 32 ≤ barrettScanStop mem0 aw0 p modulusSize - p
    unfold barrettScanStart at hstopLower
    omega
  have hdeltaLt :
      barrettScanStop mem0 aw0 p modulusSize - p - 32 < modulusSize := by
    unfold barrettScanEnd at hstopUpper
    omega
  have hlenPos : 0 < n := by
    simpa [n, wideBarrettNormalizedLenFor, barrettNormalizedLen,
      barrettNormalizedOffset, mem0, aw0, p] using Nat.sub_pos_of_lt hdeltaLt
  have hlen64 : n < 2 ^ 64 := by
    have hnLe : n ≤ modulusSize := by
      dsimp [n]
      unfold wideBarrettNormalizedLenFor barrettNormalizedLen
      exact Nat.sub_le _ _
    omega
  have hoffsetLenEq :
      barrettNormalizedOffset mem0 aw0 p modulusSize + n = modulusSize + 32 := by
    let d := barrettScanStop mem0 aw0 p modulusSize - p
    have hoffsetEq : barrettNormalizedOffset mem0 aw0 p modulusSize = d := by
      rfl
    have hdGe : 32 ≤ d := by
      dsimp [d]
      unfold barrettScanStart at hstopLower
      omega
    have hdLe : d ≤ modulusSize + 31 := by
      dsimp [d]
      unfold barrettScanEnd at hstopUpper
      omega
    rw [hnEq]
    unfold barrettNormalizedLen
    rw [hoffsetEq]
    change d + (modulusSize - (d - 32)) = modulusSize + 32
    omega
  have hmemSize : mem0.size = operandFreePtr baseSize exponentSize modulusSize + 32 := by
    simpa [mem0] using wideWordResultMemory_size I hb he hm1024
  have hmem96 : 96 ≤ mem0.size := by
    rw [hmemSize]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hmemLe : mem0.size ≤ fp := by
    rw [hmemSize]
    dsimp [fp]
    unfold wideBarrettNormalizedFp bytesAllocationSize
    omega
  have hgap : fp - mem0.size < USize.size := by
    rw [hmemSize]
    dsimp [fp]
    unfold wideBarrettNormalizedFp bytesAllocationSize
    exact lt_usize _ (by omega)
  have hsrc :
      p + barrettNormalizedOffset mem0 aw0 p modulusSize +
        barrettNormalizedLen mem0 aw0 p modulusSize ≤ fp + 32 := by
    rw [← hnEq]
    rw [show p + barrettNormalizedOffset mem0 aw0 p modulusSize + n =
        p + (modulusSize + 32) by omega]
    dsimp [fp, p]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hsourceInMem :
      p + barrettNormalizedOffset mem0 aw0 p modulusSize +
        barrettNormalizedLen mem0 aw0 p modulusSize ≤ mem0.size := by
    rw [← hnEq, hmemSize]
    rw [show p + barrettNormalizedOffset mem0 aw0 p modulusSize + n =
        p + (modulusSize + 32) by omega]
    dsimp [p]
    unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hsourceAbove :
      96 ≤ p + barrettNormalizedOffset mem0 aw0 p modulusSize := by
    dsimp [p]
    unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize
    omega
  have hsourceBelowFp :
      p + barrettNormalizedOffset mem0 aw0 p modulusSize +
        barrettNormalizedLen mem0 aw0 p modulusSize ≤ fp := by
    rw [← hnEq]
    rw [show p + barrettNormalizedOffset mem0 aw0 p modulusSize + n =
        p + (modulusSize + 32) by omega]
    dsimp [fp, p]
    unfold wideBarrettNormalizedFp operandFreePtr operandModulusPtr operandExponentPtr
      operandBasePtr bytesAllocationSize
    omega
  have hresultFpEq :
      resultFp = fp + bytesAllocationSize (barrettNormalizedLen mem0 aw0 p modulusSize) := by
    simp [resultFp, fp, wideBarrettNormalizedResultFp, wideBarrettNormalizedLenFor,
      mem0, aw0, p]
  have hraw :=
    barrettNormalizedResultMem_read_source_payload
      (mem := mem0) (aw := aw0) (fp := fp) (p := p) (m := modulusSize)
      (resultFp := resultFp)
      hmem96 hmemLe hgap (by simpa [← hnEq] using hlenPos)
      (by simpa [← hnEq] using hlen64)
      hsrc hsourceInMem hsourceAbove hsourceBelowFp hresultFpEq
  have haddr :
      p + barrettNormalizedOffset mem0 aw0 p modulusSize =
        p + 32 + wideBarrettNormalizedSkippedPrefixFor I := by
    have hskip :
        wideBarrettNormalizedSkippedPrefixFor I =
          barrettNormalizedOffset mem0 aw0 p modulusSize - 32 := by
      simp [wideBarrettNormalizedSkippedPrefixFor, I, l, baseSize, exponentSize,
        modulusSize, mem0, aw0, p]
    rw [hskip]
    omega
  simpa [wideBarrettNormalizedResultMemFor, wideBarrettNormalizedFpFor,
    wideBarrettNormalizedLenForEnv, wideBarrettNormalizedSkippedPrefixFor,
    wideBarrettNormalizedResultAwFor, I, l, baseSize, exponentSize, modulusSize,
    mem0, aw0, p, fp, n, resultFp, haddr] using hraw

def wideBarrettNormalizedWordReadFacts_of_canonical
    {ctx : BytecodeContext} (hone : wideOneWordBackendInputs ctx)
    (hfirst : wideBarrettNormalizedWordFirstByteShape ctx.executionEnv) :
    WideBarrettNormalizedWordReadFacts ctx.executionEnv where
  k := wideBarrettNormalizedSkippedPrefixFor ctx.executionEnv
  hk := wideBarrettNormalizedSkippedPrefix_add_len hone
  hread := wideBarrettNormalizedResultMem_read_canonical_payload hone
  hprefix := wideBarrettNormalizedSkippedPrefix_zero hone
  hfirst := by
    simpa [wideBarrettNormalizedWordFirstByteShape] using hfirst

/-- Nontrivial one-word inputs with odd modulus are exactly in the completed Montgomery branch. -/
theorem wideOneWordOdd_coveredAccepts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hodd : wideModulusParity ctx.executionEnv = ⟨1⟩) :
    coveredAccepts ctx := by
  rcases hone with ⟨hwideNontrivial, hmodPos, hmWord, hmod⟩
  rcases hwideNontrivial with ⟨haccepts, hcalldata, hwide, hexp, hbase⟩
  apply wideMontgomeryWord_coveredAccepts haccepts hcalldata hwide
  unfold wideMontgomeryWordCondition wideModulusNat wideModulusParity at *
  dsimp only at *
  exact ⟨hmodPos, hmWord, hexp, hbase, hmod, hodd⟩

/-- Nontrivial one-word inputs selected by the Barrett direct path are already covered. -/
theorem wideOneWordBarrettDirect_coveredAccepts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (heven : wideModulusParity ctx.executionEnv = ⟨0⟩)
    (hselector : wideBarrettDirectSelector ctx.executionEnv) :
    coveredAccepts ctx := by
  rcases hone with ⟨hwideNontrivial, hmodPos, hmWord, hmod⟩
  rcases hwideNontrivial with ⟨haccepts, hcalldata, hwide, hexp, hbase⟩
  apply wideBarrettDirectWord_coveredAccepts haccepts hcalldata hwide
  unfold wideBarrettDirectWordCondition wideModulusNat wideModulusParity
    wideBarrettDirectSelector at *
  dsimp only at *
  exact ⟨hmodPos, hmWord, hexp, hbase, hmod, heven, hselector⟩

/-- Nontrivial one-word inputs satisfying the normalized Barrett facts are already covered. -/
theorem wideOneWordBarrettNormalized_coveredAccepts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (heven : wideModulusParity ctx.executionEnv = ⟨0⟩)
    (hfacts : WideBarrettNormalizedWordFacts ctx.executionEnv) :
    coveredAccepts ctx := by
  rcases hone with ⟨hwideNontrivial, hmodPos, hmWord, hmod⟩
  rcases hwideNontrivial with ⟨haccepts, hcalldata, hwide, hexp, hbase⟩
  apply wideBarrettNormalizedWord_coveredAccepts haccepts hcalldata hwide
  unfold wideBarrettNormalizedWordCondition wideModulusNat wideModulusParity at *
  dsimp only at *
  exact ⟨hmodPos, hmWord, hexp, hbase, hmod, heven, hfacts⟩

/-- If a nontrivial one-word Barrett input is not selected by the direct branch, then the bytecode
scanner must take the normalization branch.  This closes the control-flow part of the
one-word Barrett residual; the remaining obligations are `WideBarrettNormalizedWordMemoryFacts`. -/
theorem wideOneWordBarrett_not_direct_hnorm {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hnotDirect : ¬ wideBarrettDirectSelector ctx.executionEnv) :
    let l := lengths ctx.executionEnv.calldata
    operandModulusPtr l.base l.exponent + 32 <
      barrettScanStop
        (wideWordResultMemory ctx.executionEnv l.base l.exponent l.modulus)
        (wideWordResultWords l.base l.exponent l.modulus)
        (operandModulusPtr l.base l.exponent) l.modulus := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let p := operandModulusPtr l.base l.exponent
  let mem := wideWordResultMemory I l.base l.exponent l.modulus
  let aw := wideWordResultWords l.base l.exponent l.modulus
  rcases hone with ⟨_hwideNontrivial, hmodPos, _hmWord, _hmodNat⟩
  have hmNeOne : l.modulus ≠ 1 := by
    intro hm
    exact hnotDirect (by
      unfold wideBarrettDirectSelector
      dsimp [I, l]
      exact Or.inl hm)
  have hmodPosL : 0 < l.modulus := by
    simpa [I, l] using hmodPos
  have hmGtOne : 1 < l.modulus := by omega
  have hfirstZero :
      UInt256.byteAt ⟨0⟩
        (wideLoadWord mem aw (UInt256.ofNat (p + 32))) = ⟨0⟩ := by
    by_contra hne
    exact hnotDirect (by
      unfold wideBarrettDirectSelector
      dsimp [I, l, p, mem, aw]
      exact Or.inr hne)
  have hstartLtEnd : barrettScanStart p < barrettScanEnd p l.modulus := by
    unfold barrettScanStart barrettScanEnd
    omega
  have hstartLtEnd' : p + 32 < barrettScanEnd p l.modulus := by
    simpa [barrettScanStart] using hstartLtEnd
  have hbounds := barrettScanStopAt_bounds mem aw (barrettScanEnd p l.modulus) (p + 32 + 1)
    (by
      unfold barrettScanEnd
      omega)
  change p + 32 < barrettScanStop mem aw p l.modulus
  unfold barrettScanStop barrettScanStart
  rw [barrettScanStopAt, dif_pos hstartLtEnd']
  simp [barrettScanByteAt, hfirstZero]
  omega

theorem wideBarrettNormalizedWordFirstByteShape_of_notDirect {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hnotDirect : ¬ wideBarrettDirectSelector ctx.executionEnv) :
    wideBarrettNormalizedWordFirstByteShape ctx.executionEnv := by
  let I := ctx.executionEnv
  let l := lengths I.calldata
  let baseSize := l.base
  let exponentSize := l.exponent
  let modulusSize := l.modulus
  let mem0 := wideWordResultMemory I baseSize exponentSize modulusSize
  let aw0 := wideWordResultWords baseSize exponentSize modulusSize
  let p := operandModulusPtr baseSize exponentSize
  let fp := wideBarrettNormalizedFp baseSize exponentSize modulusSize
  let n := wideBarrettNormalizedLenFor I baseSize exponentSize modulusSize
  let resultFp := wideBarrettNormalizedResultFp I baseSize exponentSize modulusSize
  let resultMem := wideBarrettNormalizedResultMemFor I
  let resultAw := wideBarrettNormalizedResultAwFor I
  by_cases hnOne : n = 1
  · left
    simpa [wideBarrettNormalizedWordFirstByteShape, I, l, baseSize, exponentSize,
      modulusSize, n] using hnOne
  · right
    have honeAll : wideOneWordBackendInputs ctx := hone
    rcases hone with ⟨hwideNontrivial, hmodPos, hmWord, hmodNat⟩
    have hwideNontrivialKeep := hwideNontrivial
    rcases hwideNontrivial with ⟨haccepts, _hcalldata, _hwide, _hexp, _hbase⟩
    have hvalid := haccepts.2
    unfold validOsaka at hvalid
    have hb : baseSize ≤ 1024 := by
      simpa [I, l, baseSize] using hvalid.1
    have he : exponentSize ≤ 1024 := by
      simpa [I, l, exponentSize] using hvalid.2.1
    have hm1024 : modulusSize ≤ 1024 := by
      have hm : (lengths I.calldata).modulus ≤ 1024 := hvalid.2.2
      simpa [I, l, modulusSize] using hm
    have hmodPosLocal : 0 < modulusSize := by
      simpa [I, l, modulusSize] using hmodPos
    have hmWordLocal : modulusSize ≤ 32 := by
      simpa [I, l, modulusSize] using hmWord
    let stop := barrettScanStop mem0 aw0 p modulusSize
    have hstartLeEnd : barrettScanStart p ≤ barrettScanEnd p modulusSize := by
      unfold barrettScanStart barrettScanEnd
      omega
    have hstopBounds := barrettScanStopAt_bounds mem0 aw0
      (barrettScanEnd p modulusSize) (barrettScanStart p) hstartLeEnd
    have hstopLower : barrettScanStart p ≤ stop := by
      simpa [stop, barrettScanStop] using hstopBounds.1
    have hstopUpper : stop ≤ barrettScanEnd p modulusSize := by
      simpa [stop, barrettScanStop] using hstopBounds.2
    have hnorm :
        p + 32 < stop := by
      simpa [I, l, baseSize, exponentSize, modulusSize, mem0, aw0, p, stop] using
        wideOneWordBarrett_not_direct_hnorm
          (ctx := ctx) honeAll hnotDirect
    have hdeltaLt : stop - p - 32 < modulusSize := by
      unfold barrettScanEnd at hstopUpper
      omega
    have hlenPos : 0 < n := by
      simpa [n, wideBarrettNormalizedLenFor, barrettNormalizedLen,
        barrettNormalizedOffset, mem0, aw0, p, stop, barrettScanStop] using
        Nat.sub_pos_of_lt hdeltaLt
    have hlen64 : n < 2 ^ 64 := by
      have hnLe : n ≤ modulusSize := by
        dsimp [n]
        unfold wideBarrettNormalizedLenFor barrettNormalizedLen
        exact Nat.sub_le _ _
      omega
    have hstopNe : barrettScanByteAt mem0 aw0 stop ≠ ⟨0⟩ := by
      have hstopCond := barrettScanStopAt_stop mem0 aw0
        (barrettScanEnd p modulusSize) (barrettScanStart p)
      have hcond :
          barrettScanEnd p modulusSize ≤ stop ∨
            barrettScanByteAt mem0 aw0 stop ≠ ⟨0⟩ := by
        simpa [stop, barrettScanStop] using hstopCond
      rcases hcond with hendLe | hne
      · exfalso
        have hstopEq : stop = barrettScanEnd p modulusSize := by omega
        apply hnOne
        dsimp [n]
        unfold wideBarrettNormalizedLenFor barrettNormalizedLen barrettNormalizedOffset
        rw [show barrettScanStop mem0 aw0 p modulusSize = stop by rfl, hstopEq]
        unfold barrettScanEnd
        omega
      · exact hne
    have hreadFirst :
        Model.bytesToNatPadded resultMem (fp + 32) 1 =
          Model.bytesToNatPadded mem0 stop 1 := by
      have hread := wideBarrettNormalizedResultMem_read_canonical_payload
        (ctx := ctx) honeAll
      have haddr :
          p + 32 + wideBarrettNormalizedSkippedPrefixFor I = stop := by
        have hskip :
            wideBarrettNormalizedSkippedPrefixFor I =
              barrettNormalizedOffset mem0 aw0 p modulusSize - 32 := by
          simp [wideBarrettNormalizedSkippedPrefixFor, I, l, baseSize, exponentSize,
            modulusSize, mem0, aw0, p]
        rw [hskip]
        dsimp [barrettNormalizedOffset, stop]
        omega
      have hfp64 : fp + 32 < 2 ^ 64 := by
        have hbounds := wideBarrettNormalizedMemoryBounds_of_oneWordBackendInputs
          (ctx := ctx) honeAll
        have hbound64 : fp + 32 + n + 32 < 2 ^ 64 := by
          simpa [wideBarrettNormalizedMemoryBounds, wideBarrettNormalizedFpFor,
            wideBarrettNormalizedLenForEnv, wideBarrettNormalizedResultAwFor, I, l,
            baseSize, exponentSize, modulusSize, fp, n, resultAw] using hbounds.1
        omega
      have hstop64 : stop < 2 ^ 64 := by
        have hsmall : stop < 2368 := by
          have hstopEnd : stop ≤ p + modulusSize + 31 := by
            simpa [barrettScanEnd] using hstopUpper
          dsimp [p] at hstopEnd
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at hstopEnd
          omega
        exact lt_of_lt_of_le hsmall (by norm_num)
      have hfirst :=
        model_bytesToNatPadded_first_eq_of_readWithPadding
          (a := resultMem) (b := mem0) (offA := fp + 32) (offB := stop)
          (width := n) hfp64 hstop64 hlen64 hlenPos
      have hread' :
          resultMem.readWithPadding (fp + 32) n =
            mem0.readWithPadding stop n := by
        simpa [resultMem, fp, n, I, l, baseSize, exponentSize, modulusSize, mem0,
          p, haddr] using hread
      exact hfirst hread'
    have htargetModel :
        (barrettScanByteAt resultMem resultAw (fp + 32)).toNat =
          Model.bytesToNatPadded resultMem (fp + 32) 1 := by
      have hbounds := wideBarrettNormalizedMemoryBounds_of_oneWordBackendInputs
        (ctx := ctx) honeAll
      have hfp32Lt64 : fp + 32 < 2 ^ 64 := by
        have hbound64 : fp + 32 + n + 32 < 2 ^ 64 := by
          simpa [wideBarrettNormalizedMemoryBounds, wideBarrettNormalizedFpFor,
            wideBarrettNormalizedLenForEnv, wideBarrettNormalizedResultAwFor, I, l,
            baseSize, exponentSize, modulusSize, fp, n, resultAw] using hbounds.1
        omega
      have hfp32LtWord : fp + 32 < UInt256.size :=
        lt_trans hfp32Lt64 (by native_decide)
      apply barrettScanByteAt_toNat_eq_model
      · exact hfp32LtWord
      · exact hfp32Lt64
      · intro hfrontier
        change (resultAw * ⟨32⟩).toNat ≤
            (UInt256.ofNat (fp + 32)).toNat at hfrontier
        have hawNat : (resultAw * ⟨32⟩).toNat = 32 * resultAw.toNat := by
          rw [umul_toNat]
          · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide, Nat.mul_comm]
          · rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
            simpa [Nat.mul_comm, wideBarrettNormalizedMemoryBounds,
              wideBarrettNormalizedResultAwFor, I, l, baseSize, exponentSize,
              modulusSize, resultAw] using hbounds.2.2
        rw [hawNat, UInt256.toNat_ofNat_of_lt hfp32LtWord] at hfrontier
        have hactive : fp + 32 + n + 32 ≤ 32 * resultAw.toNat := by
          simpa [wideBarrettNormalizedMemoryBounds, wideBarrettNormalizedFpFor,
            wideBarrettNormalizedLenForEnv, wideBarrettNormalizedResultAwFor, I, l,
            baseSize, exponentSize, modulusSize, fp, n, resultAw] using hbounds.2.1
        omega
    have hstopModel :
        (barrettScanByteAt mem0 aw0 stop).toNat =
          Model.bytesToNatPadded mem0 stop 1 := by
      have hstopLtWord : stop < UInt256.size := by
        have hsmall : stop < 2368 := by
          have hstopEnd : stop ≤ p + modulusSize + 31 := by
            simpa [barrettScanEnd] using hstopUpper
          dsimp [p] at hstopEnd
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at hstopEnd
          omega
        exact lt_of_lt_of_le hsmall (by decide)
      have hstopLt64 : stop < 2 ^ 64 := by
        have hsmall : stop < 2368 := by
          have hstopEnd : stop ≤ p + modulusSize + 31 := by
            simpa [barrettScanEnd] using hstopUpper
          dsimp [p] at hstopEnd
          unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at hstopEnd
          omega
        exact lt_of_lt_of_le hsmall (by norm_num)
      apply barrettScanByteAt_toNat_eq_model
      · exact hstopLtWord
      · exact hstopLt64
      · intro hfrontier
        change (aw0 * ⟨32⟩).toNat ≤
            (UInt256.ofNat stop).toNat at hfrontier
        rw [show (aw0 * ⟨32⟩).toNat =
            operandFreePtr baseSize exponentSize modulusSize +
              bytesAllocationSize modulusSize by
          dsimp [aw0]
          exact resultActiveBytes_toNat hb he hm1024] at hfrontier
        rw [UInt256.toNat_ofNat_of_lt hstopLtWord] at hfrontier
        have hstopEnd : stop ≤ p + modulusSize + 31 := by
          simpa [barrettScanEnd] using hstopUpper
        dsimp [p] at hfrontier hstopEnd
        unfold operandFreePtr operandModulusPtr operandExponentPtr operandBasePtr
          bytesAllocationSize at hfrontier
        unfold operandModulusPtr operandExponentPtr operandBasePtr bytesAllocationSize at hstopEnd
        omega
    have htargetNatEq :
        (barrettScanByteAt resultMem resultAw (fp + 32)).toNat =
          (barrettScanByteAt mem0 aw0 stop).toNat := by
      calc
        (barrettScanByteAt resultMem resultAw (fp + 32)).toNat
            = Model.bytesToNatPadded resultMem (fp + 32) 1 := htargetModel
        _ = Model.bytesToNatPadded mem0 stop 1 := hreadFirst
        _ = (barrettScanByteAt mem0 aw0 stop).toNat := hstopModel.symm
    intro hzero
    have hzTarget :
        (barrettScanByteAt resultMem resultAw (fp + 32)).toNat = 0 := by
      simpa [barrettScanByteAt, resultMem, resultAw, fp, I, l, baseSize,
        exponentSize, modulusSize] using congrArg UInt256.toNat hzero
    apply hstopNe
    apply u256_inj
    have hzStop : (barrettScanByteAt mem0 aw0 stop).toNat = 0 := by
      rw [← htargetNatEq]
      exact hzTarget
    simpa using hzStop

/-- One-word even Barrett inputs whose first scan selects normalization are covered once the
normalized-memory facts are available. -/
theorem wideOneWordBarrettNormalizedMemory_coveredAccepts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (heven : wideModulusParity ctx.executionEnv = ⟨0⟩)
    (hnotDirect : ¬ wideBarrettDirectSelector ctx.executionEnv)
    (hmem : WideBarrettNormalizedWordMemoryFacts ctx.executionEnv) :
    coveredAccepts ctx := by
  exact wideOneWordBarrettNormalized_coveredAccepts hone heven
    (wideBarrettNormalizedWordFacts_of_hnorm_memory
      (wideOneWordBarrett_not_direct_hnorm hone hnotDirect) hmem)

/-- One-word even Barrett direct-false inputs are covered from pure normalized-payload facts plus
the active-memory bounds needed to connect the bytecode zero/one scanners to those facts. -/
theorem wideOneWordBarrettNormalizedModel_coveredAccepts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (heven : wideModulusParity ctx.executionEnv = ⟨0⟩)
    (hnotDirect : ¬ wideBarrettDirectSelector ctx.executionEnv)
    (hbounds : wideBarrettNormalizedMemoryBounds ctx.executionEnv)
    (hmodel : WideBarrettNormalizedWordModelFacts ctx.executionEnv) :
    coveredAccepts ctx := by
  exact wideOneWordBarrettNormalizedMemory_coveredAccepts hone heven hnotDirect
    (wideBarrettNormalizedWordMemoryFacts_of_model hbounds hmodel)

/-- In the one-word backend shape, the normalized-memory bounds are automatic.  Thus only the pure
normalized-payload facts remain for the direct-false Barrett-normalized coverage theorem. -/
theorem wideOneWordBarrettNormalizedModelAuto_coveredAccepts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (heven : wideModulusParity ctx.executionEnv = ⟨0⟩)
    (hnotDirect : ¬ wideBarrettDirectSelector ctx.executionEnv)
    (hmodel : WideBarrettNormalizedWordModelFacts ctx.executionEnv) :
    coveredAccepts ctx := by
  exact wideOneWordBarrettNormalizedModel_coveredAccepts hone heven hnotDirect
    (wideBarrettNormalizedMemoryBounds_of_oneWordBackendInputs hone) hmodel

/-- Payload-oriented one-word Barrett-normalized coverage theorem.  The `≠ 0` and `≠ 1` scanner
model facts are derived from payload equality with the original modulus and `wideModulusNat > 1`. -/
theorem wideOneWordBarrettNormalizedPayload_coveredAccepts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (heven : wideModulusParity ctx.executionEnv = ⟨0⟩)
    (hnotDirect : ¬ wideBarrettDirectSelector ctx.executionEnv)
    (hpayload : WideBarrettNormalizedWordPayloadFacts ctx.executionEnv) :
    coveredAccepts ctx := by
  exact wideOneWordBarrettNormalizedModelAuto_coveredAccepts hone heven hnotDirect
    (wideBarrettNormalizedWordModelFacts_of_oneWordPayload hone hpayload)

/-- The bytecode only branches on whether the one-word modulus parity is zero or one.  Keeping
this as a named obligation makes the remaining one-word coverage theorem independent of the
particular bit-arithmetic proof for `modulusLastByteParity`. -/
def wideModulusParityCoverage (ctx : BytecodeContext) : Prop :=
  wideModulusParity ctx.executionEnv = ⟨0⟩ ∨
    wideModulusParity ctx.executionEnv = ⟨1⟩

/-- The parity value is unconditionally binary because it is computed by masking with one. -/
theorem wideModulusParityCoverage_of_landOne {ctx : BytecodeContext} :
    wideModulusParityCoverage ctx := by
  let l := lengths ctx.executionEnv.calldata
  let x :=
    modulusLastByteMasked
      (operandCopiedMemory ctx.executionEnv l.base l.exponent l.modulus)
      (operandModulusActiveWords l.base l.exponent l.modulus)
      l.base l.exponent l.modulus
  have hto :
      (UInt256.land x ⟨1⟩).toNat = x.toNat % 2 := by
    exact uInt256_land_one_toNat x
  rcases Nat.mod_two_eq_zero_or_one x.toNat with hzero | hone
  · left
    apply u256_inj
    rw [wideModulusParity, modulusLastByteParity]
    change (UInt256.land x ⟨1⟩).toNat = (⟨0⟩ : UInt256).toNat
    rw [hto, hzero]
    decide
  · right
    apply u256_inj
    rw [wideModulusParity, modulusLastByteParity]
    change (UInt256.land x ⟨1⟩).toNat = (⟨1⟩ : UInt256).toNat
    rw [hto, hone]
    decide

/-- The remaining multi-limb residual follows the bytecode dispatcher split: odd modulus goes to
Montgomery, even modulus goes to Barrett. -/
theorem wideMultiLimbBackendInputs_split {ctx : BytecodeContext}
    (hmulti : wideMultiLimbBackendInputs ctx) :
    wideMultiLimbEvenBarrettInputs ctx ∨ wideMultiLimbOddMontgomeryInputs ctx := by
  rcases wideModulusParityCoverage_of_landOne (ctx := ctx) with heven | hodd
  · exact Or.inl ⟨hmulti, heven⟩
  · exact Or.inr ⟨hmulti, hodd⟩

/-- The remaining payload obligation for the one-word Barrett-normalized fallback.  It is only
needed when the even-modulus Barrett direct selector is false. -/
def wideOneWordPayloadCoverage (ctx : BytecodeContext) : Prop :=
  ¬ wideBarrettDirectSelector ctx.executionEnv →
    WideBarrettNormalizedWordPayloadFacts ctx.executionEnv

/-- The remaining canonical normalized-shape obligation for the one-word Barrett-normalized
fallback.  The normalized payload read and skipped-prefix arithmetic are discharged separately. -/
def wideOneWordFirstByteCoverage (ctx : BytecodeContext) : Prop :=
  ¬ wideBarrettDirectSelector ctx.executionEnv →
    wideBarrettNormalizedWordFirstByteShape ctx.executionEnv

/-- Lower-level form of the one-word payload obligation.  The remaining direct-false Barrett
case can be discharged from normalized read facts; the Nat payload equality is then supplied by
`wideBarrettNormalizedPayloadNat_eq_wideModulusNat_of_read_prefix`. -/
theorem wideOneWordPayloadCoverage_of_readFacts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hreadFacts :
      ¬ wideBarrettDirectSelector ctx.executionEnv →
        WideBarrettNormalizedWordReadFacts ctx.executionEnv) :
    wideOneWordPayloadCoverage ctx := by
  intro hnotDirect
  exact wideBarrettNormalizedWordPayloadFacts_of_readFacts hone (hreadFacts hnotDirect)

/-- Canonical one-word payload coverage: after the normalized copy/read preservation proof, the
only remaining normalized Barrett fact is that the copied payload has the expected first-byte
shape. -/
theorem wideOneWordPayloadCoverage_of_firstByte {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hfirst : wideOneWordFirstByteCoverage ctx) :
    wideOneWordPayloadCoverage ctx := by
  apply wideOneWordPayloadCoverage_of_readFacts hone
  intro hnotDirect
  exact wideBarrettNormalizedWordReadFacts_of_canonical hone (hfirst hnotDirect)

theorem wideOneWordFirstByteCoverage_of_canonical {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx) :
    wideOneWordFirstByteCoverage ctx := by
  intro hnotDirect
  exact wideBarrettNormalizedWordFirstByteShape_of_notDirect hone hnotDirect

/-- Conditional coverage theorem for the entire nontrivial one-word backend.  This packages the
already-proved Montgomery/direct-Barrett/normalized-Barrett bytecode specs behind the two residual
facts that are still separate from branch-local execution: parity coverage and normalized payload
coverage. -/
theorem wideOneWordBackend_coveredAccepts_of_payloadCoverage {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hparity : wideModulusParityCoverage ctx)
    (hpayload : wideOneWordPayloadCoverage ctx) :
    coveredAccepts ctx := by
  rcases hparity with heven | hodd
  · by_cases hdirect : wideBarrettDirectSelector ctx.executionEnv
    · exact wideOneWordBarrettDirect_coveredAccepts hone heven hdirect
    · exact wideOneWordBarrettNormalizedPayload_coveredAccepts hone heven hdirect
        (hpayload hdirect)
  · exact wideOneWordOdd_coveredAccepts hone hodd

/-- Coverage theorem for the entire nontrivial one-word backend, after discharging the generic
parity fact.  The only remaining non-execution obligation is the normalized payload fact in the
even/direct-false Barrett branch. -/
theorem wideOneWordBackend_coveredAccepts_of_payload {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hpayload : wideOneWordPayloadCoverage ctx) :
    coveredAccepts ctx := by
  exact wideOneWordBackend_coveredAccepts_of_payloadCoverage hone
    wideModulusParityCoverage_of_landOne hpayload

/-- One-word backend coverage from the lower-level normalized read facts. -/
theorem wideOneWordBackend_coveredAccepts_of_readFacts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hreadFacts :
      ¬ wideBarrettDirectSelector ctx.executionEnv →
        WideBarrettNormalizedWordReadFacts ctx.executionEnv) :
    coveredAccepts ctx := by
  exact wideOneWordBackend_coveredAccepts_of_payload hone
    (wideOneWordPayloadCoverage_of_readFacts hone hreadFacts)

/-- One-word backend coverage in the current strongest canonical form: parity is automatic and the
normalized read/prefix facts are proved, so only the normalized first-byte shape remains. -/
theorem wideOneWordBackend_coveredAccepts_of_firstByte {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx)
    (hfirst : wideOneWordFirstByteCoverage ctx) :
    coveredAccepts ctx := by
  exact wideOneWordBackend_coveredAccepts_of_payload hone
    (wideOneWordPayloadCoverage_of_firstByte hone hfirst)

/-- The nontrivial one-word backend is fully covered by the completed Montgomery and Barrett
one-word bytecode specs. -/
theorem wideOneWordBackend_coveredAccepts {ctx : BytecodeContext}
    (hone : wideOneWordBackendInputs ctx) :
    coveredAccepts ctx := by
  exact wideOneWordBackend_coveredAccepts_of_firstByte hone
    (wideOneWordFirstByteCoverage_of_canonical hone)

/-- Bounded-calldata missing cases are exactly in the wide nontrivial backend region. -/
theorem missing_bounded_wideNontrivialInputs {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64) :
    wideNontrivialInputs ctx := by
  have hnotFast := missing_not_wideFast hmissing hcalldata
  refine ⟨hmissing.1, hcalldata, missing_not_wordSized hmissing, ?_, ?_⟩
  · intro hexp
    exact hnotFast (Or.inl (by
      simpa [wideExponentOffset] using hexp))
  · by_contra hbaseNot
    have hbaseLe :
        Model.bytesToNatPadded ctx.executionEnv.calldata 96
          (lengths ctx.executionEnv.calldata).base ≤ 1 := by
      omega
    exact hnotFast (Or.inr hbaseLe)

/-- Bounded-calldata missing cases are outside every backend branch whose bytecode proof is
currently completed. -/
theorem missing_bounded_not_completedBackends {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64) :
    wideNontrivialInputs ctx ∧
    ¬ wideMontgomeryWordCondition ctx.executionEnv ∧
    ¬ wideBarrettDirectWordCondition ctx.executionEnv ∧
    ¬ wideBarrettNormalizedWordCondition ctx.executionEnv := by
  exact ⟨missing_bounded_wideNontrivialInputs hmissing hcalldata,
    missing_not_wideMontgomeryWord hmissing hcalldata,
    missing_not_wideBarrettDirectWord hmissing hcalldata,
    missing_not_wideBarrettNormalizedWord hmissing hcalldata⟩

/-- A bounded missing case cannot be a nontrivial one-word odd-modulus input. -/
theorem missing_bounded_oneWord_not_odd {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    wideModulusParity ctx.executionEnv ≠ ⟨1⟩ := by
  intro hodd
  exact hmissing.2 (wideOneWordOdd_coveredAccepts hone hodd)

/-- A bounded missing case cannot be in the completed one-word Barrett-direct branch. -/
theorem missing_bounded_oneWord_not_barrettDirect {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      wideBarrettDirectSelector ctx.executionEnv) := by
  intro h
  exact hmissing.2 (wideOneWordBarrettDirect_coveredAccepts hone h.1 h.2)

/-- A bounded missing case cannot be in the completed one-word Barrett-normalized branch. -/
theorem missing_bounded_oneWord_not_barrettNormalized {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      WideBarrettNormalizedWordFacts ctx.executionEnv) := by
  intro h
  exact hmissing.2 (wideOneWordBarrettNormalized_coveredAccepts hone h.1 h.2)

/-- After closing the scanner-control fact, a bounded missing one-word even-Barrett direct-false
case can only be missing because the normalized-memory facts have not been proved. -/
theorem missing_bounded_oneWord_not_barrettNormalizedMemory {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      ¬ wideBarrettDirectSelector ctx.executionEnv ∧
      WideBarrettNormalizedWordMemoryFacts ctx.executionEnv) := by
  intro h
  exact hmissing.2
    (wideOneWordBarrettNormalizedMemory_coveredAccepts hone h.1 h.2.1 h.2.2)

/-- A bounded missing one-word even-Barrett direct-false case can only remain after the pure
normalized-payload facts or their active-memory bounds are absent. -/
theorem missing_bounded_oneWord_not_barrettNormalizedModel {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      ¬ wideBarrettDirectSelector ctx.executionEnv ∧
      wideBarrettNormalizedMemoryBounds ctx.executionEnv ∧
      WideBarrettNormalizedWordModelFacts ctx.executionEnv) := by
  intro h
  exact hmissing.2
    (wideOneWordBarrettNormalizedModel_coveredAccepts hone h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- With memory bounds automatic, a bounded missing one-word even-Barrett direct-false case can
only remain because the pure normalized-payload facts have not been proved. -/
theorem missing_bounded_oneWord_not_barrettNormalizedModelAuto {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      ¬ wideBarrettDirectSelector ctx.executionEnv ∧
      WideBarrettNormalizedWordModelFacts ctx.executionEnv) := by
  intro h
  exact hmissing.2
    (wideOneWordBarrettNormalizedModelAuto_coveredAccepts hone h.1 h.2.1 h.2.2)

/-- After reducing model facts to payload equality and first-byte shape, a bounded missing
one-word even-Barrett direct-false case can only remain because those payload facts are absent. -/
theorem missing_bounded_oneWord_not_barrettNormalizedPayload {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      ¬ wideBarrettDirectSelector ctx.executionEnv ∧
      WideBarrettNormalizedWordPayloadFacts ctx.executionEnv) := by
  intro h
  exact hmissing.2
    (wideOneWordBarrettNormalizedPayload_coveredAccepts hone h.1 h.2.1 h.2.2)

/-- If a bounded missing case is in the one-word nontrivial shape, the remaining obligation is
only the unproved branch-selection gap around the one-word Barrett normalization predicate. -/
theorem missing_bounded_oneWord_residual {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    wideModulusParity ctx.executionEnv ≠ ⟨1⟩ ∧
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      wideBarrettDirectSelector ctx.executionEnv) ∧
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      WideBarrettNormalizedWordFacts ctx.executionEnv) := by
  exact ⟨missing_bounded_oneWord_not_odd hmissing hcalldata hone,
    missing_bounded_oneWord_not_barrettDirect hmissing hcalldata hone,
    missing_bounded_oneWord_not_barrettNormalized hmissing hcalldata hone⟩

/-- Stronger one-word residual after factoring normalized Barrett facts into scanner-control plus
normalized-memory obligations. -/
theorem missing_bounded_oneWord_residual_memory {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    wideModulusParity ctx.executionEnv ≠ ⟨1⟩ ∧
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      wideBarrettDirectSelector ctx.executionEnv) ∧
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      ¬ wideBarrettDirectSelector ctx.executionEnv ∧
      WideBarrettNormalizedWordMemoryFacts ctx.executionEnv) := by
  exact ⟨missing_bounded_oneWord_not_odd hmissing hcalldata hone,
    missing_bounded_oneWord_not_barrettDirect hmissing hcalldata hone,
    missing_bounded_oneWord_not_barrettNormalizedMemory hmissing hcalldata hone⟩

/-- Residual expressed in the most model-oriented one-word form currently available. -/
theorem missing_bounded_oneWord_residual_model {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    wideModulusParity ctx.executionEnv ≠ ⟨1⟩ ∧
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      wideBarrettDirectSelector ctx.executionEnv) ∧
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      ¬ wideBarrettDirectSelector ctx.executionEnv ∧
      wideBarrettNormalizedMemoryBounds ctx.executionEnv ∧
      WideBarrettNormalizedWordModelFacts ctx.executionEnv) := by
  exact ⟨missing_bounded_oneWord_not_odd hmissing hcalldata hone,
    missing_bounded_oneWord_not_barrettDirect hmissing hcalldata hone,
    missing_bounded_oneWord_not_barrettNormalizedModel hmissing hcalldata hone⟩

/-- Residual after discharging the normalized-memory active-bounds side condition. -/
theorem missing_bounded_oneWord_residual_model_auto {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    wideModulusParity ctx.executionEnv ≠ ⟨1⟩ ∧
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      wideBarrettDirectSelector ctx.executionEnv) ∧
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      ¬ wideBarrettDirectSelector ctx.executionEnv ∧
      WideBarrettNormalizedWordModelFacts ctx.executionEnv) := by
  exact ⟨missing_bounded_oneWord_not_odd hmissing hcalldata hone,
    missing_bounded_oneWord_not_barrettDirect hmissing hcalldata hone,
    missing_bounded_oneWord_not_barrettNormalizedModelAuto hmissing hcalldata hone⟩

/-- Residual after reducing normalized model facts to payload equality and first-byte shape. -/
theorem missing_bounded_oneWord_residual_payload {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    wideModulusParity ctx.executionEnv ≠ ⟨1⟩ ∧
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      wideBarrettDirectSelector ctx.executionEnv) ∧
    ¬ (wideModulusParity ctx.executionEnv = ⟨0⟩ ∧
      ¬ wideBarrettDirectSelector ctx.executionEnv ∧
      WideBarrettNormalizedWordPayloadFacts ctx.executionEnv) := by
  exact ⟨missing_bounded_oneWord_not_odd hmissing hcalldata hone,
    missing_bounded_oneWord_not_barrettDirect hmissing hcalldata hone,
    missing_bounded_oneWord_not_barrettNormalizedPayload hmissing hcalldata hone⟩

/-- If the two residual one-word obligations are supplied, no bounded missing case can remain in
the nontrivial one-word backend. -/
theorem missing_bounded_oneWord_impossible_of_payloadCoverage {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx)
    (hparity : wideModulusParityCoverage ctx)
    (hpayload : wideOneWordPayloadCoverage ctx) :
    False := by
  exact hmissing.2
    (wideOneWordBackend_coveredAccepts_of_payloadCoverage hone hparity hpayload)

/-- No bounded missing case can remain in the nontrivial one-word backend once the normalized
payload obligation is supplied. -/
theorem missing_bounded_oneWord_impossible_of_payload {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx)
    (hpayload : wideOneWordPayloadCoverage ctx) :
    False := by
  exact hmissing.2
    (wideOneWordBackend_coveredAccepts_of_payload hone hpayload)

/-- No bounded missing case can remain in the nontrivial one-word backend once the lower-level
normalized read facts are supplied for the direct-false Barrett branch. -/
theorem missing_bounded_oneWord_impossible_of_readFacts {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx)
    (hreadFacts :
      ¬ wideBarrettDirectSelector ctx.executionEnv →
        WideBarrettNormalizedWordReadFacts ctx.executionEnv) :
    False := by
  exact hmissing.2
    (wideOneWordBackend_coveredAccepts_of_readFacts hone hreadFacts)

/-- No bounded missing case can remain in the nontrivial one-word backend once the canonical
normalized first-byte shape is supplied for the direct-false Barrett branch. -/
theorem missing_bounded_oneWord_impossible_of_firstByte {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx)
    (hfirst : wideOneWordFirstByteCoverage ctx) :
    False := by
  exact hmissing.2
    (wideOneWordBackend_coveredAccepts_of_firstByte hone hfirst)

/-- No bounded missing case can remain in the nontrivial one-word backend. -/
theorem missing_bounded_oneWord_impossible {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (_hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64)
    (hone : wideOneWordBackendInputs ctx) :
    False := by
  exact hmissing.2 (wideOneWordBackend_coveredAccepts hone)

theorem missing_bounded_not_oneWordBackend {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64) :
    ¬ wideOneWordBackendInputs ctx := by
  intro hone
  exact missing_bounded_oneWord_impossible hmissing hcalldata hone

theorem wideNontrivial_not_oneWord_notSmall_split {ctx : BytecodeContext}
    (hwide : wideNontrivialInputs ctx)
    (hnotOne : ¬ wideOneWordBackendInputs ctx)
    (hnotZero : ¬ wideZeroModulusLengthCondition ctx.executionEnv)
    (hnotSmall : ¬ wideSmallModulusValueCondition ctx.executionEnv) :
    wideBackendResidualInputs ctx := by
  by_cases hle : (lengths ctx.executionEnv.calldata).modulus ≤ 32
  · by_cases hpos : 0 < (lengths ctx.executionEnv.calldata).modulus
    · by_cases hgt : 1 < wideModulusNat ctx.executionEnv
      · exact False.elim (hnotOne ⟨hwide, hpos, hle, hgt⟩)
      · have hsmallLe : wideModulusNat ctx.executionEnv ≤ 1 := by omega
        exact False.elim (hnotSmall (by
          unfold wideSmallModulusValueCondition
          dsimp
          rcases hwide with ⟨_haccepts, _hcalldata, _hword, hexp, hbase⟩
          refine ⟨hpos, hle, ?_, hbase, ?_⟩
          · simpa using hexp
          · simpa [wideModulusNat] using hsmallLe))
    · exact False.elim (hnotZero (by
        unfold wideZeroModulusLengthCondition
        dsimp
        rcases hwide with ⟨_haccepts, _hcalldata, _hword, hexp, hbase⟩
        refine ⟨?_, ?_, hbase⟩
        · exact Nat.eq_zero_of_not_pos hpos
        · simpa using hexp))
  ·
    refine ⟨hwide, ?_⟩
    omega

theorem wideNontrivial_not_oneWord_split {ctx : BytecodeContext}
    (hwide : wideNontrivialInputs ctx)
    (hnotOne : ¬ wideOneWordBackendInputs ctx) :
    wideMultiLimbBackendInputs ctx ∨
      (wideNontrivialInputs ctx ∧
        (lengths ctx.executionEnv.calldata).modulus ≤ 32 ∧
        wideModulusNat ctx.executionEnv ≤ 1) := by
  by_cases hle : (lengths ctx.executionEnv.calldata).modulus ≤ 32
  · right
    refine ⟨hwide, hle, ?_⟩
    by_cases hpos : 0 < (lengths ctx.executionEnv.calldata).modulus
    · by_contra hnotSmall
      have hgt : 1 < wideModulusNat ctx.executionEnv := by omega
      exact hnotOne ⟨hwide, hpos, hle, hgt⟩
    · have hzero : (lengths ctx.executionEnv.calldata).modulus = 0 :=
        Nat.eq_zero_of_not_pos hpos
      simp [wideModulusNat, hzero]
  · left
    refine ⟨hwide, ?_⟩
    omega

/-- After the completed word-sized, fast-exit, zero-length, small-value, and one-word nontrivial
backend proofs, any bounded missing case is in the remaining multi-limb backend residual. -/
theorem missing_bounded_backendResidualInputs {ctx : BytecodeContext}
    (hmissing : missingModexpCases ctx)
    (hcalldata : ctx.executionEnv.calldata.size < 2 ^ 64) :
    wideBackendResidualInputs ctx := by
  exact wideNontrivial_not_oneWord_notSmall_split
    (missing_bounded_wideNontrivialInputs hmissing hcalldata)
    (missing_bounded_not_oneWordBackend hmissing hcalldata)
    (missing_not_wideZeroModulusLength hmissing hcalldata)
    (missing_not_wideSmallModulusValue hmissing hcalldata)

/-- If there are no missing cases, the current covered branch specs lift to the intended general
ModExp functional spec. -/
theorem modexpSomeExactGasSpec_of_coverage
    (hcoverage : ∀ ctx : BytecodeContext, modexpAccepts ctx → coveredAccepts ctx) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  constructor
  intro ctx hcode haccepts
  exact coveredBytecodeSomeExactGasSpec.run ctx hcode (hcoverage ctx haccepts)

/-- A more structured sufficient condition for the intended general ModExp spec.  Once every
accepted input has the calldata-size bound required by the current wide proofs, and the residual
multi-limb backend region is covered, the branch-local specs cover every accepted input. -/
theorem modexpSomeExactGasSpec_of_bounded_residualCoverage
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (hresidual :
      ∀ ctx : BytecodeContext, wideBackendResidualInputs ctx → coveredAccepts ctx) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  apply modexpSomeExactGasSpec_of_coverage
  intro ctx haccepts
  by_cases hword : wordSized ctx.executionEnv.calldata
  · exact wordSized_coveredAccepts haccepts hword
  · have hcalldata := hbounded ctx haccepts
    by_cases hfast : wideFastCondition ctx.executionEnv.calldata
    · exact wideFast_coveredAccepts haccepts hcalldata hword hfast
    · have hwide : wideNontrivialInputs ctx := by
        refine ⟨haccepts, hcalldata, hword, ?_, ?_⟩
        · intro hexp
          exact hfast (Or.inl (by
            simpa [wideExponentOffset] using hexp))
        · by_contra hbaseNot
          have hbaseLe :
              Model.bytesToNatPadded ctx.executionEnv.calldata 96
                (lengths ctx.executionEnv.calldata).base ≤ 1 := by
            omega
          exact hfast (Or.inr hbaseLe)
      by_cases hzero : wideZeroModulusLengthCondition ctx.executionEnv
      · exact wideZeroModulusLength_coveredAccepts haccepts hcalldata hword hzero
      · by_cases hsmall : wideSmallModulusValueCondition ctx.executionEnv
        · exact wideSmallModulusValue_coveredAccepts haccepts hcalldata hword hsmall
        · by_cases hone : wideOneWordBackendInputs ctx
          · exact wideOneWordBackend_coveredAccepts hone
          · exact hresidual ctx
              (wideNontrivial_not_oneWord_notSmall_split hwide hone hzero hsmall)

/-- Variant of `modexpSomeExactGasSpec_of_bounded_residualCoverage` with the remaining multi-limb
backend obligation split along the bytecode's odd/even dispatcher. -/
theorem modexpSomeExactGasSpec_of_bounded_multiLimbBranchCoverage
    (hbounded :
      ∀ ctx : BytecodeContext, modexpAccepts ctx → ctx.executionEnv.calldata.size < 2 ^ 64)
    (hodd :
      ∀ ctx : BytecodeContext, wideMultiLimbOddMontgomeryInputs ctx → coveredAccepts ctx)
    (heven :
      ∀ ctx : BytecodeContext, wideMultiLimbEvenBarrettInputs ctx → coveredAccepts ctx) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  apply modexpSomeExactGasSpec_of_bounded_residualCoverage hbounded
  intro ctx hmulti
  rcases wideMultiLimbBackendInputs_split hmulti with hevenCase | hoddCase
  · exact heven ctx hevenCase
  · exact hodd ctx hoddCase

/-- Equivalent no-missing-cases form of the coverage obligation. -/
theorem modexpSomeExactGasSpec_of_noMissing
    (hnoMissing : ∀ ctx : BytecodeContext, ¬ missingModexpCases ctx) :
    BytecodeSpec runtimeBytecode modexpAccepts modexpSomeExactGasEnsures := by
  apply modexpSomeExactGasSpec_of_coverage
  intro ctx haccepts
  by_contra hcovered
  exact hnoMissing ctx ⟨haccepts, hcovered⟩

end Modexp
