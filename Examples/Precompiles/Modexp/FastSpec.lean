import Examples.Precompiles.Modexp.BaseReturn
import Examples.Precompiles.Modexp.WordSpec

/-!
# Caller-visible specifications for the completed arbitrary-width fast paths

These theorems include the parser/dispatcher charge.  They are direct bytecode specifications;
the output side is `Model.output`, whose successful-runner correspondence is proved by
`model_runModexp_osaka_success`.
-/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Modexp

set_option maxRecDepth 30000
set_option maxHeartbeats 0
set_option Elab.async false

def wideEntryGas (input : ByteArray) : Nat :=
  let l := lengths input
  if 32 < l.base then 161 else if 32 < l.exponent then 187 else 213

private theorem sizeWord_eq_ofNat (w : UInt256) (n : Nat)
    (hword : w.toNat = n) (hn : n ≤ 1024) : w = UInt256.ofNat n := by
  apply u256_inj
  rw [hword, UInt256.toNat_ofNat_of_lt
    (lt_trans (lt_of_le_of_lt hn (by decide : 1024 < 2 ^ 64)) (by decide))]

/-- Exact dispatcher theorem for every valid input outside the all-single-word path. -/
theorem reachWideEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hvalid : validOsaka I.calldata) (hwide : ¬ wordSized I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨62⟩
      [UInt256.ofNat (lengths I.calldata).exponent,
        UInt256.ofNat (lengths I.calldata).base,
        UInt256.ofNat (lengths I.calldata).modulus]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k
      (wideEntryGas I.calldata) := by
  unfold validOsaka at hvalid
  unfold wordSized at hwide
  rcases hvalid with ⟨hb1024, he1024, hm1024⟩
  have hbWord := sizeWord_eq_ofNat (baseSizeWord I) (lengths I.calldata).base
    (baseSizeWord_toNat I) hb1024
  have heWord := sizeWord_eq_ofNat (exponentSizeWord I) (lengths I.calldata).exponent
    (exponentSizeWord_toNat I) he1024
  have hmWord := sizeWord_eq_ofNat (modulusSizeWord I) (lengths I.calldata).modulus
    (modulusSizeWord_toNat I) hm1024
  by_cases hb : (lengths I.calldata).base ≤ 32
  · by_cases he : (lengths I.calldata).exponent ≤ 32
    · have hm : 32 < (lengths I.calldata).modulus := by
        by_contra hmn
        exact hwide ⟨hb, he, by omega⟩
      obtain ⟨k, rd⟩ := reachWideModulus
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hvalue
        (by simpa using hb1024) (by simpa using he1024) (by simpa using hm1024)
        (by simpa using hb) (by simpa using he) (by simpa using hm)
      refine ⟨k, ?_⟩
      simpa [wideEntryGas, not_lt.mpr hb, not_lt.mpr he] using
        rd.withStack (by rw [hbWord, heWord, hmWord])
    · have hegt : 32 < (lengths I.calldata).exponent := by omega
      obtain ⟨k, rd⟩ := reachWideExponent
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hvalue
        (by simpa using hb1024) (by simpa using he1024) (by simpa using hm1024)
        (by simpa using hb) (by simpa using hegt)
      refine ⟨k, ?_⟩
      simpa [wideEntryGas, not_lt.mpr hb, hegt] using
        rd.withStack (by rw [hbWord, heWord, hmWord])
  · have hbgt : 32 < (lengths I.calldata).base := by omega
    obtain ⟨k, rd⟩ := reachWideBase
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode hvalue
      (by simpa using hb1024) (by simpa using he1024) (by simpa using hm1024)
      (by simpa using hbgt)
    refine ⟨k, ?_⟩
    simpa [wideEntryGas, hbgt] using rd.withStack (by rw [hbWord, heWord, hmWord])

def wideFastCondition (input : ByteArray) : Prop :=
  let l := lengths input
  Model.bytesToNatPadded input (96 + l.base) l.exponent = 0 ∨
    Model.bytesToNatPadded input 96 l.base ≤ 1

def wideFastGas (I : ExecutionEnv) : Nat :=
  let l := lengths I.calldata
  wideEntryGas I.calldata +
    if Model.bytesToNatPadded I.calldata (96 + l.base) l.exponent = 0 then
      wideExponentZeroGas I l.base l.exponent l.modulus
    else wideBaseSmallTotalGas I l.base l.exponent l.modulus

def wideFastAccepts (ctx : BytecodeContext) : Prop :=
  ctx.executionEnv.weiValue = ⟨0⟩ ∧
  ctx.executionEnv.calldata.size < 2 ^ 64 ∧
  validOsaka ctx.executionEnv.calldata ∧
  ¬ wordSized ctx.executionEnv.calldata ∧
  wideFastCondition ctx.executionEnv.calldata

def wideFastEnsures (ctx : BytecodeContext) (result : BytecodeResult) : Prop :=
  ExactGasPost ctx (Model.output ctx.executionEnv.calldata)
    (wideFastGas ctx.executionEnv) result

theorem wideFastModelExactGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hvalue : I.weiValue = ⟨0⟩)
    (hcalldata : I.calldata.size < 2 ^ 64)
    (hvalid : validOsaka I.calldata) (hwide : ¬ wordSized I.calldata)
    (hfast : wideFastCondition I.calldata) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (Model.output I.calldata) (wideFastGas I) := by
  let l := lengths I.calldata
  have hv := hvalid
  unfold validOsaka at hv
  rcases hv with ⟨hb, he, hm⟩
  obtain ⟨k, rd62⟩ := reachWideEntry
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hvalue hvalid hwide
  have hout := model_output_of_lengths I.calldata
    (by rfl) (by rfl) (by rfl)
  unfold wideFastCondition at hfast
  dsimp only at hfast
  by_cases hexp : Model.bytesToNatPadded I.calldata
      (96 + (lengths I.calldata).base) (lengths I.calldata).exponent = 0
  · have hret := wideExponentZeroExact (I := I) (g := g)
      (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
      hm hcalldata (by dsimp [l]; omega) hexp rd62
    dsimp [l] at hret
    have hexp' : Model.bytesToNatPadded I.calldata
        (96 + Model.bytesToNatPadded I.calldata 0 32)
        (Model.bytesToNatPadded I.calldata 32 32) = 0 := by
      simpa [lengths] using hexp
    rw [hout]
    convert hret using 1
    · rw [hexp', model_modPow_exponent_zero]
      simp [lengths, wideModulusOffset]
      rfl
    · simp [wideFastGas, hexp]
  · have hbase : Model.bytesToNatPadded I.calldata 96 (lengths I.calldata).base ≤ 1 :=
      hfast.resolve_left hexp
    have hret := wideBaseSmallExact (I := I) (g := g)
      (baseSize := l.base) (exponentSize := l.exponent) (modulusSize := l.modulus)
      hm hcalldata (by dsimp [l]; omega) hexp hbase rd62
    dsimp [l] at hret
    rw [hout]
    convert hret using 1
    simp [wideFastGas, hexp]

/-- Direct bytecode specification for all completed arbitrary-width fast paths. -/
theorem wideFastBytecodeSpec :
    BytecodeSpec runtimeBytecode wideFastAccepts wideFastEnsures := by
  simpa [wideFastEnsures] using
    (ExactGasSpec.ofRDxRet (code := runtimeBytecode)
      (accepts := wideFastAccepts)
      (output := fun ctx => Model.output ctx.executionEnv.calldata)
      (gasCost := fun ctx => wideFastGas ctx.executionEnv)
      (fun ctx hcode haccepts => by
        rcases haccepts with ⟨hvalue, hcalldata, hvalid, hwide, hfast⟩
        exact wideFastModelExactGas
          (cA := ctx.createdAccounts) (gh := ctx.genesisBlockHeader) (bl := ctx.blocks)
          (σ := ctx.accountMap) (σ₀ := ctx.originalAccountMap) (A := ctx.substate)
          (I := ctx.executionEnv) (g := ctx.gas)
          hcode hvalue hcalldata hvalid hwide hfast))

end Modexp
