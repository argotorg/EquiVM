import Reasoning.ReachExact

/-!
# Caller-observable bytecode specifications

This is the Solm-independent interface for precompile-like bytecode.  It observes execution at the
message-call boundary rather than exposing the raw exception taxonomy of `Ξ`.

For pure callees, the relevant projection of `Θ` consists of returned gas, the success flag, and
return data.  Every exceptional `Ξ` result has the same projection: zero returned gas, failure, and
empty return data.  In particular, OOG and `INVALID` are deliberately indistinguishable here.
`REVERT` remains distinguishable because it returns unused gas and its payload.
-/

open Ethereum Ethereum.EVM

namespace Reasoning.Reach

open Reasoning.Theory

/-- The raw result of executing a bytecode frame with `Ξ`.  This remains internal proof data; the
public specification uses `BytecodeResult`, the caller-observable projection. -/
abbrev RawBytecodeResult :=
  Except ExecutionException
    (ExecutionResult
      (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate))

/-- The part of a pure callee's result observable through `Θ`. -/
structure BytecodeResult where
  gasRemaining : UInt256
  success : Bool
  output : ByteArray
deriving DecidableEq

/-- The common `Θ` observation of every exceptional callee halt. -/
def BytecodeResult.failure : BytecodeResult where
  gasRemaining := ⟨0⟩
  success := false
  output := ByteArray.empty

/-- Pure-call observation with an exact remaining-gas value.  The success bit follows `Θ`'s
account-map sentinel convention; on ordinary reachable EVM worlds this is `true`. -/
def BytecodeResult.returned (accountMap : AccountMap) (gasRemaining : UInt256)
    (output : ByteArray) : BytecodeResult where
  gasRemaining := gasRemaining
  success := !(accountMap == (∅ : AccountMap))
  output := output

/-- Collapse a raw `Ξ` result to the gas/status/output projection used by `Θ`. -/
def observeXi : RawBytecodeResult → BytecodeResult
  | .error _ => .failure
  | .ok (.revert gas output) => ⟨gas, false, output⟩
  | .ok (.success (_, accountMap, gas, _) output) =>
      ⟨gas, !(accountMap == (∅ : AccountMap)), output⟩

/-- Project the same three components directly from a `Θ` result. -/
def observeTheta :
    (Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × Bool ×
      ByteArray) → BytecodeResult
  | (_, _, gas, _, success, output) => ⟨gas, success, output⟩

/-- The bytecode-result finalization performed by the `.Code` branch of `Θ`. -/
def thetaCodeResult
    (σ : AccountMap) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (A : Substate) (xi : RawBytecodeResult) :
    Batteries.RBSet AccountAddress compare × AccountMap × UInt256 × Substate × Bool × ByteArray :=
  let (createdAccounts', σ'', gas, A'', output) :=
    match xi with
    | .error _ => (createdAccounts, ∅, ⟨0⟩, A, ByteArray.empty)
    | .ok (.revert gas output) => (createdAccounts, ∅, gas, A, output)
    | .ok (.success (createdAccounts', σ'', gas, A'') output) =>
        (createdAccounts', σ'', gas, A'', output)
  (createdAccounts',
    if σ'' == (∅ : AccountMap) then σ else σ'',
    gas,
    if σ'' == (∅ : AccountMap) then A else A'',
    if σ'' == (∅ : AccountMap) then false else true,
    output)

/-- Unfold the `.Code` branch of `Θ` into call entry, raw `Ξ`, and `thetaCodeResult`. -/
theorem Theta_code_eq_thetaCodeResult
    (blobVersionedHashes : List ByteArray)
    (createdAccounts : Batteries.RBSet AccountAddress compare)
    (genesisBlockHeader : BlockHeader) (blocks : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate)
    (s o r : AccountAddress) (code : ByteArray) (g p v v' : UInt256)
    (d : ByteArray) (e : Fin 1025) (H : BlockHeader) (w : Bool) :
    let σ'₁ :=
      match σ.find? r with
      | none => if v != UInt256.ofNat 0 then
          σ.insert r { (default : Account) with balance := v }
        else σ
      | some acc => σ.insert r { acc with balance := acc.balance + v }
    let σ₁ :=
      match σ'₁.find? s with
      | none => σ'₁
      | some acc => σ'₁.insert s { acc with balance := acc.balance - v }
    let I : ExecutionEnv := {
      codeOwner := r
      sender := o
      gasPrice := p.toNat
      calldata := d
      source := s
      weiValue := v'
      depth := e
      perm := w
      code := code
      header := H
      blobVersionedHashes := blobVersionedHashes
    }
    Θ blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A
      s o r (.Code code) g p v v' d e H w =
      thetaCodeResult σ createdAccounts A
        (Ξ createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I) := by
  simp only
  unfold Θ thetaCodeResult
  rfl

/-- `observeXi` is exactly the projection obtained after the `.Code` branch of `Θ` finalizes a
raw result.  This is the point at which all exception constructors become indistinguishable. -/
theorem observeTheta_thetaCodeResult
    (σ : AccountMap) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (A : Substate) (xi : RawBytecodeResult) :
    observeTheta (thetaCodeResult σ createdAccounts A xi) = observeXi xi := by
  have hempty : ((∅ : AccountMap) == (∅ : AccountMap)) = true := by native_decide
  cases xi with
  | error exception =>
      simp [thetaCodeResult, observeTheta, observeXi, BytecodeResult.failure, hempty]
  | ok result => cases result <;> simp [thetaCodeResult, observeTheta, observeXi, hempty]

/-- Inputs to a direct bytecode-frame proof.  `result` immediately quotients the raw `Ξ` result by
the observation made at `Θ`; exception constructors are therefore not part of public specs. -/
structure BytecodeContext where
  createdAccounts : Batteries.RBSet AccountAddress compare
  genesisBlockHeader : BlockHeader
  blocks : ProcessedBlocks
  accountMap : AccountMap
  originalAccountMap : AccountMap
  gas : Sat256
  substate : Substate
  executionEnv : ExecutionEnv

def BytecodeContext.initialState (ctx : BytecodeContext) : State :=
  initState ctx.createdAccounts ctx.genesisBlockHeader ctx.blocks ctx.accountMap
    ctx.originalAccountMap ctx.gas ctx.substate ctx.executionEnv

def BytecodeContext.rawResult (ctx : BytecodeContext) : RawBytecodeResult :=
  Ξ ctx.createdAccounts ctx.genesisBlockHeader ctx.blocks ctx.accountMap
    ctx.originalAccountMap ctx.gas.toUInt256 ctx.substate ctx.executionEnv

/-- Execute and retain exactly the caller-visible `Θ` projection. -/
def BytecodeContext.result (ctx : BytecodeContext) : BytecodeResult :=
  observeXi ctx.rawResult

/-- A general relational property of the caller-observable behavior of deployed bytecode. -/
structure BytecodeSpec
    (code : ByteArray)
    (accepts : BytecodeContext → Prop)
    (ensures : BytecodeContext → BytecodeResult → Prop) : Prop where
  run : ∀ ctx : BytecodeContext,
    ctx.executionEnv.code = code → accepts ctx → ensures ctx ctx.result

theorem BytecodeSpec.mono
    {code : ByteArray} {accepts : BytecodeContext → Prop}
    {P Q : BytecodeContext → BytecodeResult → Prop}
    (spec : BytecodeSpec code accepts P)
    (h : ∀ ctx result, accepts ctx → P ctx result → Q ctx result) :
    BytecodeSpec code accepts Q := by
  constructor
  intro ctx hcode haccepts
  exact h ctx ctx.result haccepts (spec.run ctx hcode haccepts)

/-- Exact caller observation for a successful pure computation, including its precise OOG
boundary. -/
def ExactGasPost
    (ctx : BytecodeContext) (output : ByteArray) (gasCost : Nat)
    (result : BytecodeResult) : Prop :=
  (ctx.gas.toNat < gasCost → result = .failure) ∧
  (gasCost ≤ ctx.gas.toNat →
    result = .returned ctx.accountMap (ctx.gas.subNat gasCost).toUInt256 output)

abbrev ExactGasSpec
    (code : ByteArray) (accepts : BytecodeContext → Prop)
    (output : BytecodeContext → ByteArray) (gasCost : BytecodeContext → Nat) : Prop :=
  BytecodeSpec code accepts
    (fun ctx result => ExactGasPost ctx (output ctx) (gasCost ctx) result)

/-- Precompile-like behavior at `Θ`: valid inputs have a pure output and exact gas boundary;
invalid inputs have the unique exceptional-call observation.  There is no public exception kind or
invalid-path threshold because neither is observable here. -/
def PrecompilePost
    (ctx : BytecodeContext) (valid : Prop) (output : ByteArray) (gasCost : Nat)
    (result : BytecodeResult) : Prop :=
  (valid → ExactGasPost ctx output gasCost result) ∧
  (¬ valid → result = .failure)

abbrev PrecompileSpec
    (code : ByteArray) (accepts valid : BytecodeContext → Prop)
    (output : BytecodeContext → ByteArray) (gasCost : BytecodeContext → Nat) : Prop :=
  BytecodeSpec code accepts
    (fun ctx result => PrecompilePost ctx (valid ctx)
      (output ctx) (gasCost ctx) result)

/-- Close an exact successful trace into its caller-observable bytecode specification. -/
theorem ExactGasSpec.ofRDxRet
    {code : ByteArray} {accepts : BytecodeContext → Prop}
    {output : BytecodeContext → ByteArray} {gasCost : BytecodeContext → Nat}
    (trace : ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = code → accepts ctx →
      RDxRet code ctx.gas ctx.initialState (ctx.createdAccounts, ctx.accountMap)
        (output ctx) (gasCost ctx)) :
    ExactGasSpec code accepts output gasCost := by
  constructor
  intro ctx hcode haccepts
  have hresult := (trace ctx hcode haccepts).xiResult hcode
  constructor
  · intro hlow
    have hxi := hresult.1 hlow
    simp [BytecodeContext.result, BytecodeContext.rawResult, observeXi, hxi,
      BytecodeResult.failure]
  · intro henough
    obtain ⟨A', hxi⟩ := hresult.2 henough
    simp [BytecodeContext.result, BytecodeContext.rawResult, observeXi, hxi,
      BytecodeResult.returned]

/-- Join valid successful traces and invalid exceptional traces.  The exception and the cost of
reaching it are existential proof details: `Θ` erases both, so they do not occur in the resulting
specification. -/
theorem PrecompileSpec.ofRDxRetOrErr
    {code : ByteArray} {accepts valid : BytecodeContext → Prop}
    {output : BytecodeContext → ByteArray} {gasCost : BytecodeContext → Nat}
    (successTrace : ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = code → accepts ctx → valid ctx →
      RDxRet code ctx.gas ctx.initialState (ctx.createdAccounts, ctx.accountMap)
        (output ctx) (gasCost ctx))
    (errorTrace : ∀ ctx : BytecodeContext,
      ctx.executionEnv.code = code → accepts ctx → ¬ valid ctx →
      ∃ exception errorThreshold,
        RDxErr code ctx.gas ctx.initialState exception errorThreshold) :
    PrecompileSpec code accepts valid output gasCost := by
  constructor
  intro ctx hcode haccepts
  constructor
  · intro hvalid
    have hresult := (successTrace ctx hcode haccepts hvalid).xiResult hcode
    constructor
    · intro hlow
      have hxi := hresult.1 hlow
      simp [BytecodeContext.result, BytecodeContext.rawResult, observeXi, hxi,
        BytecodeResult.failure]
    · intro henough
      obtain ⟨A', hxi⟩ := hresult.2 henough
      simp [BytecodeContext.result, BytecodeContext.rawResult, observeXi, hxi,
        BytecodeResult.returned]
  · intro hinvalid
    obtain ⟨exception, errorThreshold, htrace⟩ := errorTrace ctx hcode haccepts hinvalid
    have hresult := htrace.xiResult hcode
    by_cases hlow : ctx.gas.toNat < errorThreshold
    · have hxi := hresult.1 hlow
      simp [BytecodeContext.result, BytecodeContext.rawResult, observeXi, hxi,
        BytecodeResult.failure]
    · have hxi := hresult.2 (Nat.le_of_not_gt hlow)
      simp [BytecodeContext.result, BytecodeContext.rawResult, observeXi, hxi,
        BytecodeResult.failure]

theorem PrecompileSpec.runValid
    {code : ByteArray} {accepts valid : BytecodeContext → Prop}
    {output : BytecodeContext → ByteArray} {gasCost : BytecodeContext → Nat}
    (spec : PrecompileSpec code accepts valid output gasCost)
    (ctx : BytecodeContext) (hcode : ctx.executionEnv.code = code)
    (haccepts : accepts ctx) (hvalid : valid ctx) :
    ExactGasPost ctx (output ctx) (gasCost ctx) ctx.result :=
  (spec.run ctx hcode haccepts).1 hvalid

theorem PrecompileSpec.runInvalid
    {code : ByteArray} {accepts valid : BytecodeContext → Prop}
    {output : BytecodeContext → ByteArray} {gasCost : BytecodeContext → Nat}
    (spec : PrecompileSpec code accepts valid output gasCost)
    (ctx : BytecodeContext) (hcode : ctx.executionEnv.code = code)
    (haccepts : accepts ctx) (hinvalid : ¬ valid ctx) :
    ctx.result = .failure :=
  (spec.run ctx hcode haccepts).2 hinvalid

end Reasoning.Reach
