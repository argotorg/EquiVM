import Benchmarks.Morpho.MorphoBlue.DiffTarget

/-!
Deterministic market sequences supplement the generic sampler: the latter does not seed
mapping keys with the keccak hash of the generated MarketParams tuple. Every message uses
the unchanged contract/config and is compared by the standard trace-replay harness.
Run: lake env lean --run Benchmarks/Morpho/MorphoBlue/DiffScenarios.lean
-/

open Solm Solm.DiffTest Ethereum Ethereum.EVM

namespace Benchmarks.Morpho.MorphoBlue

private def addr (n : Nat) : Value := .address (EVM.address n)
private def word (n : Nat) : Value := .int n
private def payload : Value := .bytes ⟨#[0x12, 0x34]⟩

private def params (token : Nat) (lltv := 800000000000000000) : Value :=
  .tuple [addr token, addr 0x6003, addr 0x6001, addr 0x6000, word lltv]

private def marketId (p : Value) : Value :=
  let encoded := (ABI.encodeReturnValue? Syntax.marketParamsABI p).getD .empty
  .fixedBytes ⟨31, by decide⟩ (KEC encoded).toList

private structure Scenario where
  name : String
  args : List Value
  time : Nat := 1700000000
  caller : Nat := 0x2000
  success : Bool := true

private def scenarios (token : Nat) : List Scenario :=
  let p := params token
  let q := params token 945000000000000000
  let actor := addr 0x2000
  let zero := word 0
  let wad := 10 ^ 18
  [ ⟨"enableIrm", [addr 0x6000], 1700000000, 0x2000, true⟩,
    ⟨"enableLltv", [word 800000000000000000], 1700000000, 0x2000, true⟩,
    ⟨"enableLltv", [word 945000000000000000], 1700000000, 0x2000, true⟩,
    ⟨"setFeeRecipient", [addr 0x3000], 1700000000, 0x2000, true⟩,
    ⟨"createMarket", [p], 1700000000, 0x2000, true⟩,
    ⟨"createMarket", [q], 1700000000, 0x2000, true⟩,
    ⟨"supply", [p, word (1000 * wad), zero, actor, payload], 1700000000, 0x2000, true⟩,
    ⟨"supplyCollateral", [p, word (100 * wad), actor, payload], 1700000000, 0x2000, true⟩,
    ⟨"borrow", [p, word (20 * wad), zero, actor, actor], 1700000000, 0x2000, true⟩,
    ⟨"repay", [p, word wad, zero, actor, payload], 1700000000, 0x2000, true⟩,
    ⟨"withdraw", [p, word wad, zero, actor, actor], 1700000000, 0x2000, true⟩,
    ⟨"withdrawCollateral", [p, word wad, actor, actor], 1700000000, 0x2000, true⟩,
    ⟨"setFee", [p, word 250000000000000000], 1700000000, 0x2000, true⟩,
    ⟨"accrueInterest", [p], 1700000060, 0x2000, true⟩,
    ⟨"flashLoan", [addr token, word (3 * wad), payload], 1700000060, 0x2000, true⟩,
    ⟨"setAuthorization", [addr 0x3000, .bool true], 1700000060, 0x2000, true⟩,
    ⟨"borrow", [p, word wad, zero, actor, actor], 1700000060, 0x3000, true⟩,
    ⟨"supply", [q, word (1000 * wad), zero, actor, .bytes .empty], 1700000060, 0x2000, true⟩,
    ⟨"supplyCollateral", [q, word (100 * wad), actor, .bytes .empty], 1700000060, 0x2000, true⟩,
    ⟨"borrow", [q, word (94 * wad), zero, actor, actor], 1700000060, 0x2000, true⟩,
    -- Interest makes the second position unhealthy; seize a portion, then all collateral.
    ⟨"liquidate", [q, actor, word wad, zero, payload], 1731536060, 0x2000, true⟩,
    ⟨"liquidate", [q, actor, word (99 * wad), zero, payload], 1800000000, 0x2000, true⟩,
    ⟨"position", [marketId p, actor], 1731536060, 0x2000, true⟩,
    ⟨"market", [marketId p], 1731536060, 0x2000, true⟩,
    ⟨"idToMarketParams", [marketId p], 1731536060, 0x2000, true⟩,
    ⟨"extSloads", [.array [marketId p, .fixedBytes ⟨31, by decide⟩ (wordBytes 0).toList]],
      1731536060, 0x2000, true⟩,
    ⟨"setOwner", [addr 0x3000], 1731536060, 0x2000, true⟩ ]

private def signatureCalldata (v : Nat) (usedNonce := 0) (deadline := 1700000001)
    (authorized := 1) : ByteArray :=
  (⟨#[0x80, 0x69, 0x21, 0x8f]⟩ : ByteArray) ++ wordBytes 0x2000 ++ wordBytes 0x3000 ++
    wordBytes authorized ++ wordBytes usedNonce ++ wordBytes deadline ++ wordBytes v ++
    wordBytes 0 ++ wordBytes 0

-- These stop before ecrecover. In particular, static dirty-v cases reach SSTORE before the
-- compiler's late uint8 validation, which an eagerly decoded typed transition cannot model.
private def signatureCases : List (String × ByteArray × Bool × String) :=
  [ ("dirty v / static", signatureCalldata 256, false, "static halt"),
    ("dirty v / mutable", signatureCalldata 256, true, "revert"),
    ("dirty v 511 / static", signatureCalldata 511, false, "static halt"),
    ("dirty v 511 / mutable", signatureCalldata 511, true, "revert"),
    ("canonical v / static", signatureCalldata 27, false, "static halt"),
    ("wrong nonce / static", signatureCalldata 256 1, false, "static halt"),
    ("wrong nonce / mutable", signatureCalldata 256 1, true, "revert"),
    ("expired / static", signatureCalldata 256 0 1699999999, false, "revert"),
    ("dirty authorization bool", signatureCalldata 256 0 1700000001 2, false, "revert"),
    ("short signature", (signatureCalldata 256).extract 0 259, false, "revert") ]

def runScenarios : IO Bool := do
  let (t, _) := diffTarget.resolveRuntime (Rng.ofSeed 2026)
  let mut summary : Summary := {}
  let mut allExpected := true
  for token in [0x6002, 0x6003] do
    let (verdict, world) := runConstructor t morphoCreationBytecode [addr 0x2000] 0
      (EVM.address 0x2000)
    summary := summary.add {
      target := "Morpho scenarios", transition := "constructor"
      label := s!"token {token}", verdict, calldata := .empty }
    let mut σ := world.getD t.world
    for step in scenarios token do
      let some tr := t.contract.transitions.find? (·.name == step.name)
        | throw (IO.userError s!"missing transition {step.name}")
      let selector := (KEC (transitionSigStr tr).toUTF8).extract 0 4
      let some cd := ABI.encodeCallWithSelector? selector (tr.params.map (·.ty)) step.args
        | throw (IO.userError s!"cannot encode {step.name}")
      let c : Case := {
        label := s!"token {token}: {step.name}", σ
        I := t.env t.runtime (EVM.address step.caller) 0 cd true step.time 19000000 }
      let run := runCase t c
      IO.println s!"  {c.label}: {run.verdict.describe}"
      if run.verdict.isSuccess != step.success then
        allExpected := false
      summary := summary.add {
        target := "Morpho scenarios", transition := transitionSigStr tr
        label := c.label, verdict := run.verdict, calldata := cd }
      if run.verdict.isSuccess then
        σ := run.postState.getD σ
  for (label, cd, perm, expected) in signatureCases do
    let c : Case := {
      label, σ := t.world
      I := t.env t.runtime (EVM.address 0x2000) 0 cd perm 1700000000 19000000 }
    let run := runCase t c
    IO.println s!"  signature {label}: {run.verdict.describe}"
    let matchesExpected := match run.verdict with
      | .agree actual => actual == expected
      | _ => false
    if !matchesExpected then
      allExpected := false
    summary := summary.add {
      target := "Morpho scenarios", transition := "setAuthorizationWithSig guards"
      label, verdict := run.verdict, calldata := cd }
  IO.println s!"Morpho scenarios: {summary.describe}"
  IO.println s!"  successful/cases: {summary.coverage}"
  printFailures summary
  return allExpected && summary.disagree == 0 && summary.stuck == 0

end Benchmarks.Morpho.MorphoBlue

def main : IO UInt32 := do
  return if ← Benchmarks.Morpho.MorphoBlue.runScenarios then 0 else 1
