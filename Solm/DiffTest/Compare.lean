import Solm.Interp
import Solm.Refine

/-!
# Executable result comparison

`execResultsEquiv`, `ctorResultEquiv`, and the four cases of `runtimeRefinementFor`, as a
decision procedure on one EVM result and one interpreter outcome.  A `Verdict.agree` means the
pair is related by the corresponding constructor; `disagree` names what differs.  Out-of-gas on
the EVM side and out-of-fuel on the specification side are inconclusive, never agreement.
-/

namespace Solm.DiffTest

open ABI Ethereum Ethereum.EVM Solm.Interp

abbrev EVMResult := Except ExecutionException (ExecutionResult (AccountMap × UInt256 × Substate))

inductive Verdict where
  | agree (how : String)
  /-- `runtimeRefinementFor.outOfGas`: the relation imposes nothing -/
  | evmOutOfGas
  /-- a hypothesis of the relation fails for the case (no `selfDeployment` encoding): it imposes nothing -/
  | inapplicable (why : String)
  | specOutOfFuel
  /-- the executable semantics does not materialise the case (`Outcome.unsupported`) -/
  | unsupported (why : String)
  | specStuck (why : String)
  | disagree (why : String)
  deriving Repr

def Verdict.isAgree : Verdict → Bool
  | .agree _ => true
  | _ => false

def Verdict.isFailure : Verdict → Bool
  | .disagree _ | .specStuck _ => true
  | _ => false

def Verdict.describe : Verdict → String
  | .agree how => s!"agree ({how})"
  | .evmOutOfGas => "inconclusive: EVM out of gas"
  | .inapplicable why => s!"inapplicable: {why}"
  | .specOutOfFuel => "inconclusive: spec out of fuel"
  | .unsupported why => s!"inconclusive: {why} (not materialised by the executable semantics)"
  | .specStuck why => s!"spec stuck: {why}"
  | .disagree why => s!"DISAGREE: {why}"

def describeEvm : EVMResult → String
  | .error e => s!"exception {repr e}"
  | .ok (.success _ o) => s!"success, {o.size} return bytes"
  | .ok (.revert _ o) => s!"revert, {o.size} bytes"

/-- Differences between two account maps, for failure reports. -/
def describeAccountDiff (expected actual : AccountMap) : String := Id.run do
  let mut notes : Array String := #[]
  let addrs := (expected.toList.map Prod.fst ++ actual.toList.map Prod.fst).eraseDups
  for a in addrs do
    match expected.get? a, actual.get? a with
    | none, some _ => notes := notes.push s!"account {a.val} only in the EVM result"
    | some _, none => notes := notes.push s!"account {a.val} only in the spec result"
    | some x, some y =>
        if x.balance != y.balance then notes := notes.push s!"balance of {a.val}: EVM {x.balance.toNat}, spec {y.balance.toNat}"
        if x.nonce != y.nonce then notes := notes.push s!"nonce of {a.val}: EVM {x.nonce.toNat}, spec {y.nonce.toNat}"
        if x.code != y.code then notes := notes.push s!"code of {a.val} differs"
        if x.storage != y.storage then
          let slots := (x.storage.toList.map Prod.fst ++ y.storage.toList.map Prod.fst).eraseDups
          for s in slots do
            let v1 := x.storage.get? s |>.getD ⟨0⟩
            let v2 := y.storage.get? s |>.getD ⟨0⟩
            if v1 != v2 then
              notes := notes.push s!"slot 0x{String.ofList (Nat.toDigits 16 s.toNat)} of {a.val}: EVM {v1.toNat}, spec {v2.toNat}"
        if x.tstorage != y.tstorage then notes := notes.push s!"transient storage of {a.val} differs"
    | none, none => pure ()
  if notes.isEmpty then "account maps differ (no visible difference found)" else
    String.intercalate "; " notes.toList

/-- `returnDataEquiv`: the bytes the specification's result must have been encoded to. -/
def expectedReturnBytes (rc : ReturnConvention) (ret : Option (List Value)) : Except String ByteArray :=
  match rc, ret with
  | .abi t, some vs =>                                                                 -- returnEquiv.returned
      match encodeReturnValues? t vs with
      | some o => pure o
      | none => throw "the returned values do not ABI-encode at the declared return types"
  | .abi t, none =>                                                                    -- returnEquiv.fallthrough
      match t.mapM defaultAbiValue with
      | none => throw "fallthrough with a return type that has no default value"
      | some dvs =>
          match encodeReturnValues? t dvs with
          | some o => pure o
          | none => throw "the default return values do not ABI-encode"
  | .rawBytes, some [.bytes o] => pure o                                               -- returnDataEquiv.rawBytes
  | .rawBytes, none => pure ByteArray.empty                                            -- returnDataEquiv.rawBytesVoid
  | .rawBytes, _ => throw "a raw-bytes return convention with a non-bytes result"

/-- `execResultsEquiv evmRes r rc`, decided. -/
def compareExecution (evmRes : EVMResult) (r : ExecResult) (rc : ReturnConvention) : Verdict :=
  match r, evmRes with
  | .returned _ st ret, .ok (.success (σ', _, _) o) =>                                   -- execResultsEquiv.success
      match expectedReturnBytes rc ret with
      | .error why => .disagree why
      | .ok expected =>
          if o != expected then
            .disagree s!"return bytes differ: EVM {Ethereum.toHex o}, spec {Ethereum.toHex expected}"
          else if σ' != st.accountMap then
            .disagree (describeAccountDiff σ' st.accountMap)
          else .agree "success"
  | .reverted, .ok (.revert _ _) => .agree "revert"                                      -- execResultsEquiv.revert
  | .reverted, .error .InvalidInstruction => .agree "invalid"                            -- execResultsEquiv.invalidHalt
  | .staticViolation, .error .StaticModeViolation => .agree "static halt"                -- execResultsEquiv.staticHalt
  | .returned .., e => .disagree s!"spec returned, EVM {describeEvm e}"
  | .reverted, e => .disagree s!"spec reverted, EVM {describeEvm e}"
  | .staticViolation, e => .disagree s!"spec static violation, EVM {describeEvm e}"
  | .ok .., _ | .break .., _ | .continue .., _ => .disagree "spec body ended without a function result"

/-- `runtimeRefinementFor`, decided for one run of each side. -/
def compareRuntime (evmRes : EVMResult) (spec : DispatchOutcome) : Verdict :=
  match evmRes with
  | .error .OutOfGass | .error .OutOfFuel => .evmOutOfGas                               -- runtimeRefinementFor.outOfGas
  | _ =>
    match spec with
    | .noDispatch =>                                                                     -- runtimeRefinementFor.noDispatch
        match evmRes with
        | .ok (.revert _ _) => .agree "no dispatch, revert"
        | e => .disagree s!"spec dispatches nothing, EVM {describeEvm e}"
    | .decodingFailed =>                                                                 -- runtimeRefinementFor.decodingFailed
        match evmRes with
        | .ok (.revert _ _) => .agree "decoding failed, revert"
        | e => .disagree s!"spec calldata does not decode, EVM {describeEvm e}"
    | .malformed why => .specStuck why
    | .ran .outOfFuel _ => .specOutOfFuel
    | .ran (.stuck why) _ => .specStuck why
    | .ran (.unsupported why) _ => .unsupported why
    | .ran (.result r) rc => compareExecution evmRes r rc                                -- runtimeRefinementFor.execution

/-- `ctorResultEquiv`, decided. -/
def compareConstructor (evmRes : EVMResult) (spec : Outcome) (runtimeCodeOf : Store → ByteArray) : Verdict :=
  match evmRes with
  | .error .OutOfGass | .error .OutOfFuel => .evmOutOfGas
  | _ =>
    match spec with
    | .outOfFuel => .specOutOfFuel
    | .stuck why => .specStuck why
    | .unsupported why => .unsupported why
    | .result r =>
      match r, evmRes with
      | .returned frame st ret, .ok (.success (σ', _, _) o) =>                           -- ctorResultEquiv.success / successVoidReturn
          if ret != none && ret != some [] then .disagree "constructor returned values"
          else if o != runtimeCodeOf frame.immutables then .disagree "deployed code differs from runtimeCodeOf the final immutables"
          else if σ' != st.accountMap then .disagree (describeAccountDiff σ' st.accountMap)
          else .agree "deployed"
      | .reverted, .ok (.revert _ _) => .agree "revert"                                  -- ctorResultEquiv.revert
      | .reverted, .error .InvalidInstruction => .agree "invalid"                        -- ctorResultEquiv.invalidHalt
      | .returned .., e => .disagree s!"constructor returned, EVM {describeEvm e}"
      | .reverted, e => .disagree s!"constructor reverted, EVM {describeEvm e}"
      | .staticViolation, e => .disagree s!"constructor static violation, EVM {describeEvm e}"
      | _, _ => .disagree "constructor body ended without a function result"

instance : BEq (Option (List Value)) where
  beq a b := match a, b with
    | none, none => true
    | some [], some [] => true
    | _, _ => false

end Solm.DiffTest
