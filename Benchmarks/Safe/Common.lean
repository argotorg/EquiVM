import Benchmarks.Safe.Bytecode
import Benchmarks.Safe.Selectors
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Solc
import Reasoning.SolmBody
import Reasoning.JumpDest

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

abbrev selWord (I : ExecutionEnv) : UInt256 := solcSelectorWord I

-- LIBRARY CANDIDATE: the flat ABI encoding of a void return.
theorem encodeReturnValues_nil : encodeReturnValues? [] [] = some ByteArray.empty := by
  simp [encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?, encodeABIValuesFrom?]
  rfl

-- LIBRARY CANDIDATE: recover the matched selector from a successful list dispatch.
theorem dispatchList_match {ts : List TransitionDecl} {cd : ByteArray} {t : TransitionDecl}
    (h : dispatchList ts cd = some t) : (selectorOf t == cd.extract 0 4) = true := by
  induction ts with
  | nil => simp only [dispatchList_nil, Option.noConfusion] at h
  | cons head tail ih =>
      rw [dispatchList_cons] at h
      split at h
      · cases h
        assumption
      · exact ih h

-- GENERALIZES Reasoning.Theory.reEquiv_execution: accept selector dispatch directly,
-- so contracts with receive and fallback entrypoints can use the same bridge.
theorem reEquivSelectorExecution {cfg : Config} {c : ContractDecl} {imms : Store}
    {σ σ₀ A I t args result} {g : UInt256}
    (hd : selectorDispatchMsg c I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody cfg c (initState σ σ₀ (.ofUInt256 g) A I)
      args t.body result imms)
    (hequiv : execResultsEquiv (Ξ σ σ₀ g A I) result (.abi t.returnType)) :
    runtimeRefinementFor cfg c σ σ₀ g A I imms :=
  .execution rfl (.intro hd rfl hdec rfl hbody) hequiv

-- LIBRARY CANDIDATE: a reverting selector entry covers both failed decoding and
-- a source body that reverts for every successfully decoded local store.
theorem reEquivSelectorRevert {cfg : Config} {c : ContractDecl} {imms : Store}
    {σ σ₀ A I t} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code)
    (hd : selectorDispatchMsg c I.calldata = some t)
    (hrev : RDrev code g (initState σ σ₀ g A I))
    (hbody : ∀ args, ExecTransitionBody cfg c (initState σ σ₀ g A I)
      args t.body .reverted imms) :
    runtimeRefinementFor cfg c σ σ₀ g.toUInt256 A I imms := by
  refine RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦ ?_
  cases hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata with
  | none => exact .decodingFailed hd rfl hdec hΞ
  | some args =>
      exact reEquivSelectorExecution hd hdec (hbody args) (.revert hΞ rfl)

end Benchmarks.Safe
