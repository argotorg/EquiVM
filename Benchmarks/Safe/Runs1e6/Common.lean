import Benchmarks.Safe.Runs1e6.Bytecode
import Benchmarks.Safe.Runs1e6.Selectors
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Solc
import Reasoning.SteleBody
import Reasoning.JumpDest

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.Runs1e6

theorem safeRoundMaskLiteral :
    UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904 =
      UInt256.lnot (UInt256.ofNat 31) := rfl

theorem safeAddressComplementLiteral :
    UInt256.ofNat 115792089237316195423570985007226406215939081747436879206741300988257197096960 =
      UInt256.lnot solcAddrMask := rfl

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
  | nil => cases h
  | cons head tail ih =>
      rw [dispatchList_cons] at h
      split at h
      · cases h
        assumption
      · exact ih h

-- LIBRARY CANDIDATE: recover the calldata length and EVM selector word from source dispatch.
theorem selectorDispatchFacts {c : ContractDecl} {t : TransitionDecl} {I : ExecutionEnv}
    (c0 c1 c2 c3 : UInt8) (w : UInt256)
    (hd : selectorDispatchMsg c I.calldata = some t)
    (hbytes : (KEC (String.toByteArray (transitionSigStr t))).extract 0 4 =
      ⟨#[c0, c1, c2, c3]⟩)
    (hnat : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = w.toNat) :
    4 ≤ I.calldata.size ∧ solcSelectorWord I = w := by
  have hm := dispatchList_match
    ((selectorDispatchMsg_eq_dispatchList c I.calldata).symm.trans hd)
  change ((KEC (String.toByteArray (transitionSigStr t))).extract 0 4 ==
    I.calldata.extract 0 4) = true at hm
  rw [hbytes] at hm
  have hlong := calldata_size_ge_of_selIs I _ (by rfl) hm
  exact ⟨hlong, solcSelectorWord_eq_of_beq I hlong c0 c1 c2 c3 w hnat hm⟩

-- GENERALIZES Reasoning.Theory.reEquiv_execution: accept selector dispatch directly,
-- so contracts with receive and fallback entrypoints can use the same bridge.
theorem reEquivSelectorExecution {cfg : Config} {c : ContractDecl} {imms : Store}
    {σ σ₀ A I t args result} {g : UInt256}
    (hd : selectorDispatchMsg c I.calldata = some t)
    (hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some args)
    (hbody : ExecTransitionBody fork cfg c (initState σ σ₀ (.ofUInt256 g) A I)
      args t.body result imms)
    (hequiv : execResultsEquiv (Ξ fork σ σ₀ g A I) result (.abi t.returnType)) :
    runtimeRefinementFor fork cfg c σ σ₀ g A I imms :=
  .execution rfl (.intro hd rfl hdec rfl hbody) hequiv

-- LIBRARY CANDIDATE: a reverting selector entry covers both failed decoding and
-- a source body that reverts for every successfully decoded local store.
theorem reEquivSelectorRevert {cfg : Config} {c : ContractDecl} {imms : Store}
    {σ σ₀ A I t} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code)
    (hd : selectorDispatchMsg c I.calldata = some t)
    (hrev : RDrev fork code g (initState σ σ₀ g A I))
    (hbody : ∀ args, ExecTransitionBody fork cfg c (initState σ σ₀ g A I)
      args t.body .reverted imms) :
    runtimeRefinementFor fork cfg c σ σ₀ g.toUInt256 A I imms := by
  refine RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦ ?_
  cases hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata with
  | none => exact .execution hΞ (.decodingFailed hd hdec) (.decodingFailed rfl rfl)
  | some args =>
      exact reEquivSelectorExecution hd hdec (hbody args) (.revert hΞ rfl)

-- GENERALIZES RDrev.reEquivDecodingFailed to contracts with receive/fallback entrypoints.
theorem reEquivSelectorDecodingFailed {cfg : Config} {c : ContractDecl} {imms : Store}
    {σ σ₀ A I t} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code)
    (hd : selectorDispatchMsg c I.calldata = some t)
    (hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = none)
    (hrev : RDrev fork code g (initState σ σ₀ g A I)) :
    runtimeRefinementFor fork cfg c σ σ₀ g.toUInt256 A I imms :=
  RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
    .execution hΞ (.decodingFailed hd hdec) (.decodingFailed rfl rfl)

-- GENERALIZES RDret.reEquivElim to a final account map changed by storage writes.
theorem reEquivReturnElim {imms : Store} {cfg c σ σ₀ σ' A I} {g : Sat256}
    {code out : ByteArray}
    (hcode : I.code = code)
    (h : RDret fork code g (initState σ σ₀ g A I) σ' out)
    (next : ∀ (g' : UInt256) (A' : Substate),
      Ξ fork σ σ₀ g.toUInt256 A I = .ok (.success (σ', g', A') out) →
        runtimeRefinementFor fork cfg c σ σ₀ g.toUInt256 A I imms) :
    runtimeRefinementFor fork cfg c σ σ₀ g.toUInt256 A I imms := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    rw [hacc] at hxi
    exact next _ _ hxi

end Benchmarks.Safe.Runs1e6
