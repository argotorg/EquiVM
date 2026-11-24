import Benchmarks.CompoundIII.Comet.GetterCommon

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES guardedGetter_refines with an additional source-level success condition.
def CheckedGetterResult (fork : Ethereum.Fork) (P : Prop) [Decidable P] (code : ByteArray) (ee : ExecutionEnv)
    (g : Sat256) (s0 : State) (σ : AccountMap) (out : ByteArray) : Prop :=
  if ee.weiValue = ⟨0⟩ ∧ ee.calldata.size < 2^255 + 4 ∧ P then RDret fork code g s0 σ out
  else RDrev fork code g s0

theorem checkedGetter_refines {cfg : Config} {C : ContractDecl} {t : TransitionDecl}
    {imms : Store} {σ σ₀ A I} {g : UInt256} {code out : ByteArray}
    {body : List Stmt} {values : List Value} {P : Prop} [Decidable P]
    (hcode : I.code = code) (hsz : 4 ≤ I.calldata.size)
    (hempty : cfg.externalABI.decodeCalldata? [] [] I.calldata = some (∅ : Store))
    (hd : selectorDispatchMsg C I.calldata = some t) (hp : t.params = [])
    (hb : t.body = calldataPrologue body)
    (hreturn : P → returnEquiv out (some values) t.returnType)
    (hsource : I.weiValue = ⟨0⟩ → I.calldata.size < 2^255 + 4 → P → ∃ frame,
      ExecTransitionBody fork cfg C (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ t.body
        (.returned frame (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some values)) imms)
    (hsourceRevert : I.weiValue = ⟨0⟩ → I.calldata.size < 2^255 + 4 → ¬ P →
      ExecTransitionBody fork cfg C (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ t.body .reverted imms)
    (hX : CheckedGetterResult fork P code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ out) :
    runtimeRefinementFor fork cfg C σ σ₀ g A I imms := by
  have hdec : cfg.externalABI.decodeCalldata? (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some (∅ : Store) := by
    simpa only [transitionSignature, hp, List.map_nil] using hempty
  by_cases hv : I.weiValue = ⟨0⟩
  · by_cases hhi : I.calldata.size < 2^255 + 4
    · by_cases hP : P
      · simp only [CheckedGetterResult, hv, hhi, hP, and_self, if_true] at hX
        obtain ⟨frame, hs⟩ := hsource hv hhi hP
        exact selectorReturn_refines hcode hX hd hdec hs (hreturn hP)
      · simp only [CheckedGetterResult, hP, and_false, if_false] at hX
        exact selectorRevert_refines hcode hX hd hdec (hsourceRevert hv hhi hP)
    · simp only [CheckedGetterResult, hhi, false_and, and_false, if_false] at hX
      apply selectorRevert_refines hcode hX hd hdec
      rw [hb]
      exact calldataPrologue_huge hv hhi
  · simp only [CheckedGetterResult, hv, false_and, if_false] at hX
    apply selectorRevert_refines hcode hX hd hdec
    rw [hb]
    exact calldataPrologue_nonpayable hv

end Benchmarks.CompoundIII.Comet
