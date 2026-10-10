import Benchmarks.CompoundIII.Comet.AbiRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def uintFunctionArgs (name : Ident) (I : ExecutionEnv) : Store :=
  (∅ : Store).insert name (.int (calldataWord I.calldata 4).toNat)

def UintFunctionResult (P : Prop) [Decidable P]
    (code : ByteArray) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ : AccountMap) (out : ByteArray) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧ P then
    RDret code g s0 σ out
  else RDrev code g s0

-- LIBRARY CANDIDATE: refinement for one-word functions whose body has a success condition.
theorem uintFunction_refines {t : TransitionDecl} {imms : Store}
    {σ σ₀ A I} {g : UInt256} {code out : ByteArray} {P : Prop} [Decidable P]
    {name : Ident} {body : List Stmt} {value : Value}
    (hcode : I.code = code)
    (hd : selectorDispatchMsg contract I.calldata = some t)
    (hp : t.params = [⟨name, .elem (.int (.uint ⟨256, by decide⟩))⟩])
    (hb : t.body = calldataPrologue body)
    (hreturn : P → returnEquiv out (some [value]) t.returnType)
    (hsource : I.weiValue = ⟨0⟩ → I.calldata.size < 2 ^ 255 + 4 → P → ∃ frame,
      ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (uintFunctionArgs name I) (calldataPrologue body)
        (.returned frame (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [value])) imms)
    (hsourceRevert : I.weiValue = ⟨0⟩ → I.calldata.size < 2 ^ 255 + 4 → ¬ P →
      ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (uintFunctionArgs name I) (calldataPrologue body) .reverted imms)
    (hX : UintFunctionResult P code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ out) :
    runtimeRefinementFor config contract σ σ₀ g A I imms := by
  have hdecode : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata =
      decodeCalldata [name] [abiUInt256] I.calldata := by
    simp only [transitionSignature, hp, List.map_cons, List.map_nil]
    exact solc0815_decodeCalldata_scalar_eq (by decide)
  by_cases hlo : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · have hdargs := decodeCalldata_uint256_ok (x := name) hlo hhi
      by_cases hv : I.weiValue = ⟨0⟩
      · by_cases hP : P
        · simp only [UintFunctionResult, hv, hlo, hhi, hP, and_self, if_true] at hX
          obtain ⟨frame, hbody⟩ := hsource hv hhi hP
          apply selectorReturn_refines hcode hX hd (hdecode.trans hdargs)
          · rw [hb]; exact hbody
          · exact hreturn hP
        · simp only [UintFunctionResult, hP, and_false, if_false] at hX
          apply selectorRevert_refines hcode hX hd (hdecode.trans hdargs)
          rw [hb]
          exact hsourceRevert hv hhi hP
      · simp only [UintFunctionResult, hv, false_and, if_false] at hX
        apply selectorRevert_refines hcode hX hd (hdecode.trans hdargs)
        rw [hb]
        exact calldataPrologue_nonpayable hv
    · simp only [UintFunctionResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_uint256_none_huge (by omega)))
  · simp only [UintFunctionResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_uint256_none_short (by omega)))

end Benchmarks.CompoundIII.Comet
