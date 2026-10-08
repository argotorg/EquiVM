import Benchmarks.CompoundIII.Comet.AddressGetter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def twoAddressGetterArgs (name₀ name₁ : Ident) (I : ExecutionEnv) : Store :=
  (addressGetterArgs name₀ I).insert name₁
    (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))

def TwoAddressGetterResult (code : ByteArray) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ : AccountMap) (out : ByteArray) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 68 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 36).toNat < EVM.addressModulus then
    RDret code g s0 σ out
  else RDrev code g s0

-- LIBRARY CANDIDATE: refinement connection for nonpayable getters of one address argument.
theorem twoAddressGetter_refines {t : TransitionDecl} {imms : Store}
    {σ σ₀ A I} {g : UInt256} {code out : ByteArray}
    {name₀ name₁ : Ident} {body : List Stmt} {values : List Value}
    (hcode : I.code = code) (hsz : 4 ≤ I.calldata.size)
    (hd : selectorDispatchMsg contract I.calldata = some t)
    (hp : t.params = [⟨name₀, .elem .address⟩, ⟨name₁, .elem .address⟩])
    (hb : t.body = calldataPrologue body)
    (hreturn : returnEquiv out (some values) t.returnType)
    (hsource : I.weiValue = ⟨0⟩ → I.calldata.size < 2 ^ 255 + 4 →
      (calldataWord I.calldata 4).toNat < EVM.addressModulus →
      (calldataWord I.calldata 36).toNat < EVM.addressModulus → ∃ frame,
      ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (twoAddressGetterArgs name₀ name₁ I) (calldataPrologue body)
        (.returned frame (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some values)) imms)
    (hX : TwoAddressGetterResult code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ out) :
    runtimeRefinementFor config contract σ σ₀ g A I imms := by
  have hdecode : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata =
      decodeCalldata [name₀, name₁] [.elem .address, .elem .address] I.calldata := by
    simp only [transitionSignature, hp, List.map_cons, List.map_nil]
    rfl
  by_cases hlo : 68 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · by_cases hc₁ : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · have hdargs := decodeCalldata_address_address_ok (x := name₀) (y := name₁) hlo hhi hc hc₁
          by_cases hv : I.weiValue = ⟨0⟩
          · simp only [TwoAddressGetterResult, hv, hlo, hhi, hc, hc₁, and_self, if_true] at hX
            obtain ⟨frame, hbody⟩ := hsource hv hhi hc hc₁
            apply selectorReturn_refines hcode hX hd (hdecode.trans hdargs)
            · rw [hb]
              exact hbody
            · exact hreturn
          · simp only [TwoAddressGetterResult, hv, false_and, if_false] at hX
            apply selectorRevert_refines hcode hX hd (hdecode.trans hdargs)
            rw [hb]
            exact calldataPrologue_nonpayable hv
        · simp only [TwoAddressGetterResult, hc₁, and_false, if_false] at hX
          exact selectorDecodeFailure_refines hcode hX hd
            (hdecode.trans (decodeCalldata_address_address_none_noncanon1 hlo hhi hc hc₁))
      · simp only [TwoAddressGetterResult, hc, false_and, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (decodeCalldata_address_address_none_noncanon0 hlo hhi hc))
    · simp only [TwoAddressGetterResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_address_address_none_huge (by omega)))
  · simp only [TwoAddressGetterResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_address_address_none_short hsz (by omega)))

end Benchmarks.CompoundIII.Comet
