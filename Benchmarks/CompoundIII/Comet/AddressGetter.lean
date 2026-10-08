import Benchmarks.CompoundIII.Comet.AbiRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def addressGetterArgs (name : Ident) (I : ExecutionEnv) : Store :=
  (∅ : Store).insert name (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))

def AddressGetterResult (code : ByteArray) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ : AccountMap) (out : ByteArray) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus then
    RDret code g s0 σ out
  else RDrev code g s0

def CheckedAddressGetterResult (P : Prop) [Decidable P]
    (code : ByteArray) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (σ : AccountMap) (out : ByteArray) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 36 ≤ I.calldata.size ∧ I.calldata.size < 2 ^ 255 + 4 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧ P then
    RDret code g s0 σ out
  else RDrev code g s0

-- LIBRARY CANDIDATE: refinement connection for nonpayable getters of one address argument.
theorem checkedAddressGetter_refines {t : TransitionDecl} {imms : Store}
    {σ σ₀ A I} {g : UInt256} {code out : ByteArray}
    {P : Prop} [Decidable P]
    {name : Ident} {body : List Stmt} {values : List Value}
    (hcode : I.code = code) (hsz : 4 ≤ I.calldata.size)
    (hd : selectorDispatchMsg contract I.calldata = some t)
    (hp : t.params = [⟨name, .elem .address⟩])
    (hb : t.body = calldataPrologue body)
    (hreturn : P → returnEquiv out (some values) t.returnType)
    (hsource : I.weiValue = ⟨0⟩ → I.calldata.size < 2 ^ 255 + 4 →
      (calldataWord I.calldata 4).toNat < EVM.addressModulus → P → ∃ frame,
      ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (addressGetterArgs name I) (calldataPrologue body)
        (.returned frame (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some values)) imms)
    (hsourceRevert : I.weiValue = ⟨0⟩ → I.calldata.size < 2 ^ 255 + 4 → ¬ P →
      ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (addressGetterArgs name I) (calldataPrologue body) .reverted imms)
    (hX : CheckedAddressGetterResult P code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ out) :
    runtimeRefinementFor config contract σ σ₀ g A I imms := by
  have hdecode : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata =
      decodeCalldata [name] [.elem .address] I.calldata := by
    simp only [transitionSignature, hp, List.map_cons, List.map_nil]
    rfl
  by_cases hlo : 36 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdargs := decodeCalldata_address_ok (x := name) hlo hhi hc
        by_cases hv : I.weiValue = ⟨0⟩
        · by_cases hP : P
          · simp only [CheckedAddressGetterResult, hv, hlo, hhi, hc, hP, and_self, if_true] at hX
            obtain ⟨frame, hbody⟩ := hsource hv hhi hc hP
            apply selectorReturn_refines hcode hX hd (hdecode.trans hdargs)
            · rw [hb]; exact hbody
            · exact hreturn hP
          · simp only [CheckedAddressGetterResult, hP, and_false, if_false] at hX
            apply selectorRevert_refines hcode hX hd (hdecode.trans hdargs)
            rw [hb]
            exact hsourceRevert hv hhi hP
        · simp only [CheckedAddressGetterResult, hv, false_and, if_false] at hX
          apply selectorRevert_refines hcode hX hd (hdecode.trans hdargs)
          rw [hb]
          exact calldataPrologue_nonpayable hv
      · simp only [CheckedAddressGetterResult, hc, false_and, and_false, if_false] at hX
        exact selectorDecodeFailure_refines hcode hX hd
          (hdecode.trans (decodeCalldata_address_none_noncanon hlo hhi hc))
    · simp only [CheckedAddressGetterResult, hhi, false_and, and_false, if_false] at hX
      exact selectorDecodeFailure_refines hcode hX hd
        (hdecode.trans (decodeCalldata_address_none_huge (by omega)))
  · simp only [CheckedAddressGetterResult, hlo, false_and, and_false, if_false] at hX
    exact selectorDecodeFailure_refines hcode hX hd
      (hdecode.trans (decodeCalldata_address_none_short hsz (by omega)))

-- LIBRARY CANDIDATE: refinement connection for nonpayable getters of one address argument.
theorem addressGetterValues_refines {t : TransitionDecl} {imms : Store}
    {σ σ₀ A I} {g : UInt256} {code out : ByteArray}
    {name : Ident} {body : List Stmt} {values : List Value}
    (hcode : I.code = code) (hsz : 4 ≤ I.calldata.size)
    (hd : selectorDispatchMsg contract I.calldata = some t)
    (hp : t.params = [⟨name, .elem .address⟩])
    (hb : t.body = calldataPrologue body)
    (hreturn : returnEquiv out (some values) t.returnType)
    (hsource : I.weiValue = ⟨0⟩ → I.calldata.size < 2 ^ 255 + 4 →
      (calldataWord I.calldata 4).toNat < EVM.addressModulus → ∃ frame,
      ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (addressGetterArgs name I) (calldataPrologue body)
        (.returned frame (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some values)) imms)
    (hX : AddressGetterResult code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ out) :
    runtimeRefinementFor config contract σ σ₀ g A I imms := by
  apply checkedAddressGetter_refines (P := True) hcode hsz hd hp hb (fun _ ↦ hreturn)
    (fun hv hhi hc _ ↦ hsource hv hhi hc) (fun _ _ hn ↦ False.elim (hn trivial))
  simpa only [CheckedAddressGetterResult, AddressGetterResult, and_true] using hX

-- LIBRARY CANDIDATE: refinement connection for nonpayable getters of one address argument.
theorem addressGetter_refines {t : TransitionDecl} {imms : Store}
    {σ σ₀ A I} {g : UInt256} {code out : ByteArray}
    {name : Ident} {body : List Stmt} {value : Value} {ty : ABIType}
    (hcode : I.code = code) (hsz : 4 ≤ I.calldata.size)
    (hd : selectorDispatchMsg contract I.calldata = some t)
    (hp : t.params = [⟨name, .elem .address⟩])
    (hb : t.body = calldataPrologue body) (ht : t.returnType = [ty])
    (henc : encodeReturnValue? ty value = some out)
    (hsource : I.weiValue = ⟨0⟩ → I.calldata.size < 2 ^ 255 + 4 →
      (calldataWord I.calldata 4).toNat < EVM.addressModulus → ∃ frame,
      ExecTransitionBody config contract (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (addressGetterArgs name I) (calldataPrologue body)
        (.returned frame (initState σ σ₀ (Sat256.ofUInt256 g) A I) (some [value])) imms)
    (hX : AddressGetterResult code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ out) :
    runtimeRefinementFor config contract σ σ₀ g A I imms := by
  apply addressGetterValues_refines hcode hsz hd hp hb ?_ hsource hX
  rw [ht]
  exact returnEquiv_of_encode henc

end Benchmarks.CompoundIII.Comet
