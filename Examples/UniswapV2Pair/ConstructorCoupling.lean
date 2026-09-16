import Reasoning.Constructor

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: execute a parameterless constructor from its body proof.
theorem solmEmptyParamsCtorExec_of_body {cfg : Config} {decl : ContractDecl}
    {cA gh bl σ σ₀ A I} {g : UInt256} {res : ExecResult}
    (hparams : decl.ctor.params = [])
    (hbody : ExecTransitionBody cfg decl (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      ∅ decl.ctor.body res) :
    solmCtorExec cfg decl [] cA gh bl σ σ₀ g A I res := by
  refine solmCtorExec.intro rfl ?_ ?_ hbody
  · rw [hparams]; rfl
  · rw [hparams]; rfl

-- GENERALIZES Reasoning.Constructor.emptyConstructorCorrect_of_RDret to a mutating body.
theorem RDret.constructorEquivalenceEmptyParams {cfg : Config} {decl : ContractDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code runtime : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {final : EVM.State} {frame : Frame}
    (rd : RDret code (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc runtime)
    (hcode : I.code = code) (hparams : decl.ctor.params = [])
    (hbody : ExecTransitionBody cfg decl (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      ∅ decl.ctor.body (.returned frame final none))
    (hc : acc.1 = final.createdAccounts) (ha : accountMapEquiv acc.2 final.accountMap) :
    constructorEquivalenceFor cfg decl [] cA gh bl σ_evm σ_solm σ₀ g A I runtime := by
  rcases rd with hoog | ⟨s, hX, hacc⟩
  · exact constructorEquivalenceFor.outOfGas
      (by simpa using Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
  · have hxi := Xi_success_of_X (by rw [← hcode] at hX; exact hX)
    have hcA : s.createdAccounts = acc.1 := congrArg Prod.fst hacc
    have hσ : s.accountMap = acc.2 := congrArg Prod.snd hacc
    rw [hcA, hσ] at hxi
    exact constructorEquivalenceFor.execution (by simpa using hxi)
      (solmEmptyParamsCtorExec_of_body hparams hbody)
      (ctorResultEquiv.success rfl rfl hc ha rfl)

-- LIBRARY CANDIDATE: constructor revert coupling with an empty parameter list.
theorem RDrev.constructorEquivalenceEmptyParams {cfg : Config} {decl : ContractDecl}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code runtime : ByteArray}
    (rd : RDrev code (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hcode : I.code = code) (hparams : decl.ctor.params = [])
    (hbody : ExecTransitionBody cfg decl (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      ∅ decl.ctor.body .reverted) :
    constructorEquivalenceFor cfg decl [] cA gh bl σ_evm σ_solm σ₀ g A I runtime := by
  rcases rd.xiResult hcode with hoog | ⟨g', o, hxi⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa using hoog)
  · exact constructorEquivalenceFor.execution (by simpa using hxi)
      (solmEmptyParamsCtorExec_of_body hparams hbody) (ctorResultEquiv.revert rfl rfl)

end UniswapV2Pair
