import Reasoning.Constructor
import Solm.Refine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: execute a parameterless constructor from its body proof.
theorem solmEmptyParamsCtorExec_of_body {cfg : Config} {decl : ContractDecl}
    {σ σ₀ A I} {g : UInt256} {res : ExecResult}
    (hparams : decl.ctor.params = [])
    (hbody : ExecTransitionBody cfg decl (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      ∅ decl.ctor.body res)
    (himm : decl.immutables = [] := by rfl) :
    solmCtorExec cfg decl [] σ σ₀ g A I res := by
  have hbody' : ExecTransitionBody cfg decl (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      ∅ decl.ctor.body res (initialImmutables decl) := by
    rw [initialImmutables_noImmutables himm]; exact hbody
  refine solmCtorExec.intro rfl ?_ ?_ hbody'
  · rw [hparams]; rfl
  · rw [hparams]; rfl

-- GENERALIZES Reasoning.Constructor.emptyConstructorCorrect_of_RDret to a mutating body.
theorem RDret.constructorRefinementEmptyParams {cfg : Config} {decl : ContractDecl}
    {σ σ₀ A I} {g : UInt256} {code runtime : ByteArray}
    {acc : AccountMap} {final : EVM.State} {frame : Frame}
    (rd : RDret code (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) acc runtime)
    (hcode : I.code = code) (hparams : decl.ctor.params = [])
    (hbody : ExecTransitionBody cfg decl (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      ∅ decl.ctor.body (.returned frame final none))
    (ha : acc = final.accountMap)
    (himm : decl.immutables = [] := by rfl) :
    typedConstructorRefinementFor cfg decl [] σ σ₀ g A I (fun _ => runtime) := by
  rcases rd with hoog | ⟨s, hX, hacc⟩
  · exact typedConstructorRefinementFor.outOfGas
      (by simpa using Xi_error_of_X (by rw [← hcode] at hoog; exact hoog))
  · have hxi := Xi_success_of_X (by rw [← hcode] at hX; exact hX)
    rw [hacc] at hxi
    exact typedConstructorRefinementFor.execution (by simpa using hxi)
      (solmEmptyParamsCtorExec_of_body hparams hbody himm)
      (ctorResultEquiv.success rfl rfl ha rfl) (ctorImmutablesFit_noImmutables himm)

-- LIBRARY CANDIDATE: constructor revert coupling with an empty parameter list.
theorem RDrev.constructorRefinementEmptyParams {cfg : Config} {decl : ContractDecl}
    {σ σ₀ A I} {g : UInt256} {code runtime : ByteArray}
    (rd : RDrev code (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I))
    (hcode : I.code = code) (hparams : decl.ctor.params = [])
    (hbody : ExecTransitionBody cfg decl (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      ∅ decl.ctor.body .reverted)
    (himm : decl.immutables = [] := by rfl) :
    typedConstructorRefinementFor cfg decl [] σ σ₀ g A I (fun _ => runtime) := by
  rcases rd.xiResult hcode with hoog | ⟨g', o, hxi⟩
  · exact typedConstructorRefinementFor.outOfGas (by simpa using hoog)
  · exact typedConstructorRefinementFor.execution (by simpa using hxi)
      (solmEmptyParamsCtorExec_of_body hparams hbody himm) (ctorResultEquiv.revert rfl rfl)
      (ctorImmutablesFit_noImmutables himm)

end UniswapV2Pair
