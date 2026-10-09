import Solidity.Examples.ERC20.TotalSupply
import Solidity.Examples.ERC20.BalanceOf
import Solidity.Examples.ERC20.Allowance
import Solidity.Examples.ERC20.Approve
import Solidity.Examples.ERC20.Transfer
import Solidity.Examples.ERC20.TransferFrom
import Solidity.Examples.ERC20.Constructor

/-!
# ERC20 — the optimizer-ON solc 0.8.35 bytecode refines the Solidity specification

Every message call: the dispatcher's value guard and selector arms are handed to the per-function
results; calldata no arm accepts reverts on both sides.  Deployment: `Constructor.lean`.
`erc20Correct` combines the two.
-/

open _root_.Solidity Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Trace

set_option maxRecDepth 2000000

namespace ERC20.Opt

/-- No arm matches the selector. -/
theorem noMatch_of_not_selIs {I : ExecutionEnv}
    (h0 : ¬ selIs I (selBytes 0)) (h1 : ¬ selIs I (selBytes 1)) (h2 : ¬ selIs I (selBytes 2))
    (h3 : ¬ selIs I (selBytes 3)) (h4 : ¬ selIs I (selBytes 4)) (h5 : ¬ selIs I (selBytes 5)) :
    ∀ i, i < 6 → (selBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs] using h0
  · simpa [selIs] using h1
  · simpa [selIs] using h2
  · simpa [selIs] using h3
  · simpa [selIs] using h4
  · simpa [selIs] using h5

theorem noDispatch_of_noMatch {I : ExecutionEnv} (hnm : ∀ i, i < 6 → (selBytes i == I.calldata.extract 0 4) = false) :
    selectorDispatch erc20Flat I.calldata = none := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact erc20Dispatch_none hsz hnm
  · exact selectorDispatch_short (by omega)

/-- `callvalue ≠ 0`: the dispatcher reverts; the spec refuses the value or rejects the call. -/
theorem nonPayableCorrect {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = erc20Runtime) (hwv : I.weiValue ≠ ⟨0⟩) :
    runtimeEquivalenceFor erc20Cfg erc20Flat σ σ₀ g A I := by
  have hX := revertNonPayable (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) hcode hwv
  have rev : ∀ {e fn retTys}, selectorDispatch erc20Flat I.calldata = some e → erc20Flat.fns[e.fn]? = some fn →
      fn.decl.mutability ≠ .payable → returnAbiTys erc20Flat.types fn.decl = some retTys →
      runtimeEquivalenceFor erc20Cfg erc20Flat σ σ₀ g A I :=
    fun he hfn hne hret => Reverted.specNonPayable hcode hX he hfn hne hwv hret
  by_cases h0 : selIs I (selBytes 0)
  · exact rev (erc20Dispatch_approve h0) erc20Flat_fns2 (by decide) rfl
  by_cases h1 : selIs I (selBytes 1)
  · exact rev (erc20Dispatch_totalSupply h1) erc20Flat_fns6 (by decide) rfl
  by_cases h2 : selIs I (selBytes 2)
  · exact rev (erc20Dispatch_transferFrom h2) erc20Flat_fns3 (by decide) rfl
  by_cases h3 : selIs I (selBytes 3)
  · exact rev (erc20Dispatch_balanceOf h3) erc20Flat_fns4 (by decide) rfl
  by_cases h4 : selIs I (selBytes 4)
  · exact rev (erc20Dispatch_transfer h4) erc20Flat_fns1 (by decide) rfl
  by_cases h5 : selIs I (selBytes 5)
  · exact rev (erc20Dispatch_allowance h5) erc20Flat_fns5 (by decide) rfl
  exact Reverted.specUndispatched hcode hX (noDispatch_of_noMatch (noMatch_of_not_selIs h0 h1 h2 h3 h4 h5))
    (Or.inl erc20Flat_receive) erc20Flat_fallback

/-! ## Runtime -/

/-- Every message call to the deployed runtime refines the Solidity specification. -/
theorem erc20RuntimeCorrect : runtimeEquivalence erc20Cfg erc20Runtime erc20Flat := by
  refine ⟨fun σ σ₀ g A I hcode hsize hperm => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases h0 : selIs I (selBytes 0)
    · exact approveCorrect hcode hsize hperm hwv h0
    by_cases h1 : selIs I (selBytes 1)
    · exact totalSupplyCorrect hcode hsize hwv h1
    by_cases h2 : selIs I (selBytes 2)
    · exact transferFromCorrect hcode hsize hperm hwv h2
    by_cases h3 : selIs I (selBytes 3)
    · exact balanceOfCorrect hcode hsize hwv h3
    by_cases h4 : selIs I (selBytes 4)
    · exact transferCorrect hcode hsize hperm hwv h4
    by_cases h5 : selIs I (selBytes 5)
    · exact allowanceCorrect hcode hsize hwv h5
    have hnm := noMatch_of_not_selIs h0 h1 h2 h3 h4 h5
    have hd := erc20Dispatches_false (noDispatch_of_noMatch hnm)
    by_cases hsz : 4 ≤ I.calldata.size
    · exact Reverted.specNoDispatch hcode (revertNoMatch hcode hwv hsz hsize hnm) hd
    · exact Reverted.specNoDispatch hcode (revertShort hcode hwv (by omega)) hd
  · exact nonPayableCorrect hcode hwv

/-! ## The capstone -/

/-- Deployment and every message call of the optimizer-ON ERC20 bytecode refine the Solidity
    specification `ERC20.SoliditySpec.program`: accounts, created set, logs, return and revert data. -/
theorem erc20Correct : contractEquivalence erc20Cfg erc20Creation erc20Flat :=
  contractEquivalence.of_constant erc20Constructor erc20RuntimeCorrect

end ERC20.Opt
