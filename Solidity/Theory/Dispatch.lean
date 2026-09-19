import Solidity.Equiv
import EVMReasoning.Reach

/-!
# From EVM traces to the refinement relation

`Reasoning.Reach`'s terminal segment facts (`RDret`, `RDrev`) at a transaction's `initState`
give the `Ξ`-level outcome; paired with a `solidityExec` derivation they discharge one case of
`runtimeEquivalenceForCore`.  Out-of-gas is absorbed by every bridge.
-/

namespace Solidity

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

/-- A success segment's `Ξ` result, for any final accounts `acc`. -/
theorem RDret.xi {cA gh bl σ σ₀ A I} {g : Sat256} {code o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hcode : I.code = code) (h : RDret code g (initState cA gh bl σ σ₀ g A I) acc o) :
    Ξ cA gh bl σ σ₀ g.toUInt256 A I = .error .OutOfGass ∨
      ∃ (g' : UInt256) (A' : Substate),
        Ξ cA gh bl σ σ₀ g.toUInt256 A I = .ok (.success (acc.1, acc.2, g', A') o) := by
  rcases h with hoog | ⟨s, hX, hacc⟩
  · exact Or.inl (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    subst hacc
    exact Or.inr ⟨_, _, hxi⟩

/-- `RDret` + a returning spec run (accounts related, return data encoded) ⇒ `execution`. -/
theorem RDret.specExecutionCore {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : Sat256} {code out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {m : Machine} {vs conv}
    (o : Oracle) (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ_evm σ₀ g A I) acc out)
    (hspec : solidityExec cfg o fc cA gh bl σ_spec σ₀ g.toUInt256 A I (.returned m vs) conv)
    (hCreated : acc.1 = m.evm.createdAccounts)
    (hAccounts : Refinement.accountMapEquiv acc.2 m.evm.accountMap)
    (henc : returnDataEquiv out vs conv) :
    runtimeEquivalenceForCore cfg fc cA gh bl σ_evm σ_spec σ₀ g.toUInt256 A I := by
  rcases RDret.xi hcode h with hoog | ⟨g', A', hxi⟩
  · exact .outOfGas hoog
  · exact .execution hxi ⟨o, hspec, .success rfl rfl hCreated hAccounts henc⟩

/-- `RDrev` + a reverting spec run ⇒ `execution` (revert data unconstrained). -/
theorem RDrev.specRevertCore {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : Sat256} {code : ByteArray}
    {d : ByteArray} {conv}
    (o : Oracle) (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (hspec : solidityExec cfg o fc cA gh bl σ_spec σ₀ g.toUInt256 A I (.reverted d) conv) :
    runtimeEquivalenceForCore cfg fc cA gh bl σ_evm σ_spec σ₀ g.toUInt256 A I := by
  rcases h.xiResult hcode with hoog | ⟨g', out, hxi⟩
  · exact .outOfGas hoog
  · exact .execution hxi ⟨o, hspec, .revert rfl rfl⟩

/-- `RDrev` when the spec accepts no entry point ⇒ `noDispatch`. -/
theorem RDrev.specNoDispatchCore {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : Sat256} {code : ByteArray}
    (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (hd : dispatches fc I.calldata = false) :
    runtimeEquivalenceForCore cfg fc cA gh bl σ_evm σ_spec σ₀ g.toUInt256 A I := by
  rcases h.xiResult hcode with hoog | ⟨g', out, hxi⟩
  · exact .outOfGas hoog
  · exact .noDispatch hd hxi

/-- `RDrev` when the spec dispatches but cannot decode the arguments ⇒ `decodingFailed`. -/
theorem RDrev.specDecodingFailedCore {cfg fc cA gh bl σ_evm σ_spec σ₀ A I} {g : Sat256} {code : ByteArray}
    {e : DispatchEntry} {fn : FnDef}
    (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (he : selectorDispatch fc I.calldata = some e) (hfn : fc.fns[e.fn]? = some fn)
    (hpay : payableOrNoValue fn.decl I)
    (hdec : decodeArgs cfg fc.types fn.decl I.calldata = none) :
    runtimeEquivalenceForCore cfg fc cA gh bl σ_evm σ_spec σ₀ g.toUInt256 A I := by
  rcases h.xiResult hcode with hoog | ⟨g', out, hxi⟩
  · exact .outOfGas hoog
  · exact .decodingFailed he hfn hpay hdec hxi

/-! ## Constructors -/

/-- `RDret` of the initcode returning the runtime code + a successful spec construction. -/
theorem RDret.specCtorCore {cfg fc args cA gh bl σ_evm σ_spec σ₀ A I} {g : Sat256} {code out : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {m : Machine} {imms : Store}
    {runtimeCodeOf : Store → Option ByteArray}
    (o : Oracle) (hcode : I.code = code)
    (h : RDret code g (initState cA gh bl σ_evm σ₀ g A I) acc out)
    (hspec : solidityCtorExec cfg o fc args cA gh bl σ_spec σ₀ g.toUInt256 A I (.ok m imms))
    (hCreated : acc.1 = m.evm.createdAccounts)
    (hAccounts : Refinement.accountMapEquiv acc.2 m.evm.accountMap)
    (hout : runtimeCodeOf imms = some out) :
    constructorEquivalenceForCore cfg fc args cA gh bl σ_evm σ_spec σ₀ g.toUInt256 A I runtimeCodeOf := by
  rcases RDret.xi hcode h with hoog | ⟨g', A', hxi⟩
  · exact .outOfGas hoog
  · exact .execution hxi ⟨o, hspec, .success rfl rfl hCreated hAccounts hout⟩

/-- `RDrev` of the initcode + a reverting spec construction. -/
theorem RDrev.specCtorRevertCore {cfg fc args cA gh bl σ_evm σ_spec σ₀ A I} {g : Sat256} {code : ByteArray}
    {d : ByteArray} {runtimeCodeOf : Store → Option ByteArray}
    (o : Oracle) (hcode : I.code = code)
    (h : RDrev code g (initState cA gh bl σ_evm σ₀ g A I))
    (hspec : solidityCtorExec cfg o fc args cA gh bl σ_spec σ₀ g.toUInt256 A I (.reverted d)) :
    constructorEquivalenceForCore cfg fc args cA gh bl σ_evm σ_spec σ₀ g.toUInt256 A I runtimeCodeOf := by
  rcases h.xiResult hcode with hoog | ⟨g', out, hxi⟩
  · exact .outOfGas hoog
  · exact .execution hxi ⟨o, hspec, .revert rfl rfl⟩

end Solidity
