import Reasoning.Dispatch
import Ethereum.Theory.OpcodeLemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

-- LIBRARY CANDIDATE: reachability of an INVALID instruction, allowing earlier out-of-gas.
def RDinvalid (code : ByteArray) (g : Sat256) (s0 : State) : Prop :=
  X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
  X (g.toNat + 1) (D_J code 0) s0 = .error .InvalidInstruction

-- LIBRARY CANDIDATE: the terminal rule corresponding to RD.revert.
theorem RD.invalidHalt {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.INVALID, .none)) : RDinvalid code g s0 := by
  rcases h with hoog | ⟨s, hX, hcode, hpc, _, _, hk, _, _, _, _, _, _, _⟩
  · exact Or.inl hoog
  · have hstep : Xstep (D_J code 0) s = .error .InvalidInstruction := by
      have hd : decode s.executionEnv.code s.machineState.pc = some (.INVALID, .none) := by
        rw [hcode, hpc]
        exact hdec
      simpa only [hcode] using Ethereum.EVM.step_invalid s hd
    have hfuel : g.toNat + 1 - k = (g.toNat + 1 - (k + 1)) + 1 := by omega
    exact Or.inr (hX.trans (by
      rw [hfuel]
      exact Ethereum.EVM.Xstep_X_X_except _ s _ _ hstep))

-- LIBRARY CANDIDATE: Solidity 0.5 arithmetic guards can revert via INVALID.
theorem RDinvalid.reEquivExecutionInvalid {cfg : Config} {contract : ContractDecl}
    {t : TransitionDecl} {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {code : ByteArray} {callargs}
    (hcode : I.code = code)
    (h : RDinvalid code (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hd : dispatchMsg contract I.calldata = some t)
    (hdec : decodeCalldataWithMode cfg.abiDecodeMode (t.params.map Param.name)
      (transitionSignature t).paramTypes I.calldata = some callargs)
    (hbody : ExecTransitionBody cfg contract
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs t.body .reverted)
    (hfallback : contract.fallback = none := by rfl)
    (hreceive : contract.receive = none := by rfl) :
    runtimeEquivalenceFor cfg contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  rcases h with hoog | hinvalid
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by rwa [← hcode] at hoog))
  · refine reEquiv_execution hd hdec hbody ?_ hfallback hreceive
    have hXi : Ξ cA gh bl σ_evm σ₀ g A I = .error .InvalidInstruction :=
      Xi_error_of_X (g := g) (by rwa [← hcode] at hinvalid)
    rw [hXi]
    exact execResultsEquiv.invalidHalt rfl rfl

end UniswapV2Pair
