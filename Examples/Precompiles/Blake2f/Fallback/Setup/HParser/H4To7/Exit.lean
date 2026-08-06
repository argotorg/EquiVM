import Examples.Precompiles.Blake2f.Fallback.Setup.HParser.H4To7.H7

/-!
# BLAKE2F fallback `h` parser loop exit
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validHLoopExitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨119⟩ [⟨0⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩]
      (h7StoredMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 2633 := by
  obtain ⟨k0, rd108⟩ := validH7StoredPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have rd119 := evm_run rd108 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨542⟩,
    jumpiNT (by native_decide),
    pop,
    push0 ]
  have hpc :
      ((⟨108⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = ⟨119⟩ := by
    native_decide
  rw [hpc] at rd119
  exact ⟨_, by simpa using rd119⟩

end Blake2f
