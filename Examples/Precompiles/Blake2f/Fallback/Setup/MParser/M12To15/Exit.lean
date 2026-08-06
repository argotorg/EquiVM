import Examples.Precompiles.Blake2f.Fallback.Setup.MParser.M12To15.M15

/-!
# BLAKE2F fallback `m` parser loop exit
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validMLoopExitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨130⟩ [⟨0⟩, ⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩]
      (m15StoredMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 5956 := by
  obtain ⟨k0, rd119⟩ := validM15StoredPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have rd130 := evm_run rd119 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨16⟩,
    dup2,
    lt,
    push2 ⟨427⟩,
    jumpiNT (by native_decide),
    pop,
    push0 ]
  have hpc :
      ((⟨119⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = ⟨130⟩ := by
    native_decide
  rw [hpc] at rd130
  exact ⟨_, by simpa using rd130⟩

end Blake2f
