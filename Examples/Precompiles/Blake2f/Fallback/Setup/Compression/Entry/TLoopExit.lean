import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.Entry.T1

/-!
# BLAKE2F fallback compression entry: TLoopExit
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validTLoopExitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨140⟩ [⟨128⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩]
      (t1StoredMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 6393 := by
  obtain ⟨k0, rd130⟩ := validT1StoredPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have rd140 := evm_run rd130 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨2⟩,
    dup2,
    lt,
    push2 ⟨312⟩,
    jumpiNT (by native_decide),
    pop ]
  have hpc :
      ((⟨130⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 +
          ⟨1⟩ + ⟨1⟩) = ⟨140⟩ := by
    native_decide
  rw [hpc] at rd140
  exact ⟨_, by simpa using rd140⟩

end Blake2f
