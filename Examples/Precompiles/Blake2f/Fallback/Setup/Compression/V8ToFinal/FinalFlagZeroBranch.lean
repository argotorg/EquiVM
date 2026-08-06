import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.V8ToFinal.TMix

/-!
# BLAKE2F fallback compression V8-to-final: FinalFlagZeroBranch
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validFinalFlagZeroBranchPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1368⟩
      [⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7634 := by
  have hflag : Model.validFinalFlag I.calldata := Or.inl hbyte
  obtain ⟨k0, rd1367⟩ := validTMixBranchPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hcond : UInt256.eq (parsedFinalFlagWord I) ⟨1⟩ = ⟨0⟩ :=
    parsedFinalFlagEqOne_of_byte_zero I hlen hbyte
  have rd1368 := evm_run rd1367 with [
    jumpiNT hcond ]
  exact ⟨_, by simpa using rd1368⟩

end Blake2f
