import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.Entry.FinalFlagCheck

/-!
# BLAKE2F fallback compression entry: CompressionEntry
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validCompressionEntryPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1154⟩
      [UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨168⟩]
      (t1StoredMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 6459 := by
  obtain ⟨k0, rd155⟩ := validFinalFlagCheckPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hflagOk : parsedFinalFlagBranchCond I = ⟨0⟩ :=
    parsedFinalFlagGuard_of_valid I hlen hflag
  have rd1154 := evm_run rd155 with [
    jumpiNT hflagOk,
    push1 ⟨1⟩,
    push2 ⟨168⟩,
    swap6,
    eq,
    swap4,
    push2 ⟨1154⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa using rd1154⟩

end Blake2f
