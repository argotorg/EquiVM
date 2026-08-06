import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.V8ToFinal.FinalFlagOneBranch

/-!
# BLAKE2F fallback compression V8-to-final: FinalFlagOneRejoin
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validFinalFlagOneRejoinPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1368⟩
      [⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7661 := by
  obtain ⟨k0, rd3298⟩ := validFinalFlagOneBranchPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte
  have rd1368 := evm_run rd3298 with [
    raw jumpdest (by decide) (by evm_ov),
    push8 ⟨16175846103906665108⟩,
    push2 ⟨448⟩,
    dup6,
    add,
    raw mstore 0 (v14FinalFlagMem I) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v14FinalFlagMem
        rfl)
      (by native_decide) (by evm_ov),
    push2 ⟨1368⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd1368⟩

end Blake2f
