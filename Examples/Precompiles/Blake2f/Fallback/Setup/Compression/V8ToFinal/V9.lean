import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.V8ToFinal.V8

/-!
# BLAKE2F fallback compression V8-to-final: V9
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validV9InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1222⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v9InitMem I) (UInt256.ofNat 56) ByteArray.empty (cA, σ) k 7443 := by
  obtain ⟨k0, rd1207⟩ := validV8InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have rd1222 := evm_run rd1207 with [
    push8 ⟨13503953896175478587⟩,
    push2 ⟨288⟩,
    dup8,
    add,
    raw mstore 4 (v9InitMem I) (UInt256.ofNat 56)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v9InitMem
        rfl)
      (by native_decide) (by evm_ov) ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd1222⟩

end Blake2f
