import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.V8ToFinal.V14

/-!
# BLAKE2F fallback compression V8-to-final: V15
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validV15InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1312⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v15InitMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7552 := by
  obtain ⟨k0, rd1297⟩ := validV14InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have rd1312 := evm_run rd1297 with [
    push8 ⟨6620516959819538809⟩,
    push2 ⟨480⟩,
    dup8,
    add,
    raw mstore 3 (v15InitMem I) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v15InitMem
        rfl)
      (by native_decide) (by evm_ov) ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd1312⟩

end Blake2f
