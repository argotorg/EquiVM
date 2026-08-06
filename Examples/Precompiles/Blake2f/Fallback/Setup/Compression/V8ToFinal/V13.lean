import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.V8ToFinal.V12

/-!
# BLAKE2F fallback compression V8-to-final: V13
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validV13InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1282⟩
      [⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13InitMem I) (UInt256.ofNat 60) ByteArray.empty (cA, σ) k 7516 := by
  obtain ⟨k0, rd1267⟩ := validV12InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have rd1282 := evm_run rd1267 with [
    push8 ⟨11170449401992604703⟩,
    push2 ⟨416⟩,
    dup8,
    add,
    raw mstore 4 (v13InitMem I) (UInt256.ofNat 60)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v13InitMem
        rfl)
      (by native_decide) (by evm_ov) ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd1282⟩

end Blake2f
