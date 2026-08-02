import Examples.Ripemd160.HashWideRun
import Examples.Ripemd160.HashRun

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

/-- The successful deployed bytecode trace returns the mathematical RIPEMD-160 raw word. -/
theorem ripemd160X_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = ripemd160RuntimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RDret ripemd160RuntimeBytecode g
      (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (Model.rawOutput I.calldata) := by
  obtain ⟨k0, C0, rd0⟩ := ripemd160X_reachBlockLoop
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  let blocks := Model.paddedLength I.calldata.size / 64
  have rdInitial : RD ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I ⟨0⟩ (runtimeInitialHashState I).chain)
      (runtimeInitialHashState I).cursor.mem
      (runtimeInitialHashState I).cursor.aw ByteArray.empty (cA, σ) k0 C0 := by
    simpa [runtimeInitialHashState, runtimeInitialChain, hashBlockLoopStack] using rd0
  obtain ⟨k1, C1, rd1, _⟩ := ripemd160X_blocks_wide (blocks := blocks)
    (le_refl blocks) (RuntimePaddedCursor.initial I hsmall) hsmall rdInitial
  have hcount := hashBlockCountWord_toNat I hsmall
  have hblocksUint : blocks < UInt256.size := by
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    rw [show UInt256.size = 2 ^ 256 from by decide]
    unfold blocks maxFallbackCalldataSize at *
    omega
  have hword : UInt256.ofNat blocks = hashBlockCountWord I := by
    apply u256_inj
    rw [ulit_toNat' blocks hblocksUint, hcount]
  have hdone : UInt256.lt (UInt256.ofNat blocks) (hashBlockCountWord I) = ⟨0⟩ := by
    rw [hword]
    exact ult_zero (le_refl _)
  have rdret := ripemd160X_finish hdone rd1
  rw [runtimeHashRun_final_digest I hsmall] at rdret
  exact rdret

end Ripemd160
