import Examples.Ripemd160Old.HashFinish

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

/-- The successful old deployed bytecode trace returns the mathematical RIPEMD-160 word. -/
theorem runtime_success {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RDret runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (Model.rawOutput I.calldata) := by
  obtain ⟨k0, C0, rd0⟩ := runtime_reachBlockLoop
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  let blocks := Model.paddedLength I.calldata.size / 64
  have rdInitial : RD runtimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨8533⟩
      (oldBlockLoopStack I ⟨0⟩ (oldRuntimeInitialHashState I).chain)
      (oldRuntimeInitialHashState I).cursor.mem
      (oldRuntimeInitialHashState I).cursor.aw
      ByteArray.empty (cA, σ) k0 C0 := by
    simpa [oldRuntimeInitialHashState] using rd0
  obtain ⟨k1, C1, rd1, _⟩ := runtime_blocks (blocks := blocks)
    (le_refl blocks) (oldScratchCursor_padded I hsmall) hsmall rdInitial
  have hcount := oldBlockCountWord_toNat I hsmall
  have hblocksUint : blocks < UInt256.size := by
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    rw [show UInt256.size = 2 ^ 256 from by decide]
    unfold blocks maxFallbackCalldataSize at *
    omega
  have hword : UInt256.ofNat blocks = oldBlockCountWord I := by
    apply u256_inj
    rw [ulit_toNat' blocks hblocksUint, hcount]
  have hdone : UInt256.lt (UInt256.ofNat blocks) (oldBlockCountWord I) = ⟨0⟩ := by
    rw [hword]
    exact ult_zero (le_refl _)
  have hrep := oldRuntimeHashRun_final_rep I hsmall
  have hbound := Model.chainBound_finalState I.calldata
  have hb0 : (oldRuntimeHashRun I blocks
      (oldRuntimeInitialHashState I)).chain.h0.toNat < 2 ^ 32 := by
    rw [hrep.1]
    exact hbound.1
  have hb1 : (oldRuntimeHashRun I blocks
      (oldRuntimeInitialHashState I)).chain.h1.toNat < 2 ^ 32 := by
    rw [hrep.2.1]
    exact hbound.2.1
  have hb2 : (oldRuntimeHashRun I blocks
      (oldRuntimeInitialHashState I)).chain.h2.toNat < 2 ^ 32 := by
    rw [hrep.2.2.1]
    exact hbound.2.2.1
  have hb3 : (oldRuntimeHashRun I blocks
      (oldRuntimeInitialHashState I)).chain.h3.toNat < 2 ^ 32 := by
    rw [hrep.2.2.2.1]
    exact hbound.2.2.2.1
  have hb4 : (oldRuntimeHashRun I blocks
      (oldRuntimeInitialHashState I)).chain.h4.toNat < 2 ^ 32 := by
    rw [hrep.2.2.2.2]
    exact hbound.2.2.2.2
  have rdret := runtime_finish hdone hb0 hb1 hb2 hb3 hb4 rd1
  rw [oldRuntimeHashRun_final_digest I hsmall] at rdret
  exact rdret

end Ripemd160Old
