import Examples.Ripemd160Old.HashBlock

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

theorem oldRuntimeHashRun_padded {I : ExecutionEnv}
    {initial : RuntimeHashState} {blocks : Nat}
    (hpadded : RuntimePaddedCursor I initial.cursor 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblocks : blocks ≤ Model.paddedLength I.calldata.size / 64) :
    RuntimePaddedCursor I (oldRuntimeHashRun I blocks initial).cursor 0 := by
  induction blocks with
  | zero => simpa [oldRuntimeHashRun] using hpadded
  | succ block ih =>
      have hprev := ih (by omega)
      simpa [oldRuntimeHashRun] using
        oldRuntimeHashStep_padded hprev hsmall (by omega)

/-- Iterate a prefix of the old runtime's outer compression loop. -/
theorem runtime_blocks {cA gh bl σ σ₀ A I} {g : Sat256}
    {initial : RuntimeHashState} {blocks k C : Nat}
    (hblocks : blocks ≤ Model.paddedLength I.calldata.size / 64)
    (hpadded : RuntimePaddedCursor I initial.cursor 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (rd8533 : RD runtimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨8533⟩
      (oldBlockLoopStack I ⟨0⟩ initial.chain)
      initial.cursor.mem initial.cursor.aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨8533⟩
      (oldBlockLoopStack I (UInt256.ofNat blocks)
        (oldRuntimeHashRun I blocks initial).chain)
      (oldRuntimeHashRun I blocks initial).cursor.mem
      (oldRuntimeHashRun I blocks initial).cursor.aw
      ByteArray.empty (cA, σ) k' C' ∧
      RuntimePaddedCursor I (oldRuntimeHashRun I blocks initial).cursor 0 := by
  induction blocks with
  | zero =>
      exact ⟨k, C, by simpa [oldRuntimeHashRun] using rd8533,
        by simpa [oldRuntimeHashRun] using hpadded⟩
  | succ block ih =>
      have hprev : block ≤ Model.paddedLength I.calldata.size / 64 := by omega
      obtain ⟨kprev, Cprev, rdprev, hpprev⟩ := ih hprev
      have hblock : block < Model.paddedLength I.calldata.size / 64 := by omega
      obtain ⟨knext, Cnext, rdnext, hinv⟩ :=
        runtime_compressBlock hpprev hsmall hblock rdprev
      have hnext : UInt256.ofNat block + ⟨1⟩ = UInt256.ofNat (block + 1) := by
        rw [u256_add_comm, u256_one_add_ofNat]
      refine ⟨knext, Cnext, ?_, ?_⟩
      · simpa [oldRuntimeHashRun, oldRuntimeHashStep, hnext] using rdnext
      · simpa [oldRuntimeHashRun, oldRuntimeHashStep] using
          hinv.padded.weaken (m := 0) (by omega)

theorem oldRuntimeHashRun_chain_rep {I : ExecutionEnv}
    {initial : RuntimeHashState} {blocks : Nat}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblocks : blocks ≤ Model.paddedLength I.calldata.size / 64)
    (hcursors : ∀ block, block < blocks →
      RuntimePaddedCursor I (oldRuntimeHashRun I block initial).cursor 0)
    (hinitial : RuntimeChainRep initial.chain Model.initial) :
    RuntimeChainRep (oldRuntimeHashRun I blocks initial).chain
      (Model.stateAfter I.calldata blocks) := by
  induction blocks with
  | zero => simpa [oldRuntimeHashRun, Model.stateAfter] using hinitial
  | succ block ih =>
      have hcursor := hcursors block (by omega)
      have hblockCount : block < Model.paddedLength I.calldata.size / 64 := by omega
      have hX : ∀ i,
          (runtimeParsedWords I (UInt256.ofNat block)
            (oldRuntimeHashRun I block initial).cursor i).toNat =
            Model.blockWord I.calldata block i.val := by
        intro i
        rw [runtimeParsedWords_model_of_cursor I hcursor hsmall hblockCount i]
        exact ulit_toNat' _ (lt_trans (modelBlockWord_lt I.calldata block i.val)
          (by rw [show UInt256.size = 2 ^ 256 from by decide]; norm_num))
      have hprev : RuntimeChainRep (oldRuntimeHashRun I block initial).chain
          (Model.stateAfter I.calldata block) :=
        ih (by omega) (fun b hb => hcursors b (by omega))
      have hnext := runtimeCompressChain_rep I.calldata block
        (runtimeParsedWords I (UInt256.ofNat block)
          (oldRuntimeHashRun I block initial).cursor)
        (oldRuntimeHashRun I block initial).chain
        (Model.stateAfter I.calldata block) hX hprev
        (Model.stateAfter_bound I.calldata block)
      simpa [oldRuntimeHashRun, oldRuntimeHashStep, Model.stateAfter] using hnext

noncomputable def oldRuntimeInitialHashState (I : ExecutionEnv) : RuntimeHashState :=
  { cursor := oldScratchCursor I
    chain := runtimeInitialChain }

theorem oldRuntimeHashRun_final_rep (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimeChainRep
      (oldRuntimeHashRun I (Model.paddedLength I.calldata.size / 64)
        (oldRuntimeInitialHashState I)).chain
      (Model.finalState I.calldata) := by
  rw [← Model.stateAfter_blockCount]
  apply oldRuntimeHashRun_chain_rep hsmall (le_refl _)
  · intro block hblock
    exact oldRuntimeHashRun_padded (oldScratchCursor_padded I hsmall) hsmall
      (by omega)
  · exact runtimeInitial_rep

theorem oldRuntimeHashRun_final_digest (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    (runtimeDigestValue
      (oldRuntimeHashRun I (Model.paddedLength I.calldata.size / 64)
        (oldRuntimeInitialHashState I)).chain).toByteArray =
      Model.rawOutput I.calldata := by
  exact runtimeDigestValue_final I.calldata
    (oldRuntimeHashRun_final_rep I hsmall)

end Ripemd160Old
