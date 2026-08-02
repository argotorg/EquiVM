import Examples.Ripemd160.ParserCursor
import Examples.Ripemd160.HashPure
import Examples.Ripemd160.HashDigest

/-!
# RIPEMD-160 block-chain bridge

This module relates the pure state threaded by the runtime trace to the corresponding prefix of
the mathematical compression chain. The cursor premise records exactly the remaining memory
obligation: every block begins with the padded input still readable.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

def Model.stateAfter (data : ByteArray) : Nat → Model.ChainState
  | 0 => Model.initial
  | block + 1 => Model.compress data block (Model.stateAfter data block)

theorem Model.stateAfter_bound (data : ByteArray) (blocks : Nat) :
    Model.ChainBound (Model.stateAfter data blocks) := by
  cases blocks with
  | zero => exact modelInitial_bound
  | succ block => exact Model.chainBound_compress data block _

theorem Model.stateAfter_eq_foldl_range (data : ByteArray) (blocks : Nat) :
    Model.stateAfter data blocks =
      (List.range blocks).foldl
        (fun state block => Model.compress data block state) Model.initial := by
  induction blocks with
  | zero => rfl
  | succ block ih =>
      simp [Model.stateAfter, List.range_succ, List.foldl_append, ih]

theorem Model.stateAfter_blockCount (data : ByteArray) :
    Model.stateAfter data (Model.paddedLength data.size / 64) =
      Model.finalState data := by
  rw [Model.stateAfter_eq_foldl_range]
  rfl

theorem runtimeHashRun_chain_rep {I : ExecutionEnv} {initial : RuntimeHashState}
    {blocks : Nat}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblocks : blocks ≤ Model.paddedLength I.calldata.size / 64)
    (hcursors : ∀ block, block < blocks →
      RuntimePaddedCursor I (runtimeHashRun I block initial).cursor 0)
    (hinitial : RuntimeChainRep initial.chain Model.initial) :
    RuntimeChainRep (runtimeHashRun I blocks initial).chain
      (Model.stateAfter I.calldata blocks) := by
  induction blocks with
  | zero => simpa [runtimeHashRun, Model.stateAfter] using hinitial
  | succ block ih =>
      have hcursor := hcursors block (by omega)
      have hblockCount : block < Model.paddedLength I.calldata.size / 64 := by omega
      have hX : ∀ i,
          (runtimeParsedWords I (UInt256.ofNat block)
            (runtimeHashRun I block initial).cursor i).toNat =
            Model.blockWord I.calldata block i.val := by
        intro i
        rw [runtimeParsedWords_model_of_cursor I hcursor hsmall hblockCount i]
        exact ulit_toNat' _ (lt_trans (modelBlockWord_lt I.calldata block i.val)
          (by rw [show UInt256.size = 2 ^ 256 from by decide]; norm_num))
      have hprev : RuntimeChainRep (runtimeHashRun I block initial).chain
          (Model.stateAfter I.calldata block) :=
        ih (by omega) (fun b hb => hcursors b (by omega))
      have hnext := runtimeCompressChain_rep I.calldata block
        (runtimeParsedWords I (UInt256.ofNat block)
          (runtimeHashRun I block initial).cursor)
        (runtimeHashRun I block initial).chain
        (Model.stateAfter I.calldata block) hX hprev
        (Model.stateAfter_bound I.calldata block)
      simpa [runtimeHashRun, runtimeHashStep, Model.stateAfter] using hnext

theorem runtimeHashRun_final_rep {I : ExecutionEnv} {initial : RuntimeHashState}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hcursors : ∀ block, block < Model.paddedLength I.calldata.size / 64 →
      RuntimePaddedCursor I (runtimeHashRun I block initial).cursor 0)
    (hinitial : RuntimeChainRep initial.chain Model.initial) :
    RuntimeChainRep
      (runtimeHashRun I (Model.paddedLength I.calldata.size / 64) initial).chain
      (Model.finalState I.calldata) := by
  rw [← Model.stateAfter_blockCount]
  exact runtimeHashRun_chain_rep hsmall (le_refl _) hcursors hinitial

end Ripemd160
