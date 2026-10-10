import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferSource
import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferMemory
import Benchmarks.Morpho.MetaMorphoV1_1.OptionalCallRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_072
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_069

/-! Safe transfer from request construction through the optional-return validation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem safeTransferSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (imms : Store) (token recipient : AccountAddress)
    (amount : UInt256) (hstack : R.length + 14 ≤ 1024) (hs : SourceState s0 I σ evm)
    (hptr : ptr.toNat < 2 ^ 64) (hlo : 128 ≤ ptr.toNat) (hsize : 128 ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨15818⟩
      (UInt256.ofNat token.toNat :: UInt256.ofNat recipient.toNat :: amount :: ret :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (safeTransferFrame imms token recipient amount ptr) evm
        allocatedSafeTransferFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      ∃ (evm' : State) (cursor : UInt256) (mem' out : ByteArray) (aw' : UInt256) (k' C' : Nat),
        SourceState s0 I evm'.accountMap evm' ∧
        ExecFuncBody config (safeTransferFrame imms token recipient amount ptr) evm
          allocatedSafeTransferFunction.body
          (.returned (safeTransferResultFrame imms token recipient amount ptr cursor) evm'
            (some [uint256Value cursor])) ∧
        RD (deployedRuntime v) I g s0 ret R mem' aw' out evm'.accountMap k' C' := by
  have h32 := uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  have h36 := uadd_word_ofNat_toNat ptr 36 (by change _ < 2 ^ 256; omega)
  have h68 := uadd_word_ofNat_toNat ptr 68 (by change _ < 2 ^ 256; omega)
  have hmask : UInt256.land (UInt256.ofNat recipient.toNat)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = UInt256.ofNat recipient.toNat := by
    rw [u256_land_comm]
    exact easWord_mask recipient
  change memLoad (UInt256.ofNat 64) mem = ptr at hfree
  have hmem : metaMorphoV1_1_block_15818_memory (mem := mem)
      (x1 := UInt256.ofNat recipient.toNat) (x2 := amount) =
      safeTransferRequestMemory mem ptr recipient amount := by
    simp only [metaMorphoV1_1_block_15818_memory, hfree, hmask, h32, h36, h68,
      safeTransferRequestMemory, twoWordCallMem, writeCascade_cons, writeCascade_nil,
      Reasoning.Theory.writeWord,
      show ptr.toNat + 32 + 4 = ptr.toNat + 36 from by omega,
      show ptr.toNat + 32 + 36 = ptr.toNat + 68 from by omega]
    rfl
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15818_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_15818_stack, hfree, hmem] at h1
  by_cases hfit : allocationFits ptr ⟨100⟩
  · obtain ⟨aw2, k2, C2, h2⟩ := allocateRoundedReturn v
      (by simp only [List.length_cons]; omega) hfit
      (by change (D_J (immutableLayout.runtime metaMorphoV1_1Bytecode
            (wordsOf (immStore v))) 0).contains _ = true
          rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    have h3 := metaMorphoV1_1_block_15877 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    have hcursor := safeTransferCursor_bound ptr hfit
    have hz : memLoad ⟨96⟩ (safeTransferCallMemory mem ptr recipient amount) = ⟨0⟩ := by
      exact ((safeTransferCallMemory_prefix mem ptr recipient amount).load_preserved
        (by decide : 96 ≤ 96) hlo hsize (by decide)).trans hzero
    rcases optionalCallSimulation (data := safeTransferCalldata recipient amount)
      v imms token (by simp only [List.length_cons]; omega) hs
      hfit.1 (by omega) (by rw [safeTransferCalldata_size]; decide)
      (safeTransferCallMemory_free mem ptr recipient amount) hz
      (by simpa only [safeTransferCalldata_size] using
        safeTransferCallMemory_length mem ptr recipient amount (by omega))
      (by simpa only [safeTransferCalldata_size] using
        safeTransferCallMemory_read mem ptr recipient amount (by omega) hptr)
      (by change (D_J (immutableLayout.runtime metaMorphoV1_1Bytecode
            (wordsOf (immStore v))) 0).contains _ = true
          rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3 with
      ⟨hsource, hrev⟩ | ⟨evm', out, aw3, k3, C3, hs', _, hsource, _, _, h4⟩
    · exact .inl ⟨safeTransferBodyRevertsCall evm imms token recipient amount ptr hfit hsource,
        hrev⟩
    · have h5 := metaMorphoV1_1_block_14753 (immWords := wordsOf (immStore v))
        (by omega) hret h4
      exact .inr ⟨evm', _, _, out, aw3, _, _, hs',
        safeTransferBodyReturns imms token recipient amount ptr _ hfit hsource, h5⟩
  · exact .inl ⟨safeTransferBodyRevertsAllocation evm imms token recipient amount ptr hfit,
      allocateRoundedRevert v (by simp only [List.length_cons]; omega) hfit h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
