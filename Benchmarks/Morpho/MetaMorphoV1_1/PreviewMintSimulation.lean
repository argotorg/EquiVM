import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedAssetsUpSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertAssetsUpRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_020

/-! Conversion trace for previewMint. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem previewMintTailReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {lost total shares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 18 ≤ 1024)
    (hs : (codeOwnerStorageWord I σ ⟨2⟩).toNat + shares.toNat < UInt256.size)
    (hc : convertAssetsUpFits v.DECIMALS_OFFSET (calldataWord I.calldata 4)
      (codeOwnerStorageWord I σ ⟨2⟩ + shares) total)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨3533⟩
      ([lost, total, shares, ⟨3544⟩, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (convertAssetsUpWord v.DECIMALS_OFFSET (calldataWord I.calldata 4)
        (codeOwnerStorageWord I σ ⟨2⟩ + shares) total :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3533_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k2, C2, h2⟩ := checkedAddReturn v
    (by simp only [List.append, List.length_cons]; omega) hs
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_3544_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  exact convertAssetsUpReturn v hstack hc hret h3

theorem previewMintTailRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {lost total shares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 18 ≤ 1024)
    (hbad : ¬ ((codeOwnerStorageWord I σ ⟨2⟩).toNat + shares.toNat < UInt256.size ∧
      convertAssetsUpFits v.DECIMALS_OFFSET (calldataWord I.calldata 4)
        (codeOwnerStorageWord I σ ⟨2⟩ + shares) total))
    (rd : RD (deployedRuntime v) I g s0 ⟨3533⟩
      ([lost, total, shares, ⟨3544⟩, ret] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3533_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hs : (codeOwnerStorageWord I σ ⟨2⟩).toNat + shares.toNat < UInt256.size
  · obtain ⟨k2, C2, h2⟩ := checkedAddReturn v
      (by simp only [List.append, List.length_cons]; omega) hs
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_3544_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact convertAssetsUpRevert v hstack (fun hc ↦ hbad ⟨hs, hc⟩) h3
  · exact checkedAddRevert v (by simp only [List.append, List.length_cons]; omega)
      (Nat.le_of_not_gt hs) h1

theorem previewMintConversionSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 37 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12247⟩
      ([⟨3533⟩, ⟨3544⟩, ret] ++ R) mem aw rdata σ k C) :
    (ExecFuncBody config (allocatedAssetsFrame (immStore v) (calldataWord I.calldata 4) ptr ⟨1⟩)
      evm allocatedConvertToAssetsFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (result ptr' : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      accountStorageStateEq evm.accountMap evm'.accountMap ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ 96 ≤ mem'.size ∧
      ExecFuncBody config (allocatedAssetsFrame (immStore v) (calldataWord I.calldata 4) ptr ⟨1⟩)
        evm allocatedConvertToAssetsFunction.body
        (.returned frame' evm' [uint256Value result, uint256Value ptr']) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
        (result :: R) mem' aw' out evm'.accountMap k' C' := by
  rcases accruedAssetsSimulation v (by change R.length + 2 + 35 ≤ 1024; omega)
      hcalldata hfree hlo hmem hs
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd with
    ⟨hbad, hrev⟩ | ⟨evm', frame', lost, total, shares, ptr', mem', out,
      hs', hstore, hfree', hlo', hmem', hbody, aw2, k2, C2, h2⟩
  · exact .inl ⟨allocatedAssetsAccrualReverts v hbad, hrev⟩
  · have hl := allocatedAssetsTotalsLocals (immStore v) (calldataWord I.calldata 4)
      ptr lost total shares ptr'
      (codeOwnerStorageWord I evm'.accountMap ⟨2⟩) ⟨1⟩
    by_cases hfit :
        (codeOwnerStorageWord I evm'.accountMap ⟨2⟩).toNat + shares.toNat < UInt256.size ∧
        convertAssetsUpFits v.DECIMALS_OFFSET (calldataWord I.calldata 4)
          (codeOwnerStorageWord I evm'.accountMap ⟨2⟩ + shares) total
    · exact .inr ⟨evm', _, _, ptr', mem', out, hs', hstore, hfree', hlo', hmem',
        ExecFuncBody.execBlockRet (allocatedAssetsPrefixSource v hbody (hs'.storageRead ⟨2⟩)
          (allocatedAssetsUpTailSource v hl hfit.1 hfit.2)),
        previewMintTailReturn v (by omega) hfit.1 hfit.2 hret h2⟩
    · exact .inl ⟨ExecFuncBody.execBlockRevert
        (allocatedAssetsPrefixSource v hbody (hs'.storageRead ⟨2⟩)
          (allocatedAssetsUpTailReverts v hl hfit)),
        previewMintTailRevert v (by omega) hfit h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
