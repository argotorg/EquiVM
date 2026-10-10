import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_010

/-! Calldata decoding and owner-call setup for the fee-recipient setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem setFeeRecipientReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨1158⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨1183⟩ :: R)
      mem aw rdata σ k' C' := by
  have rd1164 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1158_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd1176 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1164_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk_4_32 hsz hhi hsize) rd1164
  have rd11163 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1176
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1176
  exact ⟨_, _, rd11163⟩

set_option maxRecDepth 2000 in
theorem setFeeRecipientReachOwner {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨1183⟩ :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12917⟩
      (⟨1191⟩ :: calldataWord I.calldata 4 :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, rd1183⟩ := decodeAddressAt4 v hstack hcanon
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  have rd12917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1183
    (immWords := wordsOf (immStore v)) (by simpa using (show R.length + 3 ≤ 1024 by omega))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1183
  exact ⟨_, _, rd12917⟩

set_option maxRecDepth 2000 in
theorem setFeeRecipientRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1158⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1158_taken
    (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) hstack rd917

set_option maxRecDepth 2000 in
theorem setFeeRecipientRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1158⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd1164 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1158_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have rd917 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_1164_taken
    (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd1164
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_917
    (immWords := wordsOf (immStore v)) (by omega) rd917

end Benchmarks.Morpho.MetaMorphoV1_1
