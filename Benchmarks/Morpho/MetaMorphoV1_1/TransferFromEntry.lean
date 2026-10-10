import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_051
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_023

/-! Calldata guards and return encoding for delegated transfer. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem transferFromReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 100 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨10441⟩ R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩
      (⟨10469⟩ :: ⟨4161⟩ :: R) mem aw' rdata σ k' C' := by
  have h1 := metaMorphoV1_1_block_10441_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_10447_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨96⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcDecodeLenCheckOk hsz hhi hsize (by decide)) h1
  exact metaMorphoV1_1_block_10459_packed (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem transferFromRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨10441⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_10441_taken (immWords := wordsOf (immStore v))
    hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h1

theorem transferFromRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨96⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨10441⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_10441_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have h2 := metaMorphoV1_1_block_10447_taken (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h2

theorem transferFromDecodeFirst {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨10469⟩ :: ⟨4161⟩ :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11185⟩
      (⟨10477⟩ :: calldataWord I.calldata 4 :: ⟨4161⟩ :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k1, C1, h1⟩ := decodeAddressAt4 v (by simp only [List.length_cons]; omega)
    hc (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  exact metaMorphoV1_1_block_10469_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem transferFromReachFunction {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 ⟨11185⟩
      (⟨10477⟩ :: calldataWord I.calldata 4 :: ⟨4161⟩ :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12530⟩
      (UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).toNat ::
        UInt256.ofNat I.source.toNat :: calldataWord I.calldata 68 :: ⟨10492⟩ ::
        UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).toNat ::
        UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 36).toNat).toNat ::
        calldataWord I.calldata 68 :: ⟨4161⟩ :: R) mem aw' rdata σ k' C' := by
  obtain ⟨k1, C1, h1⟩ := decodeAddressAt36 v (by simp only [List.length_cons]; omega)
    hc1 (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  have heq0 : UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).toNat =
      calldataWord I.calldata 4 := by
    simpa only [keyValueToWord_address, Fin.toNat] using
      keyValueToWord_address_of_canonical _ hc0
  have heq1 : UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 36).toNat).toNat =
      calldataWord I.calldata 36 := by
    simpa only [keyValueToWord_address, Fin.toNat] using
      keyValueToWord_address_of_canonical _ hc1
  rw [heq0, heq1]
  exact metaMorphoV1_1_block_10477_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

end Benchmarks.Morpho.MetaMorphoV1_1
