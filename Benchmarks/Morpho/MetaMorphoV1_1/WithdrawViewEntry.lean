import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_012
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_014

/-! Shared argument decoding for maxWithdraw and maxRedeem. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def withdrawViewEntry (redeem : Bool) : UInt256 := if redeem then ⟨1534⟩ else ⟨1940⟩

def withdrawViewReturnStack (redeem : Bool) : List UInt256 :=
  if redeem then [⟨1572⟩, ⟨1578⟩, ⟨32⟩] else [⟨1970⟩, ⟨32⟩]

theorem withdrawViewReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (redeem : Bool) (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 (withdrawViewEntry redeem) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩
      (⟨1567⟩ :: (withdrawViewReturnStack redeem ++ R)) mem aw' rdata σ k' C' := by
  have hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩ := by
    rw [calldataNot3_eq_sub (by omega) hsize]
    exact solcDecodeLenCheckOk_4_32 hsz hhi hsize
  cases redeem with
  | false =>
      have h1 := metaMorphoV1_1_block_1940_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      have h2 := metaMorphoV1_1_block_1946_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hcond h1
      exact metaMorphoV1_1_block_1958_packed (immWords := wordsOf (immStore v))
        (by simp only [List.append]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  | true =>
      have h1 := metaMorphoV1_1_block_1534_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      have h2 := metaMorphoV1_1_block_1540_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hcond h1
      exact metaMorphoV1_1_block_1552_packed (immWords := wordsOf (immStore v))
        (by simpa only [List.append] using hstack)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem withdrawViewRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (redeem : Bool) (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (withdrawViewEntry redeem) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hrev : ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨917⟩ R mem aw' rdata σ k' C' := by
    cases redeem with
    | false =>
        exact metaMorphoV1_1_block_1940_taken_packed (immWords := wordsOf (immStore v))
          hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    | true =>
        exact metaMorphoV1_1_block_1534_taken_packed (immWords := wordsOf (immStore v))
          hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨_, _, _, h⟩ := hrev
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h

theorem withdrawViewRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (redeem : Bool) (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 (withdrawViewEntry redeem) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  cases redeem with
  | false =>
      have h1 := metaMorphoV1_1_block_1940_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      have h2 := metaMorphoV1_1_block_1946_taken
        (immWords := wordsOf (immStore v)) hstack hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h2
  | true =>
      have h1 := metaMorphoV1_1_block_1534_fallthrough
        (immWords := wordsOf (immStore v)) (by omega) hwv rd
      have h2 := metaMorphoV1_1_block_1540_taken
        (immWords := wordsOf (immStore v)) hstack hcond
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h2

theorem withdrawViewRevertNoncanonical {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (redeem : Bool) (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 (withdrawViewEntry redeem) R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  obtain ⟨_, _, _, h1⟩ := withdrawViewReachDecoder redeem v (by omega) hwv hsz hhi hsize rd
  exact decodeAddressAt4Revert v
    (by cases redeem <;> simp only [withdrawViewReturnStack, Bool.false_eq_true,
      if_false, if_true, List.length_append, List.length_cons, List.length_nil] <;> omega) hnc h1

theorem withdrawViewReachFunction {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (redeem : Bool) (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4) (hsize : I.calldata.size < UInt256.size)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (rd : RD (deployedRuntime v) I g s0 (withdrawViewEntry redeem) R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨15882⟩
      (UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).toNat ::
        (withdrawViewReturnStack redeem ++ R)) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := withdrawViewReachDecoder redeem v (by omega) hwv hsz hhi hsize rd
  obtain ⟨k2, C2, h2⟩ := decodeAddressAt4 v
    (by cases redeem <;> simp only [withdrawViewReturnStack, Bool.false_eq_true,
      if_false, if_true, List.length_append, List.length_cons, List.length_nil] <;> omega)
    hcanon (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  have heq : UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).toNat =
      calldataWord I.calldata 4 := by
    simpa only [keyValueToWord_address, Fin.toNat] using
      keyValueToWord_address_of_canonical _ hcanon
  rw [heq]
  exact metaMorphoV1_1_block_1567_packed (immWords := wordsOf (immStore v))
    (by cases redeem <;> simp only [withdrawViewReturnStack, Bool.false_eq_true,
      if_false, if_true, List.length_append, List.length_cons, List.length_nil] <;> omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem maxWithdrawEncodeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {total supply assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨1970⟩
      ([total, supply, assets, ⟨32⟩] ++ R) mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 σ assets.toByteArray := by
  have h := metaMorphoV1_1_block_1970 (immWords := wordsOf (immStore v))
    (by simpa only [List.append] using hstack) rd
  change RDret _ _ _ _ ((writeWord mem (memLoad ⟨64⟩ mem).toNat assets).readWithPadding
    (memLoad ⟨64⟩ mem).toNat 32) at h
  rw [writeWord_sparse_read_back] at h
  exact h

end Benchmarks.Morpho.MetaMorphoV1_1
