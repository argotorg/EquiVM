import Benchmarks.Morpho.MetaMorphoV1_1.PermitABI
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_012
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013

/-! Permit entry guards, ordered argument decoding, and the deadline check. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem permitRevertNonPayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 2 ≤ 1024) (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1586⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := metaMorphoV1_1_block_1586_taken (immWords := wordsOf (immStore v)) hstack hwv
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack r1

theorem permitRevertLength {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 3 ≤ 1024) (hwv : I.weiValue = ⟨0⟩)
    (hcond : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨224⟩ ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨1586⟩ R mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := metaMorphoV1_1_block_1586_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have r2 := metaMorphoV1_1_block_1592_taken (immWords := wordsOf (immStore v)) hstack hcond
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) r2

theorem permitReachDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 3 ≤ 1024) (hwv : I.weiValue = ⟨0⟩)
    (hlen : 228 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨1586⟩ R mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨1611⟩ :: R)
      mem aw rdata σ k' C' := by
  have r1 := metaMorphoV1_1_block_1586_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) hwv rd
  have r2 := metaMorphoV1_1_block_1592_fallthrough (immWords := wordsOf (immStore v)) hstack
    (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨224⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub (by omega) hsize]
      exact solcCalldataStaticLenCheckOk (words := 7) hlen hhi hsize) r1
  exact ⟨_, _, metaMorphoV1_1_block_1604 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2⟩

theorem permitDecodeRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 8 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨11163⟩ (⟨1611⟩ :: R) mem aw rdata σ k C) :
    (¬ PermitChecks I.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (PermitChecks I.calldata ∧ ∃ k' C',
      let p := permitCalldataData I.calldata
      RD (deployedRuntime v) I g s0 ⟨1641⟩
        (p.sigV :: UInt256.ofNat p.owner.toNat :: UInt256.ofNat p.spender.toNat :: p.value ::
          p.deadline :: R) mem aw rdata σ k' C') := by
  by_cases h0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  · obtain ⟨k1, C1, r1⟩ := decodeAddressAt4 v (by omega) h0
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
    have r2 := metaMorphoV1_1_block_1611 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    by_cases h32 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
    · obtain ⟨k3, C3, r3⟩ := decodeAddressAt36 v
        (by simp only [List.length_cons]; omega) h32
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r2
      by_cases hv : (calldataWord I.calldata 132).toNat < 256
      · have hclean : UInt256.land (calldataWord I.calldata 132) (UInt256.ofNat 255) =
            calldataWord I.calldata 132 := lowByteClean hv
        have r4 := metaMorphoV1_1_block_1619_fallthrough (immWords := wordsOf (immStore v))
          (by omega) (by
            change UInt256.sub (calldataWord I.calldata 132)
              (UInt256.land (calldataWord I.calldata 132) (UInt256.ofNat 255)) = ⟨0⟩
            rw [hclean]
            exact u256_sub_self _) r3
        have ha (off : Nat) (hc : (calldataWord I.calldata off).toNat < EVM.addressModulus) :
            UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata off).toNat).toNat =
              calldataWord I.calldata off := by
          simpa only [keyValueToWord_address, Fin.toNat] using
            keyValueToWord_address_of_canonical _ hc
        exact .inr ⟨⟨h0, h32, hv⟩, _, _, by
          simpa only [permitCalldataData, ha 4 h0, ha 36 h32] using r4⟩
      · have r4 := metaMorphoV1_1_block_1619_taken (immWords := wordsOf (immStore v))
          (by omega) (by
            change UInt256.sub (calldataWord I.calldata 132)
              (UInt256.land (calldataWord I.calldata 132) ⟨255⟩) ≠ ⟨0⟩
            intro hz
            exact hv ((lowByteClean_iff _).mp (u256_sub_eq_zero_iff_eq.mp hz).symm))
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r3
        exact .inl ⟨fun h ↦ hv h.2.2,
          metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
            (by change R.length + 5 + 2 ≤ 1024; omega) r4⟩
    · exact .inl ⟨fun h ↦ h32 h.2.1,
        decodeAddressAt36Revert v (by simp only [List.length_cons]; omega) h32 r2⟩
  · exact .inl ⟨fun h ↦ h0 h.1, decodeAddressAt4Revert v (by omega) h0 rd⟩

theorem permitDeadlinePass {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sigV owner spender value deadline : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (htime : (UInt256.ofNat I.header.timestamp).toNat ≤ deadline.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨1641⟩
      (sigV :: owner :: spender :: value :: deadline :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨1648⟩
      (sigV :: owner :: spender :: value :: deadline :: R) mem aw rdata σ k' C' :=
  ⟨_, _, metaMorphoV1_1_block_1641_fallthrough (immWords := wordsOf (immStore v)) hstack
    (ugt_zero htime) rd⟩

theorem permitDeadlineFail {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sigV owner spender value deadline : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (htime : ¬ (UInt256.ofNat I.header.timestamp).toNat ≤ deadline.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨1641⟩
      (sigV :: owner :: spender :: value :: deadline :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have r1 := metaMorphoV1_1_block_1641_taken (immWords := wordsOf (immStore v)) (by omega)
    (by rw [ugt_one (Nat.lt_of_not_ge htime)]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_1892 (immWords := wordsOf (immStore v)) hstack r1

end Benchmarks.Morpho.MetaMorphoV1_1
