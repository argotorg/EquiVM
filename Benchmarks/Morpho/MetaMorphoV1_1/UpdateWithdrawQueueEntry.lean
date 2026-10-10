import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.CalldataArrayView
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_040

/-! Nonpayable and calldata validation paths for the withdrawal-queue update. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open Benchmarks.EAS.Attester (arrayHead arrayHead_toNat arrayData_eq_ofNat)

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem updateWithdrawQueueNonpayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨7984⟩ R mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h := metaMorphoV1_1_block_7984_taken (immWords := wordsOf (immStore v))
    hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h

theorem updateWithdrawQueueDecode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨7984⟩ R mem aw out σ k C) :
    (¬ WordArrayCalldataChecks I.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (WordArrayCalldataChecks I.calldata ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨8032⟩
        (UInt256.ofNat (calldataArrayLength I.calldata) ::
          UInt256.ofNat (calldataArrayOffset I.calldata + 36) :: R)
        mem aw out σ k' C') := by
  have r1 := metaMorphoV1_1_block_7984_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hwv rd
  have hbad
      (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩) :
      RDrev (deployedRuntime v) g s0 := by
    have h := metaMorphoV1_1_block_7990_taken (immWords := wordsOf (immStore v))
      (by omega) hc (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h
  by_cases hhead : 36 ≤ I.calldata.size
  case neg =>
    refine .inl ⟨fun hc ↦ hhead hc.head, hbad ?_⟩
    rw [calldataNot3_eq_sub h4 hsize,
      solcDecodeLenCheckShort_4_32 h4 (by omega) hsize]
    decide
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  case neg =>
    refine .inl ⟨fun hc ↦ hhi (by have h := hc.size; omega), hbad ?_⟩
    rw [calldataNot3_eq_sub h4 hsize,
      solcDecodeLenCheckHuge_4_32 (by omega) hsize]
    decide
  have r2 := metaMorphoV1_1_block_7990_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub h4 hsize]
      exact solcDecodeLenCheckOk_4_32 hhead hhi hsize) r1
  by_cases hoff : (calldataWord I.calldata 4).toNat ≤ solcMaxU64
  case neg =>
    have h := metaMorphoV1_1_block_8002_taken (immWords := wordsOf (immStore v))
      (by omega) (by
        rw [ugt_one (by change solcMaxU64 < (calldataWord I.calldata 4).toNat; omega)]
        decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact .inl ⟨fun hc ↦ hoff hc.offset,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_8002_taken_stack, List.length_cons]; omega) h⟩
  have r3 := metaMorphoV1_1_block_8002_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (ugt_zero hoff) r2
  have r4 := metaMorphoV1_1_block_8019 (immWords := wordsOf (immStore v))
    (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r3
  rcases calldataArrayView v hstack
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r4 with
    ⟨hbad, hrev⟩ | ⟨hc, k5, C5, r5⟩
  · exact .inl ⟨fun h ↦ hbad h.runtime, hrev⟩
  · have hchecks := wordArrayCalldataChecks_of_runtime hhead hsize hoff hc
    refine .inr ⟨hchecks, k5, C5, ?_⟩
    change RD (deployedRuntime v) I g s0 ⟨8032⟩
      (calldataWord I.calldata (arrayHead I.calldata 4).toNat ::
        (arrayHead I.calldata 4 + UInt256.ofNat 32) :: R) mem aw out σ k5 C5 at r5
    rw [arrayHead_toNat hoff, arrayData_eq_ofNat hoff] at r5
    simpa only [calldataArrayLength, u256_ofNat_toNat,
      Benchmarks.EAS.Attester.arrayDataNat, calldataArrayOffset,
      show 4 + (calldataWord I.calldata 4).toNat + 32 =
        (calldataWord I.calldata 4).toNat + 36 by omega] using r5

end Benchmarks.Morpho.MetaMorphoV1_1
