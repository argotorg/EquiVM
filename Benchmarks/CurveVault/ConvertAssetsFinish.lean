import Benchmarks.CurveVault.ConversionFinish
import Benchmarks.CurveVault.RuntimeBlocks_028

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultConvertAssetsFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {x y unused unused2 dest returnPc : UInt256} {R : List UInt256} {isFloor : Bool}
    (hsize : 512 ≤ mem.size)
    (hx : memLoad (UInt256.ofNat 480) mem = x)
    (hf : memLoad (UInt256.ofNat 352) mem = if isFloor then ⟨1⟩ else ⟨0⟩)
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7483)
      (y :: unused :: unused2 :: dest :: returnPc :: R) mem aw rdata σ k C) :
    vaultConversionFinishOutcome fork s0 I g mem isFloor x y dest returnPc R rdata σ := by
  let written := y.toByteArray.write 0 mem 512 32
  have hgap : 512 - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 512 (by norm_num))
  have hsize' : 544 ≤ written.size := toByteArray_write_size_ge_off_add32 _ _ 512 hgap
  have hx' : memLoad (UInt256.ofNat 480) written = x := by
    rw [memLoad_below_write y mem 512 480 (by omega) (by omega) hgap (by decide +kernel), hx]
  have hy' : memLoad (UInt256.ofNat 512) written = y := memLoad_write_back _ _ 512 (by decide +kernel) hgap
  have hf' : memLoad (UInt256.ofNat 352) written = if isFloor then ⟨1⟩ else ⟨0⟩ := by
    rw [memLoad_below_write y mem 512 352 (by omega) (by omega) hgap (by decide +kernel), hf]
  have hframe : WordMemoryRange mem written 576 UInt256.size :=
    wordMemoryRange_write _ _ 512 576 UInt256.size hgap (Or.inr (by omega))
  cases isFloor with
  | true =>
    have rd7529 := vaultBlocks.vault_block_7483_taken
      (by simp only [List.length_cons]; omega)
      (by change memLoad (UInt256.ofNat 352) written ≠ _; rw [hf']; decide +kernel) (by native_decide) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7529) (dest :: returnPc :: R) written _ rdata σ _ _ at rd7529
    by_cases hy0 : y = ⟨0⟩
    · have rd8284 := vaultBlocks.vault_block_7529_taken
        (by simp only [List.length_cons]; omega) (by rw [hy', hy0]; decide +kernel)
        (by native_decide) rd7529
      exact Or.inl ⟨hy0, vaultBlocks.vault_block_8284 (by simp only [vaultBlocks.vault_block_7529_taken_stack, List.length_cons]; omega) rd8284⟩
    · have rd7544 := vaultBlocks.vault_block_7529_fallthrough
        (by simp only [List.length_cons]; omega) (by rw [hy']; exact isZero_eq_zero_of_ne hy0) rd7529
      have rd7554 := vaultBlocks.vault_block_7544 (by simp only [List.length_cons]; omega) rd7544
      have rdRet := vaultBlocks.vault_block_7554 (by omega) hvalid rd7554
      change RD fork vaultBytecode I g s0 returnPc R
        ((UInt256.div (memLoad (UInt256.ofNat 480) written) (memLoad (UInt256.ofNat 512) written)).toByteArray.write 0 written dest.toNat 32) _ rdata σ _ _ at rdRet
      rw [hx', hy'] at rdRet
      exact Or.inr ⟨hy0, written, _, _, _, hframe, rdRet⟩
  | false =>
    have rd7499 := vaultBlocks.vault_block_7483_fallthrough
      (by simp only [List.length_cons]; omega) hf' h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7499) (dest :: returnPc :: R) written _ rdata σ _ _ at rd7499
    have rd6946 := vaultBlocks.vault_block_7499
      (by simp only [List.length_cons]; omega) (by native_decide) rd7499
    rcases vaultConversionCeilCall hsize' hx' hy' (by simp only [List.length_cons]; omega)
      (by native_decide) rd6946 with hrev | ⟨hy0, scratch, aw', k', C', hframe', hvalue, rd7517⟩
    · exact Or.inl hrev
    · have rd7554 := vaultBlocks.vault_block_7517
        (by simp only [List.length_cons]; omega) (by native_decide) rd7517
      have rdRet := vaultBlocks.vault_block_7554 (by omega) hvalid rd7554
      change RD fork vaultBytecode I g s0 returnPc R
        ((memLoad (UInt256.ofNat 544) scratch).toByteArray.write 0 scratch dest.toNat 32) _ rdata σ _ _ at rdRet
      rw [hvalue] at rdRet
      exact Or.inr ⟨hy0, scratch, _, _, _, hframe.trans hframe', rdRet⟩
end Benchmarks.CurveVault
