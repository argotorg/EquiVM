import Benchmarks.CurveVault.ConversionFinishSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultConversionCeilCall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {returnPc x y : UInt256} {R : List UInt256}
    (hsize : 544 ≤ mem.size)
    (hx : memLoad (UInt256.ofNat 480) mem = x)
    (hy : memLoad (UInt256.ofNat 512) mem = y)
    (hstack : R.length + 12 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 6946)
      (UInt256.ofNat 544 :: returnPc :: R) (mem.write 480 mem 64 64) aw rdata σ k C) :
    (y = ⟨0⟩ ∧ RDrev fork vaultBytecode g s0) ∨
    (y ≠ ⟨0⟩ ∧ ∃ (scratch : ByteArray) (aw' : UInt256) (k' C' : Nat),
      WordMemoryRange mem scratch 576 UInt256.size ∧
      memLoad (UInt256.ofNat 544) scratch = vaultCeilDivWord x y ∧
      RD fork vaultBytecode I g s0 returnPc R scratch aw' rdata σ k' C') := by
  have hmx : memLoad (UInt256.ofNat 64) (mem.write 480 mem 64 64) = x := by
    rw [memLoad_copyWindow mem mem 480 64 64 0 (by omega) (by omega) (by omega)
      (by omega) (by decide +kernel) (by decide +kernel), hx]
  have hmy : memLoad (UInt256.ofNat 96) (mem.write 480 mem 64 64) = y := by
    rw [memLoad_copyWindow mem mem 480 64 64 32 (by omega) (by omega) (by omega)
      (by omega) (by decide +kernel) (by decide +kernel), hy]
  by_cases hy0 : y = ⟨0⟩
  · exact Or.inl ⟨hy0, vaultCeilDivReachRevert (hmy.trans hy0)
      (by simp only [List.length_cons]; omega) h⟩
  · obtain ⟨aw', k', C', rd⟩ := vaultCeilDivReach hmx hmy hy0 (by omega) hvalid h
    have hcopy := wordMemoryRange_copy mem mem 480 64 64 576 UInt256.size
      (by omega) (by omega) (by omega) (Or.inr (by omega))
    have hwrite := wordMemoryRange_write (mem.write 480 mem 64 64) (vaultCeilDivWord x y)
      544 576 UInt256.size
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 544 (by norm_num))) (Or.inr (by omega))
    exact Or.inr ⟨hy0, _, aw', k', C', hcopy.trans hwrite,
      memLoad_write_back _ _ 544 (by decide +kernel)
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 544 (by norm_num))), rd⟩

def vaultConversionFinishOutcome (fork : Ethereum.Fork) (s0 : State) (I : ExecutionEnv) (g : Sat256)
    (mem : ByteArray) (isFloor : Bool) (x y dest returnPc : UInt256)
    (R : List UInt256) (rdata : ByteArray) (σ : AccountMap) : Prop :=
  (y = ⟨0⟩ ∧ RDrev fork vaultBytecode g s0) ∨
  (y ≠ ⟨0⟩ ∧ ∃ (scratch : ByteArray) (aw' : UInt256) (k' C' : Nat),
    WordMemoryRange mem scratch 576 UInt256.size ∧
    RD fork vaultBytecode I g s0 returnPc R
      ((vaultConversionResult isFloor x y).toByteArray.write 0 scratch dest.toNat 32) aw' rdata σ k' C')

theorem vaultConvertSharesFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {x y unused dest returnPc : UInt256} {R : List UInt256} {isFloor : Bool}
    (hsize : 512 ≤ mem.size)
    (hx : memLoad (UInt256.ofNat 480) mem = x)
    (hf : memLoad (UInt256.ofNat 352) mem = if isFloor then ⟨1⟩ else ⟨0⟩)
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7261)
      (y :: unused :: dest :: returnPc :: R) mem aw rdata σ k C) :
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
    have rd7305 := vaultBlocks.vault_block_7261_taken
      (by simp only [List.length_cons]; omega)
      (by change memLoad (UInt256.ofNat 352) written ≠ _; rw [hf']; decide +kernel) (by native_decide) h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7305) (dest :: returnPc :: R) written _ rdata σ _ _ at rd7305
    by_cases hy0 : y = ⟨0⟩
    · have rd8284 := vaultBlocks.vault_block_7305_taken
        (by simp only [List.length_cons]; omega) (by rw [hy', hy0]; decide +kernel)
        (by native_decide) rd7305
      exact Or.inl ⟨hy0, vaultBlocks.vault_block_8284 (by simp only [vaultBlocks.vault_block_7305_taken_stack, List.length_cons]; omega) rd8284⟩
    · have rd7320 := vaultBlocks.vault_block_7305_fallthrough
        (by simp only [List.length_cons]; omega) (by rw [hy']; exact isZero_eq_zero_of_ne hy0) rd7305
      have rd7330 := vaultBlocks.vault_block_7320 (by simp only [List.length_cons]; omega) rd7320
      have rdRet := vaultBlocks.vault_block_7330 (by omega) hvalid rd7330
      change RD fork vaultBytecode I g s0 returnPc R
        ((UInt256.div (memLoad (UInt256.ofNat 480) written) (memLoad (UInt256.ofNat 512) written)).toByteArray.write 0 written dest.toNat 32) _ rdata σ _ _ at rdRet
      rw [hx', hy'] at rdRet
      exact Or.inr ⟨hy0, written, _, _, _, hframe, rdRet⟩
  | false =>
    have rd7275 := vaultBlocks.vault_block_7261_fallthrough
      (by simp only [List.length_cons]; omega) hf' h
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7275) (dest :: returnPc :: R) written _ rdata σ _ _ at rd7275
    have rd6946 := vaultBlocks.vault_block_7275
      (by simp only [List.length_cons]; omega) (by native_decide) rd7275
    rcases vaultConversionCeilCall hsize' hx' hy' (by simp only [List.length_cons]; omega)
      (by native_decide) rd6946 with hrev | ⟨hy0, scratch, aw', k', C', hframe', hvalue, rd7293⟩
    · exact Or.inl hrev
    · have rd7330 := vaultBlocks.vault_block_7293
        (by simp only [List.length_cons]; omega) (by native_decide) rd7293
      have rdRet := vaultBlocks.vault_block_7330 (by omega) hvalid rd7330
      change RD fork vaultBytecode I g s0 returnPc R
        ((memLoad (UInt256.ofNat 544) scratch).toByteArray.write 0 scratch dest.toNat 32) _ rdata σ _ _ at rdRet
      rw [hvalue] at rdRet
      exact Or.inr ⟨hy0, scratch, _, _, _, hframe.trans hframe', rdRet⟩
end Benchmarks.CurveVault
