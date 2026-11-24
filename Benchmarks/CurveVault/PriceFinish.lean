import Benchmarks.CurveVault.PriceFinishSource
import Benchmarks.CurveVault.RuntimeBlocks_009

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultPriceRoundReach {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {x y unused : UInt256} {isFloor : Bool} {R : List UInt256}
    (hsize : 448 ≤ mem.size) (hx : memLoad (UInt256.ofNat 416) mem = x)
    (hf : memLoad (UInt256.ofNat 320) mem = if isFloor then ⟨1⟩ else ⟨0⟩)
    (hy0 : y ≠ ⟨0⟩) (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1689) (y :: unused :: R) mem aw rdata σ k C) :
    ∃ scratch aw' k' C', RD fork vaultBytecode I g s0 (UInt256.ofNat 1765) R
      ((vaultConversionResult isFloor x y).toByteArray.write 0 scratch 480 32) aw' rdata σ k' C' := by
  let mem1 := y.toByteArray.write 0 mem 448 32
  let mem2 := (⟨0⟩ : UInt256).toByteArray.write 0 mem1 480 32
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  have hsize1 : 480 ≤ mem1.size := toByteArray_write_size_ge_off_add32 _ _ 448 (hgap _ (by omega) _)
  have hsize2 : 512 ≤ mem2.size := toByteArray_write_size_ge_off_add32 _ _ 480 (hgap _ (by omega) _)
  have hx2 : memLoad (UInt256.ofNat 416) mem2 = x := by
    rw [memLoad_below_write _ _ 480 416 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
      memLoad_below_write _ _ 448 416 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel), hx]
  have hy2 : memLoad (UInt256.ofNat 448) mem2 = y := by
    rw [memLoad_below_write _ _ 480 448 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel)]
    exact memLoad_write_back _ _ 448 (by decide +kernel) (hgap _ (by omega) _)
  have hf2 : memLoad (UInt256.ofNat 320) mem2 = if isFloor then ⟨1⟩ else ⟨0⟩ := by
    rw [memLoad_below_write _ _ 480 320 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel),
      memLoad_below_write _ _ 448 320 (by omega) (by omega) (hgap _ (by omega) _) (by decide +kernel), hf]
  cases isFloor with
  | true =>
    have rd1739 := vaultBlocks.vault_block_1689_taken (by omega)
      (by change memLoad (UInt256.ofNat 320) mem2 ≠ _; rw [hf2]; decide +kernel) (by native_decide) h
    have rd1754 := vaultBlocks.vault_block_1739_fallthrough (by simp only [vaultBlocks.vault_block_1689_taken_stack]; omega)
      (by change UInt256.isZero (memLoad (UInt256.ofNat 448) mem2) = _
          rw [hy2]; exact isZero_eq_zero_of_ne hy0) rd1739
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 1754)
      (memLoad (UInt256.ofNat 448) mem2 :: memLoad (UInt256.ofNat 416) mem2 :: R) mem2 _ rdata σ _ _ at rd1754
    rw [hx2, hy2] at rd1754
    have rd1765 := vaultBlocks.vault_block_1754 (by omega) rd1754
    exact ⟨mem2, _, _, _, rd1765⟩
  | false =>
    have rd1708 := vaultBlocks.vault_block_1689_fallthrough (by omega)
      (by change memLoad (UInt256.ofNat 320) mem2 = _; rw [hf2]; rfl) h
    have rd6946 := vaultBlocks.vault_block_1708 (by simp only [vaultBlocks.vault_block_1689_fallthrough_stack]; omega) (by native_decide) rd1708
    let argMem := mem2.write 416 mem2 64 64
    have hargX : memLoad (UInt256.ofNat 64) argMem = x := by
      rw [memLoad_copyWindow mem2 mem2 416 64 64 0 (by omega) (by omega) (by omega) (by omega)
        (by decide +kernel) (by decide +kernel), hx2]
    have hargY : memLoad (UInt256.ofNat 96) argMem = y := by
      rw [memLoad_copyWindow mem2 mem2 416 64 64 32 (by omega) (by omega) (by omega) (by omega)
        (by decide +kernel) (by decide +kernel), hy2]
    obtain ⟨aw1, k1, C1, rd1726⟩ := vaultCeilDivReach hargX hargY hy0 hstack (by native_decide) rd6946
    let scratch := (vaultCeilDivWord x y).toByteArray.write 0 argMem 512 32
    have hv : memLoad (UInt256.ofNat 512) scratch = vaultCeilDivWord x y :=
      memLoad_write_back _ _ 512 (by decide +kernel) (hgap _ (by omega) _)
    have rd1765 := vaultBlocks.vault_block_1726 (by omega) (by native_decide) rd1726
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 1765) R
      ((memLoad (UInt256.ofNat 512) scratch).toByteArray.write 0 scratch 480 32) _ rdata σ _ _ at rd1765
    rw [hv] at rd1765
    exact ⟨scratch, _, _, _, rd1765⟩

theorem vaultPriceFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {x y unused : UInt256} {isFloor : Bool} {R : List UInt256}
    (hsize : 448 ≤ mem.size) (hx : memLoad (UInt256.ofNat 416) mem = x)
    (hf : memLoad (UInt256.ofNat 320) mem = if isFloor then ⟨1⟩ else ⟨0⟩)
    (hy0 : y ≠ ⟨0⟩) (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 1689) (y :: unused :: R) mem aw rdata σ k C) :
    (vaultConversionResult isFloor x y = ⟨0⟩ ∧ RDrev fork vaultBytecode g s0) ∨
    (vaultConversionResult isFloor x y ≠ ⟨0⟩ ∧
      RDret fork vaultBytecode g s0 σ (vaultConversionResult isFloor x y).toByteArray) := by
  obtain ⟨scratch, aw', k', C', rd1765⟩ := vaultPriceRoundReach hsize hx hf hy0 hstack h
  have hgap : 480 - scratch.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 480 (by norm_num))
  have hvalue := memLoad_write_back (vaultConversionResult isFloor x y) scratch 480 (by decide +kernel) hgap
  by_cases hz : vaultConversionResult isFloor x y = ⟨0⟩
  · have rdFail := vaultBlocks.vault_block_1765_taken (by omega)
      (by rw [hvalue, hz]; decide +kernel) (by native_decide) rd1765
    exact Or.inl ⟨hz, vaultBlocks.vault_block_8284 (by omega) rdFail⟩
  · have rd1775 := vaultBlocks.vault_block_1765_fallthrough (by omega)
      (by rw [hvalue]; exact isZero_eq_zero_of_ne hz) rd1765
    have rd1780 := vaultBlocks.vault_block_1775 (by omega) rd1775
    have hret := vaultBlocks.vault_block_1780 (by omega) rd1780
    change RDret fork vaultBytecode g s0 σ
      (((vaultConversionResult isFloor x y).toByteArray.write 0 scratch 480 32).readWithPadding 480 32) at hret
    rw [toByteArray_write_read_back_of_gap _ _ _ hgap] at hret
    exact Or.inr ⟨hz, hret⟩
end Benchmarks.CurveVault
