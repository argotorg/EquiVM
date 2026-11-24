import Benchmarks.CurveVault.TokenReturnSource
import Benchmarks.CurveVault.TokenMemory
import Benchmarks.CurveVault.StringArithmetic
import Benchmarks.CurveVault.RuntimeBlocks_028
import Benchmarks.CurveVault.RuntimeBlocks_029
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: Vyper's right-shift canonicality guard for booleans.
theorem u256_shr1_zero_iff (word : UInt256) :
    UInt256.shiftRight word (UInt256.ofNat 1) = ⟨0⟩ ↔ word = ⟨0⟩ ∨ word = ⟨1⟩ := by
  constructor
  · intro h
    have hn := congrArg UInt256.toNat h
    rw [u256_shiftRight_toNat_of_lt _ 1 (by omega)] at hn
    change word.toNat / 2 = 0 at hn
    have hsmall : word.toNat = 0 ∨ word.toNat = 1 := by omega
    rcases hsmall with hz | ho
    · exact Or.inl (uint256_toNat_eq_zero hz)
    · exact Or.inr (u256_inj ho)
  · rintro (rfl | rfl) <;> decide +kernel

theorem vaultTokenReturnFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {unused returnPc : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024) (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (hload : memLoad (UInt256.ofNat 320) mem = ⟨1⟩)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7668) (unused :: returnPc :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 returnPc R mem aw' out σ k' C' := by
  have rd7680 := vaultBlocks.vault_block_7668_fallthrough
    (by simp only [List.length_cons]; omega) (by rw [hload]; decide +kernel) h
  exact vaultBlocks.vault_block_7680_packed (by omega) hvalid rd7680

theorem vaultTokenReturnEVM {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {token returnPc : UInt256} {R : List UInt256}
    (hwide : out.size < UInt256.size)
    (hload : 32 ≤ out.size → memLoad (UInt256.ofNat 192) mem = retWord out)
    (hstack : R.length + 6 ≤ 1024) (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7606) (token :: returnPc :: R) mem aw out σ k C) :
    (vaultTokenReturnAccepted σ token out ∧ ∃ aw' k' C',
      RD fork vaultBytecode I g s0 returnPc R ((UInt256.ofNat 1).toByteArray.write 0 mem 320 32) aw' out σ k' C') ∨
    (¬ vaultTokenReturnAccepted σ token out ∧ RDrev fork vaultBytecode g s0) := by
  have hgap : 320 - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 320 (by omega))
  have honeLoad : memLoad (UInt256.ofNat 320) ((UInt256.ofNat 1).toByteArray.write 0 mem 320 32) = ⟨1⟩ :=
    memLoad_write_back _ _ _ (by decide +kernel) hgap
  by_cases hempty : out.size = 0
  · have rd7612 := vaultBlocks.vault_block_7606_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hempty]) h
    by_cases hcode : extCodeSizeWord σ token = ⟨0⟩
    · obtain ⟨_, _, _, rdFail⟩ := vaultBlocks.vault_block_7612_taken_packed
        (by simp only [List.length_cons]; omega) (by rw [hcode]; decide +kernel) (by native_decide) rd7612
      refine Or.inr ⟨?_, vaultBlocks.vault_block_8284 (by simp only [List.length_cons]; omega) rdFail⟩
      simp only [vaultTokenReturnAccepted, hempty, hcode, ne_self_iff_false, and_false, false_or]
      omega
    · obtain ⟨aw1, k1, C1, rd7619⟩ := vaultBlocks.vault_block_7612_fallthrough_packed
        (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hcode) rd7612
      have rd7668 := vaultBlocks.vault_block_7619
        (by simp only [List.length_cons]; omega) (by native_decide) rd7619
      refine Or.inl ⟨Or.inl ⟨hempty, hcode⟩, ?_⟩
      exact vaultTokenReturnFinish (by omega) hvalid honeLoad rd7668
  · have hnz : UInt256.ofNat out.size ≠ UInt256.ofNat 0 := by
      intro heq
      have hn := congrArg UInt256.toNat heq
      rw [ulit_toNat' _ hwide] at hn
      exact hempty hn
    have rd7629 := vaultBlocks.vault_block_7606_taken
      (by simp only [List.length_cons]; omega) hnz (by native_decide) h
    by_cases h32 : 32 ≤ out.size
    swap
    · have hshort : out.size < 32 := by omega
      have rdFail := vaultBlocks.vault_block_7629_taken
        (by simp only [List.length_cons]; omega)
        (rdsCheck_short 192 224 out.size rfl (by decide +kernel) hshort) (by native_decide) rd7629
      refine Or.inr ⟨?_, vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_7629_taken_stack, List.length_cons]; omega) rdFail⟩
      simp only [vaultTokenReturnAccepted, hempty, h32, false_and, or_self, not_false_eq_true]
    have rd7652 := vaultBlocks.vault_block_7629_fallthrough
      (by simp only [List.length_cons]; omega)
      (rdsCheck_ok 192 224 out.size rfl (by decide +kernel) h32 hwide) rd7629
    dsimp only [vaultBlocks.vault_block_7629_fallthrough_stack] at rd7652
    rw [vyperMin32 out.size hwide, Nat.min_eq_right h32] at rd7652
    by_cases hcanon : retWord out = ⟨0⟩ ∨ retWord out = ⟨1⟩
    swap
    · have hbad : UInt256.shiftRight (retWord out) (UInt256.ofNat 1) ≠ ⟨0⟩ :=
        fun heq => hcanon ((u256_shr1_zero_iff _).mp heq)
      have rdFail := vaultBlocks.vault_block_7652_taken
        (by simp only [List.length_cons]; omega) (by rw [hload h32]; exact hbad) (by native_decide) rd7652
      refine Or.inr ⟨?_, vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_7652_taken_stack, List.length_cons]; omega) rdFail⟩
      rintro (⟨hz, _⟩ | ⟨_, ho⟩)
      · exact hempty hz
      · exact hcanon (Or.inr ho)
    have rd7663 := vaultBlocks.vault_block_7652_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hload h32]; exact (u256_shr1_zero_iff _).mpr hcanon) rd7652
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7663)
      (memLoad (UInt256.ofNat 192) mem :: UInt256.ofNat 32 :: token :: returnPc :: R)
      mem _ out σ _ _ at rd7663
    rw [hload h32] at rd7663
    have rd7668 := vaultBlocks.vault_block_7663 (by simp only [List.length_cons]; omega) rd7663
    change RD fork vaultBytecode I g s0 (UInt256.ofNat 7668) (token :: returnPc :: R)
      ((retWord out).toByteArray.write 0 mem 320 32) _ out σ _ _ at rd7668
    rcases hcanon with hz | ho
    · rw [hz] at rd7668
      have hzLoad : memLoad (UInt256.ofNat 320) ((⟨0⟩ : UInt256).toByteArray.write 0 mem 320 32) = ⟨0⟩ :=
        memLoad_write_back _ _ _ (by decide +kernel) hgap
      have rdFail := vaultBlocks.vault_block_7668_taken
        (by simp only [List.length_cons]; omega) (by rw [hzLoad]; decide +kernel) (by native_decide) rd7668
      refine Or.inr ⟨?_, vaultBlocks.vault_block_8284
        (by simp only [vaultBlocks.vault_block_7668_taken_stack, List.length_cons]; omega) rdFail⟩
      rintro (⟨he, _⟩ | ⟨_, hone⟩)
      · exact hempty he
      · rw [hz] at hone
        exact (by decide +kernel : (⟨0⟩ : UInt256) ≠ ⟨1⟩) hone
    · rw [ho] at rd7668
      exact Or.inl ⟨Or.inr ⟨h32, ho⟩, vaultTokenReturnFinish (by omega) hvalid honeLoad rd7668⟩

end Benchmarks.CurveVault
