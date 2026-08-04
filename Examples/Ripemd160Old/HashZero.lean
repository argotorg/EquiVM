import Examples.Ripemd160Old.HashCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

open Ripemd160

def oldZeroIterations (I : ExecutionEnv) : Nat :=
  Model.paddedLength I.calldata.size / 32 - oldCopyIterations I

def oldZeroIndex (I : ExecutionEnv) (i : Nat) : Nat :=
  32 * (oldCopyIterations I + i)

def oldZeroIndexWord (I : ExecutionEnv) (i : Nat) : UInt256 :=
  UInt256.ofNat (oldZeroIndex I i)

noncomputable def oldZeroCursor (I : ExecutionEnv) : Nat → RuntimeMemCursor
  | 0 => oldCopyCursor I (oldCopyIterations I)
  | i + 1 => runtimeStoreCursor (oldZeroCursor I i)
      (hashPadPtr I + oldZeroIndexWord I i) ⟨0⟩

def oldZeroStack (I : ExecutionEnv) (i : Nat) : List UInt256 :=
  [oldZeroIndexWord I i, calldataSizeWord I, oldHashBitLength I,
    hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]

theorem oldCopyIndex_le_padded (I : ExecutionEnv) :
    32 * oldCopyIterations I ≤ Model.paddedLength I.calldata.size := by
  have hm32 := Nat.mod_lt (I.calldata.size + 31) (by decide : 0 < 32)
  have hd32 := Nat.mod_add_div (I.calldata.size + 31) 32
  have hm64 := Nat.mod_lt (I.calldata.size + 72) (by decide : 0 < 64)
  have hd64 := Nat.mod_add_div (I.calldata.size + 72) 64
  unfold oldCopyIterations Model.paddedLength
  omega

theorem oldPadded_div32_mul (I : ExecutionEnv) :
    32 * (Model.paddedLength I.calldata.size / 32) =
      Model.paddedLength I.calldata.size := by
  have hm := hashPaddedLength_mod I.calldata.size
  omega

theorem oldZeroIndex_at_end (I : ExecutionEnv) :
    oldZeroIndex I (oldZeroIterations I) = Model.paddedLength I.calldata.size := by
  have hle : oldCopyIterations I ≤ Model.paddedLength I.calldata.size / 32 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 32)]
    simpa [Nat.mul_comm] using oldCopyIndex_le_padded I
  unfold oldZeroIndex oldZeroIterations
  rw [Nat.add_sub_of_le hle]
  exact oldPadded_div32_mul I

theorem oldZeroIndex_before_end (I : ExecutionEnv) {i : Nat}
    (hi : i < oldZeroIterations I) :
    oldZeroIndex I i < Model.paddedLength I.calldata.size := by
  rw [← oldZeroIndex_at_end I]
  unfold oldZeroIndex
  omega

theorem oldZeroIndexWord_toNat (I : ExecutionEnv) (i : Nat)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hi : i ≤ oldZeroIterations I) :
    (oldZeroIndexWord I i).toNat = oldZeroIndex I i := by
  unfold oldZeroIndexWord
  apply ulit_toNat'
  have hle : oldZeroIndex I i ≤ Model.paddedLength I.calldata.size := by
    rw [← oldZeroIndex_at_end I]
    unfold oldZeroIndex
    omega
  have hp := (hashPaddedLength_bounds I.calldata.size).2
  rw [show UInt256.size = 2 ^ 256 from by decide]
  unfold maxFallbackCalldataSize at hsmall
  omega

theorem oldZeroIndexWord_next (I : ExecutionEnv) (i : Nat)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hi : i < oldZeroIterations I) :
    oldZeroIndexWord I i + ⟨32⟩ = oldZeroIndexWord I (i + 1) := by
  apply u256_inj
  rw [uadd_toNat, oldZeroIndexWord_toNat I i hsmall (by omega),
    oldZeroIndexWord_toNat I (i + 1) hsmall (by omega),
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    show UInt256.size = 2 ^ 256 from by decide]
  rw [Nat.mod_eq_of_lt]
  · unfold oldZeroIndex
    omega
  · have hb := oldZeroIndex_before_end I hi
    have hp := (hashPaddedLength_bounds I.calldata.size).2
    unfold maxFallbackCalldataSize at hsmall
    omega

private theorem runtime_zeroLoopBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i k C : Nat}
    (hi : i < oldZeroIterations I)
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8359⟩ (oldZeroStack I i) (oldZeroCursor I i).mem (oldZeroCursor I i).aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8359⟩ (oldZeroStack I (i + 1))
      (oldZeroCursor I (i + 1)).mem (oldZeroCursor I (i + 1)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldZeroStack] at h ⊢
  have hlt : UInt256.lt (oldZeroIndexWord I i) (hashPaddedLengthWord I) = ⟨1⟩ := by
    apply ult_one
    rw [oldZeroIndexWord_toNat I i hsmall (by omega),
      hashPaddedLengthWord_toNat I hsmall]
    exact oldZeroIndex_before_end I hi
  have rd9064 := evm_run_rfl h with [
    jumpdest, dup5, dup2, lt, push2 ⟨9056⟩,
    jumpiT (by rw [hlt]; decide) jump_9056,
    jumpdest, dup1, push0, push1 ⟨32⟩, swap3, dup7, add ]
  have rd9065 := RD.runtimeMstore rd9064 (by old_decode) (by simp)
  have rd8359 := evm_run_rfl rd9065 with [
    add, push2 ⟨8359⟩, jump jump_8359 ]
  exact ⟨_, _, by
    simpa [oldZeroCursor, oldZeroIndexWord_next I i hsmall hi,
      runtimeStoreCursor, u256_add_comm] using rd8359⟩

private theorem runtime_zeroLoopExit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i k C : Nat}
    (hi : i = oldZeroIterations I)
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8359⟩ (oldZeroStack I i) (oldZeroCursor I i).mem (oldZeroCursor I i).aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8368⟩
      [calldataSizeWord I, oldHashBitLength I, hashPadPtr I,
        hashPaddedLengthWord I, ⟨254⟩]
      (oldZeroCursor I i).mem (oldZeroCursor I i).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldZeroStack] at h ⊢
  have hlt : UInt256.lt (oldZeroIndexWord I i) (hashPaddedLengthWord I) = ⟨0⟩ := by
    apply ult_zero
    rw [oldZeroIndexWord_toNat I i hsmall (by omega), hi,
      oldZeroIndex_at_end I, hashPaddedLengthWord_toNat I hsmall]
  exact ⟨_, _, evm_run_rfl h with [
    jumpdest, dup5, dup2, lt, push2 ⟨9056⟩,
    jumpiNT (by rw [hlt]), pop ]⟩

/-- Execute every zeroing store in the old padding routine. -/
theorem runtime_zeroPadding {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8368⟩
      [calldataSizeWord I, oldHashBitLength I, hashPadPtr I,
        hashPaddedLengthWord I, ⟨254⟩]
      (oldZeroCursor I (oldZeroIterations I)).mem
      (oldZeroCursor I (oldZeroIterations I)).aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := runtime_copyPadding
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  let Inv : Nat → Nat → Prop := fun v i => v + i = oldZeroIterations I
  let exitStk : Nat → List UInt256 := fun _ =>
    [calldataSizeWord I, oldHashBitLength I, hashPadPtr I,
      hashPaddedLengthWord I, ⟨254⟩]
  have hexit : ∀ i, Inv 0 i → ∀ k C,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8359⟩ (oldZeroStack I i) (oldZeroCursor I i).mem (oldZeroCursor I i).aw
        ByteArray.empty (cA, σ) k C →
      ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8368⟩ (exitStk i) (oldZeroCursor I i).mem (oldZeroCursor I i).aw
        ByteArray.empty (cA, σ) k' C' := by
    intro i hi k C h
    exact runtime_zeroLoopExit hsmall (by simpa [Inv] using hi) h
  have hbody : ∀ v i, Inv (v + 1) i → ∀ k C,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8359⟩ (oldZeroStack I i) (oldZeroCursor I i).mem (oldZeroCursor I i).aw
        ByteArray.empty (cA, σ) k C →
      ∃ i' k' C', Inv v i' ∧
        RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨8359⟩ (oldZeroStack I i') (oldZeroCursor I i').mem (oldZeroCursor I i').aw
          ByteArray.empty (cA, σ) k' C' := by
    intro v i hi k C h
    have hit : i < oldZeroIterations I := by dsimp [Inv] at hi; omega
    obtain ⟨k', C', h'⟩ := runtime_zeroLoopBody hsmall hit h
    exact ⟨i + 1, k', C', by dsimp [Inv]; dsimp [Inv] at hi; omega, h'⟩
  have rd0 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8359⟩ (oldZeroStack I 0) (oldZeroCursor I 0).mem (oldZeroCursor I 0).aw
      ByteArray.empty (cA, σ) k C := by
    simpa [oldZeroStack, oldZeroIndexWord, oldZeroIndex, oldZeroCursor,
      oldCopyIndexWord] using rd
  obtain ⟨i, k', C', hi, h'⟩ :=
    RD.whileLoopCarry (code := runtimeBytecode) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty)
      (acc := (cA, σ)) (α := Nat) ⟨8359⟩ ⟨8368⟩ Inv (oldZeroStack I)
      (fun i => (oldZeroCursor I i).mem) (fun i => (oldZeroCursor I i).aw)
      exitStk hexit hbody (oldZeroIterations I) 0 (by simp [Inv]) k C rd0
  have hieq : i = oldZeroIterations I := by dsimp [Inv] at hi; omega
  subst i
  exact ⟨k', C', by simpa [exitStk] using h'⟩

end Ripemd160Old
