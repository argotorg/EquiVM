import Examples.Ripemd160Old.HashPrelude
import Examples.Precompiles.Ripemd160.HashBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

open Ripemd160

def oldCopyIterations (I : ExecutionEnv) : Nat :=
  (I.calldata.size + 31) / 32

def oldCopyIndexWord (i : Nat) : UInt256 :=
  UInt256.ofNat (32 * i)

def oldCopySourceAddr (i : Nat) : UInt256 :=
  ⟨160⟩ + oldCopyIndexWord i

def oldCopyDestAddr (I : ExecutionEnv) (i : Nat) : UInt256 :=
  hashPadPtr I + oldCopyIndexWord i

noncomputable def oldCopyCursor (I : ExecutionEnv) : Nat → RuntimeMemCursor
  | 0 => ⟨hashAllocatedMem I, fallbackPaddedAw I⟩
  | i + 1 =>
      let c := oldCopyCursor I i
      let loaded := runtimeLoadCursor c (oldCopySourceAddr i)
      runtimeStoreCursor loaded (oldCopyDestAddr I i)
        (runtimeMloadValue c.mem c.aw (oldCopySourceAddr i))

def oldCopyStack (I : ExecutionEnv) (i : Nat) : List UInt256 :=
  [⟨160⟩, oldCopyIndexWord i, calldataSizeWord I, oldHashBitLength I,
    hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]

theorem oldCopyIndexWord_toNat (I : ExecutionEnv) (i : Nat)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hi : i ≤ oldCopyIterations I) :
    (oldCopyIndexWord i).toNat = 32 * i := by
  unfold oldCopyIndexWord
  apply ulit_toNat'
  have hdiv : oldCopyIterations I ≤ (I.calldata.size + 31) := by
    unfold oldCopyIterations
    exact Nat.div_le_self _ _
  rw [show UInt256.size = 2 ^ 256 from by decide]
  unfold maxFallbackCalldataSize at hsmall
  omega

theorem oldCopy_body_lt (I : ExecutionEnv) {i : Nat}
    (hi : i < oldCopyIterations I) : 32 * i < I.calldata.size := by
  by_contra hnot
  have hn : I.calldata.size ≤ 32 * i := by omega
  have hq : (I.calldata.size + 31) / 32 < i + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
    omega
  unfold oldCopyIterations at hi
  omega

theorem oldCopy_exit_le (I : ExecutionEnv) :
    I.calldata.size ≤ 32 * oldCopyIterations I := by
  have hdecomp := Nat.mod_add_div (I.calldata.size + 31) 32
  have hmod := Nat.mod_lt (I.calldata.size + 31) (by decide : 0 < 32)
  unfold oldCopyIterations
  omega

theorem oldCopyIndexWord_next (I : ExecutionEnv) (i : Nat)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hi : i < oldCopyIterations I) :
    oldCopyIndexWord i + ⟨32⟩ = oldCopyIndexWord (i + 1) := by
  apply u256_inj
  rw [uadd_toNat, oldCopyIndexWord_toNat I i hsmall (by omega),
    oldCopyIndexWord_toNat I (i + 1) hsmall (by omega),
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    show UInt256.size = 2 ^ 256 from by decide]
  rw [Nat.mod_eq_of_lt]
  · omega
  · have hbound := oldCopy_body_lt I hi
    unfold maxFallbackCalldataSize at hsmall
    omega

private theorem runtime_copyLoopBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i k C : Nat}
    (hi : i < oldCopyIterations I)
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8350⟩ (oldCopyStack I i) (oldCopyCursor I i).mem (oldCopyCursor I i).aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8350⟩ (oldCopyStack I (i + 1))
      (oldCopyCursor I (i + 1)).mem (oldCopyCursor I (i + 1)).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldCopyStack] at h ⊢
  have hlt : UInt256.lt (oldCopyIndexWord i) (calldataSizeWord I) = ⟨1⟩ := by
    apply ult_one
    rw [oldCopyIndexWord_toNat I i hsmall (by omega), calldataSizeWord,
      ulit_toNat' I.calldata.size hsize]
    exact oldCopy_body_lt I hi
  have rd9078 := evm_run_rfl h with [
    jumpdest, dup3, dup3, lt, push2 ⟨9070⟩,
    jumpiT (by rw [hlt]; decide) jump_9070,
    jumpdest, swap1, dup1, push1 ⟨32⟩, swap2, dup4, add ]
  have rd9079 := RD.runtimeMload rd9078 (by old_decode) (by simp)
  have rd9082 := evm_run_rfl rd9079 with [dup2, dup8, add]
  have rd9083 := RD.runtimeMstore rd9082 (by old_decode) (by simp)
  have rd8350 := evm_run_rfl rd9083 with [
    add, swap1, push2 ⟨8350⟩, jump jump_8350 ]
  exact ⟨_, _, by
    simpa [oldCopyStack, oldCopyCursor, oldCopySourceAddr, oldCopyDestAddr,
      runtimeLoadCursor, runtimeStoreCursor, oldCopyIndexWord_next I i hsmall hi,
      u256_add_comm] using rd8350⟩

private theorem runtime_copyLoopExit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i k C : Nat}
    (hi : i = oldCopyIterations I)
    (h : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8350⟩ (oldCopyStack I i) (oldCopyCursor I i).mem (oldCopyCursor I i).aw
      ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8359⟩
      [oldCopyIndexWord i, calldataSizeWord I, oldHashBitLength I,
        hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]
      (oldCopyCursor I i).mem (oldCopyCursor I i).aw
      ByteArray.empty (cA, σ) k' C' := by
  simp only [oldCopyStack] at h ⊢
  have hlt : UInt256.lt (oldCopyIndexWord i) (calldataSizeWord I) = ⟨0⟩ := by
    apply ult_zero
    rw [oldCopyIndexWord_toNat I i hsmall (by omega), hi, calldataSizeWord,
      ulit_toNat' I.calldata.size hsize]
    exact oldCopy_exit_le I
  exact ⟨_, _, evm_run_rfl h with [
    jumpdest, dup3, dup3, lt, push2 ⟨9070⟩,
    jumpiNT (by rw [hlt]), pop ]⟩

/-- Execute every 32-byte source-copy iteration. -/
theorem runtime_copyPadding {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8359⟩
      [oldCopyIndexWord (oldCopyIterations I), calldataSizeWord I, oldHashBitLength I,
        hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]
      (oldCopyCursor I (oldCopyIterations I)).mem
      (oldCopyCursor I (oldCopyIterations I)).aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := runtime_reachHashCopyLoop
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  let Inv : Nat → Nat → Prop := fun v i => i + v = oldCopyIterations I
  let exitStk : Nat → List UInt256 := fun i =>
    [oldCopyIndexWord i, calldataSizeWord I, oldHashBitLength I,
      hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]
  have hexit : ∀ i, Inv 0 i → ∀ k C,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8350⟩ (oldCopyStack I i) (oldCopyCursor I i).mem (oldCopyCursor I i).aw
        ByteArray.empty (cA, σ) k C →
      ∃ k' C', RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8359⟩ (exitStk i) (oldCopyCursor I i).mem (oldCopyCursor I i).aw
        ByteArray.empty (cA, σ) k' C' := by
    intro i hi k C h
    exact runtime_copyLoopExit hsize hsmall (by simpa [Inv] using hi) h
  have hbody : ∀ v i, Inv (v + 1) i → ∀ k C,
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨8350⟩ (oldCopyStack I i) (oldCopyCursor I i).mem (oldCopyCursor I i).aw
        ByteArray.empty (cA, σ) k C →
      ∃ i' k' C', Inv v i' ∧
        RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
          ⟨8350⟩ (oldCopyStack I i') (oldCopyCursor I i').mem (oldCopyCursor I i').aw
          ByteArray.empty (cA, σ) k' C' := by
    intro v i hi k C h
    have hit : i < oldCopyIterations I := by dsimp [Inv] at hi; omega
    obtain ⟨k', C', h'⟩ := runtime_copyLoopBody hsize hsmall hit h
    exact ⟨i + 1, k', C', by dsimp [Inv]; dsimp [Inv] at hi; omega, h'⟩
  have rd0 : RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8350⟩ (oldCopyStack I 0) (oldCopyCursor I 0).mem (oldCopyCursor I 0).aw
      ByteArray.empty (cA, σ) k C := by
    simpa [oldCopyStack, oldCopyIndexWord, oldCopyCursor] using rd
  obtain ⟨i, k', C', hi, h'⟩ :=
    RD.whileLoopCarry (code := runtimeBytecode) (ee := I) (g := g)
      (s0 := initState cA gh bl σ σ₀ g A I) (rdata := ByteArray.empty)
      (acc := (cA, σ)) (α := Nat) ⟨8350⟩ ⟨8359⟩ Inv (oldCopyStack I)
      (fun i => (oldCopyCursor I i).mem) (fun i => (oldCopyCursor I i).aw)
      exitStk hexit hbody (oldCopyIterations I) 0 (by simp [Inv]) k C rd0
  have hieq : i = oldCopyIterations I := by dsimp [Inv] at hi; omega
  subst i
  exact ⟨k', C', by simpa [exitStk] using h'⟩

end Ripemd160Old
