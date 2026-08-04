import Examples.Ripemd160Old.HashPaddedInvariant

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Ripemd160Old

open Ripemd160

private theorem runtimeStoreCursor_read64 {c : RuntimeMemCursor} {addr value : UInt256}
    (hmem : 96 ≤ c.mem.size) (haddr : 96 ≤ addr.toNat)
    (hgap : addr.toNat - c.mem.size < USize.size) :
    (runtimeStoreCursor c addr value).mem.readWithPadding 64 32 =
      c.mem.readWithPadding 64 32 := by
  unfold runtimeStoreCursor runtimeMstoreMem
  exact toByteArray_write_read_below_len_of_gap value c.mem addr.toNat 64 32
    hmem haddr (by decide) (by decide) hgap

private theorem runtimeStore8Cursor_read64 {c : RuntimeMemCursor} {addr value : UInt256}
    (haddrIn : addr.toNat + 1 ≤ c.mem.size)
    (haddr : 96 ≤ addr.toNat) :
    (runtimeStore8Cursor c addr value).mem.readWithPadding 64 32 =
      c.mem.readWithPadding 64 32 := by
  unfold runtimeStore8Cursor runtimeMstore8Mem
  exact write_read_below_len_from
    (⟨#[UInt8.ofNat value.toNat]⟩ : ByteArray) c.mem
    0 addr.toNat 1 64 32 (by decide) (by change 1 ≤ 1; omega)
    haddrIn haddr (by decide) (by decide)

theorem oldCopyCursor_read64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i : Nat}
    (hi : i ≤ oldCopyIterations I) :
    (oldCopyCursor I i).mem.readWithPadding 64 32 =
      (hashScratchPtr I).toByteArray := by
  induction i with
  | zero => simpa [oldCopyCursor, hashScratchPtr] using hashAllocatedMem_read64 I
  | succ i ih =>
      have hip : i ≤ oldCopyIterations I := by omega
      have hit : i < oldCopyIterations I := by omega
      obtain ⟨_, hcover, hsource, _⟩ := oldCopyCursor_invariant I hsmall hip
      have hload := (hsource i hit).load
      have hdest := oldCopyDest_toNat I i hsmall hip
      have hmem : 96 ≤ (oldCopyCursor I i).mem.size := by
        apply le_trans (b := (hashPadPtr I).toNat + 32 * i)
        · rw [hashPadPtr_toNat I hsmall]
          omega
        · exact hcover
      have hgap : (oldCopyDestAddr I i).toNat -
          (runtimeLoadCursor (oldCopyCursor I i) (oldCopySourceAddr i)).mem.size <
            USize.size := by
        simp only [runtimeLoadCursor]
        rw [hdest]
        simp [Nat.sub_eq_zero_of_le hcover, USize.size]
      rw [oldCopyCursor, hload]
      apply Eq.trans (runtimeStoreCursor_read64 hmem (by
        rw [hdest, hashPadPtr_toNat I hsmall]
        omega) hgap)
      exact ih hip

theorem oldZeroCursor_read64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {i : Nat}
    (hi : i ≤ oldZeroIterations I) :
    (oldZeroCursor I i).mem.readWithPadding 64 32 =
      (hashScratchPtr I).toByteArray := by
  induction i with
  | zero =>
      simpa [oldZeroCursor] using oldCopyCursor_read64 I hsmall
        (le_refl (oldCopyIterations I))
  | succ i ih =>
      have hip : i ≤ oldZeroIterations I := by omega
      obtain ⟨_, hcover, _, _⟩ := oldZeroCursor_invariant I hsmall hip
      have hdest := oldZeroDest_toNat I i hsmall hip
      have hmem : 96 ≤ (oldZeroCursor I i).mem.size := by
        apply le_trans (b := (hashPadPtr I).toNat + oldZeroIndex I i)
        · rw [hashPadPtr_toNat I hsmall]
          omega
        · exact hcover
      have hgap : (hashPadPtr I + oldZeroIndexWord I i).toNat -
          (oldZeroCursor I i).mem.size < USize.size := by
        rw [hdest]
        simp [Nat.sub_eq_zero_of_le hcover, USize.size]
      rw [oldZeroCursor]
      apply Eq.trans (runtimeStoreCursor_read64 hmem (by
        rw [hdest, hashPadPtr_toNat I hsmall]
        omega) hgap)
      exact ih hip

theorem oldLengthCursor_read64 (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) {q : Nat} (hq : q ≤ 8) :
    (oldLengthCursor I q).mem.readWithPadding 64 32 =
      (hashScratchPtr I).toByteArray := by
  have hz := oldZeroCursor_invariant I hsmall (le_refl (oldZeroIterations I))
  have hzeroRead := oldZeroCursor_read64 I hsmall
    (le_refl (oldZeroIterations I))
  have hmarkerEnd := oldMarkerAddr_end_le_scratch I hsmall
  have hzeroCover : (hashScratchPtr I).toNat ≤
      (oldZeroCursor I (oldZeroIterations I)).mem.size := by
    unfold hashScratchPtr
    rw [hashNewFreePtr_toNat I hsmall]
    simpa [oldZeroIndex_at_end I] using hz.2.1
  have hmarkerIn : (oldMarkerAddr I).toNat + 1 ≤
      (oldZeroCursor I (oldZeroIterations I)).mem.size :=
    le_trans hmarkerEnd hzeroCover
  have hmarkerRead : (oldMarkerCursor I).mem.readWithPadding 64 32 =
      (hashScratchPtr I).toByteArray := by
    unfold oldMarkerCursor
    rw [runtimeStore8Cursor_read64 hmarkerIn (by
      rw [oldMarkerAddr_toNat I hsmall, hashPadPtr_toNat I hsmall]
      omega)]
    exact hzeroRead
  induction q with
  | zero => exact hmarkerRead
  | succ q ih =>
      have hq8 : q < 8 := by omega
      have hb := oldLengthCursor_bounds I hsmall (q := q) (by omega)
      have hend := oldLengthAddr_end_le_scratch I hsmall hq8
      have hin : (oldLengthAddr I q).toNat + 1 ≤
          (oldLengthCursor I q).mem.size := le_trans hend hb.2.2
      simp only [oldLengthCursor]
      rw [runtimeStore8Cursor_read64 hin (by
        rw [oldLengthAddr_toNat I hsmall hq8, hashPadPtr_toNat I hsmall]
        omega)]
      exact ih (by omega)

theorem oldLengthCursor_mload64Value (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    runtimeMloadValue (oldLengthCursor I 8).mem (oldLengthCursor I 8).aw ⟨64⟩ =
      hashScratchPtr I := by
  have hb := oldLengthCursor_bounds I hsmall (q := 8) (by decide)
  have hscratch96 : 96 ≤ (hashScratchPtr I).toNat := by
    unfold hashScratchPtr
    rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall]
    omega
  have hawMul : ((oldLengthCursor I 8).aw * ⟨32⟩).toNat =
      32 * (oldLengthCursor I 8).aw.toNat := by
    rw [umul_toNat]
    · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      omega
    · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
        show UInt256.size = 2 ^ 256 from by decide]
      omega
  unfold runtimeMloadValue
  rw [if_neg]
  · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      oldLengthCursor_read64 I hsmall (by decide),
      fromByteArrayBigEndian_toByteArray]
    exact u256_ofNat_toNat _
  · push Not
    constructor
    · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      have := hb.2.2
      omega
    · intro h
      change ((oldLengthCursor I 8).aw * ⟨32⟩).toNat ≤ 64 at h
      rw [hawMul] at h
      have hactive := hb.2.1
      unfold hashScratchPtr at hactive
      rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall] at hactive
      omega

theorem oldLengthCursor_mload64Aw (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    runtimeMloadAw (oldLengthCursor I 8).aw ⟨64⟩ = (oldLengthCursor I 8).aw := by
  have hb := oldLengthCursor_bounds I hsmall (q := 8) (by decide)
  unfold runtimeMloadAw
  change UInt256.ofNat (max (oldLengthCursor I 8).aw.toNat 3) = _
  rw [max_eq_left]
  · exact u256_ofNat_toNat _
  · have hactive := hb.2.1
    unfold hashScratchPtr at hactive
    rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall] at hactive
    omega

noncomputable def oldScratchCursor (I : ExecutionEnv) : RuntimeMemCursor :=
  runtimeStoreCursor (oldLengthCursor I 8) ⟨64⟩ (hashScratchNewFreePtr I)

theorem oldScratchCursor_padded (I : ExecutionEnv)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I (oldScratchCursor I) 0 := by
  have hp := oldLengthCursor_padded I hsmall
  have hmem96 : 96 ≤ (oldLengthCursor I 8).mem.size := by
    apply le_trans (b := (hashScratchPtr I).toNat)
    · change 96 ≤ (hashNewFreePtr I).toNat
      rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall]
      omega
    · exact hp.frontier
  have hsize : (oldScratchCursor I).mem.size = (oldLengthCursor I 8).mem.size := by
    unfold oldScratchCursor runtimeStoreCursor runtimeMstoreMem
    exact toByteArray_write32_size_of_le _ _ 64 _ _ rfl (by omega) (by omega)
  have haw : (oldScratchCursor I).aw = (oldLengthCursor I 8).aw := by
    unfold oldScratchCursor runtimeStoreCursor runtimeMstoreAw
    change UInt256.ofNat (max (oldLengthCursor I 8).aw.toNat 3) = _
    rw [max_eq_left]
    · exact u256_ofNat_toNat _
    · have hactive := hp.activeCover
      unfold hashScratchPtr at hactive
      rw [hashNewFreePtr_toNat I hsmall, hashPadPtr_toNat I hsmall] at hactive
      omega
  constructor
  · simpa [haw] using hp.awSmall
  · simpa [haw] using hp.activeCover
  · simpa [hsize] using hp.frontier
  · intro p hpadded
    have hread : (hashPadPtr I).toNat + p + 1 ≤
        (oldLengthCursor I 8).mem.size := by
      apply le_trans (b := (hashScratchPtr I).toNat)
      · unfold hashScratchPtr
        rw [hashNewFreePtr_toNat I hsmall]
        omega
      · exact hp.frontier
    unfold oldScratchCursor runtimeStoreCursor runtimeMstoreMem
    change ((hashScratchNewFreePtr I).toByteArray.write 0
      (oldLengthCursor I 8).mem 64 32).readWithPadding
        ((hashPadPtr I).toNat + p) 1 = _
    rw [write32_read_above_len _ _ 64 ((hashPadPtr I).toNat + p) 1
      (by rw [toByteArray_size]) (by omega)
      (by rw [hashPadPtr_toNat I hsmall]; omega) hread (by decide) (by decide)]
    exact hp.read p hpadded

def oldBlockLoopStack (I : ExecutionEnv) (blk : UInt256)
    (h : RuntimeChain) : List UInt256 :=
  [hashPadPtr I, hashPaddedLengthWord I, hashScratchPtr I, blk,
    h.h0, h.h4, h.h3, h.h2, h.h1, ⟨254⟩]

/-- Allocate the shared 832-byte scratch layout and reach the old block loop. -/
theorem runtime_reachBlockLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8533⟩ (oldBlockLoopStack I ⟨0⟩ runtimeInitialChain)
      (oldScratchCursor I).mem (oldScratchCursor I).aw
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd8484⟩ := runtime_writePaddingTail
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  have rd8516pre := evm_run_rfl rd8484 with [
    push4 ⟨0x67452301⟩, swap1, push4 ⟨0xefcdab89⟩, swap3,
    push4 ⟨0x98badcfe⟩, swap3, push4 ⟨0x10325476⟩, swap3,
    push4 ⟨0xc3d2e1f0⟩, swap3, push1 ⟨64⟩ ]
  have rd8517 := RD.runtimeMload rd8516pre (by old_decode) (by simp)
  rw [oldLengthCursor_mload64Value I hsmall,
    oldLengthCursor_mload64Aw I hsmall] at rd8517
  have rd8530pre := evm_run_rfl rd8517 with [
    swap1, push1 ⟨160⟩, dup1, push2 ⟨512⟩, dup5, add, add, add,
    push1 ⟨64⟩ ]
  have rd8531 := RD.runtimeMstore rd8530pre (by old_decode) (by simp)
  have halloc :
      hashScratchPtr I + ⟨512⟩ + ⟨160⟩ + ⟨160⟩ =
        hashScratchNewFreePtr I := by
    unfold hashScratchNewFreePtr
    rw [u256_add_assoc, u256_add_assoc]
    congr 1
  rw [halloc] at rd8531
  have rd8533 := evm_run_rfl rd8531 with [push0, swap3]
  exact ⟨_, _, by
    simpa [oldScratchCursor, oldBlockLoopStack, runtimeInitialChain] using rd8533⟩

end Ripemd160Old
