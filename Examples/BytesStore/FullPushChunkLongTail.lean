import Examples.BytesStore.FullPacketTag

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace BytesStore

abbrev bytesStoreOptimizedLongTailMaskedWordLocal (word len : UInt256) : UInt256 :=
  UInt256.land
    (UInt256.lnot
      (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
        (UInt256.land ⟨248⟩ (UInt256.shiftLeft len ⟨3⟩))))
    word

theorem bytesStoreOptimizedLongTailMaskedWordLocal_eq_core
    (word len : UInt256) :
    bytesStoreOptimizedLongTailMaskedWordLocal word len =
      StringStoreLite.longDataTailMaskedWord word len := by
  exact bytesStoreOptimizedLongTailMaskedWord_eq_core word len

theorem bytesStoreOptimizedLongTailMaskedWordRaw_eq_core
    (word len : UInt256) :
    UInt256.land word
      (UInt256.lnot
        (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
          (UInt256.land (UInt256.shiftLeft len ⟨3⟩) ⟨248⟩))) =
      StringStoreLite.longDataTailMaskedWord word len := by
  rw [u256_land_comm word]
  rw [u256_land_comm (UInt256.shiftLeft len ⟨3⟩) ⟨248⟩]
  exact bytesStoreOptimizedLongTailMaskedWord_eq_core word len

theorem bytesStoreX_writeBytesNewLongTailStoreFrom2749Split
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot cutoff gtFlag stride baseSlot payloadStart len ret : UInt256}
    {tail : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2749⟩
      (slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len :: ret :: tail)
      mem aw rdata (cA, τ) k C)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2767⟩
        (slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len :: ret :: tail)
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ slot
          (UInt256.land
            (uInt256OfByteArray (I.calldata.readBytes (payloadStart + stride).toNat 32))
            (UInt256.lnot
              (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
                (UInt256.land (UInt256.shiftLeft len ⟨3⟩) ⟨248⟩))))) k' C' := by
  obtain ⟨_, _, rd2749⟩ := hreach
  have rd2750 := RD.push0 rd2749 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2751 := RD.not rd2750 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2753 := RD.push1 rd2751 ⟨248⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2754 := RD.dup9 rd2753 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2756 := RD.push1 rd2754 ⟨3⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2757 := RD.shl rd2756 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2758 := RD.and rd2757 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2759 := RD.shr rd2758 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2760 := RD.not rd2759 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2761 := RD.dup5 rd2760 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2762 := RD.dup8 rd2761 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2763 := RD.add rd2762 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2764 := RD.calldataload rd2763 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2765 := RD.and rd2764 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2766 := RD.dup2 rd2765 (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd2767₀⟩ := RD.sstore rd2766 hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  have hpc :
      ({ val := 2749 } + { val := 1 } + { val := 1 } + UInt256.ofNat 2 +
          { val := 1 } + UInt256.ofNat 2 + { val := 1 } + { val := 1 } +
          { val := 1 } + { val := 1 } + { val := 1 } + { val := 1 } +
          { val := 1 } + { val := 1 } + { val := 1 } + { val := 1 } +
          { val := 1 } : UInt256) = ⟨2767⟩ := by
    native_decide
  exact ⟨_, _, by
    simpa [hpc, initState]
      using rd2767₀⟩

theorem bytesStoreX_writeBytesNewLongTailStoreFrom2749CoreSplit
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot cutoff gtFlag stride baseSlot payloadStart len ret : UInt256}
    {tail : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2749⟩
      (slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len :: ret :: tail)
      mem aw rdata (cA, τ) k C)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2767⟩
        (slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len :: ret :: tail)
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ slot
          (StringStoreLite.longDataTailMaskedWord
            (bytesStoreCalldataLongDataWord I payloadStart stride 0) len)) k' C' := by
  obtain ⟨_, _, htail⟩ :=
    bytesStoreX_writeBytesNewLongTailStoreFrom2749Split
      (hperm := hperm) (hreach := hreach) (hov := hov)
  exact ⟨_, _, by
    simpa [bytesStoreCalldataLongDataWord,
      StringStoreLite.longDataWordsLoopStride,
      bytesStoreOptimizedLongTailMaskedWordRaw_eq_core]
      using htail⟩

theorem bytesStoreX_writeBytesNewLongDataWordsLoopDoneTailSplit
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride baseSlot payloadStart len ret : UInt256}
    {tail : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2707⟩
      (idx :: slot :: cutoff :: gtFlag :: stride :: baseSlot :: payloadStart :: len ::
        ret :: tail)
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (htail : UInt256.isZero (UInt256.lt cutoff len) = ⟨0⟩)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret tail mem aw rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner τ slot
            (StringStoreLite.longDataTailMaskedWord
              (bytesStoreCalldataLongDataWord I payloadStart stride 0) len))
          baseSlot (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  obtain ⟨_, _, rd2707⟩ := hreach
  have hdoneCond : UInt256.isZero (UInt256.lt idx cutoff) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have rd2739 := evm_run rd2707 with [
    jumpdest, dup3, dup2, lt, iszero, push2 ⟨2739⟩,
    jumpiT hdoneCond (by native_decide)]
  have rd2749 := evm_run rd2739 with [
    jumpdest, pop, dup7, dup3, lt, iszero, push2 ⟨2767⟩,
    jumpiNT htail]
  have htailStore := bytesStoreX_writeBytesNewLongTailStoreFrom2749CoreSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (slot := slot)
    (cutoff := cutoff) (gtFlag := gtFlag) (stride := stride)
    (baseSlot := baseSlot) (payloadStart := payloadStart) (len := len)
    (ret := ret) (tail := tail) (mem := mem) (aw := aw) (rdata := rdata)
    hperm ⟨_, _, rd2749⟩ hov
  obtain ⟨_, _, rd2767⟩ := htailStore
  have rd2779pre := evm_run rd2767 with [
    jumpdest, pop, pop, push1 ⟨1⟩, dup6, push1 ⟨1⟩, shl, add, dup4]
  obtain ⟨_, _, rd2779₀⟩ := rd2779pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd2779⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨2779⟩
        (gtFlag :: stride :: baseSlot :: payloadStart :: len :: ret :: tail)
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner τ slot
            (StringStoreLite.longDataTailMaskedWord
              (bytesStoreCalldataLongDataWord I payloadStart stride 0) len))
          baseSlot (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
    have hpc :
        ({ val := 2767 } + { val := 1 } + { val := 1 } + UInt256.ofNat 2 +
            { val := 1 } + UInt256.ofNat 2 + { val := 1 } + { val := 1 } +
            { val := 1 } + { val := 1 } + { val := 1 } : UInt256) = ⟨2779⟩ := by
      native_decide
    have hshift1 : UInt256.shiftLeft len ⟨1⟩ = UInt256.mul len ⟨2⟩ := by
      apply u256_inj
      unfold UInt256.shiftLeft
      rw [if_neg (by decide : ¬ (⟨1⟩ : UInt256).val ≥ 256)]
      show (len.toNat <<< 1) % UInt256.size = (len.toNat * 2) % UInt256.size
      rw [Nat.shiftLeft_eq]
    exact ⟨_, _, by
      simpa [hpc, hshift1, sstoreAccountMap, initState, u256_add_comm len len]
        using rd2779₀⟩
  exact ⟨_, _, evm_run rd2779 with [
    pop, pop, pop, pop, pop,
    raw jump (by native_decide) hret (by omega)]⟩

theorem bytesStoreX_writeBytesNewLongTailFromWriteBranchSplit
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2643⟩
      (slot :: payloadStart :: len :: ret :: tail) mem aw rdata (cA, τ) k C)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (hret : (D_J bytesStoreBytecode 0).contains ret = true)
    (hov : tail.length + 16 ≤ 1024) :
    ∃ k' C',
      RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret tail
        (wordAt0Mem slot mem) (StringStoreLite.clearCurrentHashAw aw) rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (bytesStoreCalldataLongDataForwardFrom I.codeOwner τ
              (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
            (StringStoreLite.longDataWordsLoopSlot
              (bytesLikeDataBase slot) (len.toNat / 32))
            (StringStoreLite.longDataTailMaskedWord
              (bytesStoreCalldataLongDataWord I payloadStart
                (StringStoreLite.longDataWordsLoopStride
                  (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
          slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloopEntry := bytesStoreX_writeBytesNewLongReachLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := τ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ret) (tail := tail) (mem := mem) (aw := aw)
    (rdata := rdata)
    hreach hlong (by omega)
  have hloop := bytesStoreX_writeBytesNewLongDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := τ) (idx := (⟨0⟩ : UInt256))
    (slot := bytesLikeDataBase slot)
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := (⟨0⟩ : UInt256)) (baseSlot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ret) (tail := tail) (mem := wordAt0Mem slot mem)
    (aw := StringStoreLite.clearCurrentHashAw aw) (rdata := rdata)
    (fuel := len.toNat / 32)
    hperm hloopEntry
    (fun i hi => StringStoreLite.longDataLoopContinue len hi)
    hov
  exact bytesStoreX_writeBytesNewLongDataWordsLoopDoneTailSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (τ := bytesStoreCalldataLongDataForwardFrom I.codeOwner τ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I (len.toNat / 32))
    (idx := StringStoreLite.longDataWordsLoopIndex (⟨0⟩ : UInt256) (len.toNat / 32))
    (slot := StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32))
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := StringStoreLite.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
    (baseSlot := slot) (payloadStart := payloadStart) (len := len) (ret := ret)
    (tail := tail) (mem := wordAt0Mem slot mem)
    (aw := StringStoreLite.clearCurrentHashAw aw) (rdata := rdata)
    hperm hloop
    (StringStoreLite.longDataLoopDone len)
    (StringStoreLite.longDataTail len htailMod)
    hret hov

theorem bytesStoreClearCurrentHashAw3 :
    StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3) = UInt256.ofNat 3 := by
  native_decide

theorem bytesStoreX_pushChunkReturnFromHelperRetSplit
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot payloadStart len sel : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1617⟩
      [slot, ⟨0⟩, len, payloadStart, ⟨263⟩, sel]
      mem aw rdata (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [(σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)), sel]
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd1617⟩ := hreach
  have rd1622pre := evm_run rd1617 with [jumpdest, pop, pop, push1 ⟨1⟩]
  obtain ⟨_, _, rd1623₀⟩ := rd1622pre.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1623⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1623⟩
        [(σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨1⟩ ⟨0⟩)),
          len, payloadStart, ⟨263⟩, sel]
        mem aw rdata (cA, σ) k C := by
    exact ⟨_, _, by simpa [initState] using rd1623₀⟩
  exact ⟨_, _, evm_run rd1623 with [
    swap3, swap2, pop, pop, jump (by native_decide)]⟩

end BytesStore
