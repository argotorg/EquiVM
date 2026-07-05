import Examples.BytesStoreLite.FullSetChunkByteDecode

/-!
# BytesStoreLite — `setChunkByte(uint256,uint256,uint8)` success paths

This module keeps the heavier successful-write/runtime equivalence proof separate from the
decoder and revert wrappers.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStoreLite

theorem bytesStoreLiteU256HighMulShiftRightOfLt256
    {w : UInt256} (hw : w.toNat < 256) :
    UInt256.shiftRight (UInt256.mul w (UInt256.shiftLeft ⟨1⟩ ⟨248⟩)) ⟨248⟩ = w := by
  rw [bytesStoreLiteShiftRight248_eq_div_scale]
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat, bytesStoreLiteShiftLeftOne248_toNat]
  have hlt : w.toNat * 2 ^ 248 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc w.toNat * 2 ^ 248 < 256 * 2 ^ 248 :=
        Nat.mul_lt_mul_of_pos_right hw (by positivity)
      _ = 2 ^ 256 := by
        rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_add]
        norm_num
  rw [Nat.mod_eq_of_lt hlt]
  rw [Nat.mul_comm]
  rw [Nat.mul_div_right _ (by positivity : 0 < 2 ^ 248)]

theorem bytesStoreLiteSetChunkByteValueHighMulShiftRightLocal
    {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.shiftRight
      (UInt256.mul (bytesStoreLiteSetChunkByteValueWord I) (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ =
      bytesStoreLiteSetChunkByteValueWord I := by
  exact bytesStoreLiteU256HighMulShiftRightOfLt256
    (by simpa [EVM.twoPow] using hcanon)

theorem bytesStoreLiteX_setChunkByteShortWriteReturnDecodedLengthLen_of_post_bound
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I).toNat)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (_hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
    (bytesStoreLiteSetChunkByteShortStoredWord σ I)
  have hheaderPost :
      bytesStoreLiteSetChunkByteHeaderWord σ' I =
        bytesStoreLiteSetChunkByteShortStoredWord σ I := by
    dsimp [σ', bytesStoreLiteSetChunkByteHeaderWord]
    exact sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
      (bytesStoreLiteSetChunkByteSlot I)
      (bytesStoreLiteSetChunkByteShortStoredWord σ I) hacc
  have hflagPost :
      UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨1⟩ = ⟨0⟩ := by
    rw [hheaderPost, bytesStoreLiteSetChunkByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
    exact ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hltLen]
    native_decide
  have hlenPost :
      UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨2⟩) ⟨127⟩ =
        len := by
    rw [hheaderPost, bytesStoreLiteSetChunkByteShortStoredWord_shortLen_eq
      (σ := σ) (I := I) (len := len) hshort hbound]
    exact hlen.symm
  have hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord σ' I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflagPost, hlenPost] using hvalidLen
  have hread := bytesStoreLiteX_setChunkByteShortWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag
    (by simpa [σ'] using hchunkBoundPost)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    hperm
  simpa [σ', hlenPost] using hread

theorem bytesStoreLiteX_setChunkByteShortReadReturnToWrapperStored
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I)) k C)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hacc : σ.find? I.codeOwner = some acc) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨301⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
    (bytesStoreLiteSetChunkByteShortStoredWord σ I)
  have hheaderPost :
      ((σ'.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)) =
          bytesStoreLiteSetChunkByteShortStoredWord σ I := by
    simpa [σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I) hacc
  have hflagPost :
      UInt256.land (bytesStoreLiteSetChunkByteShortStoredWord σ I) ⟨1⟩ = ⟨0⟩ := by
    rw [bytesStoreLiteSetChunkByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ I) =
        bytesStoreLiteSetChunkByteValueWord I :=
    bytesStoreLiteSetChunkByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul
          (UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ I))
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetChunkByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetChunkByteValueHighMulShiftRightLocal hcanon
  obtain ⟨_, _, rd905⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetChunkByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd919 := evm_run rd905 with [
    jumpdest, dup2, lt, push2 ⟨919⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd921 := evm_run rd919 with [jumpdest, dup2]
  obtain ⟨_, _, rd922₀⟩ := rd921.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd922⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨922⟩
        [bytesStoreLiteSetChunkByteShortStoredWord σ I,
          bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          ⟨0⟩, bytesStoreLiteSetChunkByteValueWord I,
          bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
    exact ⟨_, _, by simpa [σ', initState, hheaderPost] using rd922₀⟩
  have rd948 := evm_run rd922 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨948⟩,
    jumpiT (by
      rw [u256_land_comm, hflagPost]
      decide)
      (by native_decide)]
  have rd950 := evm_run rd948 with [jumpdest, swap1]
  obtain ⟨_, _, rd951₀⟩ := rd950.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd951⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨951⟩
        [bytesStoreLiteSetChunkByteShortStoredWord σ I,
          bytesStoreLiteSetChunkByteIndexWord I, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I,
          bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C := by
    exact ⟨_, _, by simpa [σ', initState, hheaderPost] using rd951₀⟩
  have rd957 := evm_run rd951 with [
    push1 ⟨1⟩, push1 ⟨248⟩, shl, swap2]
  have rd958 := RD.byte rd957 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := evm_run rd958 with [
    mul, push1 ⟨248⟩, shr,
    swap5, swap4, pop, pop, pop, pop, jump (by native_decide)]
  exact ⟨_, _, by simpa [σ', hbyte] using rd301⟩

theorem bytesStoreLiteX_setChunkByteLongWriteReturnDecodedLengthLen_of_post_bound
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I).toNat)
    (hlenPost : len = UInt256.div
      (bytesStoreLiteSetChunkByteHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (_hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (_hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨905⟩
      [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I, ⟨0⟩,
        bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))) (UInt256.ofNat 3)
      ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  have hread := bytesStoreLiteX_setChunkByteLongWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag
    (by simpa [σ'] using hchunkBoundPost)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hvalidPost)
    hperm
  simpa [σ', hlenPost] using hread

theorem bytesStoreLiteX_setChunkByteShortSuccessReturn_of_post_bound
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I).toNat)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetChunkByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
    (bytesStoreLiteSetChunkByteShortStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setChunkByteReachLengthDecoder (g := g) hreach hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    simpa [hlen] using h1270Raw
  have hread := bytesStoreLiteX_setChunkByteShortWriteReturnDecodedLengthLen_of_post_bound
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (acc := acc)
    h1270 hchunkBoundPost hlen hshort hbound hflag hvalid hperm hacc
  have hheader : header' = bytesStoreLiteSetChunkByteShortStoredWord σ I := by
    simpa [header', σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ I) hacc
  have hflag' : UInt256.land header' ⟨1⟩ = ⟨0⟩ := by
    rw [hheader, bytesStoreLiteSetChunkByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I) header' =
        bytesStoreLiteSetChunkByteValueWord I := by
    rw [hheader]
    exact bytesStoreLiteSetChunkByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I) header')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetChunkByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetChunkByteValueHighMulShiftRightLocal hcanon
  have h301 := bytesStoreLiteX_setChunkByteShortReadReturnToWrapperStored
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (acc := acc)
    hread hcanon hshort hbound hflag hacc
  have hret := bytesStoreLiteX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetChunkByteValueWord I)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 _ (wordAt0Mem_size_96 _ solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _ solcFreePtrMem_size)
      (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))
    h301
  simpa [σ', bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreLiteX_setChunkByteLongSuccessReturn_of_post_bound
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I).toNat)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreLiteSetChunkByteHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetChunkByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  let dataWord' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreLiteSetChunkByteLongDataSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setChunkByteReachLengthDecoder (g := g) hreach hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    simpa [hlen] using h1270Raw
  have hread := bytesStoreLiteX_setChunkByteLongWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len)
    h1270 hbound hflag hchunkBoundPost hflagPost hvalidPost hperm
  have hheader : header' = bytesStoreLiteSetChunkByteHeaderWord σ' I := by
    rfl
  have hdata : dataWord' = bytesStoreLiteSetChunkByteLongStoredWord σ I := by
    simpa [dataWord', σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetChunkByteLongWordIndex I) dataWord' =
        bytesStoreLiteSetChunkByteValueWord I := by
    rw [hdata]
    exact bytesStoreLiteSetChunkByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetChunkByteLongWordIndex I) dataWord')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetChunkByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetChunkByteValueHighMulShiftRightLocal hcanon
  have h301 := bytesStoreLiteX_setChunkByteLongReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := lenPost) (header := header')
    (dataWord := dataWord')
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (by simpa [hlenPost] using hread) hboundPost (by rfl)
    (by simpa [hheader, σ'] using hflagPost) (by rfl) hbyte
  have hret := bytesStoreLiteX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetChunkByteValueWord I)
    (mem := wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
      (wordAt0Mem (⟨1⟩ : UInt256)
        (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
          (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem))))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size))))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
      (bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size))
        (bytesStoreLiteWordAt0Mem_read64 _
          (wordAt0Mem_size_96 _ solcFreePtrMem_size)
          (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))))
    h301
  simpa [σ', bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreLiteX_setChunkByteLongShortSuccessReturn_of_post_bound
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1226⟩
      [bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
        bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I).toNat)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStoreLiteSetChunkByteHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetChunkByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreLiteSetChunkByteSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setChunkByteReachLengthDecoder (g := g) hreach hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    simpa [hlen] using h1270Raw
  have hread := bytesStoreLiteX_setChunkByteLongWriteReturnDecodedShortLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len)
    h1270 hbound hflag hchunkBoundPost hflagPost hvalidPost hperm
  have hheaderStored : header' = bytesStoreLiteSetChunkByteLongStoredWord σ I := by
    by_cases hEq : bytesStoreLiteSetChunkByteSlot I =
        bytesStoreLiteSetChunkByteLongDataSlot I
    · simpa [header', σ', hEq] using
        sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
          (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ I) hacc
    · have hheaderOld :
          bytesStoreLiteSetChunkByteHeaderWord σ' I =
            bytesStoreLiteSetChunkByteHeaderWord σ I := by
        simpa [σ', bytesStoreLiteSetChunkByteLongDataSlot] using
          bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
            (σ := σ) (I := I) (baseSlot := bytesStoreLiteSetChunkByteSlot I)
            (idx := bytesStoreLiteSetChunkByteIndexWord I)
            (val := bytesStoreLiteSetChunkByteLongStoredWord σ I)
            (by simpa [bytesStoreLiteSetChunkByteLongDataSlot] using hEq)
            (by rfl)
      have hzeroOld :
          UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ = ⟨0⟩ := by
        simpa [σ', header', hheaderOld] using hflagPost
      exact False.elim (hflag hzeroOld)
  have hvalid0 :
      UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlenPost, hflagPost] using hvalidPost
  have hshortPost : lenPost.toNat < 32 :=
    solidityShortBytesValid_lt32 hvalid0
  have hidxLt32 : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 32 := by
    exact lt_trans hboundPost hshortPost
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I) header' =
        bytesStoreLiteSetChunkByteValueWord I := by
    rw [hheaderStored]
    exact bytesStoreLiteSetChunkByteLongStoredWord_byteAt_index_of_lt32
      (σ := σ) (I := I) hcanon hidxLt32
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetChunkByteIndexWord I) header')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetChunkByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetChunkByteValueHighMulShiftRightLocal hcanon
  have h301 := bytesStoreLiteX_setChunkByteShortReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := lenPost) (header := header')
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (by simpa [hlenPost] using hread) hboundPost (by rfl)
    (by simpa [header', σ'] using hflagPost) hbyte
  have hret := bytesStoreLiteX_returnUInt8_301OfMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetChunkByteValueWord I)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size))
      (bytesStoreLiteWordAt0Mem_read64 _
        (wordAt0Mem_size_96 _ solcFreePtrMem_size)
        (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)))
    h301
  simpa [σ', bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreLiteSetChunkByteShortSuccessRuntime_of_post_bound
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)) I).toNat)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hret := bytesStoreLiteX_setChunkByteShortSuccessReturn_of_post_bound
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (acc := accEvm)
    hreachBody hcanon hchunkBound hchunkBoundPost hlen hshort hbound hflag hvalid hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteSlot I)
    (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hpostAccountsPre :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreLiteAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)
  have hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      (bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I))
        (I := I) howner hpostAccountsPre).symm
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body
        (.returned
          (bytesStoreLiteSetChunkByteFrame I)
          evmSolm1 (some (bytesStoreLiteSetChunkByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreLiteSetChunkByteFrame] using
      bytesStoreLiteSetChunkByteShortBodyReturns_of_post_readback
        (evm := evmSolm0) (σ := σ_evm) (I := I) (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)) I)
        (len := len) (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hchunkBound hloadChunksPost hchunkBoundPost hloadHeader
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hshort hbound hflag hvalid
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I))
        evmSolm1.accountMap := by
    exact hpostAccountsPre
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetChunkByteValueWord I) hcanon))

theorem bytesStoreLiteSetChunkByteShortReturnOobChunksLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hchunkBoundPost :
      ¬ (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)) I).toNat)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreLiteX_setChunkByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h1270Raw
  have hrev := bytesStoreLiteX_setChunkByteShortWriteReturnOobChunksLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h1270 hbound hflag hchunkBoundPost hperm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteSlot I)
    (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreLiteAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkByteSlot I)
        (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)
  have hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      (bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I))
        (I := I) howner hpostAccounts).symm
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteSetChunkByteShortBodyReturnRevertsOfPostChunksLength
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
            (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)) I)
        (len := len)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hchunkBound hloadChunksPost hchunkBoundPost hloadHeader
        hcanon hlen hshort hbound hflag
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkByteLongSuccessRuntime_of_post_bound
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I).toNat)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreLiteSetChunkByteHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hret := bytesStoreLiteX_setChunkByteLongSuccessReturn_of_post_bound
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost) (acc := accEvm)
    hreachBody hcanon hchunkBound hchunkBoundPost hlenPost hflagPost hvalidPost
    hlen hbound hboundPost hflag hvalid hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteLongDataSlot I) =
        bytesStoreLiteSetChunkByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hpostAccountsPre :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreLiteAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      (bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccountsPre).symm
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccountsPre
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body
        (.returned
          (bytesStoreLiteSetChunkByteFrame I)
          evmSolm1 (some (bytesStoreLiteSetChunkByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreLiteSetChunkByteFrame] using
      bytesStoreLiteSetChunkByteLongBodyReturns_of_post_readback
        (evm := evmSolm0) (σ := σ_evm) (I := I) (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (len := len) (lenPost := lenPost) (acc := accSolm)
        (postHeaderWord := bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hchunkBound hloadChunksPost hchunkBoundPost hloadHeader hloadData
        hloadHeaderPost
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hlenPost hbound hboundPost hflag hflagPost hvalid hvalidPost
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    exact hpostAccountsPre
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetChunkByteValueWord I) hcanon))

theorem bytesStoreLiteSetChunkByteLongReturnOobChunksLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hchunkBoundPost :
      ¬ (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I).toNat)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreLiteX_setChunkByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h1270Raw
  have hrev := bytesStoreLiteX_setChunkByteLongWriteReturnOobChunksLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h1270 hbound hflag hchunkBoundPost hperm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteLongDataSlot I) =
        bytesStoreLiteSetChunkByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreLiteAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      (bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts).symm
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteSetChunkByteLongBodyReturnRevertsOfPostChunksLength
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (len := len)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hchunkBound hloadChunksPost hchunkBoundPost hloadHeader hloadData
        hcanon hlen hbound hflag hvalid
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkByteLongReturnOobLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I).toNat)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreLiteSetChunkByteHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreLiteX_setChunkByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h1270Raw
  have hread := bytesStoreLiteX_setChunkByteLongWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h1270 hbound hflag hchunkBoundPost hflagPost hvalidPost hperm
  have hrev := bytesStoreLiteX_setChunkByteReturnOobLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
    (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
      (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := lenPost)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (by simpa [hlenPost] using hread) hboundPost
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteLongDataSlot I) =
        bytesStoreLiteSetChunkByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreLiteAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      (bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts).symm
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteSetChunkByteLongBodyReturnRevertsOfPostLongLength
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hchunkBound hloadChunksPost hchunkBoundPost hloadHeader hloadData
        hloadHeaderPost hcanon hlen hlenPost hbound hboundPost hflag hvalid hflagPost
        hvalidPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkByteLongReturnShortOobLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I).toNat)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStoreLiteSetChunkByteHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreLiteX_setChunkByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h1270Raw
  have hread := bytesStoreLiteX_setChunkByteLongWriteReturnDecodedShortLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h1270 hbound hflag hchunkBoundPost hflagPost hvalidPost hperm
  have hrev := bytesStoreLiteX_setChunkByteReturnOobLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
    (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
      (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := lenPost)
    (mem := wordAt0Mem (⟨1⟩ : UInt256)
      (wordAt0Mem (bytesStoreLiteSetChunkByteSlot I)
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem)))
    (by simpa [hlenPost] using hread) hboundPost
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteLongDataSlot I) =
        bytesStoreLiteSetChunkByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreLiteAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      (bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts).symm
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteSetChunkByteLongBodyReturnRevertsOfPostShortLength
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hchunkBound hloadChunksPost hchunkBoundPost hloadHeader hloadData
        hloadHeaderPost hcanon hlen hlenPost hbound hboundPost hflag hvalid hflagPost
        hvalidPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkByteLongReturnShortSuccessRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I).toNat)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStoreLiteSetChunkByteHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hret := bytesStoreLiteX_setChunkByteLongShortSuccessReturn_of_post_bound
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    (acc := accEvm)
    hreachBody hcanon hchunkBound hchunkBoundPost hlenPost hflagPost hvalidPost
    hlen hbound hboundPost hflag hvalid hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteLongDataSlot I) =
        bytesStoreLiteSetChunkByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hpostAccountsPre :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreLiteAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      (bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccountsPre).symm
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccountsPre
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body
        (.returned
          (bytesStoreLiteSetChunkByteFrame I)
          evmSolm1 (some (bytesStoreLiteSetChunkByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState, bytesStoreLiteSetChunkByteFrame] using
      bytesStoreLiteSetChunkByteLongBodyReturnsOfPostShortReadback
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hchunkBound hloadChunksPost hchunkBoundPost hloadHeader hloadData
        hloadHeaderPost
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hlenPost hbound hboundPost hflag hflagPost hvalid hvalidPost
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    exact hpostAccountsPre
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetChunkByteValueWord I) hcanon))

theorem bytesStoreLiteSetChunkByteLongReturnLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I).toNat)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreLiteX_setChunkByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h1270Raw
  have hrev := bytesStoreLiteX_setChunkByteLongWriteReturnLongMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h1270 hbound hflag hchunkBoundPost hflagPost hbadPost hperm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteLongDataSlot I) =
        bytesStoreLiteSetChunkByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreLiteAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      (bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts).symm
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteSetChunkByteLongBodyReturnRevertsOfPostLongMalformed
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (len := len)
        (postHeaderWord := bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hchunkBound hloadChunksPost hchunkBoundPost hloadHeader hloadData
        hloadHeaderPost hcanon hlen hbound hflag hvalid hflagPost hbadPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkByteLongReturnShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz100 : 100 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ_evm I).toNat)
    (hchunkBoundPost :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I).toNat)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetChunkByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetChunkByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetChunkByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setChunkByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz100 hhi hsize
    (bytesStoreLiteSetPacketByteLand255_eq_self_of_uint8 hcanon)
  have hdecLen := bytesStoreLiteX_setChunkByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody hchunkBound
  have h1270Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hdecLen hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h1270 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1270⟩
        [len, bytesStoreLiteSetChunkByteIndexWord I, bytesStoreLiteSetChunkByteSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetChunkByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetChunkByteValueWord I, bytesStoreLiteSetChunkByteIndexWord I,
          bytesStoreLiteSetChunkByteChunkIndexWord I, ⟨301⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem (⟨1⟩ : UInt256) solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using h1270Raw
  have hrev := bytesStoreLiteX_setChunkByteLongWriteReturnShortMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    h1270 hbound hflag hchunkBoundPost hflagPost hbadPost hperm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadChunks :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadChunksLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteLongDataSlot I) =
        bytesStoreLiteSetChunkByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetChunkByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetChunkByteLongDataSlot I)
    (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simpa [evmSolm1, evmSolm0] using
      bytesStoreLiteAccountMapEquiv_storageStore_initState
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)
  have hloadChunksPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨1⟩ =
        bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      (bytesStoreLiteChunksLengthWord_eq_storageLoad_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts).symm
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetChunkByteSlot I) =
        bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I := by
    have howner : evmSolm1.executionEnv.codeOwner = I.codeOwner := by
      simp [evmSolm1, evmSolm0, initState, storageStore_executionEnv]
    simpa [evmSolm1, storageStore_executionEnv] using
      bytesStoreLiteStorageLoadSetChunkByteHeader_of_accountMapEquiv
        (evm := evmSolm1)
        (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I))
        (I := I) howner hpostAccounts
  have hd := bytesStoreLiteDispatch_setChunkByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setChunkByte_locals (I := I) hsz100 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetChunkByteLocals I) setChunkByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteSetChunkByteLongBodyReturnRevertsOfPostShortMalformed
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (chunksLen := bytesStoreLiteChunksLengthWord σ_evm I)
        (chunksLenPost := bytesStoreLiteChunksLengthWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (len := len)
        (postHeaderWord := bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadChunks hchunkBound hloadChunksPost hchunkBoundPost hloadHeader hloadData
        hloadHeaderPost hcanon hlen hbound hflag hvalid hflagPost hbadPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetChunkByteLongHeaderPost_of_collision_cases
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {acc : Account}
    (hacc : σ.find? I.codeOwner = some acc)
    (hlen : len = UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩)
    (hflag : UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hcollisionLen :
      bytesStoreLiteSetChunkByteSlot I = bytesStoreLiteSetChunkByteLongDataSlot I →
        len = UInt256.div (bytesStoreLiteSetChunkByteLongStoredWord σ I) ⟨2⟩)
    (hcollisionFlag :
      bytesStoreLiteSetChunkByteSlot I = bytesStoreLiteSetChunkByteLongDataSlot I →
        UInt256.land (bytesStoreLiteSetChunkByteLongStoredWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hcollisionValid :
      bytesStoreLiteSetChunkByteSlot I = bytesStoreLiteSetChunkByteLongDataSlot I →
        UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteLongStoredWord σ I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteLongStoredWord σ I) ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩) :
    len = UInt256.div
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨2⟩ ∧
      UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩ ∧
      UInt256.sub (UInt256.land
        (bytesStoreLiteSetChunkByteHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
            (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
  by_cases hEq : bytesStoreLiteSetChunkByteSlot I = bytesStoreLiteSetChunkByteLongDataSlot I
  · have hheaderPost :
        bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I =
          bytesStoreLiteSetChunkByteLongStoredWord σ I := by
      dsimp [bytesStoreLiteSetChunkByteHeaderWord]
      rw [hEq]
      exact sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetChunkByteLongDataSlot I)
        (bytesStoreLiteSetChunkByteLongStoredWord σ I) hacc
    refine ⟨?_, ?_, ?_⟩
    · rw [hheaderPost]
      exact hcollisionLen hEq
    · rw [hheaderPost]
      exact hcollisionFlag hEq
    · rw [hheaderPost]
      exact hcollisionValid hEq
  · have hheaderPost :
        bytesStoreLiteSetChunkByteHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
              (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I =
          bytesStoreLiteSetChunkByteHeaderWord σ I := by
      simpa [bytesStoreLiteSetChunkByteHeaderWord, bytesStoreLiteSetChunkByteLongDataSlot] using
        bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
          (σ := σ) (I := I) (baseSlot := bytesStoreLiteSetChunkByteSlot I)
          (idx := bytesStoreLiteSetChunkByteIndexWord I)
          (val := bytesStoreLiteSetChunkByteLongStoredWord σ I) hEq (by rfl)
    refine ⟨?_, ?_, ?_⟩
    · rw [hheaderPost]
      exact hlen
    · rw [hheaderPost]
      exact hflag
    · rw [hheaderPost]
      exact hvalid

theorem bytesStoreLiteSetChunkByteShortChunkBoundPost_of_collision_cases
    {σ : AccountMap} {I : ExecutionEnv} {acc : Account}
    (hacc : σ.find? I.codeOwner = some acc)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hcollisionBound :
      (⟨1⟩ : UInt256) = bytesStoreLiteSetChunkByteSlot I →
        (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
          (bytesStoreLiteSetChunkByteShortStoredWord σ I).toNat) :
    (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
      (bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I).toNat := by
    by_cases hEq : (⟨1⟩ : UInt256) = bytesStoreLiteSetChunkByteSlot I
    · have hlengthPost :
          bytesStoreLiteChunksLengthWord
              (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteSlot I)
                (bytesStoreLiteSetChunkByteShortStoredWord σ I)) I =
            bytesStoreLiteSetChunkByteShortStoredWord σ I := by
        dsimp [bytesStoreLiteChunksLengthWord]
        rw [hEq]
        exact sstoreAccountMap_storage_findD_self_of_find_some_any
          σ I.codeOwner acc (bytesStoreLiteSetChunkByteSlot I)
          (bytesStoreLiteSetChunkByteShortStoredWord σ I) hacc
      rw [hlengthPost]
      exact hcollisionBound hEq
    · have hpostIf :
          (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
            (if (⟨1⟩ : UInt256) =
                chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I then
              ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256)
                (fun _ => bytesStoreLiteSetChunkByteShortStoredWord σ I))
            else
              bytesStoreLiteChunksLengthWord σ I).toNat := by
        have hne :
            ¬ (⟨1⟩ : UInt256) = chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I := by
          simpa [bytesStoreLiteSetChunkByteSlot] using hEq
        rw [if_neg hne]
        exact hchunkBound
      simpa [bytesStoreLiteSetChunkByteSlot] using
        bytesStoreLiteChunkBoundAfterChunkHeaderSstore_of_post_bound
          (σ := σ) (I := I) (chunkIndex := bytesStoreLiteSetChunkByteChunkIndexWord I)
          (val := bytesStoreLiteSetChunkByteShortStoredWord σ I) hpostIf

theorem bytesStoreLiteSetChunkByteLongChunkBoundPost_of_collision_cases
    {σ : AccountMap} {I : ExecutionEnv} {acc : Account}
    (hacc : σ.find? I.codeOwner = some acc)
    (hchunkBound :
      (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
        (bytesStoreLiteChunksLengthWord σ I).toNat)
    (hcollisionBound :
      (⟨1⟩ : UInt256) = bytesStoreLiteSetChunkByteLongDataSlot I →
        (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
          (bytesStoreLiteSetChunkByteLongStoredWord σ I).toNat) :
    (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
      (bytesStoreLiteChunksLengthWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I).toNat := by
    by_cases hEq : (⟨1⟩ : UInt256) = bytesStoreLiteSetChunkByteLongDataSlot I
    · have hlengthPost :
          bytesStoreLiteChunksLengthWord
              (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetChunkByteLongDataSlot I)
                (bytesStoreLiteSetChunkByteLongStoredWord σ I)) I =
            bytesStoreLiteSetChunkByteLongStoredWord σ I := by
        dsimp [bytesStoreLiteChunksLengthWord]
        rw [hEq]
        exact sstoreAccountMap_storage_findD_self_of_find_some_any
          σ I.codeOwner acc (bytesStoreLiteSetChunkByteLongDataSlot I)
          (bytesStoreLiteSetChunkByteLongStoredWord σ I) hacc
      rw [hlengthPost]
      exact hcollisionBound hEq
    · have hpostIf :
          (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
            (if (⟨1⟩ : UInt256) =
                bytesLikeDataBase (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) +
                UInt256.div (bytesStoreLiteSetChunkByteIndexWord I) ⟨32⟩ then
              ((σ.find? I.codeOwner).option (⟨0⟩ : UInt256)
                (fun _ => bytesStoreLiteSetChunkByteLongStoredWord σ I))
            else
              bytesStoreLiteChunksLengthWord σ I).toNat := by
        have hne :
            ¬ (⟨1⟩ : UInt256) =
              bytesLikeDataBase (chunksDataBase + bytesStoreLiteSetChunkByteChunkIndexWord I) +
                UInt256.div (bytesStoreLiteSetChunkByteIndexWord I) ⟨32⟩ := by
          simpa [bytesStoreLiteSetChunkByteLongDataSlot, bytesStoreLiteSetChunkByteSlot] using hEq
        rw [if_neg hne]
        exact hchunkBound
      simpa [bytesStoreLiteSetChunkByteLongDataSlot] using
        bytesStoreLiteChunkBoundAfterChunkDataSstore_of_post_bound
          (σ := σ) (I := I) (chunkIndex := bytesStoreLiteSetChunkByteChunkIndexWord I)
          (idx := bytesStoreLiteSetChunkByteIndexWord I)
          (val := bytesStoreLiteSetChunkByteLongStoredWord σ I) hpostIf

theorem bytesStoreLiteSetChunkByteRuntime_of_post_bound {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (bytesStoreLiteSetChunkByteValueWord I).toNat < EVM.twoPow 8
      · by_cases hchunkBound :
          (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
            (bytesStoreLiteChunksLengthWord σ_evm I).toNat
        · by_cases hflagLong :
            UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩
          · by_cases hvalidLong :
              UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
                  ⟨32⟩) ≠ ⟨0⟩
            · let len := UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩
              by_cases hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat
              · by_cases hchunkBoundPost :
                  (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
                    (bytesStoreLiteChunksLengthWord
                      (sstoreAccountMap I.codeOwner σ_evm
                        (bytesStoreLiteSetChunkByteLongDataSlot I)
                        (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I).toNat
                · by_cases hflagPost : UInt256.land
                      (bytesStoreLiteSetChunkByteHeaderWord
                        (sstoreAccountMap I.codeOwner σ_evm
                          (bytesStoreLiteSetChunkByteLongDataSlot I)
                          (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩
                  · by_cases hvalidPost : UInt256.sub (UInt256.land
                        (bytesStoreLiteSetChunkByteHeaderWord
                          (sstoreAccountMap I.codeOwner σ_evm
                            (bytesStoreLiteSetChunkByteLongDataSlot I)
                            (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩)
                        (UInt256.lt (UInt256.div
                          (bytesStoreLiteSetChunkByteHeaderWord
                            (sstoreAccountMap I.codeOwner σ_evm
                              (bytesStoreLiteSetChunkByteLongDataSlot I)
                              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩)
                          ⟨32⟩) ≠ ⟨0⟩
                    · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
                      · obtain ⟨accEvm, haccEq⟩ := haccSome
                        let lenPost := UInt256.div
                          (bytesStoreLiteSetChunkByteHeaderWord
                            (sstoreAccountMap I.codeOwner σ_evm
                              (bytesStoreLiteSetChunkByteLongDataSlot I)
                              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩
                        by_cases hboundPost :
                            (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat
                        · exact bytesStoreLiteSetChunkByteLongSuccessRuntime_of_post_bound
                            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (len := len) (lenPost := lenPost) (accEvm := accEvm)
                              hcode hsize hperm hwv hsel hAccounts haccEq hsz100 hhi hcanon
                              hchunkBound hchunkBoundPost
                              (by rfl) hflagPost hvalidPost
                              (by rfl) hbound hboundPost hflagLong
                              hvalidLong
                        · exact bytesStoreLiteSetChunkByteLongReturnOobLengthRuntime
                            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (len := len) (lenPost := lenPost)
                              hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                              hchunkBound hchunkBoundPost
                              (by rfl) hflagPost hvalidPost
                              (by rfl) hbound hboundPost hflagLong
                              hvalidLong
                      · have haccNone : σ_evm.find? I.codeOwner = none := by
                          cases haccEq : σ_evm.find? I.codeOwner with
                          | none => rfl
                          | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                        have hhdr :
                            bytesStoreLiteSetChunkByteHeaderWord σ_evm I = ⟨0⟩ := by
                          simp [bytesStoreLiteSetChunkByteHeaderWord, haccNone, Option.option]
                        have hflag0 :
                            UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ =
                              ⟨0⟩ := by
                          rw [hhdr]
                          native_decide
                        exact False.elim (hflagLong hflag0)
                    · have hbadPost : UInt256.sub (UInt256.land
                          (bytesStoreLiteSetChunkByteHeaderWord
                            (sstoreAccountMap I.codeOwner σ_evm
                              (bytesStoreLiteSetChunkByteLongDataSlot I)
                              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩)
                          (UInt256.lt (UInt256.div
                            (bytesStoreLiteSetChunkByteHeaderWord
                              (sstoreAccountMap I.codeOwner σ_evm
                                (bytesStoreLiteSetChunkByteLongDataSlot I)
                                (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩)
                            ⟨32⟩) = ⟨0⟩ := by
                        by_contra hne
                        exact hvalidPost hne
                      exact bytesStoreLiteSetChunkByteLongReturnLongMalformedRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len)
                        hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                        hchunkBound hchunkBoundPost (by rfl) hbound hflagLong hvalidLong
                        hflagPost hbadPost
                  · have hflagPostZero :
                        UInt256.land
                          (bytesStoreLiteSetChunkByteHeaderWord
                            (sstoreAccountMap I.codeOwner σ_evm
                              (bytesStoreLiteSetChunkByteLongDataSlot I)
                              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩ =
                          ⟨0⟩ := by
                      by_contra hne
                      exact hflagPost hne
                    by_cases hvalidShortPost :
                        UInt256.sub (UInt256.land
                          (bytesStoreLiteSetChunkByteHeaderWord
                            (sstoreAccountMap I.codeOwner σ_evm
                              (bytesStoreLiteSetChunkByteLongDataSlot I)
                              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩)
                          (UInt256.lt (UInt256.land (UInt256.div
                            (bytesStoreLiteSetChunkByteHeaderWord
                              (sstoreAccountMap I.codeOwner σ_evm
                                (bytesStoreLiteSetChunkByteLongDataSlot I)
                                (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩)
                            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
                    · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
                      · obtain ⟨accEvm, haccEq⟩ := haccSome
                        let lenPost := UInt256.land (UInt256.div
                          (bytesStoreLiteSetChunkByteHeaderWord
                            (sstoreAccountMap I.codeOwner σ_evm
                              (bytesStoreLiteSetChunkByteLongDataSlot I)
                              (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩)
                          ⟨127⟩
                        by_cases hboundPost :
                            (bytesStoreLiteSetChunkByteIndexWord I).toNat < lenPost.toNat
                        · exact bytesStoreLiteSetChunkByteLongReturnShortSuccessRuntime
                            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (len := len) (lenPost := lenPost) (accEvm := accEvm)
                              hcode hsize hperm hwv hsel hAccounts haccEq hsz100 hhi hcanon
                              hchunkBound hchunkBoundPost
                              (by rfl) hflagPostZero hvalidShortPost
                              (by rfl) hbound hboundPost hflagLong hvalidLong
                        · exact bytesStoreLiteSetChunkByteLongReturnShortOobLengthRuntime
                            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                              (len := len) (lenPost := lenPost)
                              hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                              hchunkBound hchunkBoundPost
                              (by rfl) hflagPostZero hvalidShortPost
                              (by rfl) hbound hboundPost hflagLong
                              hvalidLong
                      · have haccNone : σ_evm.find? I.codeOwner = none := by
                          cases haccEq : σ_evm.find? I.codeOwner with
                          | none => rfl
                          | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                        have hhdr :
                            bytesStoreLiteSetChunkByteHeaderWord σ_evm I = ⟨0⟩ := by
                          simp [bytesStoreLiteSetChunkByteHeaderWord, haccNone, Option.option]
                        have hflag0 :
                            UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ =
                              ⟨0⟩ := by
                          rw [hhdr]
                          native_decide
                        exact False.elim (hflagLong hflag0)
                    · have hbadPost :
                          UInt256.sub (UInt256.land
                            (bytesStoreLiteSetChunkByteHeaderWord
                              (sstoreAccountMap I.codeOwner σ_evm
                                (bytesStoreLiteSetChunkByteLongDataSlot I)
                                (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨1⟩)
                            (UInt256.lt (UInt256.land (UInt256.div
                              (bytesStoreLiteSetChunkByteHeaderWord
                                (sstoreAccountMap I.codeOwner σ_evm
                                  (bytesStoreLiteSetChunkByteLongDataSlot I)
                                  (bytesStoreLiteSetChunkByteLongStoredWord σ_evm I)) I) ⟨2⟩)
                              ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
                        by_contra hne
                        exact hvalidShortPost hne
                      exact bytesStoreLiteSetChunkByteLongReturnShortMalformedRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len)
                        hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                        hchunkBound hchunkBoundPost (by rfl) hbound hflagLong hvalidLong
                        hflagPostZero hbadPost
                · exact bytesStoreLiteSetChunkByteLongReturnOobChunksLengthRuntime
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (len := len)
                    hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                    hchunkBound hchunkBoundPost (by rfl) hbound hflagLong hvalidLong
              · exact bytesStoreLiteSetChunkByteOobLongRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                  hchunkBound hflagLong hvalidLong hbound
            · have hbad :
                UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
                  (UInt256.lt (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
                    ⟨32⟩) = ⟨0⟩ := by
                by_contra hne
                exact hvalidLong hne
              exact bytesStoreLiteSetChunkByteLongMalformedRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                hchunkBound hflagLong hbad
          · have hflagShort :
              UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
              by_contra hne
              exact hflagLong hne
            by_cases hvalidShort :
                UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
                  (UInt256.lt
                    (UInt256.land
                      (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
                      ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
            · let len :=
                UInt256.land
                  (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
              have hltNe : UInt256.lt len ⟨32⟩ ≠ ⟨0⟩ := by
                intro hlt0
                have hzero : UInt256.sub ⟨0⟩ ⟨0⟩ = (⟨0⟩ : UInt256) := by
                  native_decide
                exact hvalidShort (by simpa [len, hflagShort, hlt0] using hzero)
              have hshort : len.toNat < 32 := by
                have hlt := ult_ne_zero_toNat_lt hltNe
                simpa using hlt
              by_cases hbound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < len.toNat
              · by_cases hchunkBoundPost :
                  (bytesStoreLiteSetChunkByteChunkIndexWord I).toNat <
                    (bytesStoreLiteChunksLengthWord
                      (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetChunkByteSlot I)
                        (bytesStoreLiteSetChunkByteShortStoredWord σ_evm I)) I).toNat
                · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
                  · obtain ⟨accEvm, haccEq⟩ := haccSome
                    exact bytesStoreLiteSetChunkByteShortSuccessRuntime_of_post_bound
                      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (len := len) (accEvm := accEvm)
                      hcode hsize hperm hwv hsel hAccounts haccEq hsz100 hhi hcanon
                      hchunkBound hchunkBoundPost (by rfl) hshort hbound hflagShort hvalidShort
                  · have haccNone : σ_evm.find? I.codeOwner = none := by
                      cases haccEq : σ_evm.find? I.codeOwner with
                      | none => rfl
                      | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                    have hhdr :
                        bytesStoreLiteSetChunkByteHeaderWord σ_evm I = ⟨0⟩ := by
                      simp [bytesStoreLiteSetChunkByteHeaderWord, haccNone, Option.option]
                    have hlenZero : len = ⟨0⟩ := by
                      change
                        UInt256.land
                          (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
                          ⟨127⟩ = ⟨0⟩
                      rw [hhdr]
                      native_decide
                    have hlen0 : len.toNat = 0 := by
                      simp [hlenZero]
                    have hbadBound : (bytesStoreLiteSetChunkByteIndexWord I).toNat < 0 := by
                      simpa [hlen0] using hbound
                    exact False.elim (Nat.not_lt_zero _ hbadBound)
                · exact bytesStoreLiteSetChunkByteShortReturnOobChunksLengthRuntime
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (len := len)
                    hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                    hchunkBound hchunkBoundPost (by rfl) hshort hbound hflagShort hvalidShort
              · exact bytesStoreLiteSetChunkByteOobShortRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                  hchunkBound hflagShort hvalidShort hbound
            · have hbad :
                UInt256.sub (UInt256.land (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨1⟩)
                  (UInt256.lt
                    (UInt256.land
                      (UInt256.div (bytesStoreLiteSetChunkByteHeaderWord σ_evm I) ⟨2⟩)
                      ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
                by_contra hne
                exact hvalidShort hne
              exact bytesStoreLiteSetChunkByteShortMalformedRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
                hchunkBound hflagShort hbad
        · exact bytesStoreLiteSetChunkByteOobChunksLengthRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
            (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon hchunkBound
      · exact bytesStoreLiteSetChunkByteDecodeNoncanonValueRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz100 hhi hcanon
    · exact bytesStoreLiteSetChunkByteDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts (by omega)
  · exact bytesStoreLiteSetChunkByteDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts (by omega)

theorem bytesStoreLiteSetChunkByteRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x48, 0x1c, 0x2f, 0xfb]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact bytesStoreLiteSetChunkByteRuntime_of_post_bound
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts

end BytesStoreLite
