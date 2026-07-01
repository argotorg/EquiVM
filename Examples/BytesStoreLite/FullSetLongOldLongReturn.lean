import Examples.BytesStoreLite.FullSetLongOldLong

/-!
# BytesStoreLite — return wrappers for old-long clear long writes
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

namespace BytesStoreLite

theorem bytesStoreLite_shiftRight_add31_five_toNat_of_lt_sign {x : UInt256}
    (hx : x.toNat < 2 ^ 255) :
    (UInt256.shiftRight (x + ⟨31⟩) ⟨5⟩).toNat = (x.toNat + 31) / 32 := by
  rw [bytesStoreLite_shiftRight_five_eq_div_thirtyTwo]
  exact BytesStoreLiteCore.u256_div_add31_toNat_of_lt_sign (x := x) hx

theorem bytesStoreLite_shiftRight_add31_five_toNat_of_u64 {x : UInt256}
    (hx : x.toNat ≤ ABI.solcMaxU64) :
    (UInt256.shiftRight (x + ⟨31⟩) ⟨5⟩).toNat = (x.toNat + 31) / 32 := by
  rw [bytesStoreLite_shiftRight_five_eq_div_thirtyTwo]
  exact BytesStoreLiteCore.u256_div_add31_toNat_of_u64 (x := x) hx

theorem bytesStoreLiteX_setLongNoTailReturnsOldLongClearFromReach
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart oldLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨1⟩)
    (hnoTailMod : len.toNat % 32 = 0) :
    let τ : AccountMap := clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        BytesStoreLiteCore.clearCurrentBaseWord)
      ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
          BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
          (BytesStoreLiteCore.clearCurrentBaseMemFrom
            (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  dsimp only
  let τ : AccountMap := clearDataWordsForwardFrom I.codeOwner σ
    (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
      BytesStoreLiteCore.clearCurrentBaseWord)
    ⟨0⟩
    (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  have hbranch : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C := by
    dsimp [τ]
    exact bytesStoreLiteX_setLongOldLongClearReachWriteBranch
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (oldLen := oldLen)
      hperm hreach hnz hlong hlenMax hsrc hflag holdLen hvalid hgtOldNew
  exact bytesStoreLiteX_setWriteLongNoTailReturnAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := τ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
    (payloadStart := payloadStart)
    hperm hbranch hnz hlong hlenMax hsrc hnoTailMod

theorem bytesStoreLiteX_setLongTailReturnsOldLongClearFromReach
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {len payloadStart oldLen wordTail : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨522⟩
      [len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hflag : UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (BytesStoreLiteCore.currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen len = ⟨1⟩)
    (htailMod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hwordTail :
      wordTail = UInt256.ofNat (fromBytesBigEndian
        (((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((BytesStoreLiteCore.setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length)
            0))) :
    let τ : AccountMap := clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        BytesStoreLiteCore.clearCurrentBaseWord)
      ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (BytesStoreLiteCore.longDataWordsForwardFrom I.codeOwner τ
            BytesStoreLiteCore.clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
            (BytesStoreLiteCore.clearCurrentBaseMemFrom
              (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot BytesStoreLiteCore.clearCurrentBaseWord
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord wordTail len))
        ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (UInt256.toByteArray len) := by
  dsimp only
  let τ : AccountMap := clearDataWordsForwardFrom I.codeOwner σ
    (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
      BytesStoreLiteCore.clearCurrentBaseWord)
    ⟨0⟩
    (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  have hbranch : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2434⟩
      [len, ⟨0⟩, ⟨128⟩, ⟨592⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (BytesStoreLiteCore.clearCurrentBaseMemFrom
        (BytesStoreLiteCore.setPaddedMem I.calldata len payloadStart))
      (BytesStoreLiteCore.clearCurrentHashAw (BytesStoreLiteCore.setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C := by
    dsimp [τ]
    exact bytesStoreLiteX_setLongOldLongClearReachWriteBranch
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (oldLen := oldLen)
      hperm hreach hnz hlong hlenMax hsrc hflag holdLen hvalid hgtOldNew
  exact bytesStoreLiteX_setWriteLongTailReturnAfterClearBase
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := τ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
    (payloadStart := payloadStart) (wordTail := wordTail)
    hperm hbranch hnz hlong hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax hwordTail

end BytesStoreLite
