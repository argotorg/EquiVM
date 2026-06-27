import Examples.BlindAuction.Reveal.Loop

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000

namespace BlindAuction

/-! Helpers for assembling the nonempty `reveal` loop. -/

theorem scratch_reveal_aw_mstore0_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 1 ≤ aw.toNat) aw.val.isLt

theorem scratch_reveal_aw_mstore32_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 2 ≤ aw.toNat) aw.val.isLt

theorem scratch_reveal_aw_mstore4_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 4 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 2 ≤ aw.toNat) aw.val.isLt

theorem scratch_reveal_aw_keccak64_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 2 ≤ aw.toNat) aw.val.isLt

theorem scratch_reveal_aw_mload64_of_ge3 {aw : UInt256} (haw : 3 ≤ aw.toNat) :
    UInt256.ofNat (MachineState.M aw.toNat 64 32) = aw := by
  apply u256_inj
  simp [MachineState.M]
  rw [UInt256.toNat_ofNat_of_lt]
  · omega
  · exact lt_of_le_of_lt (by omega : max aw.toNat 3 ≤ aw.toNat) aw.val.isLt

theorem scratch_reveal_aw_M_ge3 {aw off len : UInt256} (haw : 3 ≤ aw.toNat) :
    3 ≤ (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)).toNat := by
  unfold MachineState.M
  split
  · have h : UInt256.ofNat aw.toNat = aw := u256_ofNat_toNat aw
    rw [h]
    exact haw
  · have hterm : (off.toNat + len.toNat + 31) / 32 < UInt256.size := by
      apply Nat.div_lt_of_lt_mul
      have hoff : off.toNat < 2 ^ 256 := by
        change off.val.val < 2 ^ 256
        exact off.val.isLt
      have hlen : len.toNat < 2 ^ 256 := by
        change len.val.val < 2 ^ 256
        exact len.val.isLt
      change off.toNat + len.toNat + 31 < 32 * 2 ^ 256
      omega
    have hmax : max aw.toNat ((off.toNat + len.toNat + 31) / 32) < UInt256.size :=
      max_lt aw.val.isLt hterm
    rw [UInt256.toNat_ofNat_of_lt hmax]
    exact le_trans haw (Nat.le_max_left _ _)

theorem scratch_reveal_aw_M_small {aw off len : UInt256}
    (hawSmall : aw.toNat * 32 < UInt256.size)
    (hbound : off.toNat + len.toNat + 31 < UInt256.size) :
    (UInt256.ofNat (MachineState.M aw.toNat off.toNat len.toNat)).toNat * 32 <
      UInt256.size := by
  unfold MachineState.M
  split
  · have h : UInt256.ofNat aw.toNat = aw := u256_ofNat_toNat aw
    rw [h]
    exact hawSmall
  · let n := off.toNat + len.toNat + 31
    have hdivMul : (n / 32) * 32 ≤ n := Nat.div_mul_le_self n 32
    have htermSmall : (n / 32) * 32 < UInt256.size := by
      exact lt_of_le_of_lt hdivMul (by simpa [n] using hbound)
    have hmaxSmall : max aw.toNat (n / 32) * 32 < UInt256.size := by
      rw [Nat.max_def]
      split <;> omega
    have hmaxLt : max aw.toNat (n / 32) < UInt256.size := by
      omega
    rw [UInt256.toNat_ofNat_of_lt hmaxLt]
    simpa [n] using hmaxSmall

theorem scratch_not_mload64_oob_of_aw_ge3_small {aw : UInt256}
    (haw : 3 ≤ aw.toNat) (hawSmall : aw.toNat * 32 < UInt256.size) :
    ¬ ((⟨64⟩ : UInt256) ≥ aw * ⟨32⟩) := by
  intro h
  have hmul : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
    rw [u256_mul_op_toNat]
    exact Nat.mod_eq_of_lt hawSmall
  have h64 : (⟨64⟩ : UInt256).toNat = 64 := by decide
  change (⟨64⟩ : UInt256).toNat ≥ (aw * ⟨32⟩ : UInt256).toNat at h
  rw [h64, hmul] at h
  omega

theorem scratch_not_mload_oob_after_M32 {aw off : UInt256}
    (hsmall :
      (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)).toNat * 32 <
        UInt256.size) :
    ¬ (off ≥ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)) * ⟨32⟩) := by
  intro h
  let aw' := UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)
  have hmul : (aw' * (⟨32⟩ : UInt256)).toNat = aw'.toNat * 32 := by
    rw [u256_mul_op_toNat]
    exact Nat.mod_eq_of_lt (by simpa [aw'] using hsmall)
  have hceil : off.toNat < ((off.toNat + 32 + 31) / 32) * 32 := by
    omega
  have htermDivLt : ((off.toNat + 32 + 31) / 32) < UInt256.size := by
    apply Nat.div_lt_of_lt_mul
    have hoff : off.toNat < 2 ^ 256 := by
      change off.val.val < 2 ^ 256
      exact off.val.isLt
    change off.toNat + 32 + 31 < 32 * 2 ^ 256
    omega
  have htermLt : max aw.toNat ((off.toNat + 32 + 31) / 32) < UInt256.size :=
    max_lt aw.val.isLt htermDivLt
  have hcover : off.toNat < aw'.toNat * 32 := by
    dsimp [aw']
    simp [MachineState.M, UInt256.toNat_ofNat_of_lt htermLt]
    exact lt_of_lt_of_le hceil (Nat.mul_le_mul_right 32 (Nat.le_max_right _ _))
  change off.toNat ≥ (aw' * ⟨32⟩ : UInt256).toNat at h
  rw [hmul] at h
  omega

theorem scratch_revealPackedHashWord_toBytesBE (value : UInt256) (fake : Bool)
    (secret : UInt256) :
    EVM.Word.toBytesBE
        (uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList :=
  toBytesBE_keccak_uInt256OfByteArray _

theorem scratch_revealPackedHash_ne_of_word_ne {blinded value secret : UInt256}
    {fake : Bool}
    (hne :
      blinded ≠
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) :
    EVM.Word.toBytesBE blinded ≠
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList := by
  intro hbytes
  apply hne
  apply word_toBytesBE_inj
  rw [hbytes, scratch_revealPackedHashWord_toBytesBE value fake secret]

theorem scratch_word_ne_of_u256_eq_zero {a b : UInt256}
    (h : UInt256.eq a b = ⟨0⟩) : a ≠ b := by
  intro heq
  rw [heq, u256_eq_refl] at h
  have hnat := congrArg UInt256.toNat h
  change (1 : Nat) = 0 at hnat
  omega

theorem scratch_revealPackedHash_eq_of_u256_eq_one {blinded value secret : UInt256}
    {fake : Bool}
    (h :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨1⟩) :
    EVM.Word.toBytesBE blinded =
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList := by
  have hword := uInt256_eq_one_eq h
  rw [hword, scratch_revealPackedHashWord_toBytesBE value fake secret]

theorem scratch_revealPackedHash_ne_of_u256_eq_zero {blinded value secret : UInt256}
    {fake : Bool}
    (h :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨0⟩) :
    EVM.Word.toBytesBE blinded ≠
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList := by
  exact scratch_revealPackedHash_ne_of_word_ne
    (scratch_word_ne_of_u256_eq_zero h)

-- Compatibility wrappers around reusable 32-byte `MSTORE` read lemmas.
theorem scratch_write32_read_prefix_len (src base : ByteArray) (dest len : Nat)
    (hsrc : 32 ≤ src.size) (hlo : dest ≤ base.size) (hlen : len ≤ 32)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write 0 base dest 32).readWithPadding dest len = src.extract 0 len := by
  exact Reasoning.Theory.write32_read_prefix_len src base dest len hsrc hlo hlen hpos hlen64

theorem scratch_write32_read_below_len (src base : ByteArray) (dest read len : Nat)
    (hsrc : 32 ≤ src.size) (hlo : dest ≤ base.size)
    (hbelow : read + len ≤ dest) (hin : read + len ≤ base.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write 0 base dest 32).readWithPadding read len = base.readWithPadding read len := by
  exact Reasoning.Theory.write32_read_below_len src base dest read len hsrc hlo
    hbelow hin hpos hlen64

theorem scratch_write32_read_above_len (src base : ByteArray) (dest read len : Nat)
    (hsrc : 32 ≤ src.size) (hlo : dest ≤ base.size)
    (habove : dest + 32 ≤ read) (hin : read + len ≤ base.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write 0 base dest 32).readWithPadding read len = base.readWithPadding read len := by
  exact Reasoning.Theory.write32_read_above_len src base dest read len hsrc hlo
    habove hin hpos hlen64

theorem scratch_twoWordWrite_read0_64_any (mem : ByteArray) (key slot : UInt256) :
    (((UInt256.toByteArray slot).write 0
      ((UInt256.toByteArray key).write 0 mem 0 32) 32 32).readWithPadding 0 64) =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  let mem1 := (UInt256.toByteArray key).write 0 mem 0 32
  have hmem1size : 32 ≤ mem1.size := by
    dsimp [mem1]
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    omega
  have hslotExtract : (UInt256.toByteArray slot).extract 0 32 = UInt256.toByteArray slot := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray slot).size ≤ 32
      rw [toByteArray_size])
  have hkeyExtract : (UInt256.toByteArray key).extract 0 32 = UInt256.toByteArray key := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray key).size ≤ 32
      rw [toByteArray_size])
  have hmem1extract : mem1.extract 0 32 = UInt256.toByteArray key := by
    have hmem1read : mem1.readWithPadding 0 32 = UInt256.toByteArray key := by
      dsimp [mem1]
      rw [write0_read_back_gen _ _ 32 (by decide) (by rw [toByteArray_size])
        (by norm_num)]
      exact hkeyExtract
    rw [← readWithPadding_eq_extract mem1 0 hmem1size]
    exact hmem1read
  rw [show ((UInt256.toByteArray slot).write 0
      ((UInt256.toByteArray key).write 0 mem 0 32) 32 32) =
        (UInt256.toByteArray slot).write 0 mem1 32 32 by rfl]
  rw [readWithPadding_eq_extract' _ 0 64 (by omega) (by norm_num) (by
    rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    omega)]
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  let A := mem1.extract 0 32
  let B := (UInt256.toByteArray slot).extract 0 32
  let C := mem1.extract (32 + 32) mem1.size
  have hAsize : A.size = 32 := by
    dsimp [A]
    rw [ByteArray.size_extract]
    omega
  have hBsize : B.size = 32 := by
    dsimp [B]
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hABsize : (A ++ B).size = 64 := by
    rw [ByteArray.size_append, hAsize, hBsize]
  change (A ++ B ++ C).extract 0 (0 + 64) =
    UInt256.toByteArray key ++ UInt256.toByteArray slot
  rw [show 0 + 64 = 64 by omega]
  rw [extract_append_left (A ++ B) C 0 64 (by rw [hABsize])]
  rw [← hABsize, byteArray_extract_self]
  dsimp [A, B]
  rw [hmem1extract, hslotExtract]

theorem scratch_revealBidsMappingBaseKeccak_any (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
      revealScratchBidsLengthSlot I := by
  rw [scratch_twoWordWrite_read0_64_any]
  rw [← revealScratchBidsHashMem_read0_64 I]
  exact revealScratchBidsMappingBaseKeccak I

theorem scratch_revealBidsArrayDataKeccak_any (I : ExecutionEnv) (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0 mem 0 32).readWithPadding
            0 32))) =
      uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))) := by
  rw [write0_read_back_gen _ _ 32 (by decide) (by rw [toByteArray_size]) (by norm_num)]
  rw [show (UInt256.toByteArray (revealScratchBidsLengthSlot I)).extract 0 32 =
      UInt256.toByteArray (revealScratchBidsLengthSlot I) by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray (revealScratchBidsLengthSlot I)).size ≤ 32
      rw [toByteArray_size])]
  exact keccakSlot_eq _

theorem scratch_readWithPadding_split_32_1_32 (mem : ByteArray) (base : Nat)
    (h : base + 65 ≤ mem.size) :
    mem.readWithPadding base 65 =
      mem.readWithPadding base 32 ++ mem.readWithPadding (base + 32) 1 ++
        mem.readWithPadding (base + 33) 32 := by
  rw [readWithPadding_eq_extract' mem base 65 (by norm_num) (by norm_num) h]
  rw [readWithPadding_eq_extract' mem base 32 (by norm_num) (by norm_num) (by omega)]
  rw [readWithPadding_eq_extract' mem (base + 32) 1 (by norm_num) (by norm_num) (by omega)]
  rw [readWithPadding_eq_extract' mem (base + 33) 32 (by norm_num) (by norm_num) (by omega)]
  rw [show base + 65 = base + 32 + 33 by omega]
  rw [show base + 33 = base + 32 + 1 by omega]
  have hsplit1 :
      mem.extract base (base + 65) =
        mem.extract base (base + 32) ++ mem.extract (base + 32) (base + 65) := by
    symm
    rw [ByteArray.extract_append_extract]
    congr <;> omega
  have hsplit2 :
      mem.extract (base + 32) (base + 65) =
        mem.extract (base + 32) (base + 33) ++ mem.extract (base + 33) (base + 65) := by
    symm
    rw [ByteArray.extract_append_extract]
    congr <;> omega
  rw [hsplit1, hsplit2]
  rw [show base + 32 + 1 = base + 33 by omega]
  rw [show base + 32 + 33 = base + 65 by omega]
  rw [ByteArray.append_assoc]

theorem scratch_revealPackedMem_readWithPadding {mem : ByteArray}
    {fp value fakeWord secret : UInt256} {fake : Bool}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hfp64 : 64 ≤ fp.toNat)
    (hfake : fakeWord = if fake then (⟨1⟩ : UInt256) else ⟨0⟩) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := scratch_revealPackedValueMem mem base value
    let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
    let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
    let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
    let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
    mem5.readWithPadding base.toNat packedLen.toNat =
      ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4 mem5
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hnewFreeNat : newFree.toNat = fp.toNat + 97 := by
    dsimp [newFree]
    rw [uadd_toNat, hbaseNat]
    have hlt : 65 + (fp.toNat + 32) < UInt256.size := by omega
    change (65 + (fp.toNat + 32)) % UInt256.size = fp.toNat + 97
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hpackedLenNat : packedLen.toNat = 65 := by
    have hsub1 : (UInt256.sub newFree fp).toNat = 97 := by
      rw [usub_toNat]
      · rw [hnewFreeNat]
        omega
      · rw [hnewFreeNat]
        omega
    dsimp [packedLen]
    rw [usub_toNat]
    · rw [hsub1]
      change 97 - 32 = 65
      norm_num
    · rw [hsub1]
      change 32 ≤ 97
      norm_num
  have hmem1_read : mem1.readWithPadding base.toNat 32 = UInt256.toByteArray value := by
    dsimp [mem1, scratch_revealPackedValueMem]
    rw [toByteArray_write_read_back_of_gap]
    simpa [hbaseNat] using hgap
  have hmem1_size : mem1.size = fp.toNat + 64 := by
    dsimp [mem1, scratch_revealPackedValueMem]
    rw [toByteArray_write_eq _ _ base.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        USize.toNat_ofNat_of_lt']
      · rw [toByteArray_size]
        omega
      · simpa [hbaseNat] using hgap
    · rw [hbaseNat]; exact hmemle
    · simpa [hbaseNat] using hgap
  have hmem2_value : mem2.readWithPadding base.toNat 32 = UInt256.toByteArray value := by
    dsimp [mem2, scratch_revealPackedFakeMem]
    rw [write32_read_below
      (src := UInt256.toByteArray (UInt256.shiftLeft (UInt256.isZero (UInt256.isZero fakeWord)) ⟨248⟩))
      (base := mem1) (destAddr := fakeBase.toNat) (readAddr := base.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem1_size, hfakeBaseNat])
      (hbelow := by rw [hbaseNat, hfakeBaseNat])]
    exact hmem1_read
  have hmem2_fake : mem2.readWithPadding fakeBase.toNat 1 =
      ByteArray.mk #[if fake then (1 : UInt8) else 0] := by
    dsimp [mem2, scratch_revealPackedFakeMem]
    rw [scratch_write32_read_prefix_len]
    · subst fakeWord
      rw [toByteArray_eq_toBytesBE]
      cases fake <;> native_decide
    · rw [toByteArray_size]
    · rw [hmem1_size, hfakeBaseNat]
    · omega
    · norm_num
    · norm_num
  have hmem2_size : mem2.size = fp.toNat + 96 := by
    dsimp [mem2, scratch_revealPackedFakeMem]
    rw [show fakeBase.toNat = mem1.size by rw [hmem1_size, hfakeBaseNat]]
    rw [write_at_end_eq]
    · rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hmem1_size]
      omega
    · decide
    · rw [toByteArray_size]
  have hmem3_value : mem3.readWithPadding base.toNat 32 = UInt256.toByteArray value := by
    dsimp [mem3, scratch_revealPackedSecretMem]
    rw [write32_read_below
      (src := UInt256.toByteArray secret) (base := mem2)
      (destAddr := secretBase.toNat) (readAddr := base.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem2_size, hsecretBaseNat]; omega)
      (hbelow := by rw [hbaseNat, hsecretBaseNat]; omega)]
    exact hmem2_value
  have hmem3_fake : mem3.readWithPadding fakeBase.toNat 1 =
      ByteArray.mk #[if fake then (1 : UInt8) else 0] := by
    dsimp [mem3, scratch_revealPackedSecretMem]
    rw [scratch_write32_read_below_len
      (src := UInt256.toByteArray secret) (base := mem2)
      (dest := secretBase.toNat) (read := fakeBase.toNat) (len := 1)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem2_size, hsecretBaseNat]; omega)
      (hbelow := by rw [hfakeBaseNat, hsecretBaseNat])
      (hin := by rw [hmem2_size, hfakeBaseNat]; omega)
      (hpos := by norm_num) (hlen64 := by norm_num)]
    exact hmem2_fake
  have hmem3_secret : mem3.readWithPadding secretBase.toNat 32 = UInt256.toByteArray secret := by
    dsimp [mem3, scratch_revealPackedSecretMem]
    rw [write32_read_back]
    · rw [show (UInt256.toByteArray secret).extract 0 32 = UInt256.toByteArray secret by
        rw [show 32 = (UInt256.toByteArray secret).size by rw [toByteArray_size]]
        exact byteArray_extract_self _]
    · rw [toByteArray_size]
    · rw [hmem2_size, hsecretBaseNat]; omega
  have hmem3_size : mem3.size = fp.toNat + 97 := by
    dsimp [mem3, scratch_revealPackedSecretMem]
    rw [write32_eq _ _ secretBase.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem2_size,
        hsecretBaseNat]
      omega
    · rw [toByteArray_size]
    · rw [hmem2_size, hsecretBaseNat]; omega
  have hmem4_value : mem4.readWithPadding base.toNat 32 = UInt256.toByteArray value := by
    dsimp [mem4, scratch_revealPackedLenMem]
    rw [write32_read_above
      (src := UInt256.toByteArray packedLen) (base := mem3)
      (destAddr := fp.toNat) (readAddr := base.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem3_size]; omega)
      (habove := by rw [hbaseNat])
      (hin := by rw [hmem3_size, hbaseNat]; omega)]
    exact hmem3_value
  have hmem4_fake : mem4.readWithPadding fakeBase.toNat 1 =
      ByteArray.mk #[if fake then (1 : UInt8) else 0] := by
    dsimp [mem4, scratch_revealPackedLenMem]
    rw [scratch_write32_read_above_len
      (src := UInt256.toByteArray packedLen) (base := mem3)
      (dest := fp.toNat) (read := fakeBase.toNat) (len := 1)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem3_size]; omega)
      (habove := by rw [hfakeBaseNat]; omega)
      (hin := by rw [hmem3_size, hfakeBaseNat]; omega)
      (hpos := by norm_num) (hlen64 := by norm_num)]
    exact hmem3_fake
  have hmem4_secret : mem4.readWithPadding secretBase.toNat 32 = UInt256.toByteArray secret := by
    dsimp [mem4, scratch_revealPackedLenMem]
    rw [write32_read_above
      (src := UInt256.toByteArray packedLen) (base := mem3)
      (destAddr := fp.toNat) (readAddr := secretBase.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem3_size]; omega)
      (habove := by rw [hsecretBaseNat]; omega)
      (hin := by rw [hmem3_size, hsecretBaseNat])]
    exact hmem3_secret
  have hmem4_size : mem4.size = fp.toNat + 97 := by
    dsimp [mem4, scratch_revealPackedLenMem]
    rw [write32_eq _ _ fp.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem3_size]
      omega
    · rw [toByteArray_size]
    · rw [hmem3_size]; omega
  have hmem5_value : mem5.readWithPadding base.toNat 32 = UInt256.toByteArray value := by
    dsimp [mem5, scratch_revealPackedFreePtrMem]
    rw [write32_read_above
      (src := UInt256.toByteArray newFree) (base := mem4)
      (destAddr := 64) (readAddr := base.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem4_size]; omega)
      (habove := by rw [hbaseNat]; omega)
      (hin := by rw [hmem4_size, hbaseNat]; omega)]
    exact hmem4_value
  have hmem5_fake : mem5.readWithPadding fakeBase.toNat 1 =
      ByteArray.mk #[if fake then (1 : UInt8) else 0] := by
    dsimp [mem5, scratch_revealPackedFreePtrMem]
    rw [scratch_write32_read_above_len
      (src := UInt256.toByteArray newFree) (base := mem4)
      (dest := 64) (read := fakeBase.toNat) (len := 1)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem4_size]; omega)
      (habove := by rw [hfakeBaseNat]; omega)
      (hin := by rw [hmem4_size, hfakeBaseNat]; omega)
      (hpos := by norm_num) (hlen64 := by norm_num)]
    exact hmem4_fake
  have hmem5_secret : mem5.readWithPadding secretBase.toNat 32 = UInt256.toByteArray secret := by
    dsimp [mem5, scratch_revealPackedFreePtrMem]
    rw [write32_read_above
      (src := UInt256.toByteArray newFree) (base := mem4)
      (destAddr := 64) (readAddr := secretBase.toNat)
      (hsrc := by rw [toByteArray_size])
      (hlo := by rw [hmem4_size]; omega)
      (habove := by rw [hsecretBaseNat]; omega)
      (hin := by rw [hmem4_size, hsecretBaseNat])]
    exact hmem4_secret
  have hmem5_size : mem5.size = fp.toNat + 97 := by
    dsimp [mem5, scratch_revealPackedFreePtrMem]
    rw [write32_eq _ _ 64]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem4_size]
      omega
    · rw [toByteArray_size]
    · rw [hmem4_size]; omega
  rw [hpackedLenNat]
  rw [scratch_readWithPadding_split_32_1_32 mem5 base.toNat]
  · rw [hmem5_value]
    rw [show base.toNat + 32 = fakeBase.toNat by omega]
    rw [hmem5_fake]
    rw [show base.toNat + 33 = secretBase.toNat by omega]
    rw [hmem5_secret]
    rw [toByteArray_eq_toBytesBE value, toByteArray_eq_toBytesBE secret]
    cases fake <;> rfl
  · rw [hmem5_size, hbaseNat]

theorem scratch_revealPackedMem_hash {mem : ByteArray}
    {fp value fakeWord secret : UInt256} {fake : Bool}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hfp64 : 64 ≤ fp.toNat)
    (hfake : fakeWord = if fake then (⟨1⟩ : UInt256) else ⟨0⟩) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := scratch_revealPackedValueMem mem base value
    let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
    let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
    let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
    let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
      uInt256OfByteArray
        (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)) := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4 mem5
  have hread :
      mem5.readWithPadding base.toNat packedLen.toNat =
        ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, mem1, mem2, mem3, mem4, mem5]
      using scratch_revealPackedMem_readWithPadding
        (mem := mem) (fp := fp) (value := value) (fakeWord := fakeWord)
        (secret := secret) (fake := fake) hfit hmemle hgap hfp64 hfake
  rw [hread, uInt256OfByteArray_eq]

theorem scratch_revealPackedMem_len_read {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hfp96 : 96 ≤ fp.toNat) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := scratch_revealPackedValueMem mem base value
    let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
    let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
    let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
    let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
    mem5.readWithPadding fp.toNat 32 = UInt256.toByteArray packedLen := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4 mem5
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hmem1_size : mem1.size = fp.toNat + 64 := by
    dsimp [mem1, scratch_revealPackedValueMem]
    rw [toByteArray_write_eq _ _ base.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        USize.toNat_ofNat_of_lt']
      · rw [toByteArray_size]
        omega
      · simpa [hbaseNat] using hgap
    · rw [hbaseNat]; exact hmemle
    · simpa [hbaseNat] using hgap
  have hmem2_size : mem2.size = fp.toNat + 96 := by
    dsimp [mem2, scratch_revealPackedFakeMem]
    rw [show fakeBase.toNat = mem1.size by rw [hmem1_size, hfakeBaseNat]]
    rw [write_at_end_eq]
    · rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hmem1_size]
      omega
    · decide
    · rw [toByteArray_size]
  have hmem3_size : mem3.size = fp.toNat + 97 := by
    dsimp [mem3, scratch_revealPackedSecretMem]
    rw [write32_eq _ _ secretBase.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem2_size,
        hsecretBaseNat]
      omega
    · rw [toByteArray_size]
    · rw [hmem2_size, hsecretBaseNat]; omega
  have hmem4_read : mem4.readWithPadding fp.toNat 32 = UInt256.toByteArray packedLen := by
    dsimp [mem4, scratch_revealPackedLenMem]
    rw [write32_read_back]
    · rw [show (UInt256.toByteArray packedLen).extract 0 32 = UInt256.toByteArray packedLen by
        rw [show 32 = (UInt256.toByteArray packedLen).size by rw [toByteArray_size]]
        exact byteArray_extract_self _]
    · rw [toByteArray_size]
    · rw [hmem3_size]; omega
  have hmem4_size : mem4.size = fp.toNat + 97 := by
    dsimp [mem4, scratch_revealPackedLenMem]
    rw [write32_eq _ _ fp.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem3_size]
      omega
    · rw [toByteArray_size]
    · rw [hmem3_size]; omega
  dsimp [mem5, scratch_revealPackedFreePtrMem]
  rw [write32_read_above
    (src := UInt256.toByteArray newFree) (base := mem4)
    (destAddr := 64) (readAddr := fp.toNat)
    (hsrc := by rw [toByteArray_size])
    (hlo := by rw [hmem4_size]; omega)
    (habove := by omega)
      (hin := by rw [hmem4_size]; omega)]
  exact hmem4_read

theorem scratch_revealPackedMem_beforeFreePtr_size {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := scratch_revealPackedValueMem mem base value
    let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
    let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
    let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
    mem4.size = fp.toNat + 97 := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hmem1_size : mem1.size = fp.toNat + 64 := by
    dsimp [mem1, scratch_revealPackedValueMem]
    rw [toByteArray_write_eq _ _ base.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        USize.toNat_ofNat_of_lt']
      · rw [toByteArray_size]
        omega
      · simpa [hbaseNat] using hgap
    · rw [hbaseNat]; exact hmemle
    · simpa [hbaseNat] using hgap
  have hmem2_size : mem2.size = fp.toNat + 96 := by
    dsimp [mem2, scratch_revealPackedFakeMem]
    rw [show fakeBase.toNat = mem1.size by rw [hmem1_size, hfakeBaseNat]]
    rw [write_at_end_eq]
    · rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hmem1_size]
      omega
    · decide
    · rw [toByteArray_size]
  have hmem3_size : mem3.size = fp.toNat + 97 := by
    dsimp [mem3, scratch_revealPackedSecretMem]
    rw [write32_eq _ _ secretBase.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem2_size,
        hsecretBaseNat]
      omega
    · rw [toByteArray_size]
    · rw [hmem2_size, hsecretBaseNat]; omega
  dsimp [mem4, scratch_revealPackedLenMem]
  rw [write32_eq _ _ fp.toNat]
  · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem3_size]
    omega
  · rw [toByteArray_size]
  · rw [hmem3_size]; omega

theorem scratch_revealPackedMem_size {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := scratch_revealPackedValueMem mem base value
    let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
    let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
    let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
    let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
    mem5.size = fp.toNat + 97 := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4 mem5
  have hmem4_size : mem4.size = fp.toNat + 97 := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, mem1, mem2, mem3, mem4]
      using scratch_revealPackedMem_beforeFreePtr_size
        (mem := mem) (fp := fp) (value := value) (fakeWord := fakeWord)
        (secret := secret) hfit hmemle hgap
  dsimp [mem5, scratch_revealPackedFreePtrMem]
  rw [write32_eq _ _ 64]
  · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem4_size]
    omega
  · rw [toByteArray_size]
  · rw [hmem4_size]; omega

theorem scratch_revealPackedMem_freePtr_read {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let mem1 := scratch_revealPackedValueMem mem base value
    let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
    let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
    let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
    let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
    mem5.readWithPadding 64 32 = UInt256.toByteArray newFree := by
  intro base fakeBase secretBase newFree packedLen mem1 mem2 mem3 mem4 mem5
  have hmem4_size : mem4.size = fp.toNat + 97 := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, mem1, mem2, mem3, mem4]
      using scratch_revealPackedMem_beforeFreePtr_size
        (mem := mem) (fp := fp) (value := value) (fakeWord := fakeWord)
        (secret := secret) hfit hmemle hgap
  dsimp [mem5, scratch_revealPackedFreePtrMem]
  rw [write32_read_back]
  · rw [show (UInt256.toByteArray newFree).extract 0 32 =
        UInt256.toByteArray newFree by
      rw [show 32 = (UInt256.toByteArray newFree).size by rw [toByteArray_size]]
      exact byteArray_extract_self _]
  · rw [toByteArray_size]
  · rw [hmem4_size]; omega

theorem scratch_revealPackedPrefix_size {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let mem1 := scratch_revealPackedValueMem mem base value
    let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
    let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
    mem3.size = fp.toNat + 97 := by
  intro base fakeBase secretBase mem1 mem2 mem3
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hmem1_size : mem1.size = fp.toNat + 64 := by
    dsimp [mem1, scratch_revealPackedValueMem]
    rw [toByteArray_write_eq _ _ base.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        USize.toNat_ofNat_of_lt']
      · rw [toByteArray_size]
        omega
      · simpa [hbaseNat] using hgap
    · rw [hbaseNat]; exact hmemle
    · simpa [hbaseNat] using hgap
  have hmem2_size : mem2.size = fp.toNat + 96 := by
    dsimp [mem2, scratch_revealPackedFakeMem]
    rw [show fakeBase.toNat = mem1.size by rw [hmem1_size, hfakeBaseNat]]
    rw [write_at_end_eq]
    · rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hmem1_size]
      omega
    · decide
    · rw [toByteArray_size]
  dsimp [mem3, scratch_revealPackedSecretMem]
  rw [write32_eq _ _ secretBase.toNat]
  · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, toByteArray_size, hmem2_size,
      hsecretBaseNat]
    omega
  · rw [toByteArray_size]
  · rw [hmem2_size, hsecretBaseNat]; omega

theorem scratch_revealPackedPrefix_preserve_fp {mem : ByteArray}
    {fp value fakeWord secret : UInt256}
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (hmem96 : 96 ≤ mem.size) (hfp64 : 64 ≤ fp.toNat) :
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let mem1 := scratch_revealPackedValueMem mem base value
    let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
    let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
    mem3.readWithPadding 64 32 = UInt256.toByteArray fp := by
  intro base fakeBase secretBase mem1 mem2 mem3
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hmem1_read : mem1.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [mem1, scratch_revealPackedValueMem]
    rw [toByteArray_write_read_below_of_gap]
    · exact hread
    · exact hmem96
    · rw [hbaseNat]; omega
    · simpa [hbaseNat] using hgap
  have hmem1_size : mem1.size = fp.toNat + 64 := by
    dsimp [mem1, scratch_revealPackedValueMem]
    rw [toByteArray_write_eq _ _ base.toNat]
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size,
        USize.toNat_ofNat_of_lt']
      · rw [toByteArray_size]
        omega
      · simpa [hbaseNat] using hgap
    · rw [hbaseNat]; exact hmemle
    · simpa [hbaseNat] using hgap
  have hmem2_read : mem2.readWithPadding 64 32 = UInt256.toByteArray fp := by
    dsimp [mem2, scratch_revealPackedFakeMem]
    rw [toByteArray_write_read_below_of_gap]
    · exact hmem1_read
    · rw [hmem1_size]; omega
    · rw [hfakeBaseNat]; omega
    · rw [hmem1_size, hfakeBaseNat]
      have hpos : 0 < USize.size := USize.size_pos
      omega
  have hmem2_size : mem2.size = fp.toNat + 96 := by
    dsimp [mem2, scratch_revealPackedFakeMem]
    rw [show fakeBase.toNat = mem1.size by rw [hmem1_size, hfakeBaseNat]]
    rw [write_at_end_eq]
    · rw [ByteArray.size_append, ByteArray.size_extract, toByteArray_size, hmem1_size]
      omega
    · decide
    · rw [toByteArray_size]
  dsimp [mem3, scratch_revealPackedSecretMem]
  rw [toByteArray_write_read_below_of_gap]
  · exact hmem2_read
  · rw [hmem2_size]; omega
  · rw [hsecretBaseNat]; omega
  · rw [hmem2_size, hsecretBaseNat]
    have hpos : 0 < USize.size := USize.size_pos
    omega

theorem scratch_revealPacked_aw_facts {aw fp : UInt256}
    (haw : 3 ≤ aw.toNat) (hawSmall : aw.toNat * 32 < UInt256.size)
    (hfit128 : fp.toNat + 128 < UInt256.size) :
    let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    let base := (⟨32⟩ : UInt256) + fp
    let fakeBase := base + ⟨32⟩
    let secretBase := base + ⟨33⟩
    let newFree := (⟨65⟩ : UInt256) + base
    let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
    let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
    let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
    let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
    let aw1 := UInt256.ofNat (MachineState.M awP4.toNat (⟨64⟩ : UInt256).toNat 32)
    let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
    let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
    let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
    let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
    newFree.toNat = fp.toNat + 97 ∧ packedLen.toNat = 65 ∧
      3 ≤ aw2.toNat ∧ aw2.toNat * 32 < UInt256.size ∧
      3 ≤ awP4.toNat ∧ awP4.toNat * 32 < UInt256.size ∧
      3 ≤ aw3.toNat ∧ aw3.toNat * 32 < UInt256.size ∧
      3 ≤ aw5.toNat ∧ aw5.toNat * 32 < UInt256.size := by
  intro awP1 base fakeBase secretBase newFree packedLen awP2 awP3 awP4 aw1 aw2 aw3 aw4
    aw5
  have hbaseNat : base.toNat = fp.toNat + 32 := by
    dsimp [base]
    rw [uadd_toNat]
    have hlt : 32 + fp.toNat < UInt256.size := by omega
    change (32 + fp.toNat) % UInt256.size = fp.toNat + 32
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hfakeBaseNat : fakeBase.toNat = fp.toNat + 64 := by
    dsimp [fakeBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 32 < UInt256.size := by omega
    change (fp.toNat + 32 + 32) % UInt256.size = fp.toNat + 64
    rw [Nat.mod_eq_of_lt hlt]
  have hsecretBaseNat : secretBase.toNat = fp.toNat + 65 := by
    dsimp [secretBase]
    rw [uadd_toNat, hbaseNat]
    have hlt : (fp.toNat + 32) + 33 < UInt256.size := by omega
    change (fp.toNat + 32 + 33) % UInt256.size = fp.toNat + 65
    rw [Nat.mod_eq_of_lt hlt]
  have hnewFreeNat : newFree.toNat = fp.toNat + 97 := by
    dsimp [newFree]
    rw [uadd_toNat, hbaseNat]
    have hlt : 65 + (fp.toNat + 32) < UInt256.size := by omega
    change (65 + (fp.toNat + 32)) % UInt256.size = fp.toNat + 97
    rw [Nat.mod_eq_of_lt hlt]
    omega
  have hpackedLenNat : packedLen.toNat = 65 := by
    have hsub1 : (UInt256.sub newFree fp).toNat = 97 := by
      rw [usub_toNat]
      · rw [hnewFreeNat]
        omega
      · rw [hnewFreeNat]
        omega
    dsimp [packedLen]
    rw [usub_toNat]
    · rw [hsub1]
      change 97 - 32 = 65
      norm_num
    · rw [hsub1]
      change 32 ≤ 97
      norm_num
  have hawP1_ge : 3 ≤ awP1.toNat := by
    simpa [awP1] using scratch_reveal_aw_M_ge3
      (aw := aw) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) haw
  have hawP1_small : awP1.toNat * 32 < UInt256.size := by
    simpa [awP1] using scratch_reveal_aw_M_small
      (aw := aw) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) hawSmall
      (by native_decide)
  have hawP2_ge : 3 ≤ awP2.toNat := by
    simpa [awP2] using scratch_reveal_aw_M_ge3
      (aw := awP1) (off := base) (len := ⟨32⟩) hawP1_ge
  have hawP2_small : awP2.toNat * 32 < UInt256.size := by
    simpa [awP2] using scratch_reveal_aw_M_small
      (aw := awP1) (off := base) (len := ⟨32⟩) hawP1_small
      (by
        rw [hbaseNat]
        change fp.toNat + 32 + 32 + 31 < UInt256.size
        omega)
  have hawP3_ge : 3 ≤ awP3.toNat := by
    simpa [awP3] using scratch_reveal_aw_M_ge3
      (aw := awP2) (off := fakeBase) (len := ⟨32⟩) hawP2_ge
  have hawP3_small : awP3.toNat * 32 < UInt256.size := by
    simpa [awP3] using scratch_reveal_aw_M_small
      (aw := awP2) (off := fakeBase) (len := ⟨32⟩) hawP2_small
      (by
        rw [hfakeBaseNat]
        change fp.toNat + 64 + 32 + 31 < UInt256.size
        omega)
  have hawP4_ge : 3 ≤ awP4.toNat := by
    simpa [awP4] using scratch_reveal_aw_M_ge3
      (aw := awP3) (off := secretBase) (len := ⟨32⟩) hawP3_ge
  have hawP4_small : awP4.toNat * 32 < UInt256.size := by
    simpa [awP4] using scratch_reveal_aw_M_small
      (aw := awP3) (off := secretBase) (len := ⟨32⟩) hawP3_small
      (by
        rw [hsecretBaseNat]
        change fp.toNat + 65 + 32 + 31 < UInt256.size
        omega)
  have haw1_ge : 3 ≤ aw1.toNat := by
    simpa [aw1] using scratch_reveal_aw_M_ge3
      (aw := awP4) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) hawP4_ge
  have haw1_small : aw1.toNat * 32 < UInt256.size := by
    simpa [aw1] using scratch_reveal_aw_M_small
      (aw := awP4) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) hawP4_small
      (by native_decide)
  have haw2_ge : 3 ≤ aw2.toNat := by
    simpa [aw2] using scratch_reveal_aw_M_ge3
      (aw := aw1) (off := fp) (len := ⟨32⟩) haw1_ge
  have haw2_small : aw2.toNat * 32 < UInt256.size := by
    simpa [aw2] using scratch_reveal_aw_M_small
      (aw := aw1) (off := fp) (len := ⟨32⟩) haw1_small
      (by
        change fp.toNat + 32 + 31 < UInt256.size
        omega)
  have haw3_ge : 3 ≤ aw3.toNat := by
    simpa [aw3] using scratch_reveal_aw_M_ge3
      (aw := aw2) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) haw2_ge
  have haw3_small : aw3.toNat * 32 < UInt256.size := by
    simpa [aw3] using scratch_reveal_aw_M_small
      (aw := aw2) (off := (⟨64⟩ : UInt256)) (len := ⟨32⟩) haw2_small
      (by native_decide)
  have haw4_ge : 3 ≤ aw4.toNat := by
    simpa [aw4] using scratch_reveal_aw_M_ge3
      (aw := aw3) (off := fp) (len := ⟨32⟩) haw3_ge
  have haw4_small : aw4.toNat * 32 < UInt256.size := by
    simpa [aw4] using scratch_reveal_aw_M_small
      (aw := aw3) (off := fp) (len := ⟨32⟩) haw3_small
      (by
        change fp.toNat + 32 + 31 < UInt256.size
        omega)
  have haw5_ge : 3 ≤ aw5.toNat := by
    simpa [aw5] using scratch_reveal_aw_M_ge3
      (aw := aw4) (off := base) (len := packedLen) haw4_ge
  have haw5_small : aw5.toNat * 32 < UInt256.size := by
    simpa [aw5] using scratch_reveal_aw_M_small
      (aw := aw4) (off := base) (len := packedLen) haw4_small
      (by
        rw [hbaseNat, hpackedLenNat]
        change fp.toNat + 32 + 65 + 31 < UInt256.size
        omega)
  exact ⟨hnewFreeNat, hpackedLenNat, haw2_ge, haw2_small, hawP4_ge, hawP4_small,
    haw3_ge, haw3_small, haw5_ge, haw5_small⟩

theorem scratch_mload_of_read {mem : ByteArray} {fp packedLen aw : UInt256}
    (hmem : fp.toNat < mem.size)
    (haw : ¬ fp ≥ aw * ⟨32⟩)
    (hread : mem.readWithPadding fp.toNat 32 = UInt256.toByteArray packedLen) :
    (if fp.toNat ≥ mem.size ∨ fp ≥ aw * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding fp.toNat 32))) =
      packedLen :=
  mloadWordValue_of_readWithPadding hmem haw hread

theorem scratch_evalExpr_reveal_value_of_secretStoreOf (evm : EVM.State)
    (locals : Store) (i value secret : UInt256) (fake : Bool) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
      (.var "value") = .ok (.int (Int.ofNat value.toNat)) :=
  evalExpr_reveal_var_int evm
    (scratch_revealSecretStoreOf locals evm i value secret fake) "value"
    (Int.ofNat value.toNat)
    (scratch_revealSecretStoreOf_value_get locals evm i value secret fake)

theorem scratch_evalExpr_reveal_fake_of_secretStoreOf (evm : EVM.State)
    (locals : Store) (i value secret : UInt256) (fake : Bool) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
      (.var "fake") = .ok (.bool fake) :=
  evalExpr_reveal_var_value evm
    (scratch_revealSecretStoreOf locals evm i value secret fake) "fake" (.bool fake)
    (scratch_revealSecretStoreOf_fake_get locals evm i value secret fake)

theorem scratch_evalExpr_reveal_secret_of_secretStoreOf (evm : EVM.State)
    (locals : Store) (i value secret : UInt256) (fake : Bool) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
      (.var "secret") =
        .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)) :=
  evalExpr_reveal_var_value evm
    (scratch_revealSecretStoreOf locals evm i value secret fake) "secret"
    (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
    (by
      unfold scratch_revealSecretStoreOf
      rw [store_get_self])

theorem scratch_revealSecretStoreOf_get_preserve (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) {name : Ident}
    (hsecret : ("secret" == name) = false)
    (hfake : ("fake" == name) = false)
    (hvalue : ("value" == name) = false)
    (hbid : ("bidToCheck" == name) = false) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? name =
      locals.get? name := by
  unfold scratch_revealSecretStoreOf scratch_revealFakeStoreOf scratch_revealValueStoreOf
    scratch_revealBidToCheckStoreOf
  rw [store_get_ne4]
  · exact hbid
  · exact hvalue
  · exact hfake
  · exact hsecret

theorem scratch_revealSecretStoreOf_i_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat))) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "i" =
      some (.int (Int.ofNat i.toNat)) := by
  rw [scratch_revealSecretStoreOf_get_preserve]
  · exact hi
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealSecretStoreOf_length_get (locals : Store) (evm : EVM.State)
    (i len value secret : UInt256) (fake : Bool)
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat))) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "length" =
      some (.int (Int.ofNat len.toNat)) := by
  rw [scratch_revealSecretStoreOf_get_preserve]
  · exact hlen
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealSecretStoreOf_bids_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool)
    (hbids : locals.get? "bids" = none) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "bids" = none := by
  rw [scratch_revealSecretStoreOf_get_preserve]
  · exact hbids
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealSecretStoreOf_values_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) (values : List Value)
    (hvalues : locals.get? "values" = some (.array values)) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "values" =
      some (.array values) := by
  rw [scratch_revealSecretStoreOf_get_preserve]
  · exact hvalues
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealSecretStoreOf_fakes_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) (fakes : List Value)
    (hfakes : locals.get? "fakes" = some (.array fakes)) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "fakes" =
      some (.array fakes) := by
  rw [scratch_revealSecretStoreOf_get_preserve]
  · exact hfakes
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealSecretStoreOf_secrets_get (locals : Store) (evm : EVM.State)
    (i value secret : UInt256) (fake : Bool) (secrets : List Value)
    (hsecrets : locals.get? "secrets" = some (.array secrets)) :
    (scratch_revealSecretStoreOf locals evm i value secret fake).get? "secrets" =
      some (.array secrets) := by
  rw [scratch_revealSecretStoreOf_get_preserve]
  · exact hsecrets
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundAddedStoreOf_get_preserve (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) {name : Ident}
    (hrefund : ("refund" == name) = false)
    (hsecret : ("secret" == name) = false)
    (hfake : ("fake" == name) = false)
    (hvalue : ("value" == name) = false)
    (hbid : ("bidToCheck" == name) = false) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get? name =
      locals.get? name := by
  unfold scratch_revealRefundAddedStoreOf scratch_revealSecretStoreOf scratch_revealFakeStoreOf
    scratch_revealValueStoreOf scratch_revealBidToCheckStoreOf
  rw [store_get_ne5]
  · exact hbid
  · exact hvalue
  · exact hfake
  · exact hsecret
  · exact hrefund

theorem scratch_revealRefundAddedStoreOf_i_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat))) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get? "i" =
      some (.int (Int.ofNat i.toNat)) := by
  rw [scratch_revealRefundAddedStoreOf_get_preserve]
  · exact hi
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundAddedStoreOf_length_get (locals : Store) (evm : EVM.State)
    (i refund len value secret deposit : UInt256) (fake : Bool)
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat))) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
        "length" =
      some (.int (Int.ofNat len.toNat)) := by
  rw [scratch_revealRefundAddedStoreOf_get_preserve]
  · exact hlen
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundAddedStoreOf_bids_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool)
    (hbids : locals.get? "bids" = none) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
        "bids" = none := by
  rw [scratch_revealRefundAddedStoreOf_get_preserve]
  · exact hbids
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundAddedStoreOf_values_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) (values : List Value)
    (hvalues : locals.get? "values" = some (.array values)) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
        "values" =
      some (.array values) := by
  rw [scratch_revealRefundAddedStoreOf_get_preserve]
  · exact hvalues
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundAddedStoreOf_fakes_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) (fakes : List Value)
    (hfakes : locals.get? "fakes" = some (.array fakes)) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
        "fakes" =
      some (.array fakes) := by
  rw [scratch_revealRefundAddedStoreOf_get_preserve]
  · exact hfakes
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundAddedStoreOf_secrets_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fake : Bool) (secrets : List Value)
    (hsecrets : locals.get? "secrets" = some (.array secrets)) :
    (scratch_revealRefundAddedStoreOf locals evm i refund value secret deposit fake).get?
        "secrets" =
      some (.array secrets) := by
  rw [scratch_revealRefundAddedStoreOf_get_preserve]
  · exact hsecrets
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundPlacedStoreOf_get_preserve (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) {name : Ident}
    (hrefund : ("refund" == name) = false)
    (hok : ("ok" == name) = false)
    (hsecret : ("secret" == name) = false)
    (hfake : ("fake" == name) = false)
    (hvalue : ("value" == name) = false)
    (hbid : ("bidToCheck" == name) = false) :
    (scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit).get? name =
      locals.get? name := by
  unfold scratch_revealRefundPlacedStoreOf
  rw [store_get_ne2]
  · exact scratch_revealRefundAddedStoreOf_get_preserve locals evm i refund value secret
      deposit false hrefund hsecret hfake hvalue hbid
  · exact hok
  · exact hrefund

theorem scratch_revealRefundPlacedStoreOf_i_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat))) :
    (scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit).get? "i" =
      some (.int (Int.ofNat i.toNat)) := by
  rw [scratch_revealRefundPlacedStoreOf_get_preserve]
  · exact hi
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundPlacedStoreOf_length_get (locals : Store) (evm : EVM.State)
    (i refund len value secret deposit : UInt256)
    (hlen : locals.get? "length" = some (.int (Int.ofNat len.toNat))) :
    (scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit).get?
        "length" =
      some (.int (Int.ofNat len.toNat)) := by
  rw [scratch_revealRefundPlacedStoreOf_get_preserve]
  · exact hlen
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundPlacedStoreOf_bids_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256)
    (hbids : locals.get? "bids" = none) :
    (scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit).get? "bids" =
      none := by
  rw [scratch_revealRefundPlacedStoreOf_get_preserve]
  · exact hbids
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundPlacedStoreOf_values_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (values : List Value)
    (hvalues : locals.get? "values" = some (.array values)) :
    (scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit).get? "values" =
      some (.array values) := by
  rw [scratch_revealRefundPlacedStoreOf_get_preserve]
  · exact hvalues
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundPlacedStoreOf_fakes_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (fakes : List Value)
    (hfakes : locals.get? "fakes" = some (.array fakes)) :
    (scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit).get? "fakes" =
      some (.array fakes) := by
  rw [scratch_revealRefundPlacedStoreOf_get_preserve]
  · exact hfakes
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_revealRefundPlacedStoreOf_secrets_get (locals : Store) (evm : EVM.State)
    (i refund value secret deposit : UInt256) (secrets : List Value)
    (hsecrets : locals.get? "secrets" = some (.array secrets)) :
    (scratch_revealRefundPlacedStoreOf locals evm i refund value secret deposit).get? "secrets" =
      some (.array secrets) := by
  rw [scratch_revealRefundPlacedStoreOf_get_preserve]
  · exact hsecrets
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem scratch_evalPackedArgs_cons {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ty : ABIType} {e : Expr} {v : Value} {head tailBytes : List UInt8}
    {rest : List (ABIType × Expr)}
    (he : evalExpr? cfg solm evm e = .ok v)
    (henc : encodePackedValue? ty v = some head)
    (htail : evalPackedArgs? cfg solm evm rest = .ok tailBytes) :
    evalPackedArgs? cfg solm evm ((ty, e) :: rest) = .ok (head ++ tailBytes) := by
  rw [evalPackedArgs?]
  simp only [he, henc, htail, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem scratch_evalPackedArgs_reveal_tail_secret_of_secretStoreOf
    (evm : EVM.State) (locals : Store) (i value secret : UInt256) (fake : Bool) :
    evalPackedArgs? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
      [(bytes32, .var "secret")] = .ok (EVM.Word.toBytesBE secret) := by
  simpa using
    (scratch_evalPackedArgs_cons
      (cfg := blindAuctionConfig)
      (solm :=
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake })
      (evm := evm) (ty := bytes32) (e := .var "secret")
      (v := .fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret))
      (head := EVM.Word.toBytesBE secret) (tailBytes := []) (rest := [])
      (scratch_evalExpr_reveal_secret_of_secretStoreOf evm locals i value secret fake)
      (scratch_encodePacked_bytes32 secret)
      (by rw [evalPackedArgs?]; rfl))

theorem scratch_evalPackedArgs_reveal_tail_fake_secret_of_secretStoreOf
    (evm : EVM.State) (locals : Store) (i value secret : UInt256) (fake : Bool) :
    evalPackedArgs? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
      [(boolTy, .var "fake"), (bytes32, .var "secret")] =
        .ok ([if fake then (1 : UInt8) else 0] ++ EVM.Word.toBytesBE secret) := by
  exact
    scratch_evalPackedArgs_cons
      (cfg := blindAuctionConfig)
      (solm :=
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake })
      (evm := evm) (ty := boolTy) (e := .var "fake")
      (v := .bool fake) (head := [if fake then (1 : UInt8) else 0])
      (tailBytes := EVM.Word.toBytesBE secret) (rest := [(bytes32, .var "secret")])
      (scratch_evalExpr_reveal_fake_of_secretStoreOf evm locals i value secret fake)
      (scratch_encodePacked_bool fake)
      (scratch_evalPackedArgs_reveal_tail_secret_of_secretStoreOf evm locals i value secret fake)

theorem scratch_evalPackedArgs_reveal_of_secretStoreOf (evm : EVM.State)
    (locals : Store) (i value secret : UInt256) (fake : Bool) :
    evalPackedArgs? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
      [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")] =
        .ok (scratch_revealPackedBytes value fake secret) := by
  simpa [scratch_revealPackedBytes, List.append_assoc] using
    (scratch_evalPackedArgs_cons
      (cfg := blindAuctionConfig)
      (solm :=
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake })
      (evm := evm) (ty := uint256) (e := .var "value")
      (v := .int (Int.ofNat value.toNat)) (head := EVM.Word.toBytesBE value)
      (tailBytes := [if fake then (1 : UInt8) else 0] ++ EVM.Word.toBytesBE secret)
      (rest := [(boolTy, .var "fake"), (bytes32, .var "secret")])
      (scratch_evalExpr_reveal_value_of_secretStoreOf evm locals i value secret fake)
      (scratch_encodePacked_uint256 value)
      (scratch_evalPackedArgs_reveal_tail_fake_secret_of_secretStoreOf evm locals i value
        secret fake))

theorem scratch_evalExpr_revealPackedHash_of_secretStoreOf (evm : EVM.State)
    (locals : Store) (i value secret : UInt256) (fake : Bool) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
      scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList) := by
  rw [scratch_revealPackedHashExpr]
  rw [evalExpr?]
  rw [evalExpr?]
  simp only [scratch_evalPackedArgs_reveal_of_secretStoreOf evm locals i value secret fake,
    EvalResult.bind, bind, pure]

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_callMade_fromCall_general {I} {g : Sat256}
    {s0 : State} {k C : ℕ}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {gasArg refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hbalance : refund ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (rd : RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, refund, freePtr, ⟨0⟩, freePtr, ⟨0⟩,
        freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k C)
    (hawCall :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat (⟨0⟩ : UInt256).toNat)
          freePtr.toNat (⟨0⟩ : UInt256).toNat) = aw) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (revealScratchSenderWord I))
          (toExecute σ (AccountAddress.ofUInt256 (revealScratchSenderWord I)))
          callGas (UInt256.ofNat I.gasPrice) refund refund
          ByteArray.empty (I.depth + 1) I.header I.perm)
      ∧ o.size < UInt256.size
      ∧ RD blindAuctionBytecode I g s0 ⟨1350⟩
          [(if z then ⟨1⟩ else ⟨0⟩), freePtr, refund, revealScratchSenderWord I,
            ⟨0⟩, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
            fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
          mem aw o (cA', σ') k' C' := by
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd1350₀, hoSize⟩ :=
    RD.callValueMadeEmptyInOut rd (by decide) hperm hbalance hdepth (by simp)
  have hawCall' :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat 0) freePtr.toNat 0) = aw := by
    simpa using hawCall
  have hpc : (⟨1349⟩ : UInt256) + ⟨1⟩ = ⟨1350⟩ := by
    decide
  exact ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, hoSize,
    by simpa [revealScratchSenderWord, hpc, hawCall'] using rd1350₀⟩

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_callDepth_fromCall_general {I} {g : Sat256}
    {s0 : State} {k C : ℕ}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {gasArg refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hdepth : I.depth = 1024)
    (rd : RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, refund, freePtr, ⟨0⟩, freePtr, ⟨0⟩,
        freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k C)
    (hawCall :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat (⟨0⟩ : UInt256).toNat)
          freePtr.toNat (⟨0⟩ : UInt256).toNat) = aw) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1350⟩
      [⟨0⟩, freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd1350₀⟩ :=
    RD.callValueDepthLimitEmptyInOut rd hperm (by decide) hdepth (by simp)
  have hawCall' :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat 0) freePtr.toNat 0) = aw := by
    simpa using hawCall
  have hpc : (⟨1349⟩ : UInt256) + ⟨1⟩ = ⟨1350⟩ := by
    decide
  exact ⟨k', C', by simpa [revealScratchSenderWord, hpc, hawCall'] using rd1350₀⟩

set_option maxHeartbeats 1000000 in
theorem scratch_blindAuctionRevealX_callInsufficient_fromCall_general {I} {g : Sat256}
    {s0 : State} {k C : ℕ}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {gasArg refund len freePtr revealEnd biddingEnd valuesLen valuesEnd fakesLen fakesEnd
      secretsLen secretsEnd sel : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hbalance : ¬ refund ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance)))
    (hdepth : I.depth.val < 1024)
    (rd : RD blindAuctionBytecode I g s0 ⟨1349⟩
      [gasArg, revealScratchSenderWord I, refund, freePtr, ⟨0⟩, freePtr, ⟨0⟩,
        freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k C)
    (hawCall :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat (⟨0⟩ : UInt256).toNat)
          freePtr.toNat (⟨0⟩ : UInt256).toNat) = aw) :
    ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1350⟩
      [⟨0⟩, freePtr, refund, revealScratchSenderWord I, ⟨0⟩, refund, len,
        revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen,
        valuesEnd, ⟨276⟩, sel]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd1350₀⟩ :=
    RD.callValueInsufficientBalanceEmptyInOut rd hperm (by decide) hbalance hdepth (by simp)
  have hawCall' :
      UInt256.ofNat
        (MachineState.M (MachineState.M aw.toNat freePtr.toNat 0) freePtr.toNat 0) = aw := by
    simpa using hawCall
  have hpc : (⟨1349⟩ : UInt256) + ⟨1⟩ = ⟨1350⟩ := by
    decide
  exact ⟨k', C', by simpa [revealScratchSenderWord, hpc, hawCall'] using rd1350₀⟩

def scratch_revealPanicSelector : UInt256 :=
  UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩

noncomputable def scratch_revealPanicMem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray scratch_revealPanicSelector).write 0 mem 0 32

noncomputable def scratch_revealPanicMem (panicCode : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray panicCode).write 0 (scratch_revealPanicMem0 mem) 4 32

theorem RD.blindAuctionPanic32Revert1967 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD blindAuctionBytecode ee g s0 ⟨1967⟩ R mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat)
    (hov : R.length + 2 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ = scratch_revealPanicSelector := by
    rfl
  have rd1974₀ := evm_run h with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd1974 := rd1974₀
  rw [hsel] at rd1974
  have rd1978 := evm_run rd1974 with [
    raw mstore 0 (scratch_revealPanicMem0 mem) aw
      (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [scratch_reveal_aw_mstore0_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore0_of_ge3 haw) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩]
  have rd1984 := evm_run rd1978 with [
    raw mstore 0 (scratch_revealPanicMem ⟨0x32⟩ mem) aw
      (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨4⟩ : UInt256).toNat = 4 by native_decide]
        rw [scratch_reveal_aw_mstore4_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore4_of_ge3 haw) (by evm_ov),
    push1 ⟨0x24⟩, push0]
  exact rd1984.rev 0 (by decide)
    (fun s haws hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
      rw [show (⟨36⟩ : UInt256).toNat = 36 by native_decide]
      have hM : MachineState.M aw.toNat 0 36 = aw.toNat := by
        simp [MachineState.M]
        omega
      rw [hM, u256_ofNat_toNat]
      omega)
    (by evm_ov)

theorem RD.blindAuctionPanic11Revert2025 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD blindAuctionBytecode ee g s0 ⟨2025⟩ R mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat)
    (hov : R.length + 2 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ = scratch_revealPanicSelector := by
    rfl
  have rd2032₀ := evm_run h with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2032 := rd2032₀
  rw [hsel] at rd2032
  have rd2036 := evm_run rd2032 with [
    raw mstore 0 (scratch_revealPanicMem0 mem) aw
      (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [scratch_reveal_aw_mstore0_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore0_of_ge3 haw) (by evm_ov),
    push1 ⟨0x11⟩, push1 ⟨4⟩]
  have rd2042 := evm_run rd2036 with [
    raw mstore 0 (scratch_revealPanicMem ⟨0x11⟩ mem) aw
      (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨4⟩ : UInt256).toNat = 4 by native_decide]
        rw [scratch_reveal_aw_mstore4_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore4_of_ge3 haw) (by evm_ov),
    push1 ⟨0x24⟩, push0]
  exact rd2042.rev 0 (by decide)
    (fun s haws hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
      rw [show (⟨36⟩ : UInt256).toNat = 36 by native_decide]
      have hM : MachineState.M aw.toNat 0 36 = aw.toNat := by
        simp [MachineState.M]
        omega
      rw [hM, u256_ofNat_toNat]
      omega)
    (by evm_ov)

theorem scratch_blindAuctionCheckedAddOverflowRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    (rd : RD blindAuctionBytecode ee g s0 ⟨2045⟩ (a :: b :: ret :: R)
      mem aw rdata acc k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (haw : 3 ≤ aw.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev blindAuctionBytecode g s0 := by
  have hgt := scratch_blindAuctionCheckedAddOverflowGt a b hover
  have rd2052₀ := evm_run rd with [jumpdest, dup1, dup3, add, dup1, dup3, gt]
  have rd2052 := rd2052₀
  rw [hgt] at rd2052
  have rd2025 := evm_run rd2052 with [
    iszero, push2 ⟨1654⟩, jumpiNT (by decide), push2 ⟨1654⟩, push2 ⟨2025⟩,
    jump (by jump_dest)]
  exact RD.blindAuctionPanic11Revert2025 rd2025 haw (by simp at hov ⊢; omega)

theorem scratch_revealBid_arrayIndexInBounds_revert (evm : EVM.State) (i curLen : UInt256)
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hbound : curLen.toNat ≤ i.toNat) :
    arrayIndexInBounds? blindAuctionConfig evm blindAuctionContract.storage "bids"
      [.mindex (.address evm.executionEnv.source)] (.int (Int.ofNat i.toNat)) = .revert := by
  simp [arrayIndexInBounds?, storageTypeAt?, storageTypeStep?, blindAuctionConfig,
    blindAuctionStorageLayout, blindAuctionContract, storageDecls, bidStructTy, uint256St,
    bytes32St, blindAuctionStorageLocLoad_uint256, hlen]
  omega

theorem scratch_resolveStorageRef_reveal_bid_revert_of_get (evm : EVM.State) (locals : Store)
    (i curLen : UInt256)
    (hbids : locals.get? "bids" = none)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hbound : curLen.toNat ≤ i.toNat) :
    resolveStorageRef? blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm (bidElemRef sender (.var "i")) = .revert := by
  have hbounds := scratch_revealBid_arrayIndexInBounds_revert evm i curLen hlen hbound
  have her :
      evalStorageRef blindAuctionConfig
        { contract := blindAuctionContract, locals := locals }
        evm (bidElemRef sender (.var "i")) = .revert := by
    simp only [bidElemRef, sender, evalStorageRef, evalStorageRefSteps.eq_def,
      evalStorageRefStep.eq_def, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, List.nil_append, hi]
    rw [hbounds]
  unfold resolveStorageRef?
  simp only [bidElemRef]
  have hbids' : locals["bids"]? = none := by
    simpa [Std.HashMap.get?_eq_getElem?] using hbids
  have her' :
      evalStorageRef blindAuctionConfig { contract := blindAuctionContract, locals := locals }
        evm { base := "bids", steps := [StorageRefStep.mindex sender,
          StorageRefStep.aindex (.var "i")] } = .revert := by
    simpa [bidElemRef] using her
  simp [hbids', her']

theorem scratch_revealLoopBody_revert_bounds_of_get (evm : EVM.State) (locals : Store)
    (i curLen : UInt256)
    (hbids : locals.get? "bids" = none)
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hbound : curLen.toNat ≤ i.toNat) :
    ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := locals }
      evm scratch_revealLoopBodyStmts .reverted := by
  unfold scratch_revealLoopBodyStmts
  exact ExecBlock.consRevert
    (ExecStmt.letStorageRevert
      (scratch_resolveStorageRef_reveal_bid_revert_of_get evm locals i curLen hbids hi hlen
        hbound))

theorem scratch_blindAuctionRevealX_loopBody_toElemSlot_curLen {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k C)
    (haw0 : UInt256.ofNat (MachineState.M aw.toNat 0 32) = aw)
    (haw32 : UInt256.ofNat (MachineState.M aw.toNat 32 32) = aw)
    (haw64 : UInt256.ofNat (MachineState.M aw.toNat 0 64) = aw)
    (hbaseHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hbound : i.toNat < curLen.toNat)
    (hdataHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
            ((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
              ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32) 0 32).readWithPadding 0 32))) =
        uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I)))) :
    ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1069⟩
      [bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)), i, refund, len, revealEnd,
        biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem' aw' rdata acc k' C' := by
  let mem1 : ByteArray := (UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32
  let mem2 : ByteArray := (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 mem1 32 32
  let mem3 : ByteArray := (UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0 mem2 0 32
  have rd' : RD blindAuctionBytecode I g s0 ⟨1023⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C := by
    simpa [scratch_revealEvmLoopStack] using rd
  have rd1027 := evm_run rd' with [
    caller, push0, swap1, dup2,
    raw mstore 0 mem1 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [haw0]
        simp)
      (by rfl) haw0 (by evm_ov)]
  have rd1033 := evm_run rd1027 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 mem2 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        rw [haw32]
        simp)
      (by rfl) haw32 (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (revealScratchBidsLengthSlot I) aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
        rw [haw64]
        simp)
      (by simpa [mem2, mem1, revealScratchSenderWord] using hbaseHash) haw64
      (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1039₀⟩ := rd1033.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1039⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1039⟩
      [curLen, revealScratchBidsLengthSlot I, ⟨0⟩, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem2 aw rdata acc k' C' := by
    exact ⟨_, _, by simpa [hlenLoad] using rd1039₀⟩
  have hlt : UInt256.lt i curLen = ⟨1⟩ := ult_one hbound
  have rd1047₀ := evm_run rd1039 with [dup4, swap1, dup2, lt]
  have rd1047 := rd1047₀
  rw [hlt] at rd1047
  have rd1054 := evm_run rd1047 with [
    push2 ⟨1054⟩, jumpiT one_ne_zero_uint (by jump_dest), jumpdest]
  have rd1062 := evm_run rd1054 with [
    swap1, push0,
    raw mstore 0 mem3 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [haw0]
        simp)
      (by rfl) haw0 (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0
      (uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))))
      aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        rw [haw0]
        simp)
      (by simpa [mem3, mem2, mem1, revealScratchSenderWord] using hdataHash) haw0
      (by evm_ov)]
  have hslot :
      UInt256.mul ⟨2⟩ i +
          uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))) =
        bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)) := by
    have hmul : UInt256.mul ⟨2⟩ i = UInt256.mul i ⟨2⟩ := by
      apply u256_inj
      show ((⟨2⟩ : UInt256).val * i.val).val = (i.val * (⟨2⟩ : UInt256).val).val
      rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
    rw [hmul]
    rw [u256_add_comm]
    exact scratch_revealBidsElemSlot_eq I i
  have rd1069 := evm_run rd1062 with [swap1, push1 ⟨2⟩, mul, add, swap1, pop]
  have hpc1069 :
      (⟨1054⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ :
          UInt256) = ⟨1069⟩ := by
    native_decide
  exact ⟨mem3, aw, _, _, by simpa [hslot, hpc1069] using rd1069⟩

theorem scratch_blindAuctionRevealX_loopBody_bounds_revert {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata acc k C)
    (haw : 3 ≤ aw.toNat)
    (hbaseHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (acc.2.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hbound : curLen.toNat ≤ i.toNat) :
    RDrev blindAuctionBytecode g s0 := by
  let mem1 : ByteArray := (UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32
  let mem2 : ByteArray := (UInt256.toByteArray (⟨4⟩ : UInt256)).write 0 mem1 32 32
  have rd' : RD blindAuctionBytecode I g s0 ⟨1023⟩
      [i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd,
        valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata acc k C := by
    simpa [scratch_revealEvmLoopStack] using rd
  have rd1027 := evm_run rd' with [
    caller, push0, swap1, dup2,
    raw mstore 0 mem1 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [scratch_reveal_aw_mstore0_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore0_of_ge3 haw) (by evm_ov)]
  have rd1033 := evm_run rd1027 with [
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 mem2 aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨32⟩ : UInt256).toNat = 32 by native_decide]
        rw [scratch_reveal_aw_mstore32_of_ge3 haw]
        simp)
      (by rfl) (scratch_reveal_aw_mstore32_of_ge3 haw) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (revealScratchBidsLengthSlot I) aw (by decide)
      (fun s haws hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstk]
        rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide]
        rw [scratch_reveal_aw_keccak64_of_ge3 haw]
        simp)
      (by simpa [mem2, mem1, revealScratchSenderWord] using hbaseHash)
      (scratch_reveal_aw_keccak64_of_ge3 haw)
      (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1039₀⟩ := rd1033.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd1039⟩ : ∃ k' C', RD blindAuctionBytecode I g s0 ⟨1039⟩
      [curLen, revealScratchBidsLengthSlot I, ⟨0⟩, i, refund, len, revealEnd, biddingEnd,
        secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem2 aw rdata acc k' C' := by
    exact ⟨_, _, by simpa [hlenLoad] using rd1039₀⟩
  have hlt : UInt256.lt i curLen = ⟨0⟩ := ult_zero hbound
  have rd1047₀ := evm_run rd1039 with [dup4, swap1, dup2, lt]
  have rd1047 := rd1047₀
  rw [hlt] at rd1047
  have rd1967 := evm_run rd1047 with [
    push2 ⟨1054⟩, jumpiNT (by decide),
    push2 ⟨1054⟩, push2 ⟨1967⟩, jump (by jump_dest)]
  exact RD.blindAuctionPanic32Revert1967 rd1967 haw (by simp)

theorem scratch_revealLoopBody_bounds_pair {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel : UInt256}
    (rd : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, σ) k C)
    (haw : 3 ≤ aw.toNat)
    (hbaseHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hbound : curLen.toNat ≤ i.toNat)
    (hbids : L.get? "bids" = none)
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts .reverted ∧
      RDrev blindAuctionBytecode g s0 := by
  exact ⟨
    scratch_revealLoopBody_revert_bounds_of_get evm L i curLen hbids hi hlen hbound,
    scratch_blindAuctionRevealX_loopBody_bounds_revert
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (i := i) (refund := refund) (len := len) (curLen := curLen)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel)
      rd haw hbaseHash hlenLoad hbound⟩

theorem scratch_revealLoopBody_fakeInvalid_pair {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value fakeWord : UInt256}
    {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1023⟩
      (scratch_revealEvmLoopStack i refund len revealEnd biddingEnd secretsLen secretsEnd
        fakesLen fakesEnd valuesLen valuesEnd sel)
      mem aw rdata (cA, σ) k C)
    (haw : 3 ≤ aw.toNat)
    (hbaseHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
            ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32).readWithPadding 0 64))) =
        revealScratchBidsLengthSlot I)
    (hlenLoad :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD (revealScratchBidsLengthSlot I) ⟨0⟩) = curLen)
    (hboundBids : i.toNat < curLen.toNat)
    (hdataHash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          (((UInt256.toByteArray (revealScratchBidsLengthSlot I)).write 0
            ((UInt256.toByteArray (⟨4⟩ : UInt256)).write 0
              ((UInt256.toByteArray (revealScratchSenderWord I)).write 0 mem 0 32)
              32 32) 0 32).readWithPadding 0 32))) =
        uInt256OfByteArray (ffi.KEC (UInt256.toByteArray (revealScratchBidsLengthSlot I))))
    (hvalueBound : i.toNat < valuesLen.toNat)
    (hfakesBound : i.toNat < fakesLen.toNat)
    (hvalueLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + valuesEnd).toNat 32) =
        value)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) = fakeWord)
    (hfakeZero : fakeWord ≠ ⟨0⟩)
    (hfakeOne : fakeWord ≠ ⟨1⟩)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .revert) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts .reverted ∧
      RDrev blindAuctionBytecode g s0 := by
  obtain ⟨memSlot, awSlot, k1, C1, rd1069⟩ :=
    scratch_blindAuctionRevealX_loopBody_toElemSlot_curLen
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (i := i) (refund := refund) (len := len) (curLen := curLen) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) rd
      (scratch_reveal_aw_mstore0_of_ge3 haw)
      (scratch_reveal_aw_mstore32_of_ge3 haw)
      (scratch_reveal_aw_keccak64_of_ge3 haw)
      hbaseHash hlenLoad hboundBids hdataHash
  obtain ⟨k2, C2, rd1987⟩ :=
    scratch_blindAuctionRevealX_loopBody_loads_toFakeDecoder
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (mem := memSlot) (aw := awSlot) (rdata := rdata) (acc := (cA, σ))
      (slot := bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)))
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (value := value)
      rd1069 hvalueBound hfakesBound hvalueLoad
  exact ⟨
    scratch_revealLoopBody_revert_fake_invalid_of_get evm L values fakes secrets
      curLen i value fakeRaw hbids hvalues hfakes hi hlen hboundBids hboundValues
      hboundFakes hvalueLookup hfakeLookup hfakeNorm,
    scratch_blindAuctionRevealX_loopBody_fakeDecoder_invalid_revert
      (I := I) (g := g) (s0 := s0) (k := k2) (C := C2)
      (mem := memSlot) (aw := awSlot) (rdata := rdata) (acc := (cA, σ))
      (slot := bidsElemSlot (.address I.source) (.int (Int.ofNat i.toNat)))
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (value := value) (word := fakeWord)
      rd1987 hfakeSlt hfakeLoad hfakeZero hfakeOne⟩

theorem scratch_revealLoopBody_revert_refundOverflow_of_get (evm : EVM.State)
    (locals : Store) (values fakes secrets : List Value)
    (len refund i value secret blinded deposit : UInt256) (fake : Bool) (fakeRaw : Value)
    (hashBytes : List UInt8)
    (hbids : locals.get? "bids" = none)
    (hvalues : locals.get? "values" = some (.array values))
    (hfakes : locals.get? "fakes" = some (.array fakes))
    (hsecrets : locals.get? "secrets" = some (.array secrets))
    (hi : locals.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hrefund : locals.get? "refund" = some (.int (Int.ofNat refund.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hdeposit :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidDepositSlot evm i) = deposit)
    (hhash :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf locals evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩ hashBytes))
    (heq : EVM.Word.toBytesBE blinded = hashBytes)
    (hover : UInt256.size ≤ refund.toNat + deposit.toNat) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := locals } evm
      scratch_revealLoopBodyStmts .reverted := by
  let L4 := scratch_revealSecretStoreOf locals evm i value secret fake
  have hbidL4 :
      L4.get? "bidToCheck" =
        some (.storageRef (scratch_revealBidEvaledRef evm i) bidStructTy) := by
    simpa [L4] using scratch_revealSecretStoreOf_bid_get locals evm i value secret fake
  have hguard :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
          (.keccak256 (.abiEncodePacked
            [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")]))) =
          .ok (.bool false) := by
    simpa [scratch_revealPackedHashExpr, L4] using
      scratch_evalExpr_reveal_hash_guard_false evm L4 i blinded hashBytes hbidL4 hblinded
        (by simpa [L4] using hhash) heq
  have hrefundL4 :
      L4.get? "refund" = some (.int (Int.ofNat refund.toNat)) := by
    simpa [L4] using
      scratch_revealSecretStoreOf_refund_get locals evm i refund value secret fake hrefund
  have hadd :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))) =
          .revert :=
    scratch_evalExpr_reveal_refund_add_deposit_revert evm L4 i refund deposit hbidL4
      hrefundL4 hdeposit hover
  have htail :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L4 } evm
        (List.drop 4 scratch_revealLoopBodyStmts) .reverted := by
    change ExecBlock blindAuctionConfig
      { contract := blindAuctionContract, locals := L4 } evm
      [ .ite
          (.binary .ne (.storage (aliasF "bidToCheck" "blindedBid"))
            (.keccak256 (.abiEncodePacked
              [(uint256, .var "value"), (boolTy, .var "fake"), (bytes32, .var "secret")])))
          [.continue] [],
        .assign .localVar { base := "refund" }
          (u256 (.binary .add (.var "refund") (.storage (aliasF "bidToCheck" "deposit")))),
        .ite
          (.binary .and (.unary .not (.var "fake"))
            (.binary .ge (.storage (aliasF "bidToCheck" "deposit")) (.var "value")))
          [ .internalCall "placeBid" [sender, .var "value"] "ok",
            .ite (.var "ok")
              [ .assign .localVar { base := "refund" }
                  (u256 (.binary .sub (.var "refund") (.var "value"))) ] [] ] [],
        .assign .storage (aliasF "bidToCheck" "blindedBid") (.cast (.intLit 0) bytes32St) ]
      .reverted
    refine ExecBlock.consNormal (ExecStmt.iteFalse hguard ExecBlock.nil) ?_
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert hadd)
  exact scratch_revealLoopBody_prefix_exec_of_get evm locals values fakes secrets len refund i
    value secret fake fakeRaw hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
    hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup htail

theorem scratch_revealLoopBody_hashMismatch_fromPacked_pair {I} {g : Sat256} {s0 : State}
    {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd
      valuesLen valuesEnd sel value secret fakeWord blinded fp : UInt256}
    {fake : Bool} {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1207⟩
      [((⟨65⟩ : UInt256) + ((⟨32⟩ : UInt256) + fp)), secret, fakeWord, value, slot,
        i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlenPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hhashPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)))
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨0⟩)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundBids : i.toNat < curLen.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhashEval :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf L evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList)) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.continue
          { contract := blindAuctionContract,
            locals := scratch_revealSecretStoreOf L evm i value secret fake }
          evm) ∧
      ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
          secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        mem' aw' rdata (cA, σ) k' C' := by
  have hne :
      EVM.Word.toBytesBE blinded ≠
        (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList := by
    exact scratch_revealPackedHash_ne_of_u256_eq_zero
      (blinded := blinded) (value := value) (secret := secret) (fake := fake) hflag
  have hsrc :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.continue
          { contract := blindAuctionContract,
            locals := scratch_revealSecretStoreOf L evm i value secret fake }
          evm) := by
    exact scratch_revealLoopBody_continue_hash_mismatch_of_get evm L values fakes secrets
      curLen refund i value secret blinded fake fakeRaw
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList
      hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues hboundFakes
      hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded hhashEval hne
  obtain ⟨k1, C1, rd1235⟩ :=
    scratch_blindAuctionRevealX_loopBody_packed_suffix
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (fp := fp)
      (hash :=
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)))
      (blinded := blinded) (flag := ⟨0⟩)
      rd hfp hlenPacked hhashPacked hstore hflag
  obtain ⟨k2, C2, rdNext⟩ :=
    scratch_blindAuctionRevealX_hashGuard_mismatch_toNext
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (rdata := rdata) (acc := (cA, σ))
      (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) rd1235
  exact ⟨hsrc, ⟨_, _, k2, C2, rdNext⟩⟩

theorem scratch_revealLoopBody_hashMismatch_fromPacked_concrete_pair {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd
      valuesLen valuesEnd sel value secret fakeWord blinded fp : UInt256}
    {fake : Bool} {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1207⟩
      [((⟨65⟩ : UInt256) + ((⟨32⟩ : UInt256) + fp)), secret, fakeWord, value, slot,
        i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlenPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hhashPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem fp packedLen
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)))
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨0⟩)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundBids : i.toNat < curLen.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhashEval :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf L evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList)) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.continue
          { contract := blindAuctionContract,
            locals := scratch_revealSecretStoreOf L evm i value secret fake }
          evm) ∧
      ∃ k' C',
        let base := (⟨32⟩ : UInt256) + fp
        let newFree := (⟨65⟩ : UInt256) + base
        let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
        let mem4 := scratch_revealPackedLenMem mem fp packedLen
        let aw1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
        let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
        let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
        let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
        let aw4 := UInt256.ofNat (MachineState.M aw3.toNat fp.toNat 32)
        let aw5 := UInt256.ofNat (MachineState.M aw4.toNat base.toNat packedLen.toNat)
        RD blindAuctionBytecode I g s0 ⟨1014⟩
          (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          mem5 aw5 rdata (cA, σ) k' C' := by
  have hne :
      EVM.Word.toBytesBE blinded ≠
        (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList := by
    exact scratch_revealPackedHash_ne_of_u256_eq_zero
      (blinded := blinded) (value := value) (secret := secret) (fake := fake) hflag
  have hsrc :
      ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.continue
          { contract := blindAuctionContract,
            locals := scratch_revealSecretStoreOf L evm i value secret fake }
          evm) := by
    exact scratch_revealLoopBody_continue_hash_mismatch_of_get evm L values fakes secrets
      curLen refund i value secret blinded fake fakeRaw
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList
      hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues hboundFakes
      hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded hhashEval hne
  obtain ⟨k1, C1, rd1235⟩ :=
    scratch_blindAuctionRevealX_loopBody_packed_suffix
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (σ := σ)
      (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (fp := fp)
      (hash :=
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)))
      (blinded := blinded) (flag := ⟨0⟩)
      rd hfp hlenPacked hhashPacked hstore hflag
  obtain ⟨k2, C2, rdNext⟩ :=
    scratch_blindAuctionRevealX_hashGuard_mismatch_toNext
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (rdata := rdata) (acc := (cA, σ))
      (secret := secret) (fake := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) rd1235
  exact ⟨hsrc, ⟨k2, C2, rdNext⟩⟩

theorem scratch_revealLoopBody_hashMismatch_fromElemSlot_cursor_pair {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len curLen revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd
      valuesLen valuesEnd sel value secret fakeWord blinded fp : UInt256}
    {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1069⟩
      [slot, i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (haw : 3 ≤ aw.toNat) (hawSmall : aw.toNat * 32 < UInt256.size)
    (hfit128 : fp.toNat + 128 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fp)
    (hmem96 : 96 ≤ mem.size) (hfp96 : 96 ≤ fp.toNat)
    (hfpPrefix :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hvalueBound : i.toNat < valuesLen.toNat)
    (hfakesBound : i.toNat < fakesLen.toNat)
    (hsecretsBound : i.toNat < secretsLen.toNat)
    (hvalueLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + valuesEnd).toNat 32) =
        value)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) =
        fakeWord)
    (hfakeZero : fakeWord = ⟨0⟩)
    (hsecretLoad :
      uInt256OfByteArray (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + secretsEnd).toNat 32) =
        secret)
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray))) =
        ⟨0⟩)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = curLen)
    (hboundBids : i.toNat < curLen.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool false))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.continue
          { contract := blindAuctionContract,
            locals := scratch_revealSecretStoreOf L evm i value secret false }
          evm) ∧
      ∃ nextFp memNext awNext k' C',
        RD blindAuctionBytecode I g s0 ⟨1014⟩
          (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          memNext awNext rdata (cA, σ) k' C' ∧
        3 ≤ awNext.toNat ∧
        awNext.toNat * 32 < UInt256.size ∧
        (if (⟨64⟩ : UInt256).toNat ≥ memNext.size ∨
            (⟨64⟩ : UInt256) ≥ awNext * ⟨32⟩
         then ⟨0⟩
         else UInt256.ofNat
          (fromByteArrayBigEndian
            (memNext.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = nextFp ∧
        memNext.readWithPadding 64 32 = UInt256.toByteArray nextFp ∧
        96 ≤ memNext.size ∧
        memNext.size ≤ nextFp.toNat + 32 ∧
        nextFp.toNat + 32 - memNext.size < USize.size ∧
        nextFp.toNat = fp.toNat + 97 := by
  have hfit97 : fp.toNat + 97 < UInt256.size := by
    omega
  have hfp64 : 64 ≤ fp.toNat := by
    omega
  let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let base := (⟨32⟩ : UInt256) + fp
  let fakeBase := base + ⟨32⟩
  let secretBase := base + ⟨33⟩
  let newFree := (⟨65⟩ : UInt256) + base
  let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
  let memP1 := scratch_revealPackedValueMem mem base value
  let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
  let memP2 := scratch_revealPackedFakeMem memP1 fakeBase fakeWord
  let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
  let memP3 := scratch_revealPackedSecretMem memP2 secretBase secret
  let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
  let memP4 := scratch_revealPackedLenMem memP3 fp packedLen
  let awS1 := UInt256.ofNat (MachineState.M awP4.toNat (⟨64⟩ : UInt256).toNat 32)
  let awS2 := UInt256.ofNat (MachineState.M awS1.toNat fp.toNat 32)
  let memP5 := scratch_revealPackedFreePtrMem memP4 newFree
  let awS3 := UInt256.ofNat (MachineState.M awS2.toNat (⟨64⟩ : UInt256).toNat 32)
  let awS4 := UInt256.ofNat (MachineState.M awS3.toNat fp.toNat 32)
  let awS5 := UInt256.ofNat (MachineState.M awS4.toNat base.toNat packedLen.toNat)
  have hAwFacts :
      newFree.toNat = fp.toNat + 97 ∧ packedLen.toNat = 65 ∧
        3 ≤ awS2.toNat ∧ awS2.toNat * 32 < UInt256.size ∧
        3 ≤ awP4.toNat ∧ awP4.toNat * 32 < UInt256.size ∧
        3 ≤ awS3.toNat ∧ awS3.toNat * 32 < UInt256.size ∧
        3 ≤ awS5.toNat ∧ awS5.toNat * 32 < UInt256.size := by
    simpa [awP1, base, fakeBase, secretBase, newFree, packedLen, awP2, awP3,
      awP4, awS1, awS2, awS3, awS4, awS5]
      using scratch_revealPacked_aw_facts (aw := aw) (fp := fp) haw hawSmall hfit128
  rcases hAwFacts with
    ⟨hnewFreeNat, _hpackedLenNat, hawS2, hawS2Small, hawP4, hawP4Small, _hawS3,
      _hawS3Small, hawS5, hawS5Small⟩
  have hreadP3 : memP3.readWithPadding 64 32 = UInt256.toByteArray fp := by
    simpa [base, fakeBase, secretBase, memP1, memP2, memP3]
      using scratch_revealPackedPrefix_preserve_fp (mem := mem) (fp := fp)
        (value := value) (fakeWord := fakeWord) (secret := secret) hfit97 hmemle hgap
        hread hmem96 hfp64
  have hsizeP3 : memP3.size = fp.toNat + 97 := by
    simpa [base, fakeBase, secretBase, memP1, memP2, memP3]
      using scratch_revealPackedPrefix_size (mem := mem) (fp := fp) (value := value)
        (fakeWord := fakeWord) (secret := secret) hfit97 hmemle hgap
  have hfpPacked :
      (if (⟨64⟩ : UInt256).toNat ≥ memP3.size ∨
          (⟨64⟩ : UInt256) ≥ awP4 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memP3.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        fp := by
    exact scratch_mload_of_read
      (mem := memP3) (fp := (⟨64⟩ : UInt256)) (packedLen := fp) (aw := awP4)
      (by
        change 64 < memP3.size
        rw [hsizeP3]
        omega)
      (by simpa [awP4] using scratch_not_mload64_oob_of_aw_ge3_small hawP4 hawP4Small)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using hreadP3)
  have hreadLen : memP5.readWithPadding fp.toNat 32 = UInt256.toByteArray packedLen := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, memP1, memP2, memP3,
      memP4, memP5]
      using scratch_revealPackedMem_len_read (mem := mem) (fp := fp) (value := value)
        (fakeWord := fakeWord) (secret := secret) hfit97 hmemle hgap hfp96
  have hsizeP5 : memP5.size = fp.toNat + 97 := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, memP1, memP2, memP3,
      memP4, memP5]
      using scratch_revealPackedMem_size (mem := mem) (fp := fp) (value := value)
        (fakeWord := fakeWord) (secret := secret) hfit97 hmemle hgap
  have hlenPacked :
      (let base := (⟨32⟩ : UInt256) + fp
       let newFree := (⟨65⟩ : UInt256) + base
       let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
       let mem4 := scratch_revealPackedLenMem memP3 fp packedLen
       let aw1 := UInt256.ofNat (MachineState.M awP4.toNat (⟨64⟩ : UInt256).toNat 32)
       let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
       let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
       let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
       if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen := by
    exact scratch_mload_of_read
      (mem := memP5) (fp := fp) (packedLen := packedLen) (aw := awS3)
      (by rw [hsizeP5]; omega)
      (by
        have hnotS2 : ¬ (fp ≥ awS2 * ⟨32⟩) := by
          simpa [awS2] using
            scratch_not_mload_oob_after_M32 (aw := awS1) (off := fp) hawS2Small
        have hS3eqS2 : awS3 = awS2 := by
          simpa [awS3] using scratch_reveal_aw_mload64_of_ge3 hawS2
        simpa [hS3eqS2] using hnotS2)
      hreadLen
  let hashWord : UInt256 :=
    uInt256OfByteArray
      (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value false secret).toArray))
  have hhashPacked :
      (let base := (⟨32⟩ : UInt256) + fp
       let newFree := (⟨65⟩ : UInt256) + base
       let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
       let mem4 := scratch_revealPackedLenMem memP3 fp packedLen
       let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
       UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
          hashWord) := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, memP1, memP2, memP3,
      memP4, memP5, hashWord]
      using scratch_revealPackedMem_hash (mem := mem) (fp := fp) (value := value)
        (fakeWord := fakeWord) (secret := secret) (fake := false) hfit97 hmemle hgap
        hfp64 (by simpa using hfakeZero)
  have hreadFree : memP5.readWithPadding 64 32 = UInt256.toByteArray newFree := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, memP1, memP2, memP3,
      memP4, memP5]
      using scratch_revealPackedMem_freePtr_read (mem := mem) (fp := fp) (value := value)
        (fakeWord := fakeWord) (secret := secret) hfit97 hmemle hgap
  have hfpFinal :
      (if (⟨64⟩ : UInt256).toNat ≥ memP5.size ∨
          (⟨64⟩ : UInt256) ≥ awS5 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (memP5.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        newFree := by
    exact scratch_mload_of_read
      (mem := memP5) (fp := (⟨64⟩ : UInt256)) (packedLen := newFree) (aw := awS5)
      (by
        change 64 < memP5.size
        rw [hsizeP5]
        omega)
      (by simpa [awS5] using scratch_not_mload64_oob_of_aw_ge3_small hawS5 hawS5Small)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using hreadFree)
  obtain ⟨kLoad, CLoad, rd1987⟩ :=
    scratch_blindAuctionRevealX_loopBody_loads_toFakeDecoder
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (slot := slot) (i := i) (refund := refund) (len := len)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
      rd hvalueBound hfakesBound hvalueLoad
  obtain ⟨kBool, CBool, rd1135⟩ :=
    scratch_blindAuctionRevealX_loopBody_fakeDecoder_zero_toBool
      (I := I) (g := g) (s0 := s0) (k := kLoad) (C := CLoad)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (slot := slot) (i := i) (refund := refund) (len := len)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
      rd1987 hfakeSlt (by rw [hfakeLoad, hfakeZero])
  obtain ⟨kSecret, CSecret, rd1167⟩ :=
    scratch_blindAuctionRevealX_loopBody_secret_toPacked
      (I := I) (g := g) (s0 := s0) (k := kBool) (C := CBool)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (fakeWord := fakeWord) (value := value) (slot := slot) (i := i)
      (refund := refund) (len := len) (revealEnd := revealEnd) (biddingEnd := biddingEnd)
      (secretsLen := secretsLen) (secretsEnd := secretsEnd) (fakesLen := fakesLen)
      (fakesEnd := fakesEnd) (valuesLen := valuesLen) (valuesEnd := valuesEnd)
      (sel := sel) (secret := secret) (by simpa [hfakeZero] using rd1135)
      hsecretsBound hsecretLoad
  obtain ⟨kPrefix, CPrefix, rd1207Let⟩ :=
    scratch_blindAuctionRevealX_loopBody_packed_prefix
      (I := I) (g := g) (s0 := s0) (k := kSecret) (C := CSecret)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (fp := fp) rd1167 hfpPrefix
  have rd1207 :
      RD blindAuctionBytecode I g s0 ⟨1207⟩
        [newFree, secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd,
          secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
        memP3 awP4 rdata (cA, σ) kPrefix CPrefix := by
    simpa [awP1, base, fakeBase, secretBase, newFree, memP1, awP2, memP2, awP3,
      memP3, awP4] using rd1207Let
  obtain ⟨hbody, hrd⟩ :=
    scratch_revealLoopBody_hashMismatch_fromPacked_concrete_pair
      (I := I) (g := g) (s0 := s0) (k := kPrefix) (C := CPrefix)
      (mem := memP3) (aw := awP4) (rdata := rdata) (cA := cA) (σ := σ)
      (L := L) (evm := evm) (values := values) (fakes := fakes) (secrets := secrets)
      (slot := slot) (i := i) (refund := refund) (len := len) (curLen := curLen)
      (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (value := value) (secret := secret)
      (fakeWord := fakeWord) (blinded := blinded) (fp := fp) (fake := false)
      (fakeRaw := fakeRaw) rd1207 hfpPacked
      (by simpa [base, newFree, packedLen, memP4, memP5, awS1, awS2, awS3] using hlenPacked)
      (by simpa [base, newFree, packedLen, memP4, memP5, hashWord] using hhashPacked)
      hstore
      (by simpa [hashWord] using hflag)
      hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues hboundFakes
      hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded
      (scratch_evalExpr_revealPackedHash_of_secretStoreOf evm L i value secret false)
  obtain ⟨kNext, CNext, rdNextLet⟩ := hrd
  have rdNext :
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        memP5 awS5 rdata (cA, σ) kNext CNext := by
    simpa [base, newFree, packedLen, memP4, memP5, awS1, awS2, awS3, awS4, awS5]
      using rdNextLet
  refine ⟨hbody, newFree, memP5, awS5, kNext, CNext, rdNext, hawS5, hawS5Small, hfpFinal,
    hreadFree, ?_, ?_, ?_, hnewFreeNat⟩
  · rw [hsizeP5]
    omega
  · rw [hsizeP5, hnewFreeNat]
    omega
  · rw [hsizeP5, hnewFreeNat]
    have hsmall : 32 < USize.size := lt_usize 32 (by norm_num)
    omega

theorem scratch_revealLoopBody_hashMismatch_afterSecret_pair {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret fakeWord blinded fp : UInt256}
    {fake : Bool} {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1167⟩
      [secret, fakeWord, value, slot, i, refund, len, revealEnd, biddingEnd, secretsLen,
        secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfpPrefix :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hfpPacked :
      let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let base := (⟨32⟩ : UInt256) + fp
      let fakeBase := base + ⟨32⟩
      let secretBase := base + ⟨33⟩
      let mem1 := scratch_revealPackedValueMem mem base value
      let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
      let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
      let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
      let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
      let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
      (if (⟨64⟩ : UInt256).toNat ≥ mem3.size ∨ (⟨64⟩ : UInt256) ≥ awP4 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem3.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlenPacked :
      let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let base := (⟨32⟩ : UInt256) + fp
      let fakeBase := base + ⟨32⟩
      let secretBase := base + ⟨33⟩
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem1 := scratch_revealPackedValueMem mem base value
      let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
      let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
      let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
      let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
      let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
      let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M awP4.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hfp64 : 64 ≤ fp.toNat)
    (hfakeWord : fakeWord = if fake then (⟨1⟩ : UInt256) else ⟨0⟩)
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨0⟩)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhashEval :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf L evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList)) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.continue
          { contract := blindAuctionContract,
            locals := scratch_revealSecretStoreOf L evm i value secret fake }
          evm) ∧
      ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
          secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        mem' aw' rdata (cA, σ) k' C' := by
  let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  let base := (⟨32⟩ : UInt256) + fp
  let fakeBase := base + ⟨32⟩
  let secretBase := base + ⟨33⟩
  let newFree := (⟨65⟩ : UInt256) + base
  let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
  let mem1 := scratch_revealPackedValueMem mem base value
  let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
  let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
  let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
  let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
  let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
  obtain ⟨k1, C1, rd1207⟩ :=
    scratch_blindAuctionRevealX_loopBody_packed_prefix
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (secret := secret) (fakeWord := fakeWord) (value := value) (slot := slot)
      (i := i) (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (fp := fp) rd hfpPrefix
  have hhashPacked :
      let base := (⟨32⟩ : UInt256) + fp
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      UInt256.ofNat
          (fromByteArrayBigEndian (ffi.KEC (mem5.readWithPadding base.toNat packedLen.toNat))) =
        uInt256OfByteArray
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)) := by
    simpa [base, fakeBase, secretBase, newFree, packedLen, mem1, mem2, mem3]
      using scratch_revealPackedMem_hash
        (mem := mem) (fp := fp) (value := value) (fakeWord := fakeWord)
        (secret := secret) (fake := fake) hfit hmemle hgap hfp64 hfakeWord
  exact scratch_revealLoopBody_hashMismatch_fromPacked_pair
    (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
    (mem := mem3) (aw := awP4) (rdata := rdata) (cA := cA) (σ := σ)
    (L := L) (evm := evm) (values := values) (fakes := fakes) (secrets := secrets)
    (slot := slot) (i := i) (refund := refund) (len := len)
    (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
    (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
    (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
    (secret := secret) (fakeWord := fakeWord) (blinded := blinded) (fp := fp)
    (fake := fake) (fakeRaw := fakeRaw)
    (by
      simpa [awP1, base, fakeBase, secretBase, newFree, mem1, awP2, mem2, awP3, mem3,
        awP4] using rd1207)
    (by
      simpa [awP1, base, fakeBase, secretBase, mem1, awP2, mem2, awP3, mem3, awP4]
        using hfpPacked)
    (by
      simpa [awP1, base, fakeBase, secretBase, newFree, packedLen, mem1, awP2, mem2,
        awP3, mem3, awP4] using hlenPacked)
    hhashPacked hstore hflag hbids hvalues hfakes hsecrets hi hlen hboundBids
    hboundValues hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup
    hblinded hhashEval

theorem scratch_revealLoopBody_hashMismatch_afterBool_pair {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret fakeWord blinded fp : UInt256}
    {fake : Bool} {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1135⟩
      [fakeWord, value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd,
        biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hsecretsBound : i.toNat < secretsLen.toNat)
    (hsecretLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + secretsEnd).toNat 32) =
        secret)
    (hfpPrefix :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hfpPacked :
      let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let base := (⟨32⟩ : UInt256) + fp
      let fakeBase := base + ⟨32⟩
      let secretBase := base + ⟨33⟩
      let mem1 := scratch_revealPackedValueMem mem base value
      let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
      let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
      let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
      let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
      let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
      (if (⟨64⟩ : UInt256).toNat ≥ mem3.size ∨ (⟨64⟩ : UInt256) ≥ awP4 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem3.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlenPacked :
      let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let base := (⟨32⟩ : UInt256) + fp
      let fakeBase := base + ⟨32⟩
      let secretBase := base + ⟨33⟩
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem1 := scratch_revealPackedValueMem mem base value
      let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
      let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
      let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
      let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
      let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
      let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M awP4.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hfp64 : 64 ≤ fp.toNat)
    (hfakeWord : fakeWord = if fake then (⟨1⟩ : UInt256) else ⟨0⟩)
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨0⟩)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhashEval :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf L evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList)) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.continue
          { contract := blindAuctionContract,
            locals := scratch_revealSecretStoreOf L evm i value secret fake }
          evm) ∧
      ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
          secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        mem' aw' rdata (cA, σ) k' C' := by
  obtain ⟨k1, C1, rd1167⟩ :=
    scratch_blindAuctionRevealX_loopBody_secret_toPacked
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (fakeWord := fakeWord) (value := value) (slot := slot) (i := i)
      (refund := refund) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel) (secret := secret)
      rd hsecretsBound hsecretLoad
  exact scratch_revealLoopBody_hashMismatch_afterSecret_pair
    (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
    (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (σ := σ)
    (L := L) (evm := evm) (values := values) (fakes := fakes) (secrets := secrets)
    (slot := slot) (i := i) (refund := refund) (len := len)
    (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
    (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
    (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
    (secret := secret) (fakeWord := fakeWord) (blinded := blinded) (fp := fp)
    (fake := fake) (fakeRaw := fakeRaw) rd1167 hfpPrefix hfpPacked hlenPacked hfit
    hmemle hgap hfp64 hfakeWord hstore hflag hbids hvalues hfakes hsecrets hi hlen
    hboundBids hboundValues hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm
    hsecretLookup hblinded hhashEval

set_option maxHeartbeats 3000000 in
theorem scratch_revealLoopBody_hashMismatch_fromFakeDecoder_pair {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret fakeWord blinded fp : UInt256}
    {fake : Bool} {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1987⟩
      [UInt256.mul ⟨32⟩ i + fakesEnd, UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩,
        ⟨1135⟩, value, ⟨0⟩, ⟨0⟩, ⟨0⟩, slot, i, refund, len, revealEnd,
        biddingEnd, secretsLen, secretsEnd, fakesLen, fakesEnd, valuesLen, valuesEnd,
        ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) = fakeWord)
    (hfakeWord : fakeWord = if fake then (⟨1⟩ : UInt256) else ⟨0⟩)
    (hsecretsBound : i.toNat < secretsLen.toNat)
    (hsecretLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + secretsEnd).toNat 32) =
        secret)
    (hfpPrefix :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hfpPacked :
      let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let base := (⟨32⟩ : UInt256) + fp
      let fakeBase := base + ⟨32⟩
      let secretBase := base + ⟨33⟩
      let mem1 := scratch_revealPackedValueMem mem base value
      let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
      let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
      let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
      let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
      let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
      (if (⟨64⟩ : UInt256).toNat ≥ mem3.size ∨ (⟨64⟩ : UInt256) ≥ awP4 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem3.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlenPacked :
      let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let base := (⟨32⟩ : UInt256) + fp
      let fakeBase := base + ⟨32⟩
      let secretBase := base + ⟨33⟩
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem1 := scratch_revealPackedValueMem mem base value
      let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
      let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
      let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
      let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
      let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
      let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M awP4.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hfp64 : 64 ≤ fp.toNat)
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨0⟩)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhashEval :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf L evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList)) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.continue
          { contract := blindAuctionContract,
            locals := scratch_revealSecretStoreOf L evm i value secret fake }
          evm) ∧
      ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
          secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        mem' aw' rdata (cA, σ) k' C' := by
  cases fake
  · simp at hfakeWord
    have hfakeLoad0 :
        uInt256OfByteArray
            (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) =
          (⟨0⟩ : UInt256) := by
      simpa [hfakeWord] using hfakeLoad
    obtain ⟨k1, C1, rd1135⟩ :=
      scratch_blindAuctionRevealX_loopBody_fakeDecoder_zero_toBool
        (I := I) (g := g) (s0 := s0) (k := k) (C := C)
        (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
        (slot := slot) (i := i) (refund := refund) (len := len)
        (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
        (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
        (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
        rd hfakeSlt hfakeLoad0
    exact scratch_revealLoopBody_hashMismatch_afterBool_pair
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (σ := σ)
      (L := L) (evm := evm) (values := values) (fakes := fakes) (secrets := secrets)
      (slot := slot) (i := i) (refund := refund) (len := len)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
      (secret := secret) (fakeWord := fakeWord) (blinded := blinded) (fp := fp)
      (fake := false) (fakeRaw := fakeRaw) (by simpa [hfakeWord] using rd1135)
      hsecretsBound hsecretLoad hfpPrefix hfpPacked hlenPacked hfit hmemle hgap hfp64
      hfakeWord hstore hflag hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded
      hhashEval
  · simp at hfakeWord
    have hfakeLoad1 :
        uInt256OfByteArray
            (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) =
          (⟨1⟩ : UInt256) := by
      simpa [hfakeWord] using hfakeLoad
    obtain ⟨k1, C1, rd1135⟩ :=
      scratch_blindAuctionRevealX_loopBody_fakeDecoder_one_toBool
        (I := I) (g := g) (s0 := s0) (k := k) (C := C)
        (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
        (slot := slot) (i := i) (refund := refund) (len := len)
        (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
        (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
        (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
        rd hfakeSlt hfakeLoad1
    exact scratch_revealLoopBody_hashMismatch_afterBool_pair
      (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
      (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (σ := σ)
      (L := L) (evm := evm) (values := values) (fakes := fakes) (secrets := secrets)
      (slot := slot) (i := i) (refund := refund) (len := len)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
      (secret := secret) (fakeWord := fakeWord) (blinded := blinded) (fp := fp)
      (fake := true) (fakeRaw := fakeRaw) (by simpa [hfakeWord] using rd1135)
      hsecretsBound hsecretLoad hfpPrefix hfpPacked hlenPacked hfit hmemle hgap hfp64
      hfakeWord hstore hflag hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues
      hboundFakes hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded
      hhashEval

set_option maxHeartbeats 3000000 in
theorem scratch_revealLoopBody_hashMismatch_fromElemSlot_pair {I} {g : Sat256}
    {s0 : State} {k C : ℕ} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {L : Store} {evm : EVM.State}
    {values fakes secrets : List Value}
    {slot i refund len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen
      valuesEnd sel value secret fakeWord blinded fp : UInt256}
    {fake : Bool} {fakeRaw : Value}
    (rd : RD blindAuctionBytecode I g s0 ⟨1069⟩
      [slot, i, refund, len, revealEnd, biddingEnd, secretsLen, secretsEnd, fakesLen,
        fakesEnd, valuesLen, valuesEnd, ⟨276⟩, sel]
      mem aw rdata (cA, σ) k C)
    (hvalueBound : i.toNat < valuesLen.toNat)
    (hfakesBound : i.toNat < fakesLen.toNat)
    (hvalueLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + valuesEnd).toNat 32) =
        value)
    (hfakeSlt :
      UInt256.slt
          (UInt256.sub
            (UInt256.mul ⟨32⟩ i + fakesEnd + ⟨32⟩)
            (UInt256.mul ⟨32⟩ i + fakesEnd)) ⟨32⟩ = ⟨0⟩)
    (hfakeLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + fakesEnd).toNat 32) = fakeWord)
    (hfakeWord : fakeWord = if fake then (⟨1⟩ : UInt256) else ⟨0⟩)
    (hsecretsBound : i.toNat < secretsLen.toNat)
    (hsecretLoad :
      uInt256OfByteArray
          (I.calldata.readBytes (UInt256.mul ⟨32⟩ i + secretsEnd).toNat 32) =
        secret)
    (hfpPrefix :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hfpPacked :
      let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let base := (⟨32⟩ : UInt256) + fp
      let fakeBase := base + ⟨32⟩
      let secretBase := base + ⟨33⟩
      let mem1 := scratch_revealPackedValueMem mem base value
      let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
      let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
      let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
      let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
      let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
      (if (⟨64⟩ : UInt256).toNat ≥ mem3.size ∨ (⟨64⟩ : UInt256) ≥ awP4 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat
          (fromByteArrayBigEndian (mem3.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = fp)
    (hlenPacked :
      let awP1 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
      let base := (⟨32⟩ : UInt256) + fp
      let fakeBase := base + ⟨32⟩
      let secretBase := base + ⟨33⟩
      let newFree := (⟨65⟩ : UInt256) + base
      let packedLen := UInt256.sub (UInt256.sub newFree fp) ⟨32⟩
      let mem1 := scratch_revealPackedValueMem mem base value
      let awP2 := UInt256.ofNat (MachineState.M awP1.toNat base.toNat 32)
      let mem2 := scratch_revealPackedFakeMem mem1 fakeBase fakeWord
      let awP3 := UInt256.ofNat (MachineState.M awP2.toNat fakeBase.toNat 32)
      let mem3 := scratch_revealPackedSecretMem mem2 secretBase secret
      let awP4 := UInt256.ofNat (MachineState.M awP3.toNat secretBase.toNat 32)
      let mem4 := scratch_revealPackedLenMem mem3 fp packedLen
      let aw1 := UInt256.ofNat (MachineState.M awP4.toNat (⟨64⟩ : UInt256).toNat 32)
      let aw2 := UInt256.ofNat (MachineState.M aw1.toNat fp.toNat 32)
      let mem5 := scratch_revealPackedFreePtrMem mem4 newFree
      let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (⟨64⟩ : UInt256).toNat 32)
      (if fp.toNat ≥ mem5.size ∨ fp ≥ aw3 * ⟨32⟩
       then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem5.readWithPadding fp.toNat 32))) =
        packedLen)
    (hfit : fp.toNat + 97 < UInt256.size)
    (hmemle : mem.size ≤ fp.toNat + 32)
    (hgap : fp.toNat + 32 - mem.size < USize.size)
    (hfp64 : 64 ≤ fp.toNat)
    (hstore :
      (σ.find? I.codeOwner).option ⟨0⟩
        (fun ac => ac.storage.findD ((⟨0⟩ : UInt256) + slot) ⟨0⟩) = blinded)
    (hflag :
      UInt256.eq blinded
          (uInt256OfByteArray
            (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray))) =
        ⟨0⟩)
    (hbids : L.get? "bids" = none)
    (hvalues : L.get? "values" = some (.array values))
    (hfakes : L.get? "fakes" = some (.array fakes))
    (hsecrets : L.get? "secrets" = some (.array secrets))
    (hi : L.get? "i" = some (.int (Int.ofNat i.toNat)))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hboundBids : i.toNat < len.toNat)
    (hboundValues : i.toNat < values.length)
    (hboundFakes : i.toNat < fakes.length)
    (hboundSecrets : i.toNat < secrets.length)
    (hvalueLookup :
      lookupNth? values i.toNat = some (.int (Int.ofNat value.toNat)))
    (hfakeLookup : lookupNth? fakes i.toNat = some fakeRaw)
    (hfakeNorm : normalizeRawBoolWord? fakeRaw = .ok (.bool fake))
    (hsecretLookup :
      lookupNth? secrets i.toNat =
        some (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE secret)))
    (hblinded :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (scratch_revealBidBlindedSlot evm i) = blinded)
    (hhashEval :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := scratch_revealSecretStoreOf L evm i value secret fake } evm
        scratch_revealPackedHashExpr =
        .ok (.fixedBytes ⟨31, by decide⟩
          (ffi.KEC (ByteArray.mk (scratch_revealPackedBytes value fake secret).toArray)).toList)) :
    ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
        scratch_revealLoopBodyStmts
        (.continue
          { contract := blindAuctionContract,
            locals := scratch_revealSecretStoreOf L evm i value secret fake }
          evm) ∧
      ∃ mem' aw' k' C', RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (i + ⟨1⟩) refund len revealEnd biddingEnd secretsLen
          secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        mem' aw' rdata (cA, σ) k' C' := by
  obtain ⟨k1, C1, rd1987⟩ :=
    scratch_blindAuctionRevealX_loopBody_loads_toFakeDecoder
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem) (aw := aw) (rdata := rdata) (acc := (cA, σ))
      (slot := slot) (i := i) (refund := refund) (len := len)
      (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
      rd hvalueBound hfakesBound hvalueLoad
  exact scratch_revealLoopBody_hashMismatch_fromFakeDecoder_pair
    (I := I) (g := g) (s0 := s0) (k := k1) (C := C1)
    (mem := mem) (aw := aw) (rdata := rdata) (cA := cA) (σ := σ)
    (L := L) (evm := evm) (values := values) (fakes := fakes) (secrets := secrets)
    (slot := slot) (i := i) (refund := refund) (len := len)
    (revealEnd := revealEnd) (biddingEnd := biddingEnd) (secretsLen := secretsLen)
    (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
    (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) (value := value)
    (secret := secret) (fakeWord := fakeWord) (blinded := blinded) (fp := fp)
    (fake := fake) (fakeRaw := fakeRaw) rd1987 hfakeSlt hfakeLoad hfakeWord
    hsecretsBound hsecretLoad hfpPrefix hfpPacked hlenPacked hfit hmemle hgap hfp64 hstore
    hflag hbids hvalues hfakes hsecrets hi hlen hboundBids hboundValues hboundFakes
    hboundSecrets hvalueLookup hfakeLookup hfakeNorm hsecretLookup hblinded hhashEval

-- Reveal-specialized wrapper around `Reasoning.Reach.RD.execForLoopOrRevertCarryFull`.
theorem scratch_revealLoop_from_body_or_revert {I} {g : Sat256} {s0 : State}
    {rdata : ByteArray} {α : Type}
    (len revealEnd biddingEnd secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd
      sel : UInt256)
    (Inv : ℕ → α → Store → EVM.State → Prop)
    (idx refund : α → UInt256)
    (mem : α → ByteArray) (aw : α → UInt256)
    (acc : α → Batteries.RBSet AccountAddress compare × AccountMap)
    (hshape : ∀ v a L evm, Inv v a L evm →
      L.get? "i" = some (.int (Int.ofNat (idx a).toNat)) ∧
      L.get? "length" = some (.int (Int.ofNat len.toNat)) ∧
      L.get? "refund" = some (.int (Int.ofNat (refund a).toNat)) ∧
      (idx a).toNat + v = len.toNat ∧
      (idx a).toNat ≤ len.toNat)
    (hbody : ∀ v a L evm, Inv (v + 1) a L evm → ∀ k C,
        RD blindAuctionBytecode I g s0 ⟨1023⟩
          (scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          (mem a) (aw a) rdata (acc a) k C →
        (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
            scratch_revealLoopBodyStmts .reverted ∧
          RDrev blindAuctionBytecode g s0) ∨
        ∃ a' L1 evm1 L2 evm2 k' C',
          (ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
              scratch_revealLoopBodyStmts
              (.ok { contract := blindAuctionContract, locals := L1 } evm1) ∨
            ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L } evm
              scratch_revealLoopBodyStmts
              (.continue { contract := blindAuctionContract, locals := L1 } evm1)) ∧
          ExecBlock blindAuctionConfig { contract := blindAuctionContract, locals := L1 } evm1
            scratch_revealLoopPostStmts
            (.ok { contract := blindAuctionContract, locals := L2 } evm2) ∧
          Inv v a' L2 evm2 ∧
          RD blindAuctionBytecode I g s0 ⟨1014⟩
            (scratch_revealEvmLoopStack (idx a') (refund a') len revealEnd biddingEnd
              secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
            (mem a') (aw a') rdata (acc a') k' C') :
    ∀ v a L evm, Inv v a L evm → ∀ k C,
      RD blindAuctionBytecode I g s0 ⟨1014⟩
        (scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd
          secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
        (mem a) (aw a) rdata (acc a) k C →
      (∃ a' L' evm' k' C',
        ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract, locals := L } evm
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts
          (.ok { contract := blindAuctionContract, locals := L' } evm') ∧
        Inv 0 a' L' evm' ∧
        RD blindAuctionBytecode I g s0 ⟨1331⟩
          (scratch_revealEvmLoopStack (idx a') (refund a') len revealEnd biddingEnd
            secretsLen secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
          (mem a') (aw a') rdata (acc a') k' C') ∨
      (ExecForLoop blindAuctionConfig
          { contract := blindAuctionContract, locals := L } evm
          (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
          scratch_revealLoopBodyStmts .reverted ∧
        RDrev blindAuctionBytecode g s0) := by
  refine Reasoning.Reach.RD.execForLoopOrRevertCarryFull
    (cfg := blindAuctionConfig) (contract := blindAuctionContract)
    (code := blindAuctionBytecode) (ee := I) (g := g) (s0 := s0) (rdata := rdata)
    (header := ⟨1014⟩) (bodyHeader := ⟨1023⟩) (exit := ⟨1331⟩)
    (condExpr := (.binary .lt (.var "i") (.var "length")))
    (post := scratch_revealLoopPostStmts) (body := scratch_revealLoopBodyStmts)
    (Inv := Inv)
    (stk := fun a =>
      scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
    (mem := mem) (aw := aw) (acc := acc)
    (exitStk := fun a =>
      scratch_revealEvmLoopStack (idx a) (refund a) len revealEnd biddingEnd secretsLen
        secretsEnd fakesLen fakesEnd valuesLen valuesEnd sel)
    ?_ ?_ ?_ ?_ hbody
  · intro a L evm hInv
    rcases hshape 0 a L evm hInv with ⟨hi, hlen, _hrefund, hvar, _hle⟩
    exact scratch_evalExpr_reveal_loop_cond_false_of_get evm L len (idx a) hi hlen (by omega)
  · intro a L evm hInv k C rd
    rcases hshape 0 a L evm hInv with ⟨_hi, _hlen, _hrefund, hvar, _hle⟩
    exact scratch_blindAuctionRevealX_loopCond_exit
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem a) (aw := aw a) (rdata := rdata) (acc := acc a)
      (i := idx a) (refund := refund a) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen)
      (secretsEnd := secretsEnd) (fakesLen := fakesLen) (fakesEnd := fakesEnd)
      (valuesLen := valuesLen) (valuesEnd := valuesEnd) (sel := sel) rd (by omega)
  · intro v a L evm hInv
    rcases hshape (v + 1) a L evm hInv with ⟨hi, hlen, _hrefund, hvar, _hle⟩
    exact scratch_evalExpr_reveal_loop_cond_true_of_get evm L len (idx a) hi hlen (by omega)
  · intro v a L evm hInv k C rd
    rcases hshape (v + 1) a L evm hInv with ⟨_hi, _hlen, _hrefund, hvar, _hle⟩
    obtain ⟨k1, C1, rd1023⟩ := blindAuctionRevealX_loopCond_taken
      (I := I) (g := g) (s0 := s0) (k := k) (C := C)
      (mem := mem a) (aw := aw a) (rdata := rdata) (acc := acc a)
      (i := idx a) (refund := refund a) (len := len) (revealEnd := revealEnd)
      (biddingEnd := biddingEnd) (secretsLen := secretsLen) (secretsEnd := secretsEnd)
      (fakesLen := fakesLen) (fakesEnd := fakesEnd) (valuesLen := valuesLen)
      (valuesEnd := valuesEnd) (sel := sel)
      (by simpa [scratch_revealEvmLoopStack] using rd) (by omega)
    exact ⟨k1, C1, by simpa [scratch_revealEvmLoopStack] using rd1023⟩

theorem scratch_blindAuctionRevealBodyReverts_fromLoopRevertOfLocals
    (evm : EVM.State) (callargs : Store)
    (values fakes secrets : List Value) (len : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hafter :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat <
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
    (hbefore :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)
    (hbidding : callargs.get? biddingEndRef.base = none)
    (hreveal : callargs.get? revealEndRef.base = none)
    (hbids : callargs.get? "bids" = none)
    (hvalues : callargs.get? "values" = some (.array values))
    (hfakes : callargs.get? "fakes" = some (.array fakes))
    (hsecrets : callargs.get? "secrets" = some (.array secrets))
    (hlen :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bidsBase (.address evm.executionEnv.source)) = len)
    (hvaluesLen : values.length = len.toNat)
    (hfakesLen : fakes.length = len.toNat)
    (hsecretsLen : secrets.length = len.toNat)
    (hloop :
      ExecForLoop blindAuctionConfig
        ({ contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ } :
          Frame) evm
        (.binary .lt (.var "i") (.var "length")) scratch_revealLoopPostStmts
        scratch_revealLoopBodyStmts .reverted) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm callargs revealTransition.body
      .reverted := by
  let lengthFrame : Frame :=
    { contract := blindAuctionContract, locals := scratch_revealLengthStore callargs len }
  let refundFrame : Frame :=
    { contract := blindAuctionContract, locals := scratch_revealRefundStore callargs len ⟨0⟩ }
  let initLoopFrame : Frame :=
    { contract := blindAuctionContract, locals := scratch_revealLoopStore callargs len ⟨0⟩ ⟨0⟩ }
  refine ExecFuncBody.execBlockRevert ?_
  unfold revealTransition
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_afterBiddingEnd_true evm callargs hbidding hafter)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_reveal_beforeRevealEnd_true evm callargs hreveal hbefore)) ?_
  have hlengthEval :
      evalExpr? blindAuctionConfig { contract := blindAuctionContract, locals := callargs }
        evm (.arrayLength .storage (bidsRef sender)) = .ok (.int (Int.ofNat len.toNat)) := by
    exact evalExpr_reveal_bids_length_any evm callargs len hbids hlen
  refine ExecBlock.consNormal (ExecStmt.letDecl hlengthEval) ?_
  change ExecBlock blindAuctionConfig lengthFrame evm
    (List.drop 4 revealTransition.body) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "values" values len ?_
        (by simp [scratch_revealLengthStore]) hvaluesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hvalues
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "fakes" fakes len ?_
        (by simp [scratch_revealLengthStore]) hfakesLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hfakes
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_reveal_local_array_length_eq_var_true evm
        (scratch_revealLengthStore callargs len) "secrets" secrets len ?_
        (by simp [scratch_revealLengthStore]) hsecretsLen)) ?_
  · unfold scratch_revealLengthStore
    rw [store_get_ne]
    · exact hsecrets
    · decide
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
  change ExecBlock blindAuctionConfig refundFrame evm
    [ scratch_revealForStmt,
      .lowLevelCall sender (.var "refund") (.newBytes (.intLit 0)) "success" "_data",
      .require (.var "success") ]
    .reverted
  have hfor :
      ExecStmt blindAuctionConfig refundFrame evm scratch_revealForStmt .reverted := by
    have hinit :
        ExecBlock blindAuctionConfig
          refundFrame evm
          [ .letDecl "i" (some uint256) (.intLit 0) ]
          (.ok initLoopFrame evm) := by
      refine ExecBlock.consNormal
        (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure])) ?_
      exact ExecBlock.nil
    exact ExecStmt.for hinit hloop
  exact ExecBlock.consRevert hfor

end BlindAuction
