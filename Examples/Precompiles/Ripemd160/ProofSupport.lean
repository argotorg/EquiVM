import Reasoning.Reach

/-!
# RIPEMD-160 bytecode proof support

Contract-local symbolic-execution and byte-array lemmas needed by the optimized Osaka runtime.
They live here to avoid expanding the shared Reasoning API for a single proof.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Reasoning.Theory

/-- EVM memory-word growth stays representable when its ceil-dividend is below `32 * 2^256`. -/
theorem machineM_lt_uint256 (aw : UInt256) (off len : Nat)
    (hbound : off + len + 31 < 32 * UInt256.size) :
    MachineState.M aw.toNat off len < UInt256.size := by
  cases len with
  | zero =>
      change aw.toNat < UInt256.size
      exact aw.val.isLt
  | succ len =>
      simp only [MachineState.M]
      rw [max_lt_iff]
      refine ⟨aw.val.isLt, ?_⟩
      rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 32)]
      omega

/-- A representable memory expansion never decreases the active-word count. -/
theorem machineM_ofNat_ge (aw : UInt256) (off len : Nat)
    (hbound : off + len + 31 < 32 * UInt256.size) :
    aw.toNat ≤ (UInt256.ofNat (MachineState.M aw.toNat off len)).toNat := by
  have hlt := machineM_lt_uint256 aw off len hbound
  change aw.toNat ≤ MachineState.M aw.toNat off len % UInt256.size
  rw [Nat.mod_eq_of_lt hlt]
  cases len with
  | zero => simp [MachineState.M]
  | succ len => exact Nat.le_max_left _ _

theorem u256_lor_assoc (a b c : UInt256) :
    UInt256.lor (UInt256.lor a b) c = UInt256.lor a (UInt256.lor b c) := by
  have ha : a.toNat < 2 ^ 256 := by
    have h := a.val.isLt
    change a.toNat < UInt256.size at h
    simpa [UInt256.size] using h
  have hb : b.toNat < 2 ^ 256 := by
    have h := b.val.isLt
    change b.toNat < UInt256.size at h
    simpa [UInt256.size] using h
  have hc : c.toNat < 2 ^ 256 := by
    have h := c.val.isLt
    change c.toNat < UInt256.size at h
    simpa [UInt256.size] using h
  have hab := Nat.or_lt_two_pow ha hb
  have hbc := Nat.or_lt_two_pow hb hc
  have habc := Nat.or_lt_two_pow hab hc
  have habc' := Nat.or_lt_two_pow ha hbc
  apply u256_inj
  simp only [u256_lor_toNat]
  rw [show UInt256.size = 2 ^ 256 from by decide]
  change
    ((((a.toNat ||| b.toNat) % (2 ^ 256)) ||| c.toNat) % (2 ^ 256)) =
      ((a.toNat ||| ((b.toNat ||| c.toNat) % (2 ^ 256))) % (2 ^ 256))
  rw [Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt hbc,
    Nat.mod_eq_of_lt habc, Nat.mod_eq_of_lt habc']
  exact Nat.or_assoc _ _ _

theorem ushl_ofNat_toNat (x : UInt256) (n : Nat) (hn : n < 256) :
    (UInt256.shiftLeft x (UInt256.ofNat n)).toNat =
      (x.toNat <<< n) % UInt256.size := by
  unfold UInt256.shiftLeft
  rw [if_neg]
  · change (x.toNat <<< (UInt256.ofNat n).toNat) % UInt256.size = _
    rw [ulit_toNat' n (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)]
  · change ¬(UInt256.ofNat n).toNat ≥ 256
    rw [ulit_toNat' n (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)]
    omega

theorem ushr_ofNat_toNat (x : UInt256) (n : Nat) (hn : n < 256) :
    (UInt256.shiftRight x (UInt256.ofNat n)).toNat = x.toNat >>> n := by
  unfold UInt256.shiftRight
  rw [if_neg]
  · change (x.toNat >>> (UInt256.ofNat n).toNat) % UInt256.size = _
    rw [ulit_toNat' n (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.shiftRight_le _ _) x.val.isLt)
  · change ¬(UInt256.ofNat n).toNat ≥ 256
    rw [ulit_toNat' n (by
      rw [show UInt256.size = 2 ^ 256 from by decide]
      omega)]
    omega

/-- Clearing the low `k` bits of a word-sized natural floors it to a multiple of `2^k`. -/
theorem nat_land_mask_pow (m k : ℕ) (hm : m < 2 ^ 256) (hk : k ≤ 256) :
    m &&& (2 ^ 256 - 2 ^ k) = 2 ^ k * (m / 2 ^ k) := by
  have hmask : (2 : ℕ) ^ 256 - 2 ^ k = (2 ^ (256 - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]
    simp only [one_mul]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hmask, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    show 2 ^ k * (m / 2 ^ k) = (m >>> k) * 2 ^ k by
      rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm],
    Nat.testBit_mul_two_pow, Nat.testBit_shiftRight]
  by_cases hi : k ≤ i
  · simp only [hi, decide_true, Bool.true_and]
    by_cases hi256 : i - k < 256 - k
    · simp only [hi256, decide_true, Bool.and_true]
      rw [show k + (i - k) = i by omega]
    · simp only [hi256, decide_false, Bool.and_false]
      have hiBound : 256 ≤ i := by omega
      have hb : m.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm
        (Nat.pow_le_pow_right (by norm_num) hiBound))
      rw [show k + (i - k) = i by omega, hb]
  · simp only [hi, decide_false, Bool.false_and, Bool.and_false]

theorem dup12_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP12, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
    (hov : t.length + 13 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP12, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup12 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t).length -
          12 + 13 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem dup16_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP16, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp :: t)
    (hov : t.length + 17 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
              nn :: oo :: pp :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP16, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup16 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
          oo :: pp :: t).length - 16 + 17 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap13_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP13, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
    (hov : t.length + 14 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (nn :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: a :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP13, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap13 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
          t).length - 14 + 14 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem swap14_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP14, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: t)
    (hov : t.length + 15 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (oo :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: a :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP14, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_swap14 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
          oo :: t).length - 15 + 15 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem zeroes_extract_window (total start len : Nat) (hwindow : start + len ≤ total) :
    (ffi.ByteArray.zeroes total).extract start (start + len) =
      ffi.ByteArray.zeroes len := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract]
  rw [byteArray_zeroes_toList, byteArray_zeroes_toList]
  rw [List.extract_eq_take_drop, List.drop_replicate, List.take_replicate]
  congr 1
  omega

/-- A one-byte `ByteArray` extract is the singleton containing that indexed byte. -/
theorem byteArray_extract_one (b : ByteArray) (i : Nat) (hi : i < b.size) :
    b.extract i (i + 1) = ⟨#[b[i]]⟩ := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract]
  simp only
  rw [List.extract_eq_take_drop]
  have hdrop : b.data.toList.drop i =
      b.data.toList[i] :: b.data.toList.drop (i + 1) := by
    rw [← List.cons_getElem_drop_succ]
  rw [hdrop, show i + 1 - i = 1 by omega, List.take_succ_cons, List.take_zero]
  simp
  change b.data[i] = b.data[i]
  rfl

theorem readWithoutPadding_size_le (b : ByteArray) (addr len : Nat) :
    (b.readWithoutPadding addr len).size ≤ len := by
  unfold ByteArray.readWithoutPadding
  split
  · simp
  · rw [ByteArray.size_extract]
    omega

theorem readWithPadding_size_eq (b : ByteArray) (addr len : Nat) (hlen : len < 2 ^ 64) :
    (b.readWithPadding addr len).size = len := by
  unfold ByteArray.readWithPadding
  rw [if_neg (by omega)]
  rw [ByteArray.size_append, ByteArray_zeroes_size]
  have := readWithoutPadding_size_le b addr len
  omega

/-- An in-bounds write from an arbitrary source window preserves the destination size. -/
theorem write_size_of_inbounds_from (src base : ByteArray)
    (srcAddr destAddr len : Nat) (hlen : len ≠ 0)
    (hsrc : srcAddr + len ≤ src.size) (hin : destAddr + len ≤ base.size) :
    (src.write srcAddr base destAddr len).size = base.size := by
  rw [write_eq_gen_from src base srcAddr destAddr len hlen hsrc hin,
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  omega

/-- A 32-byte read below an arbitrary source-window write is preserved, including extension. -/
theorem write_read_below_gen_extend_from (src base : ByteArray)
    (srcAddr destAddr len readAddr : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size)
    (hdest : destAddr ≤ base.size) (hbelow : readAddr + 32 ≤ destAddr) :
    (src.write srcAddr base destAddr len).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  by_cases hin : destAddr + len ≤ base.size
  · rw [write_eq_gen_from src base srcAddr destAddr len hlen hsrc hin]
    have hbasePrefix : (base.extract 0 destAddr).size = destAddr := by
      rw [ByteArray.size_extract]
      omega
    have hsrcPrefix : (src.extract srcAddr (srcAddr + len)).size = len := by
      rw [ByteArray.size_extract]
      omega
    rw [readWithPadding_eq_extract _ readAddr (by
      rw [ByteArray.size_append, ByteArray.size_append, hbasePrefix, hsrcPrefix]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hbasePrefix, hsrcPrefix]
      omega)]
    rw [extract_append_left _ _ _ _ (by rw [hbasePrefix]; omega)]
    rw [extract_prefix _ destAddr readAddr (readAddr + 32) hbelow]
    rw [← readWithPadding_eq_extract base readAddr (by omega)]
  · have hext : base.size < destAddr + len := Nat.lt_of_not_ge hin
    rw [write_eq_gen_extend_from src base srcAddr destAddr len hlen hsrc hdest hext]
    have hbasePrefix : (base.extract 0 destAddr).size = destAddr := by
      rw [ByteArray.size_extract]
      omega
    have hsrcPrefix : (src.extract srcAddr (srcAddr + len)).size = len := by
      rw [ByteArray.size_extract]
      omega
    rw [readWithPadding_eq_extract _ readAddr (by
      rw [ByteArray.size_append, hbasePrefix, hsrcPrefix]
      omega)]
    rw [extract_append_left _ _ _ _ (by rw [hbasePrefix]; omega)]
    rw [extract_prefix _ destAddr readAddr (readAddr + 32) hbelow]
    rw [← readWithPadding_eq_extract base readAddr (by omega)]

/-- The first byte of a padded 32-byte read agrees with the one-byte read at the same in-bounds
    address, including when the 32-byte window extends beyond the allocated array. -/
theorem readWithPadding32_extract_one (b : ByteArray) (addr : Nat)
    (haddr : addr < b.size) :
    (b.readWithPadding addr 32).extract 0 1 = b.readWithPadding addr 1 := by
  unfold ByteArray.readWithPadding
  rw [if_neg (by norm_num : ¬ 32 ≥ 2 ^ 64), if_neg (by norm_num : ¬ 1 ≥ 2 ^ 64)]
  dsimp only
  unfold ByteArray.readWithoutPadding
  rw [if_neg (by omega), if_neg (by omega)]
  have hread1 : (b.extract addr (addr + 1)).size = 1 := by
    rw [ByteArray.size_extract]
    omega
  have hread32 : 1 ≤ (b.extract addr (addr + min 32 b.size)).size := by
    rw [ByteArray.size_extract]
    omega
  rw [extract_append_left _ _ 0 1 hread32]
  rw [extract_extract_BA]
  rw [show addr + 0 = addr by omega,
    show min (addr + 1) (addr + min 32 b.size) = addr + 1 by omega]
  rw [show min 1 b.size = 1 by omega]
  simp only [hread1]
  rw [zeroes_zero rfl]
  simp

/-- Reading a subwindow back from an arbitrary source-window write. The destination may be
    extended, but its start must already be representable by the base byte array. -/
theorem write_read_window_from (src base : ByteArray)
    (srcAddr destAddr totalLen start len : Nat)
    (htotal : totalLen ≠ 0) (hsrc : srcAddr + totalLen ≤ src.size)
    (hdest : destAddr ≤ base.size) (hwindow : start + len ≤ totalLen)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write srcAddr base destAddr totalLen).readWithPadding (destAddr + start) len =
      src.extract (srcAddr + start) (srcAddr + start + len) := by
  have hprefix : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsource : (src.extract srcAddr (srcAddr + totalLen)).size = totalLen := by
    rw [ByteArray.size_extract]
    omega
  by_cases hin : destAddr + totalLen ≤ base.size
  · rw [write_eq_gen_from src base srcAddr destAddr totalLen htotal hsrc hin]
    rw [readWithPadding_eq_extract' _ (destAddr + start) len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hprefix, hsource]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hprefix, hsource]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show destAddr + start - destAddr = start by omega,
      show destAddr + start + len - destAddr = start + len by omega]
    rw [extract_extract_BA]
    congr 1 <;> omega
  · have hext : base.size < destAddr + totalLen := Nat.lt_of_not_ge hin
    rw [write_eq_gen_extend_from src base srcAddr destAddr totalLen htotal hsrc hdest hext]
    rw [readWithPadding_eq_extract' _ (destAddr + start) len hpos hlen64 (by
      rw [ByteArray.size_append, hprefix, hsource]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hprefix]; omega), hprefix]
    rw [show destAddr + start - destAddr = start by omega,
      show destAddr + start + len - destAddr = start + len by omega]
    rw [extract_extract_BA]
    congr 1 <;> omega

/-- A variable-length read strictly below an in-bounds arbitrary source-window write is
    preserved. -/
theorem write_read_below_len_from (src base : ByteArray)
    (srcAddr destAddr totalLen readAddr len : Nat)
    (htotal : totalLen ≠ 0) (hsrc : srcAddr + totalLen ≤ src.size)
    (hin : destAddr + totalLen ≤ base.size)
    (hbelow : readAddr + len ≤ destAddr) (hpos : 0 < len)
    (hlen64 : len < 2 ^ 64) :
    (src.write srcAddr base destAddr totalLen).readWithPadding readAddr len =
      base.readWithPadding readAddr len := by
  have hprefix : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsource : (src.extract srcAddr (srcAddr + totalLen)).size = totalLen := by
    rw [ByteArray.size_extract]
    omega
  rw [write_eq_gen_from src base srcAddr destAddr totalLen htotal hsrc hin]
  rw [readWithPadding_eq_extract' _ readAddr len hpos hlen64 (by
    rw [ByteArray.size_append, ByteArray.size_append, hprefix, hsource]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, hprefix, hsource]
    omega)]
  rw [extract_append_left _ _ _ _ (by rw [hprefix]; omega)]
  rw [extract_prefix _ destAddr readAddr (readAddr + len) hbelow]
  rw [← readWithPadding_eq_extract' base readAddr len hpos hlen64 (by omega)]

/-- A variable-length in-bounds read strictly above an in-bounds arbitrary source-window write
    is preserved. -/
theorem write_read_above_len_from (src base : ByteArray)
    (srcAddr destAddr totalLen readAddr len : Nat)
    (htotal : totalLen ≠ 0) (hsrc : srcAddr + totalLen ≤ src.size)
    (hin : destAddr + totalLen ≤ base.size)
    (habove : destAddr + totalLen ≤ readAddr)
    (hread : readAddr + len ≤ base.size) (hpos : 0 < len)
    (hlen64 : len < 2 ^ 64) :
    (src.write srcAddr base destAddr totalLen).readWithPadding readAddr len =
      base.readWithPadding readAddr len := by
  have hprefix : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hsource : (src.extract srcAddr (srcAddr + totalLen)).size = totalLen := by
    rw [ByteArray.size_extract]
    omega
  have hfront :
      (base.extract 0 destAddr ++ src.extract srcAddr (srcAddr + totalLen)).size =
        destAddr + totalLen := by
    rw [ByteArray.size_append, hprefix, hsource]
  rw [write_eq_gen_from src base srcAddr destAddr totalLen htotal hsrc hin]
  rw [readWithPadding_eq_extract' _ readAddr len hpos hlen64 (by
    rw [ByteArray.size_append, hfront, ByteArray.size_extract]
    omega)]
  rw [extract_append_right_window _ _ _ _ (by rw [hfront]; exact habove), hfront]
  rw [extract_extract_BA]
  rw [show destAddr + totalLen + (readAddr - (destAddr + totalLen)) = readAddr by omega]
  rw [show min (destAddr + totalLen + (readAddr + len - (destAddr + totalLen))) base.size =
    readAddr + len by omega]
  rw [← readWithPadding_eq_extract' base readAddr len hpos hlen64 hread]

theorem toBytes'_getD (n i : Nat) :
    (Ethereum.toBytes' n).getD i 0 = UInt8.ofNat (n >>> (8 * i)) := by
  induction n using Nat.strong_induction_on generalizing i with
  | h n ih =>
    cases n with
    | zero => simp [Ethereum.toBytes']
    | succ n =>
      rw [Ethereum.toBytes']
      cases i with
      | zero =>
        rw [← UInt8.toNat_inj]
        simp [UInt8.size]
        rfl
      | succ i =>
        simp only [List.getD_cons_succ]
        rw [ih ((n + 1) / UInt8.size) (by
          exact Nat.div_lt_self (by omega) (by decide)) i]
        rw [← UInt8.toNat_inj]
        change ((((n + 1) / UInt8.size) >>> (8 * i)) % 256) =
          (((n + 1) >>> (8 * (i + 1))) % 256)
        congr 1
        simp only [Nat.shiftRight_eq_div_pow]
        rw [Nat.div_div_eq_div_mul]
        congr 1
        change 256 * 2 ^ (8 * i) = _
        rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
        congr 1
        omega

theorem word_toBytesLE_getD (w : UInt256) (i : Nat) (hi : i < 32) :
    (EVM.Word.toBytesLE w).getD i 0 = UInt8.ofNat (w.toNat >>> (8 * i)) := by
  unfold EVM.Word.toBytesLE
  let b := Ethereum.toBytes' w.val
  change (b ++ List.replicate (32 - b.length) 0).getD i 0 = _
  by_cases hib : i < b.length
  · rw [List.getD_append _ _ _ _ hib]
    exact (show (Ethereum.toBytes' w.toNat).getD i 0 = _ from by
      exact toBytes'_getD w.toNat i)
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    have hpad : i - b.length < 32 - b.length := by
      have hblen : b.length ≤ 32 := by
        simpa [b] using Ethereum.toBytes'_le (k := 32) w.val.isLt
      omega
    have hpad' : i - b.length <
        (List.replicate (32 - b.length) (0 : UInt8)).length := by
      simpa using hpad
    have hz := List.getD_eq_getElem
      (List.replicate (32 - b.length) (0 : UInt8)) (0 : UInt8) hpad'
    rw [hz]
    simp only [List.getElem_replicate]
    rw [← UInt8.toNat_inj]
    simp only [UInt8.toNat_ofNat]
    have hnlt : w.toNat < 2 ^ (8 * b.length) := by
      simpa [b, fromBytes'_toBytes'] using
        (Ethereum.fromBytes'_le (bs := b))
    have hpow : w.toNat < 2 ^ (8 * i) :=
      lt_of_lt_of_le hnlt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hpow]
    simp

theorem word_toBytesBE_reverse (w : UInt256) :
    EVM.Word.toBytesBE w = (EVM.Word.toBytesLE w).reverse := by
  unfold EVM.Word.toBytesBE EVM.Word.toBytesLE
  simp [Ethereum.toBytesBigEndian]

theorem word_toBytesBE_getD (w : UInt256) (i : Nat) (hi : i < 32) :
    (EVM.Word.toBytesBE w).getD i 0 =
      UInt8.ofNat (w.toNat >>> ((31 - i) * 8)) := by
  rw [word_toBytesBE_reverse]
  have hlen : (EVM.Word.toBytesLE w).length = 32 := by
    unfold EVM.Word.toBytesLE
    have hb := Ethereum.toBytes'_le (k := 32) w.val.isLt
    simp
    omega
  rw [List.getD_reverse i (by rw [hlen]; exact hi), hlen]
  simpa [Nat.mul_comm] using word_toBytesLE_getD w (31 - i) (by omega)

theorem toByteArray_extract_one (w : UInt256) (i : Nat) (hi : i < 32) :
    w.toByteArray.extract i (i + 1) =
      ⟨#[UInt8.ofNat (w.toNat >>> ((31 - i) * 8))]⟩ := by
  rw [toByteArray_eq_toBytesBE]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract]
  simp only
  rw [List.extract_eq_take_drop]
  have hlen : (EVM.Word.toBytesBE w).length = 32 := by
    rw [word_toBytesBE_reverse, List.length_reverse]
    unfold EVM.Word.toBytesLE
    have hb := Ethereum.toBytes'_le (k := 32) w.val.isLt
    simp
    omega
  have hdrop : (EVM.Word.toBytesBE w).drop i =
      (EVM.Word.toBytesBE w).getD i 0 :: (EVM.Word.toBytesBE w).drop (i + 1) := by
    rw [← List.cons_getElem_drop_succ]
    rw [List.getD_eq_getElem _ _ (by rwa [hlen])]
  rw [hdrop, show i + 1 - i = 1 by omega, List.take_succ_cons, List.take_zero]
  simp only [word_toBytesBE_getD w i hi]

/-- `BYTE 0` of a 32-byte big-endian decode is the first byte of that array. -/
theorem byteAt_zero_uInt256OfByteArray {arr : ByteArray} {byte : UInt8}
    (hsize : arr.size = 32) (hfirst : arr.extract 0 1 = ⟨#[byte]⟩) :
    UInt256.byteAt ⟨0⟩ (uInt256OfByteArray arr) = UInt256.ofNat byte.toNat := by
  have hwordBytes : (uInt256OfByteArray arr).toByteArray = arr := by
    rw [toByteArray_eq_toBytesBE]
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp only
    simpa [byteArray_toList_eq] using toBytesBE_uInt256OfByteArray_of_size hsize
  have hone := congrArg (fun b : ByteArray => b.extract 0 1) hwordBytes
  change (uInt256OfByteArray arr).toByteArray.extract 0 (0 + 1) =
    arr.extract 0 1 at hone
  rw [toByteArray_extract_one (uInt256OfByteArray arr) 0 (by decide), hfirst] at hone
  have hbyte : UInt8.ofNat ((uInt256OfByteArray arr).toNat >>> 248) = byte := by
    simpa using hone
  apply u256_inj
  unfold UInt256.byteAt
  rw [if_neg (by decide)]
  rw [show (UInt256.ofNat ((31 - (⟨0⟩ : UInt256).toNat) * 8)) =
      UInt256.ofNat 248 by decide]
  change (UInt256.land
    (UInt256.shiftRight (uInt256OfByteArray arr) (UInt256.ofNat 248)) ⟨0xff⟩).toNat = _
  rw [uland_toNat, ushr_ofNat_toNat _ 248 (by decide),
    show (⟨0xff⟩ : UInt256).toNat = 255 from by decide]
  rw [ulit_toNat' byte.toNat (lt_of_lt_of_le byte.toFin.isLt (by decide))]
  have hb := congrArg UInt8.toNat hbyte
  calc
    (uInt256OfByteArray arr).toNat >>> 248 &&& 255 =
        ((uInt256OfByteArray arr).toNat >>> 248) % 256 := by
      simpa using nat_land_mask_eq_mod ((uInt256OfByteArray arr).toNat >>> 248) 8
    _ = byte.toNat := by simpa using hb

end Reasoning.Theory

namespace Reasoning.Reach

open Reasoning.Theory

theorem RD.dup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (h : RD code ee g s0
      pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup12_xstep hc hp hdec hs hov)

theorem RD.dup16 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP16, .none)) (hov : t.length + 17 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: pp :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup16_xstep hc hp hdec hs hov)

theorem RD.push8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH8, some (argv, 8)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat 9) (argv :: stk)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.pushConst argv (by decide) hdec hov

theorem RD.push3 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {stk : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C) (argv : UInt256)
    (hdec : decode code pc = some (.Push .PUSH3, some (argv, 3)))
    (hov : stk.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + UInt256.ofNat 4) (argv :: stk)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.pushConst argv (by decide) hdec hov

theorem RD.byte {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.BYTE, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.byteAt a b :: t) mem aw rdata acc (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => byte_xstep hc hp hdec hs hov)

/-- `MSTORE8`: pops `a` (offset), `b` (value); writes the low byte at `mem[a]`. -/
theorem RD.mstore8 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256} (mcost : ℕ) (memout : ByteArray) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE8, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw → s.machineState.stack = a :: b :: t →
        memoryExpansionCost s .MSTORE8 = mcost)
    (hmemout : (⟨#[UInt8.ofNat b.toNat]⟩ : ByteArray).write 0 mem a.toNat 1 = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat 1) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc (k + 1) (C + (mcost + 3)) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .MSTORE8 = mcost := hmc s haw hstk
    have st := mstore8_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost + 3)
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stMStore8 s a b t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stMStore8]; exact hcode
      · simp only [stMStore8]; rw [hpc]
      · rfl
      · simp only [stMStore8, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stMStore8]; rw [hmem, hmemout]
      · simp only [stMStore8]; rw [haw, hawout]
      · simp only [stMStore8]; exact hrdata
      · simp only [stMStore8]; exact hacc
      · exact hee
      · exact hworld

/-- `MCOPY`: pops destination, source, and length; copies bytes within memory. -/
theorem RD.mcopy {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ)
    (memout : ByteArray) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MCOPY, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: t → memoryExpansionCost s .MCOPY = mcost)
    (hmemout : mem.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat
      (MachineState.M aw.toNat (max a.toNat b.toNat) c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc
      (k + 1)
      (C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc,
    hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .MCOPY = mcost := hmc s haw hstk
    have st := mcopy_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    rw [collapse_two_stage] at st
    by_cases gg : g.toNat <
        C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · have hcost_pos :
          0 < mcost + (GasConstants.Gverylow +
            GasConstants.Gcopy * ((c.toNat + 31) / 32)) := by
        simp [GasConstants.Gverylow]
      refine Or.inr ⟨stMcopy s a b c t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stMcopy]; exact hcode
      · simp only [stMcopy]; rw [hpc]
      · rfl
      · simp only [stMcopy, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stMcopy]; rw [hmem, hmemout]
      · simp only [stMcopy]; rw [haw, hawout]
      · simp only [stMcopy]; exact hrdata
      · simp only [stMcopy]; exact hacc
      · exact hee
      · exact hworld

theorem RD.swap13 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP13, .none)) (hov : t.length + 14 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (nn :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap13_xstep hc hp hdec hs hov)

theorem RD.swap14 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: oo :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP14, .none)) (hov : t.length + 15 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (oo :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap14_xstep hc hp hdec hs hov)

end Reasoning.Reach
