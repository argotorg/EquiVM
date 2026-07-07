import Examples.StringStoreLite.ClearCurrentLong

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 8000000

namespace StringStoreLite

theorem stringStoreLiteSwap5_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP5, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: t)
    (hov : t.length + 6 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (f :: b :: c :: d :: e :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP5, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap5 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: t).length - 6 + 6 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.swap5 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP5, .none)) (hov : t.length + 6 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (f :: b :: c :: d :: e :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => stringStoreLiteSwap5_xstep hc hp hdec hs hov)

theorem stringStoreLiteSwap6_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f h : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP6, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: h :: t)
    (hov : t.length + 7 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (h :: b :: c :: d :: e :: f :: a :: t), .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP6, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap6 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: e :: f :: h :: t).length - 7 + 7 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.swap6 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f h : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: h :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP6, .none)) (hov : t.length + 7 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (h :: b :: c :: d :: e :: f :: a :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => stringStoreLiteSwap6_xstep hc hp hdec hs hov)

theorem stringStoreLiteDup9_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f h i j : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: h :: i :: j :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (j :: a :: b :: c :: d :: e :: f :: h :: i :: j :: t),
           .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP9, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup9 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: h :: i :: j :: t).length - 9 + 10 >
        1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.dup9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f h i j : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: h :: i :: j :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (j :: a :: b :: c :: d :: e :: f :: h :: i :: j :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => stringStoreLiteDup9_xstep hc hp hdec hs hov)

theorem stringStoreLiteDup10_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f h i j l : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP10, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: h :: i :: j :: l :: t)
    (hov : t.length + 11 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (l :: a :: b :: c :: d :: e :: f :: h :: i :: j :: l :: t),
           .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP10, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_dup10 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: h :: i :: j :: l :: t).length - 10 + 11 >
        1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.dup10 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f h i j l : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: h :: i :: j :: l :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP10, .none)) (hov : t.length + 11 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (l :: a :: b :: c :: d :: e :: f :: h :: i :: j :: l :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => stringStoreLiteDup10_xstep hc hp hdec hs hov)

theorem uint256_land_zero_left (x : UInt256) :
    UInt256.land ⟨0⟩ x = ⟨0⟩ := by
  apply u256_inj
  change (0 &&& x.val.val) % UInt256.size = 0
  rw [Nat.zero_and]
  decide

theorem uint256_land_zero_right (x : UInt256) :
    UInt256.land x ⟨0⟩ = ⟨0⟩ := by
  apply u256_inj
  change (x.val.val &&& 0) % UInt256.size = 0
  rw [Nat.and_zero]
  decide

theorem uint256_lor_zero_left (x : UInt256) :
    UInt256.lor ⟨0⟩ x = x := by
  apply u256_inj
  change (0 ||| x.val.val) % UInt256.size = x.val.val
  rw [Nat.zero_or]
  exact Nat.mod_eq_of_lt x.val.isLt

theorem uint256_lor_zero_right (x : UInt256) :
    UInt256.lor x ⟨0⟩ = x := by
  apply u256_inj
  change (x.val.val ||| 0) % UInt256.size = x.val.val
  rw [Nat.or_zero]
  exact Nat.mod_eq_of_lt x.val.isLt

theorem uint256_add_zero_right (x : UInt256) : x + ⟨0⟩ = x := by
  apply u256_inj
  rw [uadd_toNat]
  change (x.toNat + 0) % UInt256.size = x.toNat
  rw [Nat.add_zero]
  exact Nat.mod_eq_of_lt x.val.isLt

theorem uint256_sub_zero_right (x : UInt256) : UInt256.sub x ⟨0⟩ = x := by
  apply u256_inj
  have hle : (⟨0⟩ : UInt256).toNat ≤ x.toNat := by
    change 0 ≤ x.toNat
    exact Nat.zero_le _
  rw [usub_toNat (a := x) (b := (⟨0⟩ : UInt256)) hle]
  rfl

theorem clearCurrentHashAw6 :
    clearCurrentHashAw (UInt256.ofNat 6) = UInt256.ofNat 6 := by
  native_decide

theorem clearCurrentBaseMemFrom_currentLengthZeroReturnMem_size :
    (clearCurrentBaseMemFrom currentLengthZeroReturnMem).size = 192 := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_eq (UInt256.toByteArray ⟨0⟩) currentLengthZeroReturnMem 0
    (by rw [toByteArray_size])
    (by rw [currentLengthZeroReturnMem_size]; decide)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    currentLengthZeroReturnMem_size]
  omega

theorem clearCurrentBaseMemFrom_currentLengthZeroReturnMem_read64 :
    (clearCurrentBaseMemFrom currentLengthZeroReturnMem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨160⟩ := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_read_above (UInt256.toByteArray ⟨0⟩) currentLengthZeroReturnMem 0 64
    (by rw [toByteArray_size])
    (by rw [currentLengthZeroReturnMem_size]; decide)
    (by decide)
    (by rw [currentLengthZeroReturnMem_size]; decide)]
  exact currentLengthZeroReturnMem_read64

theorem clearCurrentBaseMemFrom_currentLengthZeroReturnMem_read128 :
    (clearCurrentBaseMemFrom currentLengthZeroReturnMem).readWithPadding 128 32 =
      UInt256.toByteArray ⟨0⟩ := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_read_above (UInt256.toByteArray ⟨0⟩) currentLengthZeroReturnMem 0 128
    (by rw [toByteArray_size])
    (by rw [currentLengthZeroReturnMem_size]; decide)
    (by decide)
    (by rw [currentLengthZeroReturnMem_size]; decide)]
  exact currentLengthZeroReturnMem_read128

theorem clearCurrentBaseMemFrom_size_of_ge32 (mem : ByteArray) (hmem : 32 ≤ mem.size) :
    (clearCurrentBaseMemFrom mem).size = mem.size := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_eq (UInt256.toByteArray ⟨0⟩) mem 0
    (by rw [toByteArray_size])
    (by omega)]
  have htail : (mem.extract (0 + 32) mem.size).size = mem.size - 32 := by
    rw [ByteArray.size_extract]
    omega
  have hzeroExtract : ((⟨0⟩ : UInt256).toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    htail, hzeroExtract]
  omega

theorem clearCurrentBaseMemFrom_idem {mem : ByteArray} (hmem : 32 ≤ mem.size) :
    clearCurrentBaseMemFrom (clearCurrentBaseMemFrom mem) =
      clearCurrentBaseMemFrom mem := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_eq (UInt256.toByteArray ⟨0⟩)
    (clearCurrentBaseMemFrom mem) 0 (by rw [toByteArray_size])]
  · rw [clearCurrentBaseMemFrom]
    rw [write32_eq (UInt256.toByteArray ⟨0⟩) mem 0
      (by rw [toByteArray_size]) (by omega)]
    have hprefixEmpty : mem.extract 0 0 = ByteArray.empty := by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_empty_of_le (by omega)
    rw [hprefixEmpty, empty_append]
    have hleftEmpty :
        (((UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32 ++
            mem.extract (0 + 32) mem.size).extract 0 0) = ByteArray.empty := by
      apply ByteArray.ext
      rw [ByteArray.data_extract]
      exact Array.extract_eq_empty_of_le (by omega)
    rw [hleftEmpty, empty_append]
    have htail :
        (((UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32 ++
            mem.extract (0 + 32) mem.size).extract (0 + 32)
          (((UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32 ++
            mem.extract (0 + 32) mem.size).size)) =
          mem.extract (0 + 32) mem.size := by
      have hright := extract_append_right_window
        ((UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32)
        (mem.extract (0 + 32) mem.size) 32
        (((UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0 32 ++
          mem.extract (0 + 32) mem.size).size)
        (by rw [ByteArray.size_extract, toByteArray_size]; omega)
      rw [hright, extract_extract_BA]
      simp [hmem]
    rw [htail]
  · rw [clearCurrentBaseMemFrom_size_of_ge32 mem hmem]
    omega

theorem nat_ceil32_le_ceil32 {a b : Nat} (h : a ≤ b) :
    (a + 31) / 32 ≤ (b + 31) / 32 := by
  exact Nat.div_le_div_right (Nat.add_le_add_right h 31)

theorem nat_ceil32_eq_div_of_mod_zero {n : Nat} (hmod : n % 32 = 0) :
    (n + 31) / 32 = n / 32 := by
  have hdiv := Nat.div_add_mod n 32
  omega

theorem u256_div_add31_toNat_of_lt_sign {x : UInt256} (hx : x.toNat < 2 ^ 255) :
    (UInt256.div (x + ⟨31⟩) ⟨32⟩).toNat = (x.toNat + 31) / 32 := by
  have hadd : (x + (⟨31⟩ : UInt256)).toNat = x.toNat + 31 := by
    rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
    exact Nat.mod_eq_of_lt (by
      have hsize' : (2 : Nat) ^ 255 + 31 < UInt256.size := by
        norm_num [UInt256.size]
      omega)
  rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]

theorem u256_div_add31_toNat_of_u64 {x : UInt256}
    (hx : x.toNat ≤ ABI.solcMaxU64) :
    (UInt256.div (x + ⟨31⟩) ⟨32⟩).toNat = (x.toNat + 31) / 32 := by
  exact u256_div_add31_toNat_of_lt_sign (x := x) (by
    have hmax : ABI.solcMaxU64 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega)

theorem ugt_eq_zero_toNat_le {a b : UInt256} (h : UInt256.gt a b = ⟨0⟩) :
    a.toNat ≤ b.toNat := by
  by_contra hle
  have hgt : b.toNat < a.toNat := Nat.lt_of_not_ge hle
  have hone : UInt256.gt a b = ⟨1⟩ := ugt_one hgt
  rw [hone] at h
  contradiction

theorem ugt_eq_one_toNat_lt {a b : UInt256} (h : UInt256.gt a b = ⟨1⟩) :
    b.toNat < a.toNat := by
  by_contra hlt
  have hle : a.toNat ≤ b.toNat := Nat.le_of_not_gt hlt
  have hzero : UInt256.gt a b = ⟨0⟩ := ugt_zero hle
  rw [hzero] at h
  contradiction

theorem clearCurrentBaseMemFrom_setPaddedMem_read160_short_nonzero
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding 160 32 =
      (setPaddedMem cd len payloadStart).readWithPadding 160 32 := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_read_above (UInt256.toByteArray ⟨0⟩) (setPaddedMem cd len payloadStart) 0 160
    (by rw [toByteArray_size])
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)
      rw [hsize]
      omega)
    (by decide)
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)
      rw [hsize]
      omega)]

theorem clearCurrentBaseMemFrom_setPaddedMem_read160_u64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding 160 32 =
      (setPaddedMem cd len payloadStart).readWithPadding 160 32 := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_read_above (UInt256.toByteArray ⟨0⟩) (setPaddedMem cd len payloadStart) 0 160
    (by rw [toByteArray_size])
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax)
      rw [hsize]
      omega)
    (by decide)
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax)
      rw [hsize]
      omega)]

theorem clearCurrentBaseMemFrom_setPaddedMem_read128_short_nonzero
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding 128 32 =
      (setPaddedMem cd len payloadStart).readWithPadding 128 32 := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_read_above (UInt256.toByteArray ⟨0⟩) (setPaddedMem cd len payloadStart) 0 128
    (by rw [toByteArray_size])
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)
      rw [hsize]
      omega)
    (by decide)
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)
      rw [hsize]
      omega)]

theorem clearCurrentBaseMemFrom_setPaddedMem_read128_u64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding 128 32 =
      (setPaddedMem cd len payloadStart).readWithPadding 128 32 := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_read_above (UInt256.toByteArray ⟨0⟩) (setPaddedMem cd len payloadStart) 0 128
    (by rw [toByteArray_size])
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax)
      rw [hsize]
      omega)
    (by decide)
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax)
      rw [hsize]
      omega)]

theorem clearCurrentBaseMemFrom_setPaddedMem_read64_short_nonzero
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding 64 32 =
      (setPaddedMem cd len payloadStart).readWithPadding 64 32 := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_read_above (UInt256.toByteArray ⟨0⟩) (setPaddedMem cd len payloadStart) 0 64
    (by rw [toByteArray_size])
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)
      rw [hsize]
      omega)
    (by decide)
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort)
      rw [hsize]
      omega)]

theorem clearCurrentBaseMemFrom_setPaddedMem_read64_u64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding 64 32 =
      (setPaddedMem cd len payloadStart).readWithPadding 64 32 := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_read_above (UInt256.toByteArray ⟨0⟩) (setPaddedMem cd len payloadStart) 0 64
    (by rw [toByteArray_size])
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax)
      rw [hsize]
      omega)
    (by decide)
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax)
      rw [hsize]
      omega)]

theorem setCalldataMem_read_payload_word
    (cd : ByteArray) (len payloadStart : UInt256) (i : Nat)
    (hnz : len.toNat ≠ 0)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hi : i < len.toNat / 32) :
    (setCalldataMem cd len payloadStart).readWithPadding (160 + 32 * i) 32 =
      (cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).extract
        (32 * i) (32 * i + 32) := by
  exact solcBytesSetCalldataMem_read_payload_word cd len payloadStart i hnz hsrc hi

theorem setPaddedMem_read_payload_word
    (cd : ByteArray) (len payloadStart : UInt256) (i : Nat)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hi : i < len.toNat / 32) :
    (setPaddedMem cd len payloadStart).readWithPadding (160 + 32 * i) 32 =
      (cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).extract
        (32 * i) (32 * i + 32) := by
  exact solcBytesSetPaddedMem_read_payload_word cd len payloadStart i hnz hlenMax hsrc hi

theorem clearCurrentBaseMemFrom_setPaddedMem_read_payload_word
    (cd : ByteArray) (len payloadStart : UInt256) (i : Nat)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hi : i < len.toNat / 32) :
    (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding
        (160 + 32 * i) 32 =
      (cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).extract
        (32 * i) (32 * i + 32) := by
  rw [clearCurrentBaseMemFrom]
  rw [write32_read_above (UInt256.toByteArray ⟨0⟩) (setPaddedMem cd len payloadStart)
    0 (160 + 32 * i)
    (by rw [toByteArray_size])
    (by
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax)
      rw [hsize]
      omega)
    (by omega)
    (by
      have hfull : 32 * i + 32 ≤ len.toNat := by
        have hlt : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
        have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
          Nat.mul_le_mul_left 32 hlt
        have hle : 32 * (len.toNat / 32) ≤ len.toNat := by
          simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
        nlinarith
      have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax)
      rw [hsize]
      omega)]
  exact setPaddedMem_read_payload_word cd len payloadStart i hnz hlenMax hsrc hi

theorem clearCurrentBaseMemFrom_setPaddedMem_mload128_short_nonzero_payloadAw
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).size
        ∨ (⟨128⟩ : UInt256) ≥ setHelperPayloadAw len * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) = len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := setHelperPayloadAw len) (v := len)
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      rw [clearCurrentBaseMemFrom_size_of_ge32]
      · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega
      · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega)
    (by
      rw [setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort]
      decide)
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      rw [clearCurrentBaseMemFrom_setPaddedMem_read128_short_nonzero
        cd len payloadStart hnz hshort hsrc]
      exact setPaddedMem_read128 cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort))

theorem clearCurrentBaseMemFrom_setPaddedMem_mload64_short_nonzero
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).size
        ∨ (⟨64⟩ : UInt256) ≥ setHelperPayloadAw len * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = currentLengthFreePtr len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := setHelperPayloadAw len)
    (v := currentLengthFreePtr len)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      rw [clearCurrentBaseMemFrom_size_of_ge32]
      · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega
      · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega)
    (by
      rw [setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort]
      decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      rw [clearCurrentBaseMemFrom_setPaddedMem_read64_short_nonzero
        cd len payloadStart hnz hshort hsrc]
      exact setPaddedMem_read64 cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort))

theorem clearCurrentBaseMemFrom_setPaddedMem_mload128_nonzero_u64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).size
        ∨ (⟨128⟩ : UInt256) ≥ clearCurrentHashAw (setHelperEntryAw len) * ⟨32⟩ then
        ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) = len := by
  have hentryGe : 1 ≤ (setHelperEntryAw len).toNat := by
    have hge := setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
    omega
  have hawEq : clearCurrentHashAw (setHelperEntryAw len) = setHelperEntryAw len :=
    clearCurrentHashAw_eq_self_of_ge1 hentryGe
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := clearCurrentHashAw (setHelperEntryAw len))
    (v := len)
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      rw [clearCurrentBaseMemFrom_size_of_ge32]
      · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_u64 hlenMax)
        rw [hsize]
        omega
      · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_u64 hlenMax)
        rw [hsize]
        omega)
    (by
      rw [hawEq]
      exact setHelperEntryAw_mload128_of_u64 hlenMax)
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      rw [clearCurrentBaseMemFrom_setPaddedMem_read128_u64
        cd len payloadStart hnz hlenMax hsrc]
      exact setPaddedMem_read128 cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax))

theorem clearCurrentBaseMemFrom_setPaddedMem_mload64_nonzero_u64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).size
        ∨ (⟨64⟩ : UInt256) ≥ clearCurrentHashAw (setHelperEntryAw len) * ⟨32⟩ then
        ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = currentLengthFreePtr len := by
  have hentryGe : 1 ≤ (setHelperEntryAw len).toNat := by
    have hge := setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
    omega
  have hawEq : clearCurrentHashAw (setHelperEntryAw len) = setHelperEntryAw len :=
    clearCurrentHashAw_eq_self_of_ge1 hentryGe
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := clearCurrentHashAw (setHelperEntryAw len))
    (v := currentLengthFreePtr len)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      rw [clearCurrentBaseMemFrom_size_of_ge32]
      · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_u64 hlenMax)
        rw [hsize]
        omega
      · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_u64 hlenMax)
        rw [hsize]
        omega)
    (by
      rw [hawEq]
      exact setHelperEntryAw_mload64_of_u64 hlenMax)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      rw [clearCurrentBaseMemFrom_setPaddedMem_read64_u64
        cd len payloadStart hnz hlenMax hsrc]
      exact setPaddedMem_read64 cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_u64 hlenMax))

theorem currentLengthFreePtr_le_setPaddedMem_size_u64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (currentLengthFreePtr len).toNat ≤ (setPaddedMem cd len payloadStart).size := by
  have hlenLt : len.toNat < 2 ^ 255 := by
    have hmax : ABI.solcMaxU64 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega
  have hpos : 0 < len.toNat := Nat.pos_of_ne_zero hnz
  rw [setPaddedMem_size cd len payloadStart hnz hsrc (setDataEnd_toNat_of_u64 hlenMax)]
  rw [currentLengthFreePtr_toNat_of_len_lt_sign_pos hlenLt hpos]
  have hdiv : 32 * ((len.toNat - 1) / 32) ≤ len.toNat - 1 := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (len.toNat - 1) 32
  omega

theorem currentLengthFreePtr_le_clearCurrentBaseMemFrom_setPaddedMem_size_u64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (currentLengthFreePtr len).toNat ≤
      (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).size := by
  rw [clearCurrentBaseMemFrom_size_of_ge32]
  · exact currentLengthFreePtr_le_setPaddedMem_size_u64 cd len payloadStart hnz hlenMax hsrc
  · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
      (setDataEnd_toNat_of_u64 hlenMax)
    rw [hsize]
    omega

theorem setHelperEntryAw_mstoreFreePtr_mul32_lt_u64 {len : UInt256}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    (UInt256.ofNat
      (MachineState.M (setHelperEntryAw len).toNat (currentLengthFreePtr len).toNat 32)).toNat *
        32 < UInt256.size := by
  have hlenLt : len.toNat < 2 ^ 255 := by
    have hmax : ABI.solcMaxU64 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega
  have hpos : 0 < len.toNat := Nat.pos_of_ne_zero hnz
  exact machineState_M_word_mul32_lt_of_bounds
    (aw := setHelperEntryAw len) (off := currentLengthFreePtr len) (len := (⟨32⟩ : UInt256))
    (setHelperEntryAw_mul32_lt_of_u64 hlenMax)
    (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      exact currentLengthFreePtr_add63_lt_size_of_len_lt_sign_pos hlenLt hpos)

theorem setHelperEntryAw_mstoreFreePtr_ge3_u64 {len : UInt256}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    3 ≤
      (UInt256.ofNat
        (MachineState.M (setHelperEntryAw len).toNat (currentLengthFreePtr len).toNat 32)).toNat := by
  have hentryGe : 5 ≤ (setHelperEntryAw len).toNat :=
    setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
  have hMNoWrap :
      MachineState.M (setHelperEntryAw len).toNat (currentLengthFreePtr len).toNat 32 <
        UInt256.size := by
    have hmul :
        MachineState.M (setHelperEntryAw len).toNat (currentLengthFreePtr len).toNat 32 * 32 <
          UInt256.size := by
      apply machineState_M_mul32_lt_of_bounds
      · exact setHelperEntryAw_mul32_lt_of_u64 hlenMax
      · have hlenLt : len.toNat < 2 ^ 255 := by
          have hmax : ABI.solcMaxU64 < 2 ^ 255 := by
            norm_num [ABI.solcMaxU64]
          omega
        exact currentLengthFreePtr_add63_lt_size_of_len_lt_sign_pos hlenLt
          (Nat.pos_of_ne_zero hnz)
    have hle :
        MachineState.M (setHelperEntryAw len).toNat (currentLengthFreePtr len).toNat 32 ≤
          MachineState.M (setHelperEntryAw len).toNat (currentLengthFreePtr len).toNat 32 * 32 := by
      simpa using Nat.mul_le_mul_left
        (MachineState.M (setHelperEntryAw len).toNat (currentLengthFreePtr len).toNat 32)
        (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt hle hmul
  rw [ulit_toNat' _ hMNoWrap]
  have hgeLeft :
      (setHelperEntryAw len).toNat ≤
        MachineState.M (setHelperEntryAw len).toNat (currentLengthFreePtr len).toNat 32 :=
    machineState_M_ge_left
  omega

theorem stringStoreLiteX_setLongReturnFromWrite
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256} {σ' : AccountMap}
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨261⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
      ByteArray.empty (cA, σ') k C) :
    RDret stringStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd261⟩ := hreach
  have hentryGe5 : 5 ≤ (setHelperEntryAw len).toNat :=
    setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
  have hentryGe3 : 3 ≤ (setHelperEntryAw len).toNat := by omega
  have hlenLt : len.toNat < 2 ^ 255 := by
    have hmax : ABI.solcMaxU64 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ := by
    have hgtNat : 31 < len.toNat := by omega
    rw [ult_one (by simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using hgtNat)]
    decide
  have hfreeGe96 : 96 ≤ (currentLengthFreePtr len).toNat :=
    currentLengthFreePtr_ge96_of_long (len := len) hlenLt hgt31
  have hfreeLeMem :
      (currentLengthFreePtr len).toNat ≤ (setPaddedMem I.calldata len payloadStart).size :=
    currentLengthFreePtr_le_setPaddedMem_size_u64
      I.calldata len payloadStart hnz hlenMax hsrc
  have rd93 := evm_run rd261 with [
    jumpdest, pop, dup1,
    raw mload 0 len (setHelperEntryAw len) (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [set_activeWordsMload128_eq_self hentryGe5]
        omega)
      (setPaddedMem_mload128_nonzero_u64 I.calldata len payloadStart hnz hlenMax hsrc)
      (set_activeWordsMload128_eq_self hentryGe5) (by evm_ov),
    swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd744 := evm_run rd93 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (setHelperEntryAw len) (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [activeWordsMload64_eq_self hentryGe3]
        omega)
      (setPaddedMem_mload64_nonzero_u64 I.calldata len payloadStart hnz hlenMax hsrc)
      (activeWordsMload64_eq_self hentryGe3) (by evm_ov),
    push2 ⟨106⟩, swap2, swap1, push2 ⟨744⟩, jump (by jump_dest)]
  have rd729 := evm_run rd744 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨763⟩,
    push0, dup4, add, dup5, push2 ⟨729⟩, jump (by jump_dest)]
  have rd720 := evm_run rd729 with [
    jumpdest, push2 ⟨738⟩, dup2, push2 ⟨720⟩, jump (by jump_dest)]
  have rd738 := evm_run rd720 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  let returnMem := len.toByteArray.write 0 (setPaddedMem I.calldata len payloadStart)
    (currentLengthFreePtr len + ⟨0⟩).toNat 32
  let awStore :=
    UInt256.ofNat
      (MachineState.M (setHelperEntryAw len).toNat
        (currentLengthFreePtr len + ⟨0⟩).toNat 32)
  have hawStore :
      UInt256.ofNat
          (MachineState.M (setHelperEntryAw len).toNat
            (currentLengthFreePtr len + ⟨0⟩).toNat 32) =
        awStore := rfl
  have rd763 := evm_run rd738 with [
    jumpdest, dup3,
    raw mstore
      (Cₘ awStore - Cₘ (setHelperEntryAw len))
      returnMem awStore (by decide)
      (by
        intro s haw hstk
        simpa [awStore, returnMem, currentLength_add_zero_toNat] using
          (mstoreCostSpec (aw := setHelperEntryAw len)
            (off := currentLengthFreePtr len + ⟨0⟩)
            (stk := [len, len, currentLengthFreePtr len + ⟨0⟩, ⟨763⟩,
              currentLengthFreePtr len + ⟨32⟩, currentLengthFreePtr len, len,
              ⟨106⟩, stringStoreLiteSelWord I]) s haw hstk))
      (by rfl)
      hawStore (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd106 := evm_run rd763 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have hreturnRead64 :
      returnMem.readWithPadding 64 32 = UInt256.toByteArray (currentLengthFreePtr len) := by
    simpa [returnMem] using
      currentLengthReturnWrite_preserves_read64_zero
        (mem := setPaddedMem I.calldata len payloadStart) (len := len)
        (freePtr := currentLengthFreePtr len) hfreeGe96 hfreeLeMem
        (setPaddedMem_read64 I.calldata len payloadStart hnz hsrc
          (setDataEnd_toNat_of_u64 hlenMax))
  have hreturnSize64 : 64 < returnMem.size := by
    have hge := writeWord_size_gt64_of_mem
      (mem := setPaddedMem I.calldata len payloadStart)
      (off := (currentLengthFreePtr len + ⟨0⟩).toNat) (word := len)
      (by
        have hsize := setPaddedMem_size I.calldata len payloadStart hnz hsrc
          (setDataEnd_toNat_of_u64 hlenMax)
        rw [hsize]
        omega)
      (by simpa [currentLength_add_zero_toNat] using hfreeLeMem)
    simpa [returnMem] using hge
  have hawStoreNoWrap :
      awStore.toNat * 32 < UInt256.size := by
    simpa [awStore, currentLength_add_zero_toNat] using
      setHelperEntryAw_mstoreFreePtr_mul32_lt_u64 (len := len) hnz hlenMax
  have hawStoreGe3 : 3 ≤ awStore.toNat := by
    simpa [awStore, currentLength_add_zero_toNat] using
      setHelperEntryAw_mstoreFreePtr_ge3_u64 (len := len) hnz hlenMax
  have hfinalFreePtr :
      (if (⟨64⟩ : UInt256).toNat ≥ returnMem.size
          ∨ (⟨64⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (returnMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        currentLengthFreePtr len := by
    exact mloadWordValue_of_readWithPadding
      (mem := returnMem) (aw := awStore) (off := (⟨64⟩ : UInt256))
      (v := currentLengthFreePtr len)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnSize64)
      (wordMul32_not_le64_of_ge3 hawStoreGe3 hawStoreNoWrap)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnRead64)
  let awFinal := UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawFinal :
      UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32) = awFinal := rfl
  have hretLen : (UInt256.sub (currentLengthFreePtr len + ⟨32⟩)
      (currentLengthFreePtr len)).toNat = 32 :=
    currentLengthFreePtr_retLen_of_len_lt_sign_pos (len := len) hlenLt
      (Nat.pos_of_ne_zero hnz)
  have hretBytes :
      returnMem.readWithPadding (currentLengthFreePtr len).toNat
        (UInt256.sub (currentLengthFreePtr len + ⟨32⟩) (currentLengthFreePtr len)).toNat =
        UInt256.toByteArray len := by
    simpa [returnMem] using
      currentLengthReturnWrite_retBytes
        (mem := setPaddedMem I.calldata len payloadStart) (len := len)
        (freePtr := currentLengthFreePtr len) hfreeLeMem hretLen
  exact evm_run rd106 with [
    jumpdest, push1 ⟨64⟩,
    raw mload
      (Cₘ awFinal - Cₘ awStore)
      (currentLengthFreePtr len) awFinal (by decide)
      (by
        intro s haw hstk
        simpa [awFinal] using
          (mloadCostSpec (aw := awStore) (off := (⟨64⟩ : UInt256))
            (stk := [currentLengthFreePtr len + ⟨32⟩, stringStoreLiteSelWord I]) s haw hstk))
      hfinalFreePtr
      hawFinal (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret
      (Cₘ (UInt256.ofNat
        (MachineState.M awFinal.toNat (currentLengthFreePtr len).toNat
          (UInt256.sub (currentLengthFreePtr len + ⟨32⟩)
            (currentLengthFreePtr len)).toNat)) - Cₘ awFinal)
      (UInt256.toByteArray len) (by decide)
      (by
        intro s haw hstk
        simpa using
          (returnCostSpec
            (aw := awFinal) (off := currentLengthFreePtr len)
            (len := UInt256.sub (currentLengthFreePtr len + ⟨32⟩)
              (currentLengthFreePtr len))
            (stk := [stringStoreLiteSelWord I]) s haw hstk))
      hretBytes
      (by evm_ov)]

theorem stringStoreLiteX_setLongReturnFromWriteAfterClearBase
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256} {σ' : AccountMap}
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨261⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (clearCurrentHashAw (setHelperEntryAw len))
      ByteArray.empty (cA, σ') k C) :
    RDret stringStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd261⟩ := hreach
  have hentryGe5 : 5 ≤ (setHelperEntryAw len).toNat :=
    setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
  have hentryGe1 : 1 ≤ (setHelperEntryAw len).toNat := by omega
  have hawEq : clearCurrentHashAw (setHelperEntryAw len) = setHelperEntryAw len :=
    clearCurrentHashAw_eq_self_of_ge1 hentryGe1
  have hentryGe3 : 3 ≤ (setHelperEntryAw len).toNat := by omega
  have hlenLt : len.toNat < 2 ^ 255 := by
    have hmax : ABI.solcMaxU64 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    omega
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ := by
    have hgtNat : 31 < len.toNat := by omega
    rw [ult_one (by simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using hgtNat)]
    decide
  have hfreeGe96 : 96 ≤ (currentLengthFreePtr len).toNat :=
    currentLengthFreePtr_ge96_of_long (len := len) hlenLt hgt31
  have hfreeLeMem :
      (currentLengthFreePtr len).toNat ≤
        (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).size :=
    currentLengthFreePtr_le_clearCurrentBaseMemFrom_setPaddedMem_size_u64
      I.calldata len payloadStart hnz hlenMax hsrc
  have rd93 := evm_run rd261 with [
    jumpdest, pop, dup1,
    raw mload 0 len (clearCurrentHashAw (setHelperEntryAw len)) (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [hawEq, set_activeWordsMload128_eq_self hentryGe5]
        omega)
      (clearCurrentBaseMemFrom_setPaddedMem_mload128_nonzero_u64
        I.calldata len payloadStart hnz hlenMax hsrc)
      (by rw [hawEq]; exact set_activeWordsMload128_eq_self hentryGe5)
      (by evm_ov),
    swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd744 := evm_run rd93 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (clearCurrentHashAw (setHelperEntryAw len))
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [hawEq, activeWordsMload64_eq_self hentryGe3]
        omega)
      (clearCurrentBaseMemFrom_setPaddedMem_mload64_nonzero_u64
        I.calldata len payloadStart hnz hlenMax hsrc)
      (by rw [hawEq]; exact activeWordsMload64_eq_self hentryGe3)
      (by evm_ov),
    push2 ⟨106⟩, swap2, swap1, push2 ⟨744⟩, jump (by jump_dest)]
  have rd729 := evm_run rd744 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨763⟩,
    push0, dup4, add, dup5, push2 ⟨729⟩, jump (by jump_dest)]
  have rd720 := evm_run rd729 with [
    jumpdest, push2 ⟨738⟩, dup2, push2 ⟨720⟩, jump (by jump_dest)]
  have rd738 := evm_run rd720 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  let returnMem := len.toByteArray.write 0
    (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
    (currentLengthFreePtr len + ⟨0⟩).toNat 32
  let awStore :=
    UInt256.ofNat
      (MachineState.M (clearCurrentHashAw (setHelperEntryAw len)).toNat
        (currentLengthFreePtr len + ⟨0⟩).toNat 32)
  have hawStore :
      UInt256.ofNat
          (MachineState.M (clearCurrentHashAw (setHelperEntryAw len)).toNat
            (currentLengthFreePtr len + ⟨0⟩).toNat 32) =
        awStore := rfl
  have rd763 := evm_run rd738 with [
    jumpdest, dup3,
    raw mstore
      (Cₘ awStore - Cₘ (clearCurrentHashAw (setHelperEntryAw len)))
      returnMem awStore (by decide)
      (by
        intro s haw hstk
        simpa [awStore, returnMem, currentLength_add_zero_toNat] using
          (mstoreCostSpec (aw := clearCurrentHashAw (setHelperEntryAw len))
            (off := currentLengthFreePtr len + ⟨0⟩)
            (stk := [len, len, currentLengthFreePtr len + ⟨0⟩, ⟨763⟩,
              currentLengthFreePtr len + ⟨32⟩, currentLengthFreePtr len, len,
              ⟨106⟩, stringStoreLiteSelWord I]) s haw hstk))
      (by rfl)
      hawStore (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd106 := evm_run rd763 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  have hreturnRead64 :
      returnMem.readWithPadding 64 32 = UInt256.toByteArray (currentLengthFreePtr len) := by
    simpa [returnMem] using
      currentLengthReturnWrite_preserves_read64_zero
        (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
        (len := len) (freePtr := currentLengthFreePtr len) hfreeGe96 hfreeLeMem
        (by
          rw [clearCurrentBaseMemFrom_setPaddedMem_read64_u64
            I.calldata len payloadStart hnz hlenMax hsrc]
          exact setPaddedMem_read64 I.calldata len payloadStart hnz hsrc
            (setDataEnd_toNat_of_u64 hlenMax))
  have hreturnSize64 : 64 < returnMem.size := by
    have hge := writeWord_size_gt64_of_mem
      (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (off := (currentLengthFreePtr len + ⟨0⟩).toNat) (word := len)
      (by
        rw [clearCurrentBaseMemFrom_size_of_ge32]
        · have hsize := setPaddedMem_size I.calldata len payloadStart hnz hsrc
            (setDataEnd_toNat_of_u64 hlenMax)
          rw [hsize]
          omega
        · have hsize := setPaddedMem_size I.calldata len payloadStart hnz hsrc
            (setDataEnd_toNat_of_u64 hlenMax)
          rw [hsize]
          omega)
      (by simpa [currentLength_add_zero_toNat] using hfreeLeMem)
    simpa [returnMem] using hge
  have hawStoreNoWrap :
      awStore.toNat * 32 < UInt256.size := by
    simpa [awStore, hawEq, currentLength_add_zero_toNat] using
      setHelperEntryAw_mstoreFreePtr_mul32_lt_u64 (len := len) hnz hlenMax
  have hawStoreGe3 : 3 ≤ awStore.toNat := by
    simpa [awStore, hawEq, currentLength_add_zero_toNat] using
      setHelperEntryAw_mstoreFreePtr_ge3_u64 (len := len) hnz hlenMax
  have hfinalFreePtr :
      (if (⟨64⟩ : UInt256).toNat ≥ returnMem.size
          ∨ (⟨64⟩ : UInt256) ≥ awStore * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            (returnMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        currentLengthFreePtr len := by
    exact mloadWordValue_of_readWithPadding
      (mem := returnMem) (aw := awStore) (off := (⟨64⟩ : UInt256))
      (v := currentLengthFreePtr len)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnSize64)
      (wordMul32_not_le64_of_ge3 hawStoreGe3 hawStoreNoWrap)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hreturnRead64)
  let awFinal := UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32)
  have hawFinal :
      UInt256.ofNat (MachineState.M awStore.toNat (⟨64⟩ : UInt256).toNat 32) = awFinal := rfl
  have hretLen : (UInt256.sub (currentLengthFreePtr len + ⟨32⟩)
      (currentLengthFreePtr len)).toNat = 32 :=
    currentLengthFreePtr_retLen_of_len_lt_sign_pos (len := len) hlenLt
      (Nat.pos_of_ne_zero hnz)
  have hretBytes :
      returnMem.readWithPadding (currentLengthFreePtr len).toNat
        (UInt256.sub (currentLengthFreePtr len + ⟨32⟩) (currentLengthFreePtr len)).toNat =
        UInt256.toByteArray len := by
    simpa [returnMem] using
      currentLengthReturnWrite_retBytes
        (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
        (len := len) (freePtr := currentLengthFreePtr len) hfreeLeMem hretLen
  exact evm_run rd106 with [
    jumpdest, push1 ⟨64⟩,
    raw mload
      (Cₘ awFinal - Cₘ awStore)
      (currentLengthFreePtr len) awFinal (by decide)
      (by
        intro s haw hstk
        simpa [awFinal] using
          (mloadCostSpec (aw := awStore) (off := (⟨64⟩ : UInt256))
            (stk := [currentLengthFreePtr len + ⟨32⟩, stringStoreLiteSelWord I]) s haw hstk))
      hfinalFreePtr
      hawFinal (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret
      (Cₘ (UInt256.ofNat
        (MachineState.M awFinal.toNat (currentLengthFreePtr len).toNat
          (UInt256.sub (currentLengthFreePtr len + ⟨32⟩)
            (currentLengthFreePtr len)).toNat)) - Cₘ awFinal)
      (UInt256.toByteArray len) (by decide)
      (by
        intro s haw hstk
        simpa using
          (returnCostSpec
            (aw := awFinal) (off := currentLengthFreePtr len)
            (len := UInt256.sub (currentLengthFreePtr len + ⟨32⟩)
              (currentLengthFreePtr len))
            (stk := [stringStoreLiteSelWord I]) s haw hstk))
      hretBytes
      (by evm_ov)]

noncomputable def setShortReturnMemAfterClearBase
    (cd : ByteArray) (len payloadStart : UInt256) : ByteArray :=
  len.toByteArray.write 0
    (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)) 192 32

theorem setShortReturnMemAfterClearBase_mload64
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (setShortReturnMemAfterClearBase cd len payloadStart).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((setShortReturnMemAfterClearBase cd len payloadStart).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = currentLengthFreePtr len := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 7)
    (v := currentLengthFreePtr len)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        setShortReturnMemAfterClearBase]
      exact writeWord_size_gt64_of_mem
        (mem := clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart))
        (off := 192) (word := len)
        (by
          rw [clearCurrentBaseMemFrom_size_of_ge32]
          · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
              (setDataEnd_toNat_of_short hshort)
            rw [hsize]
            omega
          · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
              (setDataEnd_toNat_of_short hshort)
            rw [hsize]
            omega)
        (by
          rw [clearCurrentBaseMemFrom_size_of_ge32]
          · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
              (setDataEnd_toNat_of_short hshort)
            rw [hsize]
            omega
          · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
              (setDataEnd_toNat_of_short hshort)
            rw [hsize]
            omega))
    (by decide)
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
      rw [setShortReturnMemAfterClearBase]
      rw [write32_read_below (UInt256.toByteArray len)
        (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)) 192 64
        (by rw [toByteArray_size])
        (by
          rw [clearCurrentBaseMemFrom_size_of_ge32]
          · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
              (setDataEnd_toNat_of_short hshort)
            rw [hsize]
            omega
          · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
              (setDataEnd_toNat_of_short hshort)
            rw [hsize]
            omega)
        (by decide)]
      rw [clearCurrentBaseMemFrom_setPaddedMem_read64_short_nonzero
        cd len payloadStart hnz hshort hsrc]
      exact setPaddedMem_read64 cd len payloadStart hnz hsrc
        (setDataEnd_toNat_of_short hshort))

theorem setShortReturnMemAfterClearBase_read192
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size) :
    (setShortReturnMemAfterClearBase cd len payloadStart).readWithPadding 192 32 =
      UInt256.toByteArray len := by
  rw [setShortReturnMemAfterClearBase]
  rw [write32_read_back (UInt256.toByteArray len)
    (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)) 192
    (by rw [toByteArray_size])
    (by
      rw [clearCurrentBaseMemFrom_size_of_ge32]
      · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega
      · have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega)]
  rw [toByteArray_extract_all]

theorem clearCurrentBaseMemFrom_currentLengthZeroReturnMem_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ (clearCurrentBaseMemFrom currentLengthZeroReturnMem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clearCurrentBaseMemFrom currentLengthZeroReturnMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 6) (v := (⟨160⟩ : UInt256))
    (by
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        clearCurrentBaseMemFrom_currentLengthZeroReturnMem_size]
      decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      clearCurrentBaseMemFrom_currentLengthZeroReturnMem_read64)

theorem clearCurrentBaseMemFrom_currentLengthZeroReturnMem_mload128 :
    (if (⟨128⟩ : UInt256).toNat ≥ (clearCurrentBaseMemFrom currentLengthZeroReturnMem).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((clearCurrentBaseMemFrom currentLengthZeroReturnMem).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) = ⟨0⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨128⟩ : UInt256)) (aw := UInt256.ofNat 6) (v := (⟨0⟩ : UInt256))
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        clearCurrentBaseMemFrom_currentLengthZeroReturnMem_size]
      decide)
    (by decide)
    (by simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide] using
      clearCurrentBaseMemFrom_currentLengthZeroReturnMem_read128)

noncomputable def setEmptyReturnMemLong : ByteArray :=
  (⟨0⟩ : UInt256).toByteArray.write 0
    (clearCurrentBaseMemFrom currentLengthZeroReturnMem) 160 32

theorem setEmptyReturnMemLong_size : setEmptyReturnMemLong.size = 192 := by
  rw [setEmptyReturnMemLong]
  rw [write32_eq (UInt256.toByteArray ⟨0⟩)
    (clearCurrentBaseMemFrom currentLengthZeroReturnMem) 160
    (by rw [toByteArray_size])
    (by rw [clearCurrentBaseMemFrom_currentLengthZeroReturnMem_size]; decide)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    clearCurrentBaseMemFrom_currentLengthZeroReturnMem_size]
  omega

theorem setEmptyReturnMemLong_read64 :
    setEmptyReturnMemLong.readWithPadding 64 32 = UInt256.toByteArray ⟨160⟩ := by
  rw [setEmptyReturnMemLong]
  rw [write32_read_below (UInt256.toByteArray ⟨0⟩)
    (clearCurrentBaseMemFrom currentLengthZeroReturnMem) 160 64
    (by rw [toByteArray_size])
    (by rw [clearCurrentBaseMemFrom_currentLengthZeroReturnMem_size]; decide)
    (by decide)]
  exact clearCurrentBaseMemFrom_currentLengthZeroReturnMem_read64

theorem setEmptyReturnMemLong_read160 :
    setEmptyReturnMemLong.readWithPadding 160 32 = UInt256.toByteArray ⟨0⟩ := by
  rw [setEmptyReturnMemLong]
  rw [write32_read_back (UInt256.toByteArray ⟨0⟩)
    (clearCurrentBaseMemFrom currentLengthZeroReturnMem) 160
    (by rw [toByteArray_size])
    (by rw [clearCurrentBaseMemFrom_currentLengthZeroReturnMem_size]; decide)]
  rw [toByteArray_extract_all]

theorem setEmptyReturnMemLong_mload64 :
    (if (⟨64⟩ : UInt256).toNat ≥ setEmptyReturnMemLong.size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          (setEmptyReturnMemLong.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨160⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 6) (v := (⟨160⟩ : UInt256))
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, setEmptyReturnMemLong_size]; decide)
    (by decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      setEmptyReturnMemLong_read64)

theorem stringStoreLiteX_setClearDataWordsLoopDone {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx base count ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1164⟩
      (idx :: base :: count :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx count = ⟨0⟩)
    (hret : (D_J stringStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd1164⟩ := hreach
  have hcond : UInt256.isZero (UInt256.lt idx count) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have hovStack : (idx :: base :: count :: ret :: rest).length ≤ 1024 := by
    simp only [List.length_cons]
    omega
  have hlenBase : (base :: count :: ret :: rest).length = rest.length + 3 := by
    simp only [List.length_cons]
  have hlenCount : (count :: ret :: rest).length = rest.length + 2 := by
    simp only [List.length_cons]
  have hlenRet : (ret :: rest).length = rest.length + 1 := by
    simp only [List.length_cons]
  have hlenIdx : (idx :: base :: count :: ret :: rest).length = rest.length + 4 := by
    simp only [List.length_cons]
  have hlenCond :
      (UInt256.isZero (UInt256.lt idx count) :: idx :: base :: count :: ret :: rest).length =
        rest.length + 5 := by
    simp only [List.length_cons]
  have rd1165 := rd1164.jumpdest (by native_decide) hovStack
  have rd1166 := rd1165.dup3 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1167 := rd1166.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1168 := rd1167.lt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1169 := rd1168.iszero (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1172 := rd1169.push2 ⟨1195⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1195 := rd1172.jumpiT (by native_decide) hcond (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd1196 := rd1195.jumpdest (by native_decide) hovStack
  have rd1197 := rd1196.pop (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1198 := rd1197.pop (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1199 := rd1198.pop (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd1199.jump (by native_decide) hret (by omega)⟩

theorem stringStoreLiteX_setClearDataWordsLoopReachStoreHelper {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {idx base count ret : UInt256}
    {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1164⟩
      (idx :: base :: count :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.lt idx count) = ⟨0⟩)
    (hov : rest.length + 8 ≤ 1024) :
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1138⟩
      ((base + idx) :: ⟨0⟩ :: ⟨1184⟩ :: idx :: base :: count :: ret :: rest)
      mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd1164⟩ := hreach
  have hovStack : (idx :: base :: count :: ret :: rest).length ≤ 1024 := by
    simp only [List.length_cons]
    omega
  have rd1165 := rd1164.jumpdest (by native_decide) hovStack
  have rd1166 := rd1165.dup3 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1167 := rd1166.dup2 (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1168 := rd1167.lt (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1169 := rd1168.iszero (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1172 := rd1169.push2 ⟨1195⟩ (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd1173 := rd1172.jumpiNT (by native_decide) hcontinue
    (by simp only [List.length_cons]; omega)
  have rd1183 := evm_run rd1173 with [
    push2 ⟨1184⟩, push0, dup3, dup5, add, push2 ⟨1138⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [u256_add_comm idx base] using rd1183⟩

theorem stringStoreLiteX_setStoreHelperZero {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {slot idx base count ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1138⟩
      (slot :: ⟨0⟩ :: ⟨1184⟩ :: idx :: base :: count :: ret :: rest)
      mem aw rdata (cA, τ) k C)
    (hov : rest.length + 64 ≤ 1024) :
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1184⟩
      (idx :: base :: count :: ret :: rest) mem aw rdata
      (cA, sstoreAccountMap I.codeOwner τ slot ⟨0⟩) k C := by
  obtain ⟨_, _, rd1138⟩ := hreach
  have rd1118pre := evm_run rd1138 with [
    jumpdest, push2 ⟨1146⟩, push2 ⟨1131⟩, jump (by jump_dest),
    jumpdest, push0, push0, swap1, pop, swap1, jump (by jump_dest),
    jumpdest, push2 ⟨1157⟩, dup2, dup5, dup5, push2 ⟨1094⟩, jump (by jump_dest),
    jumpdest, push2 ⟨1103⟩, dup4, push2 ⟨1052⟩, jump (by jump_dest),
    jumpdest, push0, push2 ⟨1078⟩, push2 ⟨1073⟩, push2 ⟨1068⟩, dup5,
    push2 ⟨720⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨1043⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨720⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest),
    jumpdest, swap1, pop, swap2, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨1123⟩, push2 ⟨1115⟩, dup3, push2 ⟨1085⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest),
    jumpdest, dup5, dup5]
  obtain ⟨_, _, rd1119⟩ := rd1118pre.sload (by native_decide) (by evm_ov)
  have rd1009pre := evm_run rd1119 with [
    push2 ⟨962⟩, jump (by jump_dest),
    jumpdest, push0, push1 ⟨8⟩, dup4, mul, push2 ⟨1009⟩]
  have rd1009const := RD.pushConst rd1009pre
    ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩
    (width := 32) (op := Operation.POp.PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1019 := evm_run rd1009const with [
    dup3, push2 ⟨950⟩, jump (by jump_dest),
    jumpdest, push0, dup3, dup3, shl, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, push2 ⟨1019⟩, dup7, dup4, push2 ⟨950⟩, jump (by jump_dest),
    jumpdest, push0, dup3, dup3, shl, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest]
  have rd1021 := RD.swap6 rd1019 (by native_decide) (by evm_ov)
  have rd1123 := evm_run rd1021 with [
    pop, dup1, not, dup5, and, swap4, pop, dup1, dup7,
    and, dup5, lor, swap3, pop, pop, pop, swap4, swap3, pop, pop, pop,
    jump (by jump_dest),
    jumpdest, dup3]
  obtain ⟨_, _, rd1126₀⟩ := rd1123.sstore hperm (by native_decide) (by evm_ov)
  have hstored :
      (UInt256.lor
        (UInt256.land
          (Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage slot ⟨0⟩)
            (Batteries.RBMap.find? τ I.codeOwner))
          (UInt256.lnot
            (UInt256.shiftLeft
              ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩
              (UInt256.mul ⟨0⟩ ⟨8⟩))))
        (UInt256.land
          (UInt256.shiftLeft ⟨0⟩ (UInt256.mul ⟨0⟩ ⟨8⟩))
          (UInt256.shiftLeft
            ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩
            (UInt256.mul ⟨0⟩ ⟨8⟩)))) = ⟨0⟩ := by
    have hmaxShift :
        UInt256.shiftLeft
          ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩
          (UInt256.mul ⟨0⟩ ⟨8⟩) =
        ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩ := by
      native_decide
    have hzeroShift : UInt256.shiftLeft ⟨0⟩ (UInt256.mul ⟨0⟩ ⟨8⟩) = ⟨0⟩ := by
      native_decide
    have hnotMax :
        UInt256.lnot
          ⟨115792089237316195423570985008687907853269984665640564039457584007913129639935⟩ =
        ⟨0⟩ := by
      native_decide
    rw [hmaxShift, hzeroShift, hnotMax]
    simp [uint256_land_zero_left, uint256_land_zero_right, uint256_lor_zero_right]
  obtain ⟨_, _, rd1126⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1126⟩
        (⟨0⟩ :: slot :: ⟨0⟩ :: ⟨0⟩ :: ⟨1157⟩ :: ⟨0⟩ :: slot :: ⟨0⟩ ::
          ⟨1184⟩ :: idx :: base :: count :: ret :: rest)
        mem aw rdata (cA, sstoreAccountMap I.codeOwner τ slot ⟨0⟩) k C := by
    exact ⟨_, _, by
      simpa [initState, sstoreAccountMap, hstored] using rd1126₀⟩
  have rd1184 := evm_run rd1126 with [
    pop, pop, pop, pop, jump (by jump_dest),
    jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd1184⟩

theorem stringStoreLiteX_setClearDataWordsLoopStep {cA gh bl σinit σ₀ A I} {g : Sat256}
    {τ : AccountMap} {idx base count ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1164⟩
      (idx :: base :: count :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.lt idx count) = ⟨0⟩)
    (hov : rest.length + 64 ≤ 1024) :
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1164⟩
      (((⟨1⟩ : UInt256) + idx) :: base :: count :: ret :: rest) mem aw rdata
      (cA, sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩) k C := by
  have hhelper := stringStoreLiteX_setClearDataWordsLoopReachStoreHelper
    (g := g) hreach hcontinue (by omega)
  have hstored := stringStoreLiteX_setStoreHelperZero
    (g := g) (slot := base + idx) hperm hhelper (by omega)
  obtain ⟨_, _, rd1184⟩ := hstored
  have rd1164 := evm_run rd1184 with [
    jumpdest, push1 ⟨1⟩, dup2, add, swap1, pop, push2 ⟨1164⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [u256_add_comm idx ⟨1⟩] using rd1164⟩

theorem stringStoreLiteX_setClearDataWordsLoopGenerated {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {idx base count ret : UInt256}
    {rest : List UInt256} {mem rdata : ByteArray} {aw : UInt256} {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1164⟩
      (idx :: base :: count :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero (UInt256.lt (clearDataWordsLoopIndex idx i) count) = ⟨0⟩)
    (hdone : UInt256.lt (clearDataWordsLoopIndex idx fuel) count = ⟨0⟩)
    (hret : (D_J stringStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 64 ≤ 1024) :
    ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret rest mem aw rdata
      (cA, clearDataWordsForwardFrom I.codeOwner τ base idx fuel) k C := by
  induction fuel generalizing idx τ with
  | zero =>
      simpa [clearDataWordsLoopIndex, clearDataWordsForwardFrom] using
        stringStoreLiteX_setClearDataWordsLoopDone
          (σinit := σinit) (τ := τ) (idx := idx) (base := base) (count := count)
          (ret := ret) (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
          hreach hdone hret (by omega)
  | succ n ih =>
      have hstep := stringStoreLiteX_setClearDataWordsLoopStep
        (σinit := σinit) (τ := τ) (idx := idx) (base := base) (count := count)
        (ret := ret) (rest := rest) (mem := mem) (aw := aw) (rdata := rdata)
        hperm hreach
        (by simpa [clearDataWordsLoopIndex] using hcontinue 0 (Nat.zero_lt_succ n))
        hov
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.lt (clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i) count) =
              ⟨0⟩ := by
        intro i hi
        simpa [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have hdoneTail :
          UInt256.lt (clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) n) count =
            ⟨0⟩ := by
        simpa [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base] using hdone
      simpa [clearDataWordsForwardFrom] using
        ih
          (idx := (⟨1⟩ : UInt256) + idx)
          (τ := sstoreAccountMap I.codeOwner τ (base + idx) ⟨0⟩)
          hstep hcontinueTail hdoneTail

theorem stringStoreLiteX_setEmptyWriteZeroFrom1405 {cA gh bl σinit σ₀ A I}
    {g : Sat256} {τ : AccountMap} {payloadStart len : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [len, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
        payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem aw rdata (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ ⟨0⟩) k' C' := by
  have rd1436 := evm_run hreach with [
    jumpdest, push0, push1 ⟨32⟩, swap1, pop,
    push1 ⟨31⟩, dup4, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨1454⟩,
    jumpiNT (by decide),
    push0, dup5, iszero, push2 ⟨1436⟩, jumpiT (by decide) (by jump_dest)]
  have rd1323 := evm_run rd1436 with [
    jumpdest, push2 ⟨1446⟩, dup6, dup3, push2 ⟨1323⟩, jump (by jump_dest)]
  have rd1446 := evm_run rd1323 with [
    jumpdest, push0, push2 ⟨1334⟩, dup4, dup4, push2 ⟨1295⟩,
    jump (by jump_dest),
    jumpdest, push0, push2 ⟨1310⟩, push0, not, dup5, push1 ⟨8⟩, mul,
    push2 ⟨1283⟩, jump (by jump_dest),
    jumpdest, push0, dup3, dup3, shr, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, not, dup1, dup4, and, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, swap2, pop, dup3, push1 ⟨2⟩, mul, dup3, lor, swap1, pop,
    swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd1448pre := evm_run rd1446 with [jumpdest, dup7]
  obtain ⟨_, _, rd1449₀⟩ := rd1448pre.sstore hperm (by native_decide) (by evm_ov)
  have hpacked0 :
      ((⟨0⟩ : UInt256).land ((⟨0⟩ : UInt256).lnot.shiftRight ((⟨8⟩ : UInt256).mul ⟨0⟩)).lnot).lor
          ((⟨2⟩ : UInt256).mul ⟨0⟩) = ⟨0⟩ := by
    native_decide
  obtain ⟨_, _, rd1449⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1449⟩
        [⟨0⟩, UInt256.gt ⟨0⟩ ⟨31⟩, ⟨32⟩, len, ⟨0⟩, ⟨0⟩,
          ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩,
          stringStoreLiteSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩ ⟨0⟩) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState, hpacked0] using rd1449₀⟩
  exact ⟨_, _, evm_run rd1449 with [
    pop, push2 ⟨1549⟩, jump (by jump_dest),
    jumpdest, pop, pop, pop, pop, pop, pop, jump (by jump_dest)]⟩

theorem stringStoreLiteX_setWriteLongReachLoopFrom1405
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len oldLen : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C : Nat}
    (hlong : ¬ len.toNat < 32)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1470⟩
        [⟨0⟩, clearCurrentBaseWord, UInt256.land len (UInt256.lnot ⟨31⟩),
          UInt256.gt len ⟨31⟩, ⟨32⟩, oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom mem) (clearCurrentHashAw aw) rdata (cA, τ) k' C' := by
  have hgt31 : UInt256.gt len ⟨31⟩ = ⟨1⟩ := by
    apply ugt_one
    have hge32 : 32 ≤ len.toNat := Nat.le_of_not_gt hlong
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      (by omega : 31 < len.toNat)
  have rd1454 := evm_run hreach with [
    jumpdest, push0, push1 ⟨32⟩, swap1, pop,
    push1 ⟨31⟩, dup4, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨1454⟩,
    jumpiT
      (by
        rw [hgt31]
        decide)
      (by jump_dest)]
  have rd917 := evm_run rd1454 with [
    jumpdest, push1 ⟨31⟩, not, dup5, and, push2 ⟨1468⟩, dup7,
    push2 ⟨917⟩, jump (by jump_dest)]
  have rd923 := evm_run rd917 with [jumpdest, push0, dup2, swap1, pop, dup2, push0]
  have rd924 := RD.mstore
    (Cₘ (clearCurrentBaseAw aw) - Cₘ aw)
    (clearCurrentBaseMemFrom mem)
    (clearCurrentBaseAw aw)
    rd923 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, clearCurrentBaseAw])
    (by rfl) (by rfl) (by evm_ov)
  have rd928 := evm_run rd924 with [push1 ⟨32⟩, push0]
  have rd929 := RD.keccak256
    (Cₘ (clearCurrentHashAw aw) - Cₘ (clearCurrentBaseAw aw))
    clearCurrentBaseWord
    (clearCurrentHashAw aw)
    rd928 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        clearCurrentHashAw, clearCurrentBaseAw])
    (clearCurrentBaseMemFrom_keccak mem)
    (by rfl)
    (by evm_ov)
  have rd1468 := evm_run rd929 with [
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  exact ⟨_, _, by
    simpa [clearCurrentBaseWord_eq_solidityBytesDataBaseSlot] using
      (evm_run rd1468 with [jumpdest, push0])⟩

theorem byteArray_extract_toList (bytes : ByteArray) (start stop : Nat) :
    (bytes.extract start stop).toList =
      (bytes.toList.drop start).take (stop - start) := by
  rw [byteArray_toList_eq (bytes.extract start stop)]
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  rw [← byteArray_toList_eq bytes]

theorem byteArray_extract_toList_length_of_le {bytes : ByteArray} {start stop : Nat}
    (hle : stop ≤ bytes.size) :
    (bytes.extract start stop).toList.length = stop - start := by
  rw [byteArray_extract_toList]
  rw [List.length_take, List.length_drop]
  have hlen : bytes.toList.length = bytes.size := by
    rw [byteArray_toList_eq bytes, Array.length_toList]
    rw [ByteArray.size_data]
  rw [hlen]
  omega

theorem setDecodedValueBytes_full_chunk_length {I : ExecutionEnv} {len : UInt256} {i : Nat}
    (hsize : (setDecodedValueBytes I).size = len.toNat)
    (hi : i < len.toNat / 32) :
    (((setDecodedValueBytes I).toList.drop (32 * i)).take 32).length = 32 := by
  rw [List.length_take, List.length_drop]
  have hlist : (setDecodedValueBytes I).toList.length = (setDecodedValueBytes I).size := by
    rw [byteArray_toList_eq (setDecodedValueBytes I), Array.length_toList, ByteArray.size_data]
  rw [hlist, hsize]
  have hle : 32 * (i + 1) ≤ len.toNat := by
    have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
    have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) := Nat.mul_le_mul_left 32 hsucc
    have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    exact le_trans hmul hdiv
  omega

theorem setDecodedValueBytes_readWithPadding_full_word
    {I : ExecutionEnv} {len : UInt256} {i : Nat}
    (hsize : (setDecodedValueBytes I).size = len.toNat)
    (hi : i < len.toNat / 32) :
    uInt256OfByteArray ((setDecodedValueBytes I).readWithPadding (32 * i) 32) =
      UInt256.ofNat
        (fromBytesBigEndian (((setDecodedValueBytes I).toList.drop (32 * i)).take 32)) := by
  have hread : 32 * i + 32 ≤ (setDecodedValueBytes I).size := by
    rw [hsize]
    have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
    have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) := Nat.mul_le_mul_left 32 hsucc
    have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    have hle := le_trans hmul hdiv
    omega
  rw [uInt256OfByteArray_eq]
  unfold fromByteArrayBigEndian
  rw [readWithPadding_eq_extract _ (32 * i) hread]
  rw [byteArray_extract_toList]
  have hwidth : 32 * i + 32 - 32 * i = 32 := by omega
  simp [hwidth]

theorem readWithPadding_tail32_toList (b : ByteArray) {addr : Nat}
    (hsize32 : 32 ≤ b.size) (haddr : addr < b.size) (htail : b.size < addr + 32) :
    (b.readWithPadding addr 32).toList =
      b.toList.drop addr ++ List.replicate (32 - (b.toList.drop addr).length) 0 := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [if_neg (by omega : ¬ addr ≥ b.size)]
  rw [show min 32 b.size = 32 by omega]
  change
    (b.extract addr (addr + 32) ++
        ffi.ByteArray.zeroes (32 - (b.extract addr (addr + 32)).size)).toList =
      b.toList.drop addr ++ List.replicate (32 - (b.toList.drop addr).length) 0
  rw [byteArray_toList_eq (_ ++ _), ByteArray.data_append, Array.toList_append]
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]
  rw [← byteArray_toList_eq b]
  have hdropLen : (b.toList.drop addr).length = b.size - addr := by
    rw [List.length_drop]
    rw [byteArray_toList_eq b, Array.length_toList, ByteArray.size_data]
  have htake : (b.toList.drop addr).take (addr + 32 - addr) = b.toList.drop addr := by
    rw [show addr + 32 - addr = 32 by omega]
    exact List.take_of_length_le (by rw [hdropLen]; omega)
  rw [htake]
  have hreadSize : (b.extract addr (addr + 32)).size = b.size - addr := by
    rw [ByteArray.size_extract]
    omega
  rw [hreadSize, byteArray_zeroes_toList]
  rw [hdropLen]

theorem setDecodedValueBytes_readWithPadding_tail_word
    {I : ExecutionEnv} {len : UInt256}
    (hsize : (setDecodedValueBytes I).size = len.toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0) :
    uInt256OfByteArray
        ((setDecodedValueBytes I).readWithPadding (32 * (len.toNat / 32)) 32) =
      UInt256.ofNat
        (fromBytesBigEndian
          (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
            List.replicate
              (32 - ((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))).length)
              0)) := by
  have hsize32 : 32 ≤ (setDecodedValueBytes I).size := by
    rw [hsize]
    omega
  have haddr : 32 * (len.toNat / 32) < (setDecodedValueBytes I).size := by
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hrem : 0 < len.toNat % 32 := Nat.pos_of_ne_zero hmod
    omega
  have htail : (setDecodedValueBytes I).size < 32 * (len.toNat / 32) + 32 := by
    rw [hsize]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    omega
  rw [uInt256OfByteArray_eq]
  unfold fromByteArrayBigEndian
  rw [readWithPadding_tail32_toList (setDecodedValueBytes I) hsize32 haddr htail]

theorem list_drop_take_full_chunk_succ (xs : List UInt8) (i fuel : Nat) :
    (xs.drop (32 * i)).take (32 * (fuel + 1)) =
      (xs.drop (32 * i)).take 32 ++
        (xs.drop (32 * (i + 1))).take (32 * fuel) := by
  rw [show 32 * (fuel + 1) = 32 + 32 * fuel by omega]
  rw [List.take_add]
  rw [List.drop_drop]
  rw [show 32 * i + 32 = 32 * (i + 1) by omega]

theorem setDecodedValueBytes_tail_length {I : ExecutionEnv} {len : UInt256}
    (hsize : (setDecodedValueBytes I).size = len.toNat) :
    ((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))).length =
      len.toNat % 32 := by
  rw [List.length_drop]
  have hlist : (setDecodedValueBytes I).toList.length = len.toNat := by
    rw [byteArray_toList_eq (setDecodedValueBytes I), Array.length_toList,
      ByteArray.size_data, hsize]
  rw [hlist]
  have hdiv := Nat.div_add_mod len.toNat 32
  omega

theorem setDecodedValueBytes_split_full_tail {I : ExecutionEnv} {len : UInt256} :
    (setDecodedValueBytes I).toList =
      ((setDecodedValueBytes I).toList.take (32 * (len.toNat / 32))) ++
        ((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) := by
  rw [List.take_append_drop]

theorem stringStoreLiteX_setLongDataWordsLoopStep
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride oldLen len ptr ret payloadStart word aw awLoad : UInt256}
    {mem rdata : ByteArray} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1470⟩
      [idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : UInt256.isZero (UInt256.lt idx cutoff) = ⟨0⟩)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr + stride, idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + stride).toNat ≥ mem.size ∨ (ptr + stride) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding (ptr + stride).toNat 32))) = word)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32) = awLoad) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1470⟩
        [(⟨32⟩ : UInt256) + idx, (⟨1⟩ : UInt256) + slot, cutoff, gtFlag,
          (⟨32⟩ : UInt256) + stride, oldLen, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner τ slot word) k' C' := by
  obtain ⟨_, _, rd1470⟩ := hreach
  have rd1479 := evm_run rd1470 with [
    jumpdest, dup3, dup2, lt, iszero, push2 ⟨1507⟩,
    jumpiNT hcontinue]
  have rd1480 := RD.dup5 rd1479 (by native_decide) (by evm_ov)
  have rd1481 := RD.dup10 rd1480 (by native_decide) (by evm_ov)
  have rd1482pre := evm_run rd1481 with [add]
  have rd1483 := RD.mload mloadCost word awLoad rd1482pre
    (by native_decide) hmloadCost hmload hawLoad (by evm_ov)
  have rd1484pre := evm_run rd1483 with [dup3]
  obtain ⟨_, _, rd1485₀⟩ := rd1484pre.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1485⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1485⟩
        [idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner τ slot word) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd1485₀⟩
  have rd1495pre := evm_run rd1485 with [
    push1 ⟨1⟩, dup3, add, swap2, pop,
    push1 ⟨32⟩, dup6, add]
  have rd1496 := RD.swap5 rd1495pre (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [u256_add_comm slot ⟨1⟩, u256_add_comm stride ⟨32⟩,
      u256_add_comm idx ⟨32⟩] using
      (evm_run rd1496 with [
        pop, push1 ⟨32⟩, dup2, add, swap1, pop,
        push2 ⟨1470⟩, jump (by jump_dest)])⟩

def longDataWordsLoopIndex (idx : UInt256) : Nat → UInt256
  | 0 => idx
  | n + 1 => (⟨32⟩ : UInt256) + longDataWordsLoopIndex idx n

def longDataWordsLoopSlot (slot : UInt256) : Nat → UInt256
  | 0 => slot
  | n + 1 => (⟨1⟩ : UInt256) + longDataWordsLoopSlot slot n

def longDataWordsLoopStride (stride : UInt256) : Nat → UInt256
  | 0 => stride
  | n + 1 => (⟨32⟩ : UInt256) + longDataWordsLoopStride stride n

def longDataWordsLoopAw (aw ptr stride : UInt256) : Nat → UInt256
  | 0 => aw
  | n + 1 =>
      UInt256.ofNat
        (MachineState.M
          (longDataWordsLoopAw aw ptr stride n).toNat
          (ptr + longDataWordsLoopStride stride n).toNat 32)

def longDataWordsLoopWord (mem : ByteArray) (aw ptr stride : UInt256) (n : Nat) :
    UInt256 :=
  if (ptr + longDataWordsLoopStride stride n).toNat ≥ mem.size ∨
      (ptr + longDataWordsLoopStride stride n) ≥
        longDataWordsLoopAw aw ptr stride n * ⟨32⟩ then
    ⟨0⟩
  else
    UInt256.ofNat (fromByteArrayBigEndian
      (mem.readWithPadding (ptr + longDataWordsLoopStride stride n).toNat 32))

def longDataWordsForwardFrom (owner : AccountAddress) (τ : AccountMap)
    (slot stride ptr aw : UInt256) (mem : ByteArray) : Nat → AccountMap
  | 0 => τ
  | n + 1 =>
      longDataWordsForwardFrom owner
        (sstoreAccountMap owner τ slot (longDataWordsLoopWord mem aw ptr stride 0))
        ((⟨1⟩ : UInt256) + slot) ((⟨32⟩ : UInt256) + stride) ptr
        (UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32)) mem n

theorem longDataWordsForwardFrom_absent_same {owner : AccountAddress} {τ : AccountMap}
    {slot stride ptr aw : UInt256} {mem : ByteArray} :
    ∀ fuel, τ.find? owner = none →
      longDataWordsForwardFrom owner τ slot stride ptr aw mem fuel = τ
  | 0, _hmissing => rfl
  | fuel + 1, hmissing => by
      simp [longDataWordsForwardFrom, sstoreAccountMap_absent_same hmissing]
      exact longDataWordsForwardFrom_absent_same (owner := owner) (τ := τ)
        (slot := (⟨1⟩ : UInt256) + slot) (stride := (⟨32⟩ : UInt256) + stride)
        (ptr := ptr) (aw := UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        (mem := mem) fuel hmissing

theorem accountMapEquiv_longDataWordsForwardFrom
    {owner : AccountAddress} {σ τ : AccountMap}
    {slot stride ptr aw : UInt256} {mem : ByteArray} :
    ∀ fuel, accountMapEquiv σ τ →
      accountMapEquiv
        (longDataWordsForwardFrom owner σ slot stride ptr aw mem fuel)
        (longDataWordsForwardFrom owner τ slot stride ptr aw mem fuel)
  | 0, hAccounts => hAccounts
  | fuel + 1, hAccounts => by
      simp [longDataWordsForwardFrom]
      exact accountMapEquiv_longDataWordsForwardFrom fuel
        (accountMapEquiv_sstoreAccountMap owner slot
          (longDataWordsLoopWord mem aw ptr stride 0) hAccounts)

theorem u256_add_assoc (a b c : UInt256) : (a + b) + c = a + (b + c) := by
  apply u256_inj
  repeat rw [uadd_toNat]
  have ha : a.toNat % UInt256.size = a.toNat := Nat.mod_eq_of_lt a.val.isLt
  have hc : c.toNat % UInt256.size = c.toNat := Nat.mod_eq_of_lt c.val.isLt
  conv_lhs => rw [← hc]
  rw [← Nat.add_mod (a.toNat + b.toNat) c.toNat UInt256.size]
  conv_rhs => rw [← ha]
  rw [← Nat.add_mod a.toNat (b.toNat + c.toNat) UInt256.size]
  rw [Nat.add_assoc]

theorem u256_32_add_ofNat (n : Nat) :
    (⟨32⟩ : UInt256) + UInt256.ofNat n = UInt256.ofNat (n + 32) := by
  apply u256_inj
  rw [uadd_toNat]
  change (32 + (Fin.ofNat UInt256.size n).val) % UInt256.size =
    (Fin.ofNat UInt256.size (n + 32)).val
  rw [Fin.val_ofNat, Fin.val_ofNat]
  have h32 : 32 % UInt256.size = 32 := by norm_num [UInt256.size]
  rw [← h32, ← Nat.add_mod]
  congr 1
  omega

theorem u256_base_one_add_ofNat (base : UInt256) (i : Nat) :
    (⟨1⟩ : UInt256) + (base + UInt256.ofNat i) =
      base + UInt256.ofNat (i + 1) := by
  rw [u256_add_comm (⟨1⟩ : UInt256) (base + UInt256.ofNat i)]
  rw [u256_add_assoc]
  rw [u256_add_comm (UInt256.ofNat i) (⟨1⟩ : UInt256)]
  rw [u256_one_add_ofNat]

theorem u256_add_left_cancel (a b c : UInt256) (h : a + b = a + c) : b = c := by
  cases a with
  | mk av =>
      cases b with
      | mk bv =>
          cases c with
          | mk cv =>
              simp [HAdd.hAdd, Add.add, UInt256.add] at h ⊢
              exact add_left_cancel h

theorem u256_base_ofNat_ne_of_ne {base : UInt256} {i j : Nat}
    (hi : i < UInt256.size) (hj : j < UInt256.size) (hne : i ≠ j) :
    base + UInt256.ofNat i ≠ base + UInt256.ofNat j := by
  intro h
  have hij : UInt256.ofNat i = UInt256.ofNat j := u256_add_left_cancel base _ _ h
  have hnat := congrArg UInt256.toNat hij
  rw [ulit_toNat' i hi, ulit_toNat' j hj] at hnat
  exact hne hnat

theorem currentDataSlot_ofNat_ne {i j : Nat}
    (hi : i < 2 ^ 251) (hj : j < 2 ^ 251) (hne : i ≠ j) :
    bytesLikeDataBase ⟨0⟩ + UInt256.ofNat i ≠
      bytesLikeDataBase ⟨0⟩ + UInt256.ofNat j := by
  apply u256_base_ofNat_ne_of_ne
  · exact lt_trans hi (by norm_num [UInt256.size])
  · exact lt_trans hj (by norm_num [UInt256.size])
  · exact hne

theorem clearDataWordsLoopIndex_ofNat (i : Nat) :
    ∀ j, clearDataWordsLoopIndex (UInt256.ofNat i) j = UInt256.ofNat (i + j)
  | 0 => by simp [clearDataWordsLoopIndex]
  | j + 1 => by
      simp [clearDataWordsLoopIndex, clearDataWordsLoopIndex_ofNat i j,
        u256_one_add_ofNat]
      congr 1

theorem u256_stride32_succ_ofNat (i : Nat) :
    (⟨32⟩ : UInt256) + UInt256.ofNat (32 * (i + 1)) =
      UInt256.ofNat (32 * (i + 2)) := by
  rw [u256_32_add_ofNat]
  congr 1

theorem longDataWordsLoopIndex_zero_ofNat :
    ∀ i, longDataWordsLoopIndex ⟨0⟩ i = UInt256.ofNat (32 * i)
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopIndex, longDataWordsLoopIndex_zero_ofNat i,
        u256_32_add_ofNat]
      congr 1

theorem longDataWordsLoopStride_32_ofNat :
    ∀ i, longDataWordsLoopStride ⟨32⟩ i = UInt256.ofNat (32 * (i + 1))
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopStride, longDataWordsLoopStride_32_ofNat i,
        u256_32_add_ofNat]
      congr 1

theorem longDataWordsLoopSlot_clearBase :
    ∀ i, longDataWordsLoopSlot clearCurrentBaseWord i =
      clearCurrentBaseWord + UInt256.ofNat i
  | 0 => by
      rw [longDataWordsLoopSlot]
      change clearCurrentBaseWord = clearCurrentBaseWord + (⟨0⟩ : UInt256)
      rw [uint256_add_zero_right]
  | i + 1 => by
      rw [longDataWordsLoopSlot, longDataWordsLoopSlot_clearBase i]
      rw [u256_add_comm (⟨1⟩ : UInt256) (clearCurrentBaseWord + UInt256.ofNat i)]
      rw [u256_add_assoc]
      rw [u256_add_comm (UInt256.ofNat i) (⟨1⟩ : UInt256)]
      rw [u256_one_add_ofNat]

theorem setHelperEntryAw_covers_payload_u64 {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    160 + len.toNat + 32 ≤ (setHelperEntryAw len).toNat * 32 := by
  let copyWords := MachineState.M (UInt256.ofNat 5).toNat 160 len.toNat
  have hcopyNoWrap : copyWords * 32 < UInt256.size := by
    dsimp [copyWords]
    apply set_machineState_M_mul32_lt_of_bounds
    · change 5 * 32 < UInt256.size
      norm_num [UInt256.size]
    · have hmax : 160 + ABI.solcMaxU64 + 31 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      omega
  have hcopySize : copyWords < UInt256.size := by
    have hle : copyWords ≤ copyWords * 32 := by
      simpa using Nat.mul_le_mul_left copyWords (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt hle hcopyNoWrap
  have hcopyToNat : (UInt256.ofNat copyWords).toNat = copyWords :=
    ulit_toNat' copyWords hcopySize
  have hentryNoWrap :
      MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 * 32 <
        UInt256.size := by
    apply set_machineState_M_mul32_lt_of_bounds
    · exact hcopyNoWrap
    · rw [setDataEnd_toNat_of_u64 hlenMax]
      have hmax : 160 + ABI.solcMaxU64 + 32 + 31 < UInt256.size := by
        norm_num [ABI.solcMaxU64, UInt256.size]
      omega
  have hentrySize :
      MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 <
        UInt256.size := by
    have hle :
        MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 ≤
          MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32 * 32 := by
      simpa using Nat.mul_le_mul_left
        (MachineState.M copyWords (((⟨160⟩ : UInt256) + len).toNat) 32)
        (by decide : 1 ≤ 32)
    exact lt_of_le_of_lt hle hentryNoWrap
  dsimp [setHelperEntryAw]
  change 160 + len.toNat + 32 ≤
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat copyWords).toNat (((⟨160⟩ : UInt256) + len).toNat)
        32)).toNat * 32
  rw [hcopyToNat, ulit_toNat' _ hentrySize]
  rw [setDataEnd_toNat_of_u64 hlenMax]
  simp only [MachineState.M]
  have hceil : 160 + len.toNat + 32 ≤ ((160 + len.toNat + 32 + 31) / 32) * 32 := by
    have hmod := Nat.mod_lt (160 + len.toNat + 32 + 31) (by decide : 0 < 32)
    have hdiv := Nat.div_add_mod (160 + len.toNat + 32 + 31) 32
    nlinarith
  exact le_trans hceil (Nat.mul_le_mul_right 32 (Nat.le_max_right _ _))

theorem longDataWordsLoopReadAddr_toNat {len : UInt256} {i : Nat}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hi : i < len.toNat / 32) :
    ((⟨128⟩ : UInt256) + longDataWordsLoopStride ⟨32⟩ i).toNat =
      160 + 32 * i := by
  rw [longDataWordsLoopStride_32_ofNat]
  rw [uadd_toNat]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
  have hstrideLt : 32 * (i + 1) < UInt256.size := by
    have hle : 32 * (i + 1) ≤ len.toNat := by
      have hlt : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) := Nat.mul_le_mul_left 32 hlt
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      exact le_trans hmul hdiv
    exact lt_of_le_of_lt hle len.val.isLt
  rw [ulit_toNat' _ hstrideLt]
  have hsumLt : 128 + 32 * (i + 1) < UInt256.size := by
    have hle : 32 * (i + 1) ≤ len.toNat := by
      have hlt : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) := Nat.mul_le_mul_left 32 hlt
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      exact le_trans hmul hdiv
    have hmax : 128 + ABI.solcMaxU64 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  rw [Nat.mod_eq_of_lt hsumLt]
  omega

theorem longDataWordsLoopReadAddr_tail_toNat {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (_hmod : len.toNat % 32 ≠ 0) :
    ((⟨128⟩ : UInt256) + UInt256.ofNat (32 * (len.toNat / 32 + 1))).toNat =
      160 + 32 * (len.toNat / 32) := by
  rw [uadd_toNat]
  rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
  have hstrideLt : 32 * (len.toNat / 32 + 1) < UInt256.size := by
    have hdiv := Nat.div_add_mod len.toNat 32
    have hmax : ABI.solcMaxU64 + 32 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  rw [ulit_toNat' _ hstrideLt]
  have hsumLt : 128 + 32 * (len.toNat / 32 + 1) < UInt256.size := by
    have hdiv := Nat.div_add_mod len.toNat 32
    have hmax : 128 + ABI.solcMaxU64 + 32 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  rw [Nat.mod_eq_of_lt hsumLt]
  omega

theorem longDataWordsLoopAw_setHelper_eq {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    ∀ i, i ≤ len.toNat / 32 →
      longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i =
        clearCurrentHashAw (setHelperEntryAw len)
  | 0, _ => rfl
  | i + 1, hi => by
      have hiPrev : i ≤ len.toNat / 32 := by omega
      have hiRead : i < len.toNat / 32 := by omega
      have hprev := longDataWordsLoopAw_setHelper_eq hlenMax i hiPrev
      simp [longDataWordsLoopAw, hprev]
      have hentryGe : 1 ≤ (setHelperEntryAw len).toNat := by
        have hge := setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
        omega
      have hawEq : clearCurrentHashAw (setHelperEntryAw len) = setHelperEntryAw len :=
        clearCurrentHashAw_eq_self_of_ge1 hentryGe
      have haddr := longDataWordsLoopReadAddr_toNat (len := len) (i := i) hlenMax hiRead
      have hcover := setHelperEntryAw_covers_payload_u64 (len := len) hlenMax
      have hM : MachineState.M (clearCurrentHashAw (setHelperEntryAw len)).toNat
          ((⟨128⟩ : UInt256) + longDataWordsLoopStride ⟨32⟩ i).toNat 32 =
          (clearCurrentHashAw (setHelperEntryAw len)).toNat := by
        rw [hawEq, haddr]
        simp only [MachineState.M]
        apply max_eq_left
        rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
        omega
      rw [hM]
      exact u256_ofNat_toNat (clearCurrentHashAw (setHelperEntryAw len))

theorem longDataWordsLoopWord_setHelper_payload_word
    (cd : ByteArray) (len payloadStart : UInt256) (i : Nat)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (hi : i < len.toNat / 32) :
    longDataWordsLoopWord
      (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart))
      (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i =
        UInt256.ofNat (fromByteArrayBigEndian
          ((cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).extract
            (32 * i) (32 * i + 32))) := by
  unfold longDataWordsLoopWord
  have haddr := longDataWordsLoopReadAddr_toNat (len := len) (i := i) hlenMax hi
  have haw := longDataWordsLoopAw_setHelper_eq (len := len) hlenMax i (Nat.le_of_lt hi)
  have hcover := setHelperEntryAw_covers_payload_u64 (len := len) hlenMax
  have hsizeMem :
      (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).size =
        (setPaddedMem cd len payloadStart).size := by
    rw [clearCurrentBaseMemFrom_size_of_ge32]
    have hsize := setPaddedMem_size cd len payloadStart hnz hsrc
      (setDataEnd_toNat_of_u64 hlenMax)
    rw [hsize]
    omega
  have hsizePadded :
      (setPaddedMem cd len payloadStart).size = 192 + len.toNat :=
    setPaddedMem_size cd len payloadStart hnz hsrc (setDataEnd_toNat_of_u64 hlenMax)
  have hnotSize : ¬((⟨128⟩ : UInt256) + longDataWordsLoopStride ⟨32⟩ i).toNat ≥
      (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).size := by
    rw [haddr, hsizeMem, hsizePadded]
    have hle : 32 * (i + 1) ≤ len.toNat := by
      have hlt : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) := Nat.mul_le_mul_left 32 hlt
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      exact le_trans hmul hdiv
    omega
  have hnotAw : ¬((⟨128⟩ : UInt256) + longDataWordsLoopStride ⟨32⟩ i) ≥
      longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i *
        ⟨32⟩ := by
    intro hge
    have haddrLt : ((⟨128⟩ : UInt256) + longDataWordsLoopStride ⟨32⟩ i).toNat <
        (longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i *
          ⟨32⟩).toNat := by
      rw [haddr, haw]
      have hentryGe : 1 ≤ (setHelperEntryAw len).toNat := by
        have hge := setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
        omega
      have hawEq : clearCurrentHashAw (setHelperEntryAw len) = setHelperEntryAw len :=
        clearCurrentHashAw_eq_self_of_ge1 hentryGe
      rw [hawEq]
      rw [umul_toNat (a := setHelperEntryAw len) (b := (⟨32⟩ : UInt256))
        (setHelperEntryAw_mul32_lt_of_u64 hlenMax)]
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      have hleLen : 32 * i ≤ len.toNat := by
        have hlt : i ≤ len.toNat / 32 := Nat.le_of_lt hi
        have hmul : 32 * i ≤ 32 * (len.toNat / 32) := Nat.mul_le_mul_left 32 hlt
        have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
          simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
        exact le_trans hmul hdiv
      omega
    have hgeNat :
        ((⟨128⟩ : UInt256) + longDataWordsLoopStride ⟨32⟩ i).toNat ≥
          (longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i *
            ⟨32⟩).toNat := hge
    exact not_lt_of_ge hgeNat haddrLt
  rw [if_neg]
  · rw [haddr]
    rw [clearCurrentBaseMemFrom_setPaddedMem_read_payload_word
      cd len payloadStart i hnz hlenMax hsrc hi]
  · exact not_or.mpr ⟨hnotSize, hnotAw⟩

theorem longDataWordsLoopWord_setHelper_decoded_word {I : ExecutionEnv}
    {len payloadStart : UInt256} {i : Nat}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hi : i < len.toNat / 32)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    longDataWordsLoopWord
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i =
        UInt256.ofNat (fromByteArrayBigEndian
          ((setDecodedValueBytes I).extract (32 * i) (32 * i + 32))) := by
  rw [longDataWordsLoopWord_setHelper_payload_word I.calldata len payloadStart i
    hnz hlenMax hsrc hi]
  rw [setDecodedValueBytes_eq_extract (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax]

theorem longDataWordsLoopWord_setHelper_decoded_list_word {I : ExecutionEnv}
    {len payloadStart : UInt256} {i : Nat}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hi : i < len.toNat / 32)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    longDataWordsLoopWord
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i =
        UInt256.ofNat (fromBytesBigEndian
          (((setDecodedValueBytes I).toList.drop (32 * i)).take 32)) := by
  rw [longDataWordsLoopWord_setHelper_decoded_word
    (I := I) (len := len) (payloadStart := payloadStart) (i := i)
    hnz hlenMax hsrc hi hlenAbi hpayloadStart hoffMax]
  unfold fromByteArrayBigEndian
  rw [byteArray_extract_toList]
  simp

theorem longDataWordsLoopWord_setHelper_decoded_list_word_at {I : ExecutionEnv}
    {len payloadStart : UInt256} {i : Nat}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hi : i < len.toNat / 32)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    longDataWordsLoopWord
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩
      (UInt256.ofNat (32 * (i + 1))) 0 =
        UInt256.ofNat (fromBytesBigEndian
          (((setDecodedValueBytes I).toList.drop (32 * i)).take 32)) := by
  have h := longDataWordsLoopWord_setHelper_decoded_list_word
    (I := I) (len := len) (payloadStart := payloadStart) (i := i)
    hnz hlenMax hsrc hi hlenAbi hpayloadStart hoffMax
  simpa [longDataWordsLoopWord, longDataWordsLoopStride, longDataWordsLoopStride_32_ofNat,
    longDataWordsLoopAw_setHelper_eq (len := len) hlenMax i (Nat.le_of_lt hi)] using h

theorem accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_full
    {I : ExecutionEnv} {len payloadStart : UInt256} {owner : AccountAddress}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hsize : (setDecodedValueBytes I).size = len.toNat)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    ∀ {τ : AccountMap} {i fuel : Nat},
      i + fuel ≤ len.toNat / 32 →
      accountMapEquiv
        (solidityDataWordsForwardFrom owner τ ⟨0⟩ (setDecodedValueBytes I) i fuel)
        (longDataWordsForwardFrom owner τ (clearCurrentBaseWord + UInt256.ofNat i)
          (UInt256.ofNat (32 * (i + 1))) ⟨128⟩
          (clearCurrentHashAw (setHelperEntryAw len))
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)) fuel)
  | τ, i, 0, _hfuel => by
      simp [solidityDataWordsForwardFrom, longDataWordsForwardFrom, accountMapEquiv_refl]
  | τ, i, fuel + 1, hfuel => by
      have hi : i < len.toNat / 32 := by omega
      have htailFuel : i + 1 + fuel ≤ len.toNat / 32 := by omega
      have hwordDirect :
          uInt256OfByteArray ((setDecodedValueBytes I).readWithPadding (i * 32) 32) =
            UInt256.ofNat
              (fromBytesBigEndian (((setDecodedValueBytes I).toList.drop (32 * i)).take 32)) := by
        simpa [Nat.mul_comm] using
          setDecodedValueBytes_readWithPadding_full_word
            (I := I) (len := len) (i := i) hsize hi
      have hwordLoop :
          longDataWordsLoopWord
            (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
            (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩
            (UInt256.ofNat (32 * (i + 1))) 0 =
              UInt256.ofNat
                (fromBytesBigEndian (((setDecodedValueBytes I).toList.drop (32 * i)).take 32)) := by
        exact longDataWordsLoopWord_setHelper_decoded_list_word_at
          (I := I) (len := len) (payloadStart := payloadStart) (i := i)
          hnz hlenMax hsrc hi hlenAbi hpayloadStart hoffMax
      have hword :
          uInt256OfByteArray ((setDecodedValueBytes I).readWithPadding (i * 32) 32) =
            longDataWordsLoopWord
              (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
              (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩
              (UInt256.ofNat (32 * (i + 1))) 0 := by
        rw [hwordDirect, hwordLoop]
      have hawStep :
          UInt256.ofNat
            (MachineState.M (clearCurrentHashAw (setHelperEntryAw len)).toNat
              (⟨128⟩ + UInt256.ofNat (32 * (i + 1))).toNat 32) =
            clearCurrentHashAw (setHelperEntryAw len) := by
        have hcur := longDataWordsLoopAw_setHelper_eq (len := len) hlenMax i (Nat.le_of_lt hi)
        have hiNext : i + 1 ≤ len.toNat / 32 := by omega
        have hnext := longDataWordsLoopAw_setHelper_eq (len := len) hlenMax (i + 1) hiNext
        simpa [longDataWordsLoopAw, hcur, longDataWordsLoopStride_32_ofNat] using hnext
      have ih := accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_full
        (I := I) (len := len) (payloadStart := payloadStart) (owner := owner)
        hnz hlenMax hsrc hsize hlenAbi hpayloadStart hoffMax
        (τ := sstoreAccountMap owner τ
          (clearCurrentBaseWord + UInt256.ofNat i)
          (longDataWordsLoopWord
            (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
            (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩
            (UInt256.ofNat (32 * (i + 1))) 0))
        (i := i + 1) (fuel := fuel) htailFuel
      simpa [solidityDataWordsForwardFrom, longDataWordsForwardFrom, hword,
        longDataWordsLoopSlot, longDataWordsLoopSlot_clearBase,
        clearCurrentBaseWord_eq_solidityBytesDataBaseSlot,
        solidityBytesDataSlot, u256_base_one_add_ofNat, u256_stride32_succ_ofNat,
        hawStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem clearCurrentBaseMemFrom_setPaddedMem_read_payload_tail_toList
    (cd : ByteArray) (len payloadStart : UInt256)
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ cd.size)
    (_hmod : len.toNat % 32 ≠ 0) :
    ((clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding
        (160 + 32 * (len.toNat / 32)) 32).toList =
      ((cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).toList.drop
          (32 * (len.toNat / 32))) ++
        List.replicate
          (32 - ((cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).toList.drop
            (32 * (len.toNat / 32))).length) 0 := by
  let q := len.toNat / 32
  let payload := cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)
  have hbaseSize :
      (setCalldataMem cd len payloadStart).size = 160 + len.toNat :=
    setCalldataMem_size cd len payloadStart hnz hsrc
  have hpaddedSize :
      (setPaddedMem cd len payloadStart).size = 192 + len.toNat :=
    setPaddedMem_size cd len payloadStart hnz hsrc (setDataEnd_toNat_of_u64 hlenMax)
  have hclearRead :
      (clearCurrentBaseMemFrom (setPaddedMem cd len payloadStart)).readWithPadding
          (160 + 32 * q) 32 =
        (setPaddedMem cd len payloadStart).readWithPadding (160 + 32 * q) 32 := by
    rw [clearCurrentBaseMemFrom]
    rw [write32_read_above (UInt256.toByteArray ⟨0⟩) (setPaddedMem cd len payloadStart)
      0 (160 + 32 * q)
      (by rw [toByteArray_size])
      (by
        rw [hpaddedSize]
        omega)
      (by omega)
      (by
        rw [hpaddedSize]
        have hdiv := Nat.div_add_mod len.toNat 32
        omega)]
  have hspan :
      (setPaddedMem cd len payloadStart).readWithPadding (160 + 32 * q) 32 =
        (setCalldataMem cd len payloadStart).extract (160 + 32 * q) (160 + len.toNat) ++
          (UInt256.toByteArray (⟨0⟩ : UInt256)).extract 0
            (160 + 32 * q + 32 - (160 + len.toNat)) := by
    rw [setPaddedMem]
    simpa [q, hbaseSize, setDataEnd_toNat_of_u64 hlenMax] using
      write32_read_span_end (UInt256.toByteArray (⟨0⟩ : UInt256))
        (setCalldataMem cd len payloadStart) (160 + 32 * q)
        (by rw [toByteArray_size])
        (by
          rw [hbaseSize]
          have hdiv := Nat.div_add_mod len.toNat 32
          omega)
        (by
          rw [hbaseSize]
          have hdiv := Nat.div_add_mod len.toNat 32
          omega)
  rw [hclearRead, hspan]
  have hpayloadExtract :
      (setCalldataMem cd len payloadStart).extract (160 + 32 * q) (160 + len.toNat) =
        payload.extract (32 * q) len.toNat := by
    dsimp [payload]
    rw [← setCalldataMem_extract_payload cd len payloadStart hnz hsrc]
    rw [extract_extract_BA]
    simp [q]
  rw [hpayloadExtract]
  rw [byteArray_toList_eq (_ ++ _), ByteArray.data_append, Array.toList_append]
  rw [← byteArray_toList_eq (payload.extract (32 * q) len.toNat)]
  conv_lhs =>
    rw [byteArray_extract_toList]
  have hpayloadLen : payload.toList.length = len.toNat := by
    dsimp [payload]
    rw [byteArray_toList_eq, Array.length_toList, ByteArray.size_data,
      ByteArray.size_extract]
    omega
  have htailTake :
      (payload.toList.drop (32 * q)).take (len.toNat - 32 * q) =
        payload.toList.drop (32 * q) := by
    apply List.take_of_length_le
    rw [List.length_drop, hpayloadLen]
  rw [htailTake]
  rw [zero_toByteArray_eq_zeroes32]
  rw [zeroes32_extract_zeroes (160 + 32 * q + 32 - (160 + len.toNat)) (by
    have hdiv := Nat.div_add_mod len.toNat 32
    omega)]
  rw [byteArray_zeroes_toList]
  dsimp [payload]
  simp only [q]
  congr 1
  have hpayloadLen' :
      (cd.extract payloadStart.toNat (payloadStart.toNat + len.toNat)).toList.length =
        len.toNat := by
    simpa [payload] using hpayloadLen
  congr 1
  rw [List.length_drop]
  rw [hpayloadLen']
  have hdiv := Nat.div_add_mod len.toNat 32
  omega

theorem longDataWordsLoopWord_setHelper_decoded_tail_word {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hmod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    longDataWordsLoopWord
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩
      (UInt256.ofNat (32 * (len.toNat / 32 + 1))) 0 =
        UInt256.ofNat (fromBytesBigEndian
          (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
            List.replicate
              (32 - ((setDecodedValueBytes I).toList.drop
                (32 * (len.toNat / 32))).length) 0)) := by
  unfold longDataWordsLoopWord
  have haddr := longDataWordsLoopReadAddr_tail_toNat (len := len) hlenMax hmod
  have haw := longDataWordsLoopAw_setHelper_eq (len := len) hlenMax
    (len.toNat / 32) (by omega)
  have hcover := setHelperEntryAw_covers_payload_u64 (len := len) hlenMax
  have hsizeMem :
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).size =
        (setPaddedMem I.calldata len payloadStart).size := by
    rw [clearCurrentBaseMemFrom_size_of_ge32]
    have hsize := setPaddedMem_size I.calldata len payloadStart hnz hsrc
      (setDataEnd_toNat_of_u64 hlenMax)
    rw [hsize]
    omega
  have hsizePadded :
      (setPaddedMem I.calldata len payloadStart).size = 192 + len.toNat :=
    setPaddedMem_size I.calldata len payloadStart hnz hsrc (setDataEnd_toNat_of_u64 hlenMax)
  have hnotSize :
      ¬((⟨128⟩ : UInt256) + UInt256.ofNat (32 * (len.toNat / 32 + 1))).toNat ≥
        (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).size := by
    rw [haddr, hsizeMem, hsizePadded]
    have hdiv := Nat.div_add_mod len.toNat 32
    omega
  have hnotAw :
      ¬((⟨128⟩ : UInt256) + UInt256.ofNat (32 * (len.toNat / 32 + 1))) ≥
        longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩
          (UInt256.ofNat (32 * (len.toNat / 32 + 1))) 0 * ⟨32⟩ := by
    intro hge
    have haddrLt :
        ((⟨128⟩ : UInt256) + UInt256.ofNat (32 * (len.toNat / 32 + 1))).toNat <
          (longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩
            (UInt256.ofNat (32 * (len.toNat / 32 + 1))) 0 * ⟨32⟩).toNat := by
      rw [haddr]
      simp [longDataWordsLoopAw]
      have hentryGe : 1 ≤ (setHelperEntryAw len).toNat := by
        have hge := setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
        omega
      have hawEq : clearCurrentHashAw (setHelperEntryAw len) = setHelperEntryAw len :=
        clearCurrentHashAw_eq_self_of_ge1 hentryGe
      rw [hawEq]
      rw [umul_toNat (a := setHelperEntryAw len) (b := (⟨32⟩ : UInt256))
        (setHelperEntryAw_mul32_lt_of_u64 hlenMax)]
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      have htailCover : 160 + 32 * (len.toNat / 32) <
          (setHelperEntryAw len).toNat * 32 := by
        have hdiv := Nat.div_add_mod len.toNat 32
        omega
      exact htailCover
    have hgeNat :
        ((⟨128⟩ : UInt256) + UInt256.ofNat (32 * (len.toNat / 32 + 1))).toNat ≥
          (longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩
            (UInt256.ofNat (32 * (len.toNat / 32 + 1))) 0 * ⟨32⟩).toNat := hge
    exact not_lt_of_ge hgeNat haddrLt
  simp [longDataWordsLoopStride] at hnotSize hnotAw ⊢
  rw [if_neg (not_or.mpr ⟨not_le_of_gt hnotSize, hnotAw⟩)]
  rw [haddr]
  unfold fromByteArrayBigEndian
  apply congrArg UInt256.ofNat
  rw [clearCurrentBaseMemFrom_setPaddedMem_read_payload_tail_toList
    I.calldata len payloadStart hnz hlenMax hsrc hmod]
  rw [setDecodedValueBytes_eq_extract (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax]
  rw [List.length_drop]

theorem longDataWordsLoopMload_setHelper_decoded_tail_word {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hmod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    (if (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat ≥
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).size ∨
        (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) ≥
          longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩
            (len.toNat / 32) * ⟨32⟩ then
        ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
      ((clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).readWithPadding
        (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat 32))) =
      UInt256.ofNat (fromBytesBigEndian
        (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length) 0)) := by
  have hcur := longDataWordsLoopAw_setHelper_eq (len := len) hlenMax
    (len.toNat / 32) (by omega)
  rw [hcur]
  change longDataWordsLoopWord
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩
      (longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) 0 =
      UInt256.ofNat (fromBytesBigEndian
        (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((setDecodedValueBytes I).toList.drop
              (32 * (len.toNat / 32))).length) 0))
  simpa [longDataWordsLoopStride_32_ofNat] using
    longDataWordsLoopWord_setHelper_decoded_tail_word
      (I := I) (len := len) (payloadStart := payloadStart)
      hnz hlenMax hsrc hmod hlenAbi hpayloadStart hoffMax

theorem longDataWordsLoopMloadCost_setHelper_zero
    {I : ExecutionEnv} {len oldLen payloadStart : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    ∀ i, i < len.toNat / 32 → ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw
        (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + longDataWordsLoopStride ⟨32⟩ i, longDataWordsLoopIndex ⟨0⟩ i,
          longDataWordsLoopSlot clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          longDataWordsLoopStride ⟨32⟩ i, oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = 0 := by
  intro i hi s haw hstk
  rw [set_mloadCostSpec
    (aw := longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ i)
    (off := (⟨128⟩ : UInt256) + longDataWordsLoopStride ⟨32⟩ i) s haw hstk]
  have hcur := longDataWordsLoopAw_setHelper_eq (len := len) hlenMax i (Nat.le_of_lt hi)
  have hnext := longDataWordsLoopAw_setHelper_eq (len := len) hlenMax (i + 1)
    (Nat.succ_le_of_lt hi)
  simp [longDataWordsLoopAw, hcur] at hnext
  rw [hcur, hnext]
  simp

theorem longDataWordsLoopAw_setHelper_tail_mload_eq
    {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hmod : len.toNat % 32 ≠ 0) :
    UInt256.ofNat
      (MachineState.M
        (longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len))
          ⟨128⟩ ⟨32⟩ (len.toNat / 32)).toNat
        (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat 32) =
      clearCurrentHashAw (setHelperEntryAw len) := by
  have hcur := longDataWordsLoopAw_setHelper_eq (len := len) hlenMax
    (len.toNat / 32) (by omega)
  rw [hcur]
  have hentryGe : 1 ≤ (setHelperEntryAw len).toNat := by
    have hge := setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
    omega
  have hawEq : clearCurrentHashAw (setHelperEntryAw len) = setHelperEntryAw len :=
    clearCurrentHashAw_eq_self_of_ge1 hentryGe
  have haddr := longDataWordsLoopReadAddr_tail_toNat (len := len) hlenMax hmod
  have hcover := setHelperEntryAw_covers_payload_u64 (len := len) hlenMax
  have hM : MachineState.M (clearCurrentHashAw (setHelperEntryAw len)).toNat
      ((⟨128⟩ : UInt256) + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat 32 =
      (clearCurrentHashAw (setHelperEntryAw len)).toNat := by
    rw [hawEq]
    rw [show longDataWordsLoopStride ⟨32⟩ (len.toNat / 32) =
        UInt256.ofNat (32 * (len.toNat / 32 + 1)) by
      exact longDataWordsLoopStride_32_ofNat (len.toNat / 32)]
    rw [haddr]
    simp only [MachineState.M]
    apply max_eq_left
    rw [Nat.div_le_iff_le_mul (by decide : 0 < 32)]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hremLt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    omega
  rw [hM]
  exact u256_ofNat_toNat (clearCurrentHashAw (setHelperEntryAw len))

theorem longDataWordsLoopTailMloadCost_setHelper_zero
    {I : ExecutionEnv} {len oldLen payloadStart : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hmod : len.toNat % 32 ≠ 0) :
    ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw
        (clearCurrentHashAw (setHelperEntryAw len)) ⟨128⟩ ⟨32⟩ (len.toNat / 32) →
      s.machineState.stack =
        [⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32),
          longDataWordsLoopIndex ⟨0⟩ (len.toNat / 32),
          longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32),
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          longDataWordsLoopStride ⟨32⟩ (len.toNat / 32), oldLen, len, ⟨0⟩, ⟨128⟩,
          ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩,
          stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = 0 := by
  intro s haw hstk
  rw [set_mloadCostSpec
    (aw := longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len))
      ⟨128⟩ ⟨32⟩ (len.toNat / 32))
    (off := (⟨128⟩ : UInt256) + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32))
    s haw hstk]
  have hcur := longDataWordsLoopAw_setHelper_eq (len := len) hlenMax
    (len.toNat / 32) (by omega)
  rw [longDataWordsLoopAw_setHelper_tail_mload_eq
    (len := len) hlenMax hmod, hcur]
  simp

theorem solidityBytesHeaderWord_eq_len_mul_two_add_one
    {len : UInt256} {n : Nat}
    (hsize : n = len.toNat)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    solidityBytesHeaderWord n = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
  subst n
  rw [solidityBytesHeaderWord, if_neg hlong]
  apply u256_inj
  rw [uadd_toNat]
  rw [umul_toNat (a := len) (b := (⟨2⟩ : UInt256)) (by
    have hmax : ABI.solcMaxU64 * 2 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    have htwo : (⟨2⟩ : UInt256).toNat = 2 := by decide
    rw [htwo]
    omega)]
  rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide]
  rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
  have hwordLt : len.toNat * 2 + 1 < UInt256.size := by
    have hmax : ABI.solcMaxU64 * 2 + 1 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  rw [Nat.mod_eq_of_lt hwordLt]
  rw [ulit_toNat' (len.toNat * 2 + 1) hwordLt]

theorem u256_lnot_31_toNat :
    (UInt256.lnot (⟨31⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 5 := by
  native_decide

theorem nat_land_31_eq_mod_32 (n : Nat) :
    Nat.land n 31 = n % 32 := by
  have hmask : Nat.land n (2 ^ 5 - 1) = n % 2 ^ 5 := by
    apply Nat.eq_of_testBit_eq
    intro i
    show (n &&& (2 ^ 5 - 1)).testBit i = (n % 2 ^ 5).testBit i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    by_cases hi : i < 5
    · rw [decide_eq_true hi]
      simp
    · rw [decide_eq_false hi]
      simp
  simpa using hmask

theorem u256_land_31_toNat (len : UInt256) :
    (UInt256.land len ⟨31⟩).toNat = len.toNat % 32 := by
  rw [u256_land_toNat]
  rw [show (⟨31⟩ : UInt256).toNat = 31 from by decide]
  rw [nat_land_31_eq_mod_32]
  exact Nat.mod_eq_of_lt (by
    have hlt := Nat.mod_lt len.toNat (by decide : 0 < 32)
    norm_num [UInt256.size] at hlt ⊢
    omega)

theorem nat_land_high_mask5_eq_div_mul {n : Nat} (hn : n < 2 ^ 256) :
    Nat.land n (2 ^ 256 - 2 ^ 5) = (n / 32) * 32 := by
  have h32 : (32 : Nat) = 2 ^ 5 := by norm_num
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& (2 ^ 256 - 2 ^ 5)).testBit i = ((n / 32) * 32).testBit i
  rw [Nat.testBit_and]
  rw [show (n / 32) * 32 = (n / 2 ^ 5) <<< 5 by
    rw [h32, Nat.shiftLeft_eq]]
  rw [nat_testBit_shiftLeft]
  by_cases hi5 : i < 5
  · have hmask : (2 ^ 256 - 2 ^ 5).testBit i = false := by
      rw [show (2 : Nat) ^ 256 - 2 ^ 5 = (2 ^ (256 - 5) - 1) <<< 5 by
        rw [Nat.shiftLeft_eq]
        rw [Nat.sub_mul]
        simp]
      rw [nat_testBit_shiftLeft]
      simp [hi5]
    rw [hmask]
    simp [hi5]
  · have h5i : 5 ≤ i := Nat.le_of_not_gt hi5
    by_cases hi256 : i < 256
    · have hmask :
          (2 ^ 256 - 2 ^ 5).testBit i = true := by
        rw [show (2 : Nat) ^ 256 - 2 ^ 5 = (2 ^ (256 - 5) - 1) <<< 5 by
          rw [Nat.shiftLeft_eq]
          rw [Nat.sub_mul]
          simp]
        rw [nat_testBit_shiftLeft]
        simp [hi5]
        change (2 ^ (256 - 5) - 1).testBit (i - 5) = true
        rw [Nat.testBit_two_pow_sub_one]
        simp [show i - 5 < 256 - 5 by omega]
      rw [hmask]
      simp [hi5]
      simpa [h32] using (nat_div_pow_testBit n 5 i h5i).symm
    · have hmask :
          (2 ^ 256 - 2 ^ 5).testBit i = false := by
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by
          have hpos : 0 < 2 ^ 5 := by norm_num
          omega) (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_gt hi256)))
      have hnbit : n.testBit i = false := by
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hn
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_gt hi256)))
      have hdivbit : (n / 2 ^ 5).testBit (i - 5) = false := by
        rw [nat_div_pow_testBit n 5 i h5i, hnbit]
      rw [hmask, hdivbit]
      simp [hi5]

theorem longDataCutoff_toNat (len : UInt256) :
    (UInt256.land len (UInt256.lnot ⟨31⟩)).toNat = (len.toNat / 32) * 32 := by
  rw [u256_land_toNat, u256_lnot_31_toNat]
  have hlenLt : len.toNat < 2 ^ 256 := by
    change len.toNat < UInt256.size
    exact len.val.isLt
  have hland := nat_land_high_mask5_eq_div_mul (n := len.toNat) hlenLt
  rw [hland]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_mul_le_self len.toNat 32) len.val.isLt)

theorem longDataLoopContinue (len : UInt256) {i : Nat}
    (hi : i < len.toNat / 32) :
    UInt256.isZero
      (UInt256.lt (longDataWordsLoopIndex ⟨0⟩ i)
        (UInt256.land len (UInt256.lnot ⟨31⟩))) = ⟨0⟩ := by
  have hidxLt : 32 * i < UInt256.size := by
    have hle : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    have hlt : 32 * i < 32 * (len.toNat / 32) := by nlinarith
    exact lt_of_lt_of_le hlt (le_trans hle (Nat.le_of_lt len.val.isLt))
  have hidxNat : (longDataWordsLoopIndex ⟨0⟩ i).toNat = 32 * i := by
    rw [longDataWordsLoopIndex_zero_ofNat]
    exact ulit_toNat' _ hidxLt
  have hltWord :
      UInt256.lt (longDataWordsLoopIndex ⟨0⟩ i)
        (UInt256.land len (UInt256.lnot ⟨31⟩)) = ⟨1⟩ := by
    apply ult_one
    rw [hidxNat, longDataCutoff_toNat]
    nlinarith
  rw [hltWord]
  decide

theorem longDataLoopDone (len : UInt256) :
    UInt256.lt (longDataWordsLoopIndex ⟨0⟩ (len.toNat / 32))
      (UInt256.land len (UInt256.lnot ⟨31⟩)) = ⟨0⟩ := by
  have hidxLt : 32 * (len.toNat / 32) < UInt256.size := by
    have hle : 32 * (len.toNat / 32) ≤ len.toNat := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
    exact lt_of_le_of_lt hle len.val.isLt
  have hidxNat :
      (longDataWordsLoopIndex ⟨0⟩ (len.toNat / 32)).toNat =
        32 * (len.toNat / 32) := by
    rw [longDataWordsLoopIndex_zero_ofNat]
    exact ulit_toNat' _ hidxLt
  apply ult_zero
  rw [hidxNat, longDataCutoff_toNat]
  exact Nat.le_of_eq (Nat.mul_comm _ _)

theorem longDataNoTail (len : UInt256) (hmod : len.toNat % 32 = 0) :
    UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len = ⟨0⟩ := by
  apply ult_zero
  rw [longDataCutoff_toNat]
  have hdiv := Nat.div_add_mod len.toNat 32
  omega

theorem longDataTail (len : UInt256) (hmod : len.toNat % 32 ≠ 0) :
    UInt256.isZero (UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len) = ⟨0⟩ := by
  have hltWord : UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len = ⟨1⟩ := by
    apply ult_one
    rw [longDataCutoff_toNat]
    have hdiv := Nat.div_add_mod len.toNat 32
    have hmodPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero hmod
    omega
  rw [hltWord]
  decide

theorem longDataWordsLoopIndex_succ_base (idx : UInt256) :
    ∀ i, longDataWordsLoopIndex ((⟨32⟩ : UInt256) + idx) i =
      (⟨32⟩ : UInt256) + longDataWordsLoopIndex idx i
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopIndex, longDataWordsLoopIndex_succ_base idx i]

theorem longDataWordsLoopSlot_succ_base (slot : UInt256) :
    ∀ i, longDataWordsLoopSlot ((⟨1⟩ : UInt256) + slot) i =
      (⟨1⟩ : UInt256) + longDataWordsLoopSlot slot i
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopSlot, longDataWordsLoopSlot_succ_base slot i]

theorem longDataWordsLoopStride_succ_base (stride : UInt256) :
    ∀ i, longDataWordsLoopStride ((⟨32⟩ : UInt256) + stride) i =
      (⟨32⟩ : UInt256) + longDataWordsLoopStride stride i
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopStride, longDataWordsLoopStride_succ_base stride i]

theorem longDataWordsLoopAw_succ_base (aw ptr stride : UInt256) :
    ∀ i, longDataWordsLoopAw
        (UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        ptr ((⟨32⟩ : UInt256) + stride) i =
      longDataWordsLoopAw aw ptr stride (i + 1)
  | 0 => rfl
  | i + 1 => by
      simp [longDataWordsLoopAw, longDataWordsLoopAw_succ_base aw ptr stride i,
        longDataWordsLoopStride, longDataWordsLoopStride_succ_base]

theorem longDataWordsLoopWord_succ_base (mem : ByteArray) (aw ptr stride : UInt256) :
    ∀ i, longDataWordsLoopWord mem
        (UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        ptr ((⟨32⟩ : UInt256) + stride) i =
      longDataWordsLoopWord mem aw ptr stride (i + 1)
  | 0 => by
      simp [longDataWordsLoopWord, longDataWordsLoopAw, longDataWordsLoopStride]
  | i + 1 => by
      simp [longDataWordsLoopWord, longDataWordsLoopAw_succ_base,
        longDataWordsLoopStride, longDataWordsLoopStride_succ_base]

theorem stringStoreLiteX_setLongDataWordsLoopGenerated
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride oldLen len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray} {fuel : Nat} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1470⟩
      [idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hmloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw aw ptr stride i →
      s.machineState.stack =
        [ptr + longDataWordsLoopStride stride i, longDataWordsLoopIndex idx i,
          longDataWordsLoopSlot slot i, cutoff, gtFlag, longDataWordsLoopStride stride i,
          oldLen, len, ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
          ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1470⟩
        [longDataWordsLoopIndex idx fuel, longDataWordsLoopSlot slot fuel, cutoff,
          gtFlag, longDataWordsLoopStride stride fuel, oldLen, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem (longDataWordsLoopAw aw ptr stride fuel) rdata
        (cA, longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel) k' C' := by
  induction fuel generalizing idx slot stride aw τ with
  | zero =>
      simpa [longDataWordsLoopIndex, longDataWordsLoopSlot, longDataWordsLoopStride,
        longDataWordsLoopAw, longDataWordsForwardFrom] using hreach
  | succ n ih =>
      have hstep := stringStoreLiteX_setLongDataWordsLoopStep
        (σinit := σinit) (τ := τ) (idx := idx) (slot := slot) (cutoff := cutoff)
        (gtFlag := gtFlag) (stride := stride) (oldLen := oldLen) (len := len)
        (ptr := ptr) (ret := ret) (payloadStart := payloadStart)
        (word := longDataWordsLoopWord mem aw ptr stride 0)
        (aw := aw)
        (awLoad := UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        (mem := mem) (rdata := rdata) (mloadCost := mloadCost)
        hperm hreach
        (by simpa [longDataWordsLoopIndex] using hcontinue 0 (Nat.zero_lt_succ n))
        (by
          intro s haw hstk
          simpa [longDataWordsLoopIndex, longDataWordsLoopSlot,
            longDataWordsLoopStride, longDataWordsLoopAw] using
            hmloadCost 0 (Nat.zero_lt_succ n) s haw hstk)
        (by simp [longDataWordsLoopWord, longDataWordsLoopStride, longDataWordsLoopAw])
        rfl
      have hcontinueTail : ∀ i, i < n →
          UInt256.isZero
            (UInt256.lt (longDataWordsLoopIndex ((⟨32⟩ : UInt256) + idx) i) cutoff) =
              ⟨0⟩ := by
        intro i hi
        simpa [longDataWordsLoopIndex, longDataWordsLoopIndex_succ_base] using
          hcontinue (i + 1) (Nat.succ_lt_succ hi)
      have hmloadCostTail : ∀ i, i < n → ∀ s : State,
          s.machineState.activeWords =
            longDataWordsLoopAw
              (UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
              ptr ((⟨32⟩ : UInt256) + stride) i →
          s.machineState.stack =
            [ptr + longDataWordsLoopStride ((⟨32⟩ : UInt256) + stride) i,
              longDataWordsLoopIndex ((⟨32⟩ : UInt256) + idx) i,
              longDataWordsLoopSlot ((⟨1⟩ : UInt256) + slot) i, cutoff, gtFlag,
              longDataWordsLoopStride ((⟨32⟩ : UInt256) + stride) i, oldLen, len,
              ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩,
              stringStoreLiteSelWord I] →
          memoryExpansionCost s .MLOAD = mloadCost := by
        intro i hi s haw hstk
        have haw' :
            s.machineState.activeWords = longDataWordsLoopAw aw ptr stride (i + 1) := by
          simpa [longDataWordsLoopAw_succ_base] using haw
        have hstk' :
            s.machineState.stack =
              [ptr + longDataWordsLoopStride stride (i + 1),
                longDataWordsLoopIndex idx (i + 1),
                longDataWordsLoopSlot slot (i + 1), cutoff, gtFlag,
                longDataWordsLoopStride stride (i + 1), oldLen, len, ⟨0⟩, ptr,
                ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩,
                stringStoreLiteSelWord I] := by
          simpa [longDataWordsLoopIndex, longDataWordsLoopIndex_succ_base,
            longDataWordsLoopSlot_succ_base, longDataWordsLoopStride_succ_base,
            longDataWordsLoopStride] using hstk
        exact hmloadCost (i + 1) (Nat.succ_lt_succ hi) s haw' hstk'
      have htail := ih
        (idx := (⟨32⟩ : UInt256) + idx)
        (slot := (⟨1⟩ : UInt256) + slot)
        (stride := (⟨32⟩ : UInt256) + stride)
        (aw := UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32))
        (τ := sstoreAccountMap I.codeOwner τ slot (longDataWordsLoopWord mem aw ptr stride 0))
        hstep hcontinueTail hmloadCostTail
      simpa [longDataWordsForwardFrom, longDataWordsLoopIndex, longDataWordsLoopSlot,
        longDataWordsLoopStride, longDataWordsLoopAw, longDataWordsLoopIndex_succ_base,
        longDataWordsLoopSlot_succ_base, longDataWordsLoopStride_succ_base,
        longDataWordsLoopAw_succ_base, longDataWordsLoopWord_succ_base] using htail

theorem stringStoreLiteX_setLongDataWordsLoopDoneNoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride oldLen len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1470⟩
      [idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (hnoTail : UInt256.lt cutoff len = ⟨0⟩)
    (hret : (D_J stringStoreLiteBytecode 0).contains ret = true) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩
          (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  obtain ⟨_, _, rd1470⟩ := hreach
  have hdoneCond : UInt256.isZero (UInt256.lt idx cutoff) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have htailCond : UInt256.isZero (UInt256.lt cutoff len) ≠ ⟨0⟩ := by
    rw [hnoTail]
    decide
  have rd1507 := evm_run rd1470 with [
    jumpdest, dup3, dup2, lt, iszero, push2 ⟨1507⟩,
    jumpiT hdoneCond (by jump_dest)]
  have rd1536 := evm_run rd1507 with [
    jumpdest, dup7, dup4, lt, iszero, push2 ⟨1536⟩,
    jumpiT htailCond (by jump_dest)]
  have rd1542pre := evm_run rd1536 with [jumpdest, push1 ⟨1⟩, push1 ⟨2⟩]
  have rd1543 := RD.dup9 rd1542pre (by native_decide) (by evm_ov)
  have rd1545pre₀ := evm_run rd1543 with [mul, add]
  have rd1545pre := RD.dup9 rd1545pre₀ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1546₀⟩ := rd1545pre.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1546⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1546⟩
        [idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem aw rdata
        (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩
          (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd1546₀⟩
  have rd1556 := evm_run rd1546 with [
    pop, pop, pop,
    jumpdest, pop, pop, pop, pop, pop, pop]
  exact ⟨_, _, rd1556.jump (by native_decide) hret (by evm_ov)⟩

def longDataTailMaskedWord (word len : UInt256) : UInt256 :=
  UInt256.land word
    (UInt256.lnot
      (UInt256.shiftRight (UInt256.lnot ⟨0⟩)
        (UInt256.mul ⟨8⟩ (UInt256.land len ⟨31⟩))))

theorem longDataTailMaskedWord_padded {len word : UInt256} {bytes : List UInt8}
    (hbytesLen : bytes.length = len.toNat % 32)
    (hword :
      word = UInt256.ofNat
        (fromBytesBigEndian (bytes ++ List.replicate (32 - bytes.length) 0))) :
    longDataTailMaskedWord word len = word := by
  let remWord := UInt256.land len ⟨31⟩
  have hremNat : remWord.toNat = bytes.length := by
    dsimp [remWord]
    rw [u256_land_31_toNat, hbytesLen]
  have hremLt : remWord.toNat < 32 := by
    rw [hremNat]
    rw [hbytesLen]
    exact Nat.mod_lt _ (by decide : 0 < 32)
  have hmask := setShortPackedHeader_mask_of_short (len := remWord) hremLt
  have hwordZero :
      word.toNat % 2 ^ (256 - 8 * bytes.length) = 0 := by
    subst word
    have hbe :
        fromBytesBigEndian (bytes ++ List.replicate (32 - bytes.length) 0) =
          fromBytesBigEndian bytes * 2 ^ (8 * (32 - bytes.length)) := by
      exact fromBytesBigEndian_append_zeros bytes (32 - bytes.length)
    have hlt :
        fromBytesBigEndian (bytes ++ List.replicate (32 - bytes.length) 0) <
          UInt256.size := by
      unfold fromBytesBigEndian Function.comp
      have hbound := EVM.fromBytes'_le
        (bs := (bytes ++ List.replicate (32 - bytes.length) (0 : UInt8)).reverse)
      rw [List.length_reverse, List.length_append, List.length_replicate] at hbound
      have hlen32 : bytes.length + (32 - bytes.length) = 32 := by
        rw [hbytesLen]
        have hlt := Nat.mod_lt len.toNat (by decide : 0 < 32)
        omega
      simpa [hlen32, UInt256.size] using hbound
    rw [ulit_toNat' _ hlt, hbe]
    have hpowEq : 8 * (32 - bytes.length) = 256 - 8 * bytes.length := by
      have hle : bytes.length ≤ 32 := by
        rw [hbytesLen]
        exact Nat.le_of_lt (Nat.mod_lt _ (by decide : 0 < 32))
      omega
    rw [← hpowEq]
    rw [Nat.mul_comm]
    exact Nat.mul_mod_right (2 ^ (8 * (32 - bytes.length))) (fromBytesBigEndian bytes)
  unfold longDataTailMaskedWord
  rw [show UInt256.land len ⟨31⟩ = remWord from rfl]
  rw [hmask]
  rw [hremNat]
  exact u256_land_high_mask_eq_self word (by omega) hwordZero

theorem accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_tail
    {I : ExecutionEnv} {len payloadStart wordTail : UInt256} {owner : AccountAddress}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hsize : (setDecodedValueBytes I).size = len.toNat)
    (hlong : ¬ len.toNat < 32)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hmod : len.toNat % 32 ≠ 0)
    (hwordTail :
      wordTail = UInt256.ofNat (fromBytesBigEndian
        (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))).length)
            0)))
    (τ : AccountMap) :
    accountMapEquiv
      (solidityDataWordsForwardFrom owner τ ⟨0⟩ (setDecodedValueBytes I) 0
        (len.toNat / 32 + 1))
      (sstoreAccountMap owner
        (longDataWordsForwardFrom owner τ clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (clearCurrentHashAw (setHelperEntryAw len))
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
          (len.toNat / 32))
        (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
        (longDataTailMaskedWord wordTail len)) := by
  let fullFuel := len.toNat / 32
  have hfull := accountMapEquiv_solidityDataWordsForwardFrom_longDataWordsForwardFrom_full
    (I := I) (len := len) (payloadStart := payloadStart) (owner := owner)
    hnz hlenMax hsrc hsize hlenAbi hpayloadStart hoffMax
    (τ := τ) (i := 0) (fuel := fullFuel) (by omega)
  have hfullTarget :
      accountMapEquiv
        (solidityDataWordsForwardFrom owner τ ⟨0⟩ (setDecodedValueBytes I) 0 fullFuel)
        (longDataWordsForwardFrom owner τ clearCurrentBaseWord ⟨32⟩ ⟨128⟩
          (clearCurrentHashAw (setHelperEntryAw len))
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
          fullFuel) := by
    have hbase0 : clearCurrentBaseWord + UInt256.ofNat 0 = clearCurrentBaseWord := by
      simpa using uint256_add_zero_right clearCurrentBaseWord
    have hstride : UInt256.ofNat 32 = (⟨32⟩ : UInt256) := by native_decide
    simpa [fullFuel, hbase0, hstride] using hfull
  have htailWord :
      uInt256OfByteArray ((setDecodedValueBytes I).readWithPadding (fullFuel * 32) 32) =
        wordTail := by
    dsimp [fullFuel]
    rw [Nat.mul_comm]
    exact (setDecodedValueBytes_readWithPadding_tail_word
      (I := I) (len := len) hsize hlong hmod).trans hwordTail.symm
  have htailLen :
      ((setDecodedValueBytes I).toList.drop (32 * fullFuel)).length = len.toNat % 32 := by
    dsimp [fullFuel]
    exact setDecodedValueBytes_tail_length (I := I) (len := len) hsize
  have hmask :
      longDataTailMaskedWord wordTail len = wordTail := by
    exact longDataTailMaskedWord_padded (len := len) (word := wordTail)
      (bytes := (setDecodedValueBytes I).toList.drop (32 * fullFuel))
      htailLen hwordTail
  have hslotEq :
      longDataWordsLoopSlot clearCurrentBaseWord fullFuel =
        solidityBytesDataSlot ⟨0⟩ fullFuel := by
    rw [longDataWordsLoopSlot_clearBase]
    simp [clearCurrentBaseWord_eq_solidityBytesDataBaseSlot, solidityBytesDataSlot,
      solidityBytesDataBaseSlot]
  have hcong :=
    accountMapEquiv_sstoreAccountMap owner
      (solidityBytesDataSlot ⟨0⟩ fullFuel) wordTail hfullTarget
  have hsplit :
      solidityDataWordsForwardFrom owner τ ⟨0⟩ (setDecodedValueBytes I) 0
          (fullFuel + 1) =
        sstoreAccountMap owner
          (solidityDataWordsForwardFrom owner τ ⟨0⟩ (setDecodedValueBytes I) 0 fullFuel)
          (solidityBytesDataSlot ⟨0⟩ fullFuel) wordTail := by
    have happ := solidityDataWordsForwardFrom_append owner τ ⟨0⟩
      (setDecodedValueBytes I) 0 fullFuel 1
    rw [happ]
    simp [solidityDataWordsForwardFrom, htailWord]
  rw [hsplit]
  rw [hmask, hslotEq]
  exact hcong

theorem stringStoreLiteX_setLongDataWordsLoopDoneTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride oldLen len ptr ret payloadStart word aw awLoad : UInt256}
    {mem rdata : ByteArray} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1470⟩
      [idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hdone : UInt256.lt idx cutoff = ⟨0⟩)
    (htail : UInt256.isZero (UInt256.lt cutoff len) = ⟨0⟩)
    (hmloadCost : ∀ s : State, s.machineState.activeWords = aw →
      s.machineState.stack =
        [ptr + stride, idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr,
          ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩,
          stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + stride).toNat ≥ mem.size ∨ (ptr + stride) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding (ptr + stride).toNat 32))) = word)
    (hawLoad : UInt256.ofNat (MachineState.M aw.toNat (ptr + stride).toNat 32) = awLoad)
    (hret : (D_J stringStoreLiteBytecode 0).contains ret = true) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner τ slot (longDataTailMaskedWord word len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  obtain ⟨_, _, rd1470⟩ := hreach
  have hdoneCond : UInt256.isZero (UInt256.lt idx cutoff) ≠ ⟨0⟩ := by
    rw [hdone]
    decide
  have rd1507 := evm_run rd1470 with [
    jumpdest, dup3, dup2, lt, iszero, push2 ⟨1507⟩,
    jumpiT hdoneCond (by jump_dest)]
  have rd1516 := evm_run rd1507 with [
    jumpdest, dup7, dup4, lt, iszero, push2 ⟨1536⟩,
    jumpiNT htail]
  have rd1517 := RD.dup5 rd1516 (by native_decide) (by evm_ov)
  have rd1518 := RD.dup10 rd1517 (by native_decide) (by evm_ov)
  have rd1519pre := evm_run rd1518 with [add]
  have rd1520 := RD.mload mloadCost word awLoad rd1519pre
    (by native_decide) hmloadCost hmload hawLoad (by evm_ov)
  have rd1525pre := evm_run rd1520 with [push2 ⟨1532⟩, push1 ⟨31⟩]
  have rd1526 := RD.dup10 rd1525pre (by native_decide) (by evm_ov)
  have rd1532 := evm_run rd1526 with [
    and, dup3, push2 ⟨1295⟩, jump (by jump_dest),
    jumpdest, push0, push2 ⟨1310⟩, push0, not, dup5, push1 ⟨8⟩, mul,
    push2 ⟨1283⟩, jump (by jump_dest),
    jumpdest, push0, dup3, dup3, shr, swap1, pop, swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest, not, dup1, dup4, and, swap2, pop, pop, swap3, swap2, pop, pop,
    jump (by jump_dest)]
  have rd1534pre := evm_run rd1532 with [jumpdest, dup4]
  obtain ⟨_, _, rd1535₀⟩ := rd1534pre.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1535⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1535⟩
        [word, idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner τ slot (longDataTailMaskedWord word len)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState, longDataTailMaskedWord] using rd1535₀⟩
  have rd1542pre := evm_run rd1535 with [pop, jumpdest, push1 ⟨1⟩, push1 ⟨2⟩]
  have rd1543 := RD.dup9 rd1542pre (by native_decide) (by evm_ov)
  have rd1545pre₀ := evm_run rd1543 with [mul, add]
  have rd1545pre := RD.dup9 rd1545pre₀ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1546₀⟩ := rd1545pre.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1546⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1546⟩
        [idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem awLoad rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner τ slot (longDataTailMaskedWord word len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd1546₀⟩
  have rd1556 := evm_run rd1546 with [
    pop, pop, pop,
    jumpdest, pop, pop, pop, pop, pop, pop]
  exact ⟨_, _, rd1556.jump (by native_decide) hret (by evm_ov)⟩

theorem stringStoreLiteX_setLongDataWordsGeneratedNoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride oldLen len ptr ret payloadStart aw : UInt256}
    {mem rdata : ByteArray} {fuel : Nat} {mloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1470⟩
      [idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hdone : UInt256.lt (longDataWordsLoopIndex idx fuel) cutoff = ⟨0⟩)
    (hnoTail : UInt256.lt cutoff len = ⟨0⟩)
    (hmloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw aw ptr stride i →
      s.machineState.stack =
        [ptr + longDataWordsLoopStride stride i, longDataWordsLoopIndex idx i,
          longDataWordsLoopSlot slot i, cutoff, gtFlag, longDataWordsLoopStride stride i,
          oldLen, len, ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
          ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hret : (D_J stringStoreLiteBytecode 0).contains ret = true) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem (longDataWordsLoopAw aw ptr stride fuel) rdata
        (cA, sstoreAccountMap I.codeOwner
          (longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloop := stringStoreLiteX_setLongDataWordsLoopGenerated
    (σinit := σinit) (τ := τ) (idx := idx) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (oldLen := oldLen) (len := len)
    (ptr := ptr) (ret := ret) (payloadStart := payloadStart) (aw := aw)
    (mem := mem) (rdata := rdata) (fuel := fuel) (mloadCost := mloadCost)
    hperm hreach hcontinue hmloadCost
  exact stringStoreLiteX_setLongDataWordsLoopDoneNoTail
    (σinit := σinit) (τ := longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
    (idx := longDataWordsLoopIndex idx fuel)
    (slot := longDataWordsLoopSlot slot fuel) (cutoff := cutoff) (gtFlag := gtFlag)
    (stride := longDataWordsLoopStride stride fuel) (oldLen := oldLen) (len := len)
    (ptr := ptr) (ret := ret) (payloadStart := payloadStart)
    (aw := longDataWordsLoopAw aw ptr stride fuel)
    (mem := mem) (rdata := rdata)
    hperm hloop hdone hnoTail hret

theorem stringStoreLiteX_setLongDataWordsGeneratedTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {idx slot cutoff gtFlag stride oldLen len ptr ret payloadStart aw awTail wordTail : UInt256}
    {mem rdata : ByteArray} {fuel : Nat} {mloadCost loopMloadCost : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1470⟩
      [idx, slot, cutoff, gtFlag, stride, oldLen, len, ⟨0⟩, ptr, ret,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (longDataWordsLoopIndex idx i) cutoff) = ⟨0⟩)
    (hdone : UInt256.lt (longDataWordsLoopIndex idx fuel) cutoff = ⟨0⟩)
    (htail : UInt256.isZero (UInt256.lt cutoff len) = ⟨0⟩)
    (hloopMloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw aw ptr stride i →
      s.machineState.stack =
        [ptr + longDataWordsLoopStride stride i, longDataWordsLoopIndex idx i,
          longDataWordsLoopSlot slot i, cutoff, gtFlag, longDataWordsLoopStride stride i,
          oldLen, len, ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
          ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = loopMloadCost)
    (hmloadCost : ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw aw ptr stride fuel →
      s.machineState.stack =
        [ptr + longDataWordsLoopStride stride fuel, longDataWordsLoopIndex idx fuel,
          longDataWordsLoopSlot slot fuel, cutoff, gtFlag, longDataWordsLoopStride stride fuel,
          oldLen, len, ⟨0⟩, ptr, ret, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
          ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (ptr + longDataWordsLoopStride stride fuel).toNat ≥ mem.size ∨
          (ptr + longDataWordsLoopStride stride fuel) ≥
            longDataWordsLoopAw aw ptr stride fuel * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        (mem.readWithPadding (ptr + longDataWordsLoopStride stride fuel).toNat 32))) =
        wordTail)
    (hawTail :
      UInt256.ofNat
        (MachineState.M (longDataWordsLoopAw aw ptr stride fuel).toNat
          (ptr + longDataWordsLoopStride stride fuel).toNat 32) = awTail)
    (hret : (D_J stringStoreLiteBytecode 0).contains ret = true) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ret
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        mem awTail rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
            (longDataWordsLoopSlot slot fuel) (longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloop := stringStoreLiteX_setLongDataWordsLoopGenerated
    (σinit := σinit) (τ := τ) (idx := idx) (slot := slot) (cutoff := cutoff)
    (gtFlag := gtFlag) (stride := stride) (oldLen := oldLen) (len := len)
    (ptr := ptr) (ret := ret) (payloadStart := payloadStart) (aw := aw)
    (mem := mem) (rdata := rdata) (fuel := fuel) (mloadCost := loopMloadCost)
    hperm hreach hcontinue hloopMloadCost
  exact stringStoreLiteX_setLongDataWordsLoopDoneTail
    (σinit := σinit) (τ := longDataWordsForwardFrom I.codeOwner τ slot stride ptr aw mem fuel)
    (idx := longDataWordsLoopIndex idx fuel)
    (slot := longDataWordsLoopSlot slot fuel) (cutoff := cutoff) (gtFlag := gtFlag)
    (stride := longDataWordsLoopStride stride fuel) (oldLen := oldLen) (len := len)
    (ptr := ptr) (ret := ret) (payloadStart := payloadStart) (word := wordTail)
    (aw := longDataWordsLoopAw aw ptr stride fuel) (awLoad := awTail)
    (mem := mem) (rdata := rdata) (mloadCost := mloadCost)
    hperm hloop hdone htail hmloadCost hmload hawTail hret

theorem stringStoreLiteX_setWriteLongFrom1405NoTailWithLoopSchedule
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len oldLen : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C fuel mloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (longDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.land len (UInt256.lnot ⟨31⟩))) = ⟨0⟩)
    (hdone :
      UInt256.lt (longDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.land len (UInt256.lnot ⟨31⟩)) = ⟨0⟩)
    (hnoTail : UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len = ⟨0⟩)
    (hmloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + longDataWordsLoopStride ⟨32⟩ i, longDataWordsLoopIndex ⟨0⟩ i,
          longDataWordsLoopSlot clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          longDataWordsLoopStride ⟨32⟩ i, oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom mem)
        (longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel) rdata
        (cA, sstoreAccountMap I.codeOwner
          (longDataWordsForwardFrom I.codeOwner τ clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (clearCurrentHashAw aw) (clearCurrentBaseMemFrom mem) fuel)
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloopStart := stringStoreLiteX_setWriteLongReachLoopFrom1405
    (τ := τ) (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
    (mem := mem) (rdata := rdata) (aw := aw) hlong hreach
  exact stringStoreLiteX_setLongDataWordsGeneratedNoTail
    (σinit := σinit) (τ := τ) (idx := (⟨0⟩ : UInt256)) (slot := clearCurrentBaseWord)
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := (⟨32⟩ : UInt256)) (oldLen := oldLen) (len := len)
    (ptr := (⟨128⟩ : UInt256)) (ret := (⟨261⟩ : UInt256))
    (payloadStart := payloadStart) (aw := clearCurrentHashAw aw)
    (mem := clearCurrentBaseMemFrom mem) (rdata := rdata)
    (fuel := fuel) (mloadCost := mloadCost)
    hperm hloopStart hcontinue hdone hnoTail hmloadCost (by jump_dest)

theorem stringStoreLiteX_setWriteLongFrom1405TailWithLoopSchedule
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len oldLen wordTail awTail : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C fuel mloadCost loopMloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (longDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.land len (UInt256.lnot ⟨31⟩))) = ⟨0⟩)
    (hdone :
      UInt256.lt (longDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.land len (UInt256.lnot ⟨31⟩)) = ⟨0⟩)
    (htail :
      UInt256.isZero (UInt256.lt (UInt256.land len (UInt256.lnot ⟨31⟩)) len) = ⟨0⟩)
    (hloopMloadCost : ∀ i, i < fuel → ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + longDataWordsLoopStride ⟨32⟩ i, longDataWordsLoopIndex ⟨0⟩ i,
          longDataWordsLoopSlot clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          longDataWordsLoopStride ⟨32⟩ i, oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = loopMloadCost)
    (hmloadCost : ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel →
      s.machineState.stack =
        [⟨128⟩ + longDataWordsLoopStride ⟨32⟩ fuel, longDataWordsLoopIndex ⟨0⟩ fuel,
          longDataWordsLoopSlot clearCurrentBaseWord fuel,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          longDataWordsLoopStride ⟨32⟩ fuel, oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ fuel).toNat ≥
            (clearCurrentBaseMemFrom mem).size ∨
          (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ fuel) ≥
            longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((clearCurrentBaseMemFrom mem).readWithPadding
          (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ fuel).toNat 32))) = wordTail)
    (hawTail :
      UInt256.ofNat
        (MachineState.M
          (longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ fuel).toNat
          (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ fuel).toNat 32) = awTail) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom mem) awTail rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (longDataWordsForwardFrom I.codeOwner τ clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (clearCurrentHashAw aw) (clearCurrentBaseMemFrom mem) fuel)
            (longDataWordsLoopSlot clearCurrentBaseWord fuel)
            (longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hloopStart := stringStoreLiteX_setWriteLongReachLoopFrom1405
    (τ := τ) (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
    (mem := mem) (rdata := rdata) (aw := aw) hlong hreach
  exact stringStoreLiteX_setLongDataWordsGeneratedTail
    (σinit := σinit) (τ := τ) (idx := (⟨0⟩ : UInt256)) (slot := clearCurrentBaseWord)
    (cutoff := UInt256.land len (UInt256.lnot ⟨31⟩)) (gtFlag := UInt256.gt len ⟨31⟩)
    (stride := (⟨32⟩ : UInt256)) (oldLen := oldLen) (len := len)
    (ptr := (⟨128⟩ : UInt256)) (ret := (⟨261⟩ : UInt256))
    (payloadStart := payloadStart) (aw := clearCurrentHashAw aw) (awTail := awTail)
    (wordTail := wordTail) (mem := clearCurrentBaseMemFrom mem) (rdata := rdata)
    (fuel := fuel) (mloadCost := mloadCost) (loopMloadCost := loopMloadCost)
    hperm hloopStart hcontinue hdone htail hloopMloadCost hmloadCost hmload hawTail
    (by jump_dest)

theorem stringStoreLiteX_setWriteLongFrom1405NoTail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len oldLen aw : UInt256} {mem rdata : ByteArray}
    {k C mloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hmloadCost : ∀ i, i < len.toNat / 32 → ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + longDataWordsLoopStride ⟨32⟩ i, longDataWordsLoopIndex ⟨0⟩ i,
          longDataWordsLoopSlot clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          longDataWordsLoopStride ⟨32⟩ i, oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom mem)
        (longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ (len.toNat / 32)) rdata
        (cA, sstoreAccountMap I.codeOwner
          (longDataWordsForwardFrom I.codeOwner τ clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (clearCurrentHashAw aw) (clearCurrentBaseMemFrom mem) (len.toNat / 32))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  exact stringStoreLiteX_setWriteLongFrom1405NoTailWithLoopSchedule
    (σinit := σinit) (τ := τ) (payloadStart := payloadStart) (len := len)
    (oldLen := oldLen) (mem := mem) (rdata := rdata) (aw := aw)
    (fuel := len.toNat / 32) (mloadCost := mloadCost)
    hperm hlong hreach
    (fun i hi => longDataLoopContinue len hi)
    (longDataLoopDone len)
    (longDataNoTail len hnoTailMod)
    hmloadCost

theorem stringStoreLiteX_setWriteLongFrom1405Tail
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len oldLen wordTail awTail : UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {k C mloadCost loopMloadCost : Nat}
    (hperm : I.perm = true)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      mem aw rdata (cA, τ) k C)
    (hloopMloadCost : ∀ i, i < len.toNat / 32 → ∀ s : State,
      s.machineState.activeWords = longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ i →
      s.machineState.stack =
        [⟨128⟩ + longDataWordsLoopStride ⟨32⟩ i, longDataWordsLoopIndex ⟨0⟩ i,
          longDataWordsLoopSlot clearCurrentBaseWord i,
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          longDataWordsLoopStride ⟨32⟩ i, oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = loopMloadCost)
    (hmloadCost : ∀ s : State,
      s.machineState.activeWords =
        longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ (len.toNat / 32) →
      s.machineState.stack =
        [⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32),
          longDataWordsLoopIndex ⟨0⟩ (len.toNat / 32),
          longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32),
          UInt256.land len (UInt256.lnot ⟨31⟩), UInt256.gt len ⟨31⟩,
          longDataWordsLoopStride ⟨32⟩ (len.toNat / 32), oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I] →
      memoryExpansionCost s .MLOAD = mloadCost)
    (hmload :
      (if (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat ≥
            (clearCurrentBaseMemFrom mem).size ∨
          (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) ≥
            longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ (len.toNat / 32) * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((clearCurrentBaseMemFrom mem).readWithPadding
          (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat 32))) = wordTail)
    (hawTail :
      UInt256.ofNat
        (MachineState.M
          (longDataWordsLoopAw (clearCurrentHashAw aw) ⟨128⟩ ⟨32⟩ (len.toNat / 32)).toNat
          (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat 32) = awTail) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom mem) awTail rdata
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (longDataWordsForwardFrom I.codeOwner τ clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (clearCurrentHashAw aw) (clearCurrentBaseMemFrom mem) (len.toNat / 32))
            (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
            (longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  exact stringStoreLiteX_setWriteLongFrom1405TailWithLoopSchedule
    (σinit := σinit) (τ := τ) (payloadStart := payloadStart) (len := len)
    (oldLen := oldLen) (wordTail := wordTail) (awTail := awTail)
    (mem := mem) (rdata := rdata) (aw := aw)
    (fuel := len.toNat / 32) (mloadCost := mloadCost)
    (loopMloadCost := loopMloadCost)
    hperm hlong hreach
    (fun i hi => longDataLoopContinue len hi)
    (longDataLoopDone len)
    (longDataTail len htailMod)
    hloopMloadCost hmloadCost hmload hawTail

theorem stringStoreLiteX_setWriteLongFrom1405NoTailAfterClearBase
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len oldLen : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hnoTailMod : len.toNat % 32 = 0)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (clearCurrentHashAw (setHelperEntryAw len)) ByteArray.empty (cA, τ) k C) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
        (clearCurrentHashAw (setHelperEntryAw len)) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (longDataWordsForwardFrom I.codeOwner τ clearCurrentBaseWord ⟨32⟩ ⟨128⟩
            (clearCurrentHashAw (setHelperEntryAw len))
            (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
            (len.toNat / 32))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hentryGe : 1 ≤ (setHelperEntryAw len).toNat := by
    have hge := setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
    omega
  have hawEq : clearCurrentHashAw (setHelperEntryAw len) = setHelperEntryAw len :=
    clearCurrentHashAw_eq_self_of_ge1 hentryGe
  have hmemGe : 32 ≤ (setPaddedMem I.calldata len payloadStart).size := by
    have hsize := setPaddedMem_size I.calldata len payloadStart hnz hsrc
      (setDataEnd_toNat_of_u64 hlenMax)
    rw [hsize]
    omega
  have hmemIdem :
      clearCurrentBaseMemFrom
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)) =
        clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart) :=
    clearCurrentBaseMemFrom_idem hmemGe
  obtain ⟨k', C', rd⟩ :=
    stringStoreLiteX_setWriteLongFrom1405NoTail
      (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
      (aw := clearCurrentHashAw (setHelperEntryAw len))
      (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (rdata := ByteArray.empty)
      hperm hlong hnoTailMod hreach
      (by
        intro i hi s haw hstk
        have haw' :
            s.machineState.activeWords =
              longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len))
                ⟨128⟩ ⟨32⟩ i := by
          simpa [hawEq] using haw
        simpa [hawEq] using
          longDataWordsLoopMloadCost_setHelper_zero
            (I := I) (len := len) (oldLen := oldLen) (payloadStart := payloadStart)
            hlenMax i hi s haw' hstk)
  have hawLoop :
      longDataWordsLoopAw (setHelperEntryAw len)
          ⟨128⟩ ⟨32⟩ (len.toNat / 32) =
        setHelperEntryAw len := by
    simpa [hawEq] using
      longDataWordsLoopAw_setHelper_eq (len := len) hlenMax (len.toNat / 32) (by omega)
  refine ⟨k', C', ?_⟩
  simpa [hmemIdem, hawEq, hawLoop] using rd

theorem stringStoreLiteX_setWriteLongFrom1405TailAfterClearBase
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len oldLen wordTail : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hnz : len.toNat ≠ 0)
    (hlong : ¬ len.toNat < 32)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (htailMod : len.toNat % 32 ≠ 0)
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hwordTail :
      wordTail = UInt256.ofNat (fromBytesBigEndian
        (((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))) ++
          List.replicate
            (32 - ((setDecodedValueBytes I).toList.drop (32 * (len.toNat / 32))).length)
            0)))
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (clearCurrentHashAw (setHelperEntryAw len)) ByteArray.empty (cA, τ) k C) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
        (clearCurrentHashAw (setHelperEntryAw len)) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (longDataWordsForwardFrom I.codeOwner τ clearCurrentBaseWord ⟨32⟩ ⟨128⟩
              (clearCurrentHashAw (setHelperEntryAw len))
              (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
              (len.toNat / 32))
            (longDataWordsLoopSlot clearCurrentBaseWord (len.toNat / 32))
            (longDataTailMaskedWord wordTail len))
          ⟨0⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) k' C' := by
  have hentryGe : 1 ≤ (setHelperEntryAw len).toNat := by
    have hge := setHelperEntryAw_ge5_of_u64 (len := len) hlenMax
    omega
  have hawEq : clearCurrentHashAw (setHelperEntryAw len) = setHelperEntryAw len :=
    clearCurrentHashAw_eq_self_of_ge1 hentryGe
  have hmemGe : 32 ≤ (setPaddedMem I.calldata len payloadStart).size := by
    have hsize := setPaddedMem_size I.calldata len payloadStart hnz hsrc
      (setDataEnd_toNat_of_u64 hlenMax)
    rw [hsize]
    omega
  have hmemIdem :
      clearCurrentBaseMemFrom
          (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)) =
        clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart) :=
    clearCurrentBaseMemFrom_idem hmemGe
  have hmloadTail :
      (if (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat ≥
            (clearCurrentBaseMemFrom
              (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))).size ∨
          (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)) ≥
            longDataWordsLoopAw
              (clearCurrentHashAw (clearCurrentHashAw (setHelperEntryAw len)))
              ⟨128⟩ ⟨32⟩ (len.toNat / 32) * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian
        ((clearCurrentBaseMemFrom
            (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))).readWithPadding
          (⟨128⟩ + longDataWordsLoopStride ⟨32⟩ (len.toNat / 32)).toNat 32))) =
        wordTail := by
    simpa [hmemIdem, hawEq, hwordTail] using
      longDataWordsLoopMload_setHelper_decoded_tail_word
        (I := I) (len := len) (payloadStart := payloadStart)
        hnz hlenMax hsrc htailMod hlenAbi hpayloadStart hoffMax
  obtain ⟨k', C', rd⟩ :=
    stringStoreLiteX_setWriteLongFrom1405Tail
      (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
      (wordTail := wordTail) (awTail := clearCurrentHashAw (setHelperEntryAw len))
      (aw := clearCurrentHashAw (setHelperEntryAw len))
      (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (rdata := ByteArray.empty)
      hperm hlong htailMod hreach
      (by
        intro i hi s haw hstk
        have haw' :
            s.machineState.activeWords =
              longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len))
                ⟨128⟩ ⟨32⟩ i := by
          simpa [hawEq] using haw
        simpa [hawEq] using
          longDataWordsLoopMloadCost_setHelper_zero
            (I := I) (len := len) (oldLen := oldLen) (payloadStart := payloadStart)
            hlenMax i hi s haw' hstk)
      (by
        intro s haw hstk
        have haw' :
            s.machineState.activeWords =
              longDataWordsLoopAw (clearCurrentHashAw (setHelperEntryAw len))
                ⟨128⟩ ⟨32⟩ (len.toNat / 32) := by
          simpa [hawEq] using haw
        simpa [hawEq] using
          longDataWordsLoopTailMloadCost_setHelper_zero
            (I := I) (len := len) (oldLen := oldLen) (payloadStart := payloadStart)
            hlenMax htailMod s haw' hstk)
      hmloadTail
      (by
        simpa [hawEq] using
          longDataWordsLoopAw_setHelper_tail_mload_eq (len := len) hlenMax htailMod)
  refine ⟨k', C', ?_⟩
  simpa [hmemIdem, hawEq] using rd

theorem stringStoreLiteX_setShortValidWriteLongReach1405
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {payloadStart len oldLen : UInt256} {k C : Nat}
    (hnz : len.toNat ≠ 0)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (holdLen :
      oldLen = UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1405⟩
        [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
        ByteArray.empty (cA, σ) k' C' := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 len (setHelperEntryAw len) (by native_decide)
      (by
        intro s haw hstk
        rw [set_mloadCostSpec (aw := setHelperEntryAw len) (off := ⟨128⟩) s haw hstk]
        rw [set_activeWordsMload128_eq_self
          (aw := setHelperEntryAw len) (setHelperEntryAw_ge5_of_u64 (len := len) hlenMax)]
        simp)
      (setPaddedMem_mload128_nonzero_u64 I.calldata len payloadStart hnz hlenMax hsrc)
      (by
        exact set_activeWordsMload128_eq_self
          (aw := setHelperEntryAw len) (setHelperEntryAw_ge5_of_u64 (len := len) hlenMax))
      (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT
      (by
        have hgtMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
          apply ugt_zero
          rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 from rfl]
          exact hlenMax
        rw [hgtMax]
        decide)
      (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, len, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  have hvalidHeader :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := stringStoreLiteX_bytesLengthDecoderShortValidMem
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
      len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I])
    (mem := setPaddedMem I.calldata len payloadStart) (aw := setHelperEntryAw len)
    (rdata := ByteArray.empty) hflag hvalidHeader (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1394₀⟩ := hdecoded
  obtain ⟨_, _, rd1394⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1394⟩
        [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
          len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (setPaddedMem I.calldata len payloadStart) (setHelperEntryAw len)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd1394₀⟩
  have hvalid0 : UInt256.sub ⟨0⟩ (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hflag] using hvalid
  have holdLt32 : oldLen.toNat < 32 := currentLength_short_valid_lt32 hvalid0
  have holdNotGt31 : UInt256.lt ⟨31⟩ oldLen = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 holdLt32
  have rd1200 := evm_run rd1394 with [
    jumpdest, push2 ⟨1405⟩, dup3, dup3, dup6, push2 ⟨1200⟩, jump (by jump_dest)]
  have rd1405 := evm_run rd1200 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1278⟩,
    jumpiT
      (by
        rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl,
          holdNotGt31]
        decide)
      (by jump_dest),
    jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, rd1405⟩

theorem stringStoreLiteX_setEmptyWriteLongValidToClearLoop {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart len : UInt256} {k C : Nat}
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k' C', RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1162⟩
      [clearCurrentBaseWord + ⟨0⟩,
        UInt256.sub (UInt256.div (len + ⟨31⟩) ⟨32⟩) ⟨0⟩,
        ⟨1272⟩, clearCurrentBaseWord + ⟨0⟩, ⟨0⟩,
        UInt256.div (len + ⟨31⟩) ⟨32⟩, clearCurrentBaseWord, ⟨0⟩, len,
        ⟨0⟩, ⟨1405⟩, len, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩,
        ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom currentLengthZeroReturnMem)
      (clearCurrentHashAw (UInt256.ofNat 6)) ByteArray.empty (cA, σ) k' C' := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      currentLengthZeroReturnMem_mload128
      (by decide) (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT (by decide) (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  have hvalidHeader :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← hlen] using hvalid
  have hdecoded := stringStoreLiteX_bytesLengthDecoderLongValidMem
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
      payloadStart, ⟨93⟩, stringStoreLiteSelWord I])
    (mem := currentLengthZeroReturnMem) (aw := UInt256.ofNat 6) (rdata := ByteArray.empty)
    hflag hvalidHeader (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1394₀⟩ := hdecoded
  obtain ⟨_, _, rd1394⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1394⟩
        [len, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩,
          payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← hlen] using rd1394₀⟩
  have hgt31 : UInt256.lt ⟨31⟩ len ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31 (header := currentLengthHeaderWord σ I) (len := len)
      hflag hvalid
  have hgt31One : UInt256.lt ⟨31⟩ len = ⟨1⟩ :=
    clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hgtNat : 31 < len.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtLen0 : UInt256.gt len ⟨0⟩ = ⟨1⟩ :=
    ugt_one (a := len) (b := ⟨0⟩) (by
      have hpos : 0 < len.toNat := by omega
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide] using hpos)
  have rd1200 := evm_run rd1394 with [
    jumpdest, push2 ⟨1405⟩, dup3, dup3, dup6, push2 ⟨1200⟩, jump (by jump_dest)]
  have rd1210 := evm_run rd1200 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1278⟩,
    jumpiNT
      (by
        rw [show UInt256.gt len ⟨31⟩ = UInt256.lt ⟨31⟩ len from rfl]
        rw [hgt31One]
        decide)]
  have rd1218 := evm_run rd1210 with [
    dup3, dup3, gt, iszero, push2 ⟨1277⟩,
    jumpiNT
      (by
        rw [hgtLen0]
        decide)]
  have rd1226 := evm_run rd1218 with [
    push2 ⟨1226⟩, dup2, push2 ⟨917⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, dup2, push0,
    raw mstore (Cₘ (clearCurrentBaseAw (UInt256.ofNat 6)) - Cₘ (UInt256.ofNat 6))
      (clearCurrentBaseMemFrom currentLengthZeroReturnMem)
      (clearCurrentBaseAw (UInt256.ofNat 6)) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256
      (Cₘ (clearCurrentHashAw (UInt256.ofNat 6)) -
        Cₘ (clearCurrentBaseAw (UInt256.ofNat 6)))
      clearCurrentBaseWord (clearCurrentHashAw (UInt256.ofNat 6)) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          clearCurrentHashAw, clearCurrentBaseAw])
      (clearCurrentBaseMemFrom_keccak currentLengthZeroReturnMem) (by rfl) (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1235 := evm_run rd1226 with [
    jumpdest, push2 ⟨1235⟩, dup4, push2 ⟨935⟩, jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, push1 ⟨31⟩, dup4, add, div, swap1, pop,
    swap2, swap1, pop, jump (by jump_dest)]
  have rd1244 := evm_run rd1235 with [
    jumpdest, push2 ⟨1244⟩, dup6, push2 ⟨935⟩, jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, push1 ⟨31⟩, dup4, add, div, swap1, pop,
    swap2, swap1, pop, jump (by jump_dest)]
  have rd1257 := evm_run rd1244 with [
    jumpdest, push1 ⟨32⟩, dup7, lt, iszero, push2 ⟨1257⟩,
    jumpiNT (by decide),
    push0, swap1, pop,
    jumpdest]
  have rd1162 := evm_run rd1257 with [
    dup1, dup4, add, push2 ⟨1272⟩, dup3, dup5, sub, dup3,
    push2 ⟨1162⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [UInt256.sub] using rd1162⟩

theorem stringStoreLiteX_setEmptyWriteLongValidWithLoopSchedule {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart len : UInt256} {k C fuel : Nat}
    (hperm : I.perm = true)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.div (len + ⟨31⟩) ⟨32⟩) ⟨0⟩)) = ⟨0⟩)
    (hdone :
      UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.div (len + ⟨31⟩) ⟨32⟩) ⟨0⟩) = ⟨0⟩) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom currentLengthZeroReturnMem)
        (clearCurrentHashAw (UInt256.ofNat 6)) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ (clearCurrentBaseWord + ⟨0⟩) ⟨0⟩ fuel)
          ⟨0⟩ ⟨0⟩) k' C' := by
  have hloopStart := stringStoreLiteX_setEmptyWriteLongValidToClearLoop
    (g := g) (payloadStart := payloadStart) (len := len)
    hreach hflag hlen hvalid
  obtain ⟨_, _, rd1162⟩ := hloopStart
  have hentry : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
      [⟨0⟩, clearCurrentBaseWord + ⟨0⟩,
        UInt256.sub (UInt256.div (len + ⟨31⟩) ⟨32⟩) ⟨0⟩,
        ⟨1272⟩, clearCurrentBaseWord + ⟨0⟩, ⟨0⟩,
        UInt256.div (len + ⟨31⟩) ⟨32⟩, clearCurrentBaseWord, ⟨0⟩, len,
        ⟨0⟩, ⟨1405⟩, len, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩,
        ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩,
        stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom currentLengthZeroReturnMem)
      (clearCurrentHashAw (UInt256.ofNat 6)) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd1162 with [jumpdest, push0]⟩
  have hloop := stringStoreLiteX_setClearDataWordsLoopGenerated
    (σinit := σ) (τ := σ) (idx := (⟨0⟩ : UInt256))
    (base := clearCurrentBaseWord + ⟨0⟩)
    (count := UInt256.sub (UInt256.div (len + ⟨31⟩) ⟨32⟩) ⟨0⟩)
    (ret := (⟨1272⟩ : UInt256))
    (rest := [clearCurrentBaseWord + ⟨0⟩, ⟨0⟩,
      UInt256.div (len + ⟨31⟩) ⟨32⟩, clearCurrentBaseWord, ⟨0⟩, len,
      ⟨0⟩, ⟨1405⟩, len, ⟨0⟩, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩,
      ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, stringStoreLiteSelWord I])
    (mem := clearCurrentBaseMemFrom currentLengthZeroReturnMem)
    (aw := clearCurrentHashAw (UInt256.ofNat 6)) (rdata := ByteArray.empty)
    (fuel := fuel)
    hperm hentry hcontinue hdone (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1272⟩ := hloop
  have rd1405 := evm_run rd1272 with [
    jumpdest, pop, pop, pop, pop,
    jumpdest, jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact stringStoreLiteX_setEmptyWriteZeroFrom1405
    (g := g) (τ := clearDataWordsForwardFrom I.codeOwner σ
      (clearCurrentBaseWord + ⟨0⟩) ⟨0⟩ fuel)
    (payloadStart := payloadStart) (len := len)
    hperm rd1405

theorem stringStoreLiteX_setEmptyWriteLongValid {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart len : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      currentLengthZeroReturnMem (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom currentLengthZeroReturnMem)
        (clearCurrentHashAw (UInt256.ofNat 6)) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ (clearCurrentBaseWord + ⟨0⟩) ⟨0⟩
            (UInt256.sub (UInt256.div (len + ⟨31⟩) ⟨32⟩) ⟨0⟩).toNat)
          ⟨0⟩ ⟨0⟩) k' C' := by
  let count := UInt256.sub (UInt256.div (len + ⟨31⟩) ⟨32⟩) ⟨0⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero (UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ i) count) = ⟨0⟩ := by
    intro i hi
    have hidx : (clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ count.toNat) count = ⟨0⟩ := by
    rw [clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    stringStoreLiteX_setEmptyWriteLongValidWithLoopSchedule
      (g := g) (payloadStart := payloadStart) (len := len) (fuel := count.toNat)
      hperm hreach hflag hlen hvalid hcontinue hdone

theorem stringStoreLiteX_setShortNonemptyWriteLongValidToClearLoop
    {cA gh bl σ σ₀ A I} {g : Sat256} {payloadStart newLen oldLen : UInt256} {k C : Nat}
    (hnz : newLen.toNat ≠ 0)
    (hshort : newLen.toNat < 32)
    (hsrc : payloadStart.toNat + newLen.toNat ≤ I.calldata.size)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k' C', RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1162⟩
      [clearCurrentBaseWord + ⟨0⟩,
        UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩) ⟨0⟩,
        ⟨1272⟩, clearCurrentBaseWord + ⟨0⟩, ⟨0⟩,
        UInt256.div (oldLen + ⟨31⟩) ⟨32⟩, clearCurrentBaseWord, ⟨0⟩, oldLen,
        newLen, ⟨1405⟩, oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
      (clearCurrentHashAw (setHelperEntryAw newLen)) ByteArray.empty (cA, σ) k' C' := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 newLen (setHelperEntryAw newLen) (by native_decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [setHelperEntryAw_eq_7_of_short_nonzero hnz hshort]
        decide)
      (setPaddedMem_mload128_short_nonzero I.calldata newLen payloadStart hnz hshort hsrc)
      (by rw [setHelperEntryAw_eq_7_of_short_nonzero hnz hshort]; decide) (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT
      (by
        have hgtMax : UInt256.gt newLen ⟨18446744073709551615⟩ = ⟨0⟩ := by
          apply ugt_zero
          rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 from rfl]
          norm_num [ABI.solcMaxU64]
          omega
        rw [hgtMax]
        decide)
      (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  have hvalidHeader :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := stringStoreLiteX_bytesLengthDecoderLongValidMem
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
      newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I])
    (mem := setPaddedMem I.calldata newLen payloadStart) (aw := setHelperEntryAw newLen)
    (rdata := ByteArray.empty)
    hflag hvalidHeader (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1394₀⟩ := hdecoded
  obtain ⟨_, _, rd1394⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1394⟩
        [oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
          newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd1394₀⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldLen ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31 (header := currentLengthHeaderWord σ I) (len := oldLen)
      hflag hvalid
  have hgt31One : UInt256.lt ⟨31⟩ oldLen = ⟨1⟩ :=
    clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hgtNat : 31 < oldLen.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtLen0 : UInt256.gt oldLen ⟨0⟩ = ⟨1⟩ :=
    ugt_one (a := oldLen) (b := ⟨0⟩) (by
      have hpos : 0 < oldLen.toNat := by omega
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide] using hpos)
  have hgtOldNew : UInt256.gt oldLen newLen = ⟨1⟩ :=
    ugt_one (a := oldLen) (b := newLen) (by omega)
  have hnewLt32Word : UInt256.lt newLen ⟨32⟩ = ⟨1⟩ :=
    ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  have rd1200 := evm_run rd1394 with [
    jumpdest, push2 ⟨1405⟩, dup3, dup3, dup6, push2 ⟨1200⟩, jump (by jump_dest)]
  have rd1210 := evm_run rd1200 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1278⟩,
    jumpiNT
      (by
        rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl]
        rw [hgt31One]
        decide)]
  have rd1218 := evm_run rd1210 with [
    dup3, dup3, gt, iszero, push2 ⟨1277⟩,
    jumpiNT
      (by
        rw [hgtOldNew]
        decide)]
  have rd1226 := evm_run rd1218 with [
    push2 ⟨1226⟩, dup2, push2 ⟨917⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, dup2, push0,
    raw mstore
      (Cₘ (clearCurrentBaseAw (setHelperEntryAw newLen)) - Cₘ (setHelperEntryAw newLen))
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
      (clearCurrentBaseAw (setHelperEntryAw newLen)) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256
      (Cₘ (clearCurrentHashAw (setHelperEntryAw newLen)) -
        Cₘ (clearCurrentBaseAw (setHelperEntryAw newLen)))
      clearCurrentBaseWord (clearCurrentHashAw (setHelperEntryAw newLen)) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          clearCurrentHashAw, clearCurrentBaseAw])
      (clearCurrentBaseMemFrom_keccak (setPaddedMem I.calldata newLen payloadStart))
      (by rfl) (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1235 := evm_run rd1226 with [
    jumpdest, push2 ⟨1235⟩, dup4, push2 ⟨935⟩, jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, push1 ⟨31⟩, dup4, add, div, swap1, pop,
    swap2, swap1, pop, jump (by jump_dest)]
  have rd1244 := evm_run rd1235 with [
    jumpdest, push2 ⟨1244⟩, dup6, push2 ⟨935⟩, jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, push1 ⟨31⟩, dup4, add, div, swap1, pop,
    swap2, swap1, pop, jump (by jump_dest)]
  have rd1257 := evm_run rd1244 with [
    jumpdest, push1 ⟨32⟩, dup7, lt, iszero, push2 ⟨1257⟩,
    jumpiNT
      (by
        rw [hnewLt32Word]
        decide),
    push0, swap1, pop,
    jumpdest]
  have rd1162 := evm_run rd1257 with [
    dup1, dup4, add, push2 ⟨1272⟩, dup3, dup5, sub, dup3,
    push2 ⟨1162⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [UInt256.sub] using rd1162⟩

theorem stringStoreLiteX_setLongNonemptyWriteLongValidToClearLoop
    {cA gh bl σ σ₀ A I} {g : Sat256} {payloadStart newLen oldLen : UInt256} {k C : Nat}
    (hnz : newLen.toNat ≠ 0)
    (hlong : ¬ newLen.toNat < 32)
    (hlenMax : newLen.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + newLen.toNat ≤ I.calldata.size)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen newLen = ⟨1⟩) :
    ∃ k' C', RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1162⟩
      [clearCurrentBaseWord + UInt256.div (newLen + ⟨31⟩) ⟨32⟩,
        UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
          (UInt256.div (newLen + ⟨31⟩) ⟨32⟩),
        ⟨1272⟩,
        clearCurrentBaseWord + UInt256.div (newLen + ⟨31⟩) ⟨32⟩,
        UInt256.div (newLen + ⟨31⟩) ⟨32⟩,
        UInt256.div (oldLen + ⟨31⟩) ⟨32⟩, clearCurrentBaseWord, ⟨0⟩, oldLen,
        newLen, ⟨1405⟩, oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
      (clearCurrentHashAw (setHelperEntryAw newLen)) ByteArray.empty (cA, σ) k' C' := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 newLen (setHelperEntryAw newLen) (by native_decide)
      (by
        intro s haw hstk
        rw [set_mloadCostSpec (aw := setHelperEntryAw newLen) (off := ⟨128⟩) s haw hstk]
        rw [set_activeWordsMload128_eq_self
          (aw := setHelperEntryAw newLen) (setHelperEntryAw_ge5_of_u64 (len := newLen) hlenMax)]
        simp)
      (setPaddedMem_mload128_nonzero_u64 I.calldata newLen payloadStart hnz hlenMax hsrc)
      (by
        exact set_activeWordsMload128_eq_self
          (aw := setHelperEntryAw newLen) (setHelperEntryAw_ge5_of_u64 (len := newLen) hlenMax))
      (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT
      (by
        have hgtMax : UInt256.gt newLen ⟨18446744073709551615⟩ = ⟨0⟩ := by
          apply ugt_zero
          rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 from rfl]
          exact hlenMax
        rw [hgtMax]
        decide)
      (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  have hvalidHeader :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := stringStoreLiteX_bytesLengthDecoderLongValidMem
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
      newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I])
    (mem := setPaddedMem I.calldata newLen payloadStart) (aw := setHelperEntryAw newLen)
    (rdata := ByteArray.empty)
    hflag hvalidHeader (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1394₀⟩ := hdecoded
  obtain ⟨_, _, rd1394⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1394⟩
        [oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
          newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd1394₀⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldLen ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31 (header := currentLengthHeaderWord σ I) (len := oldLen)
      hflag hvalid
  have hgt31One : UInt256.lt ⟨31⟩ oldLen = ⟨1⟩ :=
    clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hnewNotLt32 : UInt256.lt newLen ⟨32⟩ = ⟨0⟩ :=
    ult_zero (a := newLen) (b := ⟨32⟩) (by
      have hge : 32 ≤ newLen.toNat := Nat.le_of_not_gt hlong
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hge)
  have rd1200 := evm_run rd1394 with [
    jumpdest, push2 ⟨1405⟩, dup3, dup3, dup6, push2 ⟨1200⟩, jump (by jump_dest)]
  have rd1210 := evm_run rd1200 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1278⟩,
    jumpiNT
      (by
        rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl]
        rw [hgt31One]
        decide)]
  have rd1218 := evm_run rd1210 with [
    dup3, dup3, gt, iszero, push2 ⟨1277⟩,
    jumpiNT
      (by
        rw [hgtOldNew]
        decide)]
  have rd1226 := evm_run rd1218 with [
    push2 ⟨1226⟩, dup2, push2 ⟨917⟩, jump (by jump_dest),
    jumpdest, push0, dup2, swap1, pop, dup2, push0,
    raw mstore
      (Cₘ (clearCurrentBaseAw (setHelperEntryAw newLen)) - Cₘ (setHelperEntryAw newLen))
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
      (clearCurrentBaseAw (setHelperEntryAw newLen)) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, clearCurrentBaseAw])
      (by rfl) (by rfl) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256
      (Cₘ (clearCurrentHashAw (setHelperEntryAw newLen)) -
        Cₘ (clearCurrentBaseAw (setHelperEntryAw newLen)))
      clearCurrentBaseWord (clearCurrentHashAw (setHelperEntryAw newLen)) (by native_decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          clearCurrentHashAw, clearCurrentBaseAw])
      (clearCurrentBaseMemFrom_keccak (setPaddedMem I.calldata newLen payloadStart))
      (by rfl) (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1235 := evm_run rd1226 with [
    jumpdest, push2 ⟨1235⟩, dup4, push2 ⟨935⟩, jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, push1 ⟨31⟩, dup4, add, div, swap1, pop,
    swap2, swap1, pop, jump (by jump_dest)]
  have rd1244 := evm_run rd1235 with [
    jumpdest, push2 ⟨1244⟩, dup6, push2 ⟨935⟩, jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, push1 ⟨31⟩, dup4, add, div, swap1, pop,
    swap2, swap1, pop, jump (by jump_dest)]
  have rd1257 := evm_run rd1244 with [
    jumpdest, push1 ⟨32⟩, dup7, lt, iszero, push2 ⟨1257⟩,
    jumpiT
      (by
        rw [hnewNotLt32]
        decide)
      (by jump_dest)]
  have rd1162 := evm_run rd1257 with [
    jumpdest, dup1, dup4, add, push2 ⟨1272⟩, dup3, dup5, sub, dup3,
    push2 ⟨1162⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa [UInt256.sub] using rd1162⟩

theorem stringStoreLiteX_setLongNonemptyWriteLongValidNoClearTo1405
    {cA gh bl σ σ₀ A I} {g : Sat256} {payloadStart newLen oldLen : UInt256} {k C : Nat}
    (hnz : newLen.toNat ≠ 0)
    (_hlong : ¬ newLen.toNat < 32)
    (hlenMax : newLen.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + newLen.toNat ≤ I.calldata.size)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen newLen = ⟨0⟩) :
    ∃ k' C', RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1405⟩
      [oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
        newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
      ByteArray.empty (cA, σ) k' C' := by
  have rd769 := evm_run hreach with [
    jumpdest, push2 ⟨1359⟩, dup3, push2 ⟨769⟩, jump (by jump_dest)]
  have rd1359 := evm_run rd769 with [
    jumpdest, push0, dup2,
    raw mload 0 newLen (setHelperEntryAw newLen) (by native_decide)
      (by
        intro s haw hstk
        rw [set_mloadCostSpec (aw := setHelperEntryAw newLen) (off := ⟨128⟩) s haw hstk]
        rw [set_activeWordsMload128_eq_self
          (aw := setHelperEntryAw newLen) (setHelperEntryAw_ge5_of_u64 (len := newLen) hlenMax)]
        simp)
      (setPaddedMem_mload128_nonzero_u64 I.calldata newLen payloadStart hnz hlenMax hsrc)
      (by
        exact set_activeWordsMload128_eq_self
          (aw := setHelperEntryAw newLen) (setHelperEntryAw_ge5_of_u64 (len := newLen) hlenMax))
      (by evm_ov),
    swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd1384 := evm_run rd1359 with [jumpdest]
  have rd1369 := RD.pushConst rd1384 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd1384' := evm_run rd1369 with [
    dup2, gt, iszero, push2 ⟨1384⟩, jumpiT
      (by
        have hgtMax : UInt256.gt newLen ⟨18446744073709551615⟩ = ⟨0⟩ := by
          apply ugt_zero
          rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 from rfl]
          exact hlenMax
        rw [hgtMax]
        decide)
      (by jump_dest)]
  have rd1389 := evm_run rd1384' with [jumpdest, push2 ⟨1394⟩, dup3]
  obtain ⟨_, _, rd1390₀⟩ := rd1389.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1390⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1390⟩
        [currentLengthHeaderWord σ I, ⟨1394⟩, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩,
          ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [currentLengthHeaderWord, initState] using rd1390₀⟩
  have hvalidHeader :
      UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    simpa [← holdLen] using hvalid
  have hdecoded := stringStoreLiteX_bytesLengthDecoderLongValidMem
    (hreach := ⟨_, _, evm_run rd1390 with [push2 ⟨869⟩, jump (by jump_dest)]⟩)
    (header := currentLengthHeaderWord σ I) (ret := ⟨1394⟩)
    (rest := [newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
      newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I])
    (mem := setPaddedMem I.calldata newLen payloadStart) (aw := setHelperEntryAw newLen)
    (rdata := ByteArray.empty)
    hflag hvalidHeader (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1394₀⟩ := hdecoded
  obtain ⟨_, _, rd1394⟩ :
      ∃ k C, RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1394⟩
        [oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
          newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [← holdLen] using rd1394₀⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldLen ≠ ⟨0⟩ :=
    clearCurrentLongValid_gt31 (header := currentLengthHeaderWord σ I) (len := oldLen)
      hflag hvalid
  have hgt31One : UInt256.lt ⟨31⟩ oldLen = ⟨1⟩ :=
    clearCurrent_ult_eq_one_of_ne_zero hgt31
  have rd1200 := evm_run rd1394 with [
    jumpdest, push2 ⟨1405⟩, dup3, dup3, dup6, push2 ⟨1200⟩, jump (by jump_dest)]
  have rd1210 := evm_run rd1200 with [
    jumpdest, push1 ⟨31⟩, dup3, gt, iszero, push2 ⟨1278⟩,
    jumpiNT
      (by
        rw [show UInt256.gt oldLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldLen from rfl]
        rw [hgt31One]
        decide)]
  have rd1405 := evm_run rd1210 with [
    dup3, dup3, gt, iszero, push2 ⟨1277⟩,
    jumpiT
      (by
        rw [hgtOldNew]
        decide)
      (by jump_dest),
    jumpdest, jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, rd1405⟩

theorem stringStoreLiteX_setLongNonemptyWriteLongValidClearTo1405WithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {payloadStart newLen oldLen : UInt256}
    {k C fuel : Nat}
    (hperm : I.perm = true)
    (hnz : newLen.toNat ≠ 0)
    (hlong : ¬ newLen.toNat < 32)
    (hlenMax : newLen.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + newLen.toNat ≤ I.calldata.size)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen newLen = ⟨1⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
            (UInt256.div (newLen + ⟨31⟩) ⟨32⟩))) = ⟨0⟩)
    (hdone :
      UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
          (UInt256.div (newLen + ⟨31⟩) ⟨32⟩)) = ⟨0⟩) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1405⟩
        [oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
          newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
        (clearCurrentHashAw (setHelperEntryAw newLen)) ByteArray.empty
        (cA, clearDataWordsForwardFrom I.codeOwner σ
          (clearCurrentBaseWord + UInt256.div (newLen + ⟨31⟩) ⟨32⟩)
          ⟨0⟩ fuel) k' C' := by
  have hloopStart := stringStoreLiteX_setLongNonemptyWriteLongValidToClearLoop
    (g := g) (payloadStart := payloadStart) (newLen := newLen) (oldLen := oldLen)
    hnz hlong hlenMax hsrc hreach hflag holdLen hvalid hgtOldNew
  obtain ⟨_, _, rd1162⟩ := hloopStart
  have hentry : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
      [⟨0⟩, clearCurrentBaseWord + UInt256.div (newLen + ⟨31⟩) ⟨32⟩,
        UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
          (UInt256.div (newLen + ⟨31⟩) ⟨32⟩),
        ⟨1272⟩,
        clearCurrentBaseWord + UInt256.div (newLen + ⟨31⟩) ⟨32⟩,
        UInt256.div (newLen + ⟨31⟩) ⟨32⟩,
        UInt256.div (oldLen + ⟨31⟩) ⟨32⟩, clearCurrentBaseWord, ⟨0⟩, oldLen,
        newLen, ⟨1405⟩, oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
      (clearCurrentHashAw (setHelperEntryAw newLen)) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd1162 with [jumpdest, push0]⟩
  have hloop := stringStoreLiteX_setClearDataWordsLoopGenerated
    (σinit := σ) (τ := σ) (idx := (⟨0⟩ : UInt256))
    (base := clearCurrentBaseWord + UInt256.div (newLen + ⟨31⟩) ⟨32⟩)
    (count := UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
      (UInt256.div (newLen + ⟨31⟩) ⟨32⟩))
    (ret := (⟨1272⟩ : UInt256))
    (rest := [clearCurrentBaseWord + UInt256.div (newLen + ⟨31⟩) ⟨32⟩,
      UInt256.div (newLen + ⟨31⟩) ⟨32⟩,
      UInt256.div (oldLen + ⟨31⟩) ⟨32⟩, clearCurrentBaseWord, ⟨0⟩, oldLen,
      newLen, ⟨1405⟩, oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩,
      ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I])
    (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
    (aw := clearCurrentHashAw (setHelperEntryAw newLen)) (rdata := ByteArray.empty)
    (fuel := fuel)
    hperm hentry hcontinue hdone (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1272⟩ := hloop
  have rd1405 := evm_run rd1272 with [
    jumpdest, pop, pop, pop, pop,
    jumpdest, jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd1405⟩

theorem stringStoreLiteX_setLongNonemptyWriteLongValidClearTo1405
    {cA gh bl σ σ₀ A I} {g : Sat256} {payloadStart newLen oldLen : UInt256}
    {k C : Nat}
    (hperm : I.perm = true)
    (hnz : newLen.toNat ≠ 0)
    (hlong : ¬ newLen.toNat < 32)
    (hlenMax : newLen.toNat ≤ ABI.solcMaxU64)
    (hsrc : payloadStart.toNat + newLen.toNat ≤ I.calldata.size)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldLen newLen = ⟨1⟩) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1405⟩
        [oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩,
          newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
        (clearCurrentHashAw (setHelperEntryAw newLen)) ByteArray.empty
        (cA, clearDataWordsForwardFrom I.codeOwner σ
          (clearCurrentBaseWord + UInt256.div (newLen + ⟨31⟩) ⟨32⟩)
          ⟨0⟩
          (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
            (UInt256.div (newLen + ⟨31⟩) ⟨32⟩)).toNat) k' C' := by
  let count := UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩)
    (UInt256.div (newLen + ⟨31⟩) ⟨32⟩)
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero (UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ i) count) = ⟨0⟩ := by
    intro i hi
    have hidx : (clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ count.toNat) count = ⟨0⟩ := by
    rw [clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    stringStoreLiteX_setLongNonemptyWriteLongValidClearTo1405WithLoopSchedule
      (g := g) (payloadStart := payloadStart) (newLen := newLen) (oldLen := oldLen)
      (fuel := count.toNat)
      hperm hnz hlong hlenMax hsrc hreach hflag holdLen hvalid hgtOldNew hcontinue hdone

theorem stringStoreLiteX_setWriteShortNonemptyFrom1405AfterClearBase
    {cA gh bl σinit σ₀ A I} {g : Sat256} {τ : AccountMap}
    {payloadStart len oldLen : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1405⟩
      [oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
        payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (clearCurrentHashAw (setHelperEntryAw len))
      ByteArray.empty (cA, τ) k C) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
        (setHelperPayloadAw len)
        ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner τ ⟨0⟩
          (setShortPackedHeader (setHelperPayloadWord I.calldata len payloadStart) len)) k' C' := by
  have hnotGt31 : UInt256.lt ⟨31⟩ len = ⟨0⟩ :=
    currentLength_notGt31_of_lt32 hshort
  have hnonzero : len ≠ ⟨0⟩ := by
    intro hzero
    exact hnz (by rw [hzero]; rfl)
  have hlenNotZero : UInt256.isZero len = ⟨0⟩ :=
    isZero_eq_zero_of_ne hnonzero
  have hawEntry : setHelperEntryAw len = ⟨7⟩ :=
    setHelperEntryAw_eq_7_of_short_nonzero hnz hshort
  have hawHash : clearCurrentHashAw (setHelperEntryAw len) = ⟨7⟩ := by
    rw [hawEntry]
    native_decide
  have hawPayload : setHelperPayloadAw len = ⟨7⟩ :=
    setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort
  have hclearSize :
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).size =
        (setPaddedMem I.calldata len payloadStart).size := by
    exact clearCurrentBaseMemFrom_size_of_ge32
      (setPaddedMem I.calldata len payloadStart)
      (by
        have hsize := setPaddedMem_size I.calldata len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega)
  have hread160 :
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).readWithPadding
          160 32 =
        (setPaddedMem I.calldata len payloadStart).readWithPadding 160 32 :=
    clearCurrentBaseMemFrom_setPaddedMem_read160_short_nonzero
      I.calldata len payloadStart hnz hshort hsrc
  have rd1430 := evm_run hreach with [
    jumpdest, push0, push1 ⟨32⟩, swap1, pop,
    push1 ⟨31⟩, dup4, gt, push1 ⟨1⟩, dup2, eq, push2 ⟨1454⟩,
    jumpiNT
      (by
        rw [show UInt256.gt len ⟨31⟩ = UInt256.lt ⟨31⟩ len from rfl, hnotGt31]
        decide),
    push0, dup5, iszero, push2 ⟨1436⟩,
    jumpiNT
      (by
        rw [hlenNotZero]),
    dup3, dup8, add]
  have haddrWord : ((⟨128⟩ : UInt256) + ⟨32⟩) = ⟨160⟩ := by native_decide
  have haddr : (((⟨128⟩ : UInt256) + ⟨32⟩).toNat) = 160 := by native_decide
  have hmload :
      (if (⟨160⟩ : UInt256).toNat ≥
            (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).size
          ∨ (⟨160⟩ : UInt256) ≥ clearCurrentHashAw (setHelperEntryAw len) * ⟨32⟩ then
          ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart)).readWithPadding
              (⟨160⟩ : UInt256).toNat 32))) =
        setHelperPayloadWord I.calldata len payloadStart := by
    rw [if_neg]
    · rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, hread160]
      exact (setHelperPayloadWord_eq_mload160_short_nonzero
        I.calldata len payloadStart hnz hshort hsrc).symm
    · apply not_or.mpr
      constructor
      · rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide, hclearSize]
        have hsize := setPaddedMem_size I.calldata len payloadStart hnz hsrc
          (setDataEnd_toNat_of_short hshort)
        rw [hsize]
        omega
      · rw [hawHash]
        decide
  have rd1434 := RD.mload
    (Cₘ (setHelperPayloadAw len) - Cₘ (clearCurrentHashAw (setHelperEntryAw len)))
    (setHelperPayloadWord I.calldata len payloadStart)
    (setHelperPayloadAw len)
    rd1430 (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, hawHash, hawPayload]
      native_decide)
    (by
      simpa [haddrWord] using hmload)
    (by
      rw [hawHash, hawPayload, haddr]
      native_decide)
    (by evm_ov)
  have rd1436 : ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1436⟩
        [setHelperPayloadWord I.calldata len payloadStart, UInt256.gt len ⟨31⟩, ⟨32⟩,
          oldLen, len, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, len,
          payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
        (setHelperPayloadAw len) ByteArray.empty (cA, τ) k' C' := by
    exact ⟨_, _, by simpa only using evm_run rd1434 with [swap1, pop]⟩
  obtain ⟨_, _, rd1436'⟩ := rd1436
  exact stringStoreLiteX_setWriteShortPackedFrom1436
    (g := g) (σinit := σinit) (τ := τ)
    (payloadStart := payloadStart) (len := len) (oldLen := oldLen)
    (payloadWord := setHelperPayloadWord I.calldata len payloadStart)
    (aw := setHelperPayloadAw len)
    hperm rd1436'

theorem stringStoreLiteX_setShortNonemptyWriteLongValidWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {payloadStart newLen oldLen : UInt256}
    {k C fuel : Nat}
    (hperm : I.perm = true)
    (hnz : newLen.toNat ≠ 0)
    (hshort : newLen.toNat < 32)
    (hsrc : payloadStart.toNat + newLen.toNat ≤ I.calldata.size)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩) ⟨0⟩)) = ⟨0⟩)
    (hdone :
      UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩) ⟨0⟩) = ⟨0⟩) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
        (setHelperPayloadAw newLen) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ (clearCurrentBaseWord + ⟨0⟩) ⟨0⟩ fuel)
          ⟨0⟩ (setShortPackedHeader
            (setHelperPayloadWord I.calldata newLen payloadStart) newLen)) k' C' := by
  have hloopStart := stringStoreLiteX_setShortNonemptyWriteLongValidToClearLoop
    (g := g) (payloadStart := payloadStart) (newLen := newLen) (oldLen := oldLen)
    hnz hshort hsrc hreach hflag holdLen hvalid
  obtain ⟨_, _, rd1162⟩ := hloopStart
  have hentry : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1164⟩
      [⟨0⟩, clearCurrentBaseWord + ⟨0⟩,
        UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩) ⟨0⟩,
        ⟨1272⟩, clearCurrentBaseWord + ⟨0⟩, ⟨0⟩,
        UInt256.div (oldLen + ⟨31⟩) ⟨32⟩, clearCurrentBaseWord, ⟨0⟩, oldLen,
        newLen, ⟨1405⟩, oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩,
        ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
      (clearCurrentHashAw (setHelperEntryAw newLen)) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd1162 with [jumpdest, push0]⟩
  have hloop := stringStoreLiteX_setClearDataWordsLoopGenerated
    (σinit := σ) (τ := σ) (idx := (⟨0⟩ : UInt256))
    (base := clearCurrentBaseWord + ⟨0⟩)
    (count := UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩) ⟨0⟩)
    (ret := (⟨1272⟩ : UInt256))
    (rest := [clearCurrentBaseWord + ⟨0⟩, ⟨0⟩,
      UInt256.div (oldLen + ⟨31⟩) ⟨32⟩, clearCurrentBaseWord, ⟨0⟩, oldLen,
      newLen, ⟨1405⟩, oldLen, newLen, ⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩,
      ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I])
    (mem := clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
    (aw := clearCurrentHashAw (setHelperEntryAw newLen)) (rdata := ByteArray.empty)
    (fuel := fuel)
    hperm hentry hcontinue hdone (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd1272⟩ := hloop
  have rd1405 := evm_run rd1272 with [
    jumpdest, pop, pop, pop, pop,
    jumpdest, jumpdest, pop, pop, pop, jump (by jump_dest)]
  exact stringStoreLiteX_setWriteShortNonemptyFrom1405AfterClearBase
    (g := g) (σinit := σ) (τ := clearDataWordsForwardFrom I.codeOwner σ
      (clearCurrentBaseWord + ⟨0⟩) ⟨0⟩ fuel)
    (payloadStart := payloadStart) (len := newLen) (oldLen := oldLen)
    hperm hnz hshort hsrc rd1405

theorem stringStoreLiteX_setShortNonemptyWriteLongValid
    {cA gh bl σ σ₀ A I} {g : Sat256} {payloadStart newLen oldLen : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hnz : newLen.toNat ≠ 0)
    (hshort : newLen.toNat < 32)
    (hsrc : payloadStart.toNat + newLen.toNat ≤ I.calldata.size)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k' C',
      RD stringStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨261⟩
        [⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
        (clearCurrentBaseMemFrom (setPaddedMem I.calldata newLen payloadStart))
        (setHelperPayloadAw newLen) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ (clearCurrentBaseWord + ⟨0⟩) ⟨0⟩
            (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩) ⟨0⟩).toNat)
          ⟨0⟩ (setShortPackedHeader
            (setHelperPayloadWord I.calldata newLen payloadStart) newLen)) k' C' := by
  let count := UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩) ⟨0⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero (UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ i) count) = ⟨0⟩ := by
    intro i hi
    have hidx : (clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (clearDataWordsLoopIndex ⟨0⟩ count.toNat) count = ⟨0⟩ := by
    rw [clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    stringStoreLiteX_setShortNonemptyWriteLongValidWithLoopSchedule
      (g := g) (payloadStart := payloadStart) (newLen := newLen) (oldLen := oldLen)
      (fuel := count.toNat)
      hperm hnz hshort hsrc hreach hflag holdLen hvalid hcontinue hdone

theorem stringStoreLiteX_setShortNonemptyReturnFromWriteAfterClearBase
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart : UInt256} {σ' : AccountMap}
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨261⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom (setPaddedMem I.calldata len payloadStart))
      (setHelperPayloadAw len) ByteArray.empty (cA, σ') k C) :
    RDret stringStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray len) := by
  obtain ⟨_, _, rd261⟩ := hreach
  have haw : setHelperPayloadAw len = ⟨7⟩ :=
    setHelperPayloadAw_eq_7_of_short_nonzero hnz hshort
  have rd93 := evm_run rd261 with [
    jumpdest, pop, dup1,
    raw mload 0 len (setHelperPayloadAw len) (by native_decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (clearCurrentBaseMemFrom_setPaddedMem_mload128_short_nonzero_payloadAw
        I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd744 := evm_run rd93 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (setHelperPayloadAw len) (by decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw]
        decide)
      (clearCurrentBaseMemFrom_setPaddedMem_mload64_short_nonzero
        I.calldata len payloadStart hnz hshort hsrc)
      (by rw [haw]; decide) (by evm_ov),
    push2 ⟨106⟩, swap2, swap1, push2 ⟨744⟩, jump (by jump_dest)]
  have hfree : currentLengthFreePtr len = ⟨192⟩ :=
    currentLengthFreePtr_eq_192_of_short_nonzero
      (by
        intro hzero
        apply hnz
        rw [hzero]
        decide)
      hshort
  have rd729 := evm_run rd744 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨763⟩,
    push0, dup4, add, dup5, push2 ⟨729⟩, jump (by jump_dest)]
  have rd720 := evm_run rd729 with [
    jumpdest, push2 ⟨738⟩, dup2, push2 ⟨720⟩, jump (by jump_dest)]
  have rd738 := evm_run rd720 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd763 := evm_run rd738 with [
    jumpdest, dup3,
    raw mstore 0 (setShortReturnMemAfterClearBase I.calldata len payloadStart)
      (UInt256.ofNat 7) (by decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, haw, hfree]
        decide)
      (by rw [hfree, show (((⟨192⟩ : UInt256) + ⟨0⟩).toNat) = 192 from by decide]; rfl)
      (by rw [haw, hfree]; decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd106 := evm_run rd763 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd106 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 (currentLengthFreePtr len) (UInt256.ofNat 7) (by decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, hfree]
        decide)
      (setShortReturnMemAfterClearBase_mload64 I.calldata len payloadStart hnz hshort hsrc)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray len) (by decide)
      (by
        intro s haw' hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw', hstk, hfree]
        decide)
      (by
        rw [hfree, show (⟨192⟩ : UInt256).toNat = 192 from by decide,
          show (UInt256.sub ((⟨192⟩ : UInt256) + ⟨32⟩) ⟨192⟩).toNat = 32 from by decide,
          setShortReturnMemAfterClearBase_read192 I.calldata len payloadStart hnz hshort hsrc])
      (by evm_ov)]

theorem stringStoreLiteX_setShortNonemptyLongValidReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {payloadStart newLen oldLen : UInt256} {k C : Nat}
    (hperm : I.perm = true)
    (hnz : newLen.toNat ≠ 0)
    (hshort : newLen.toNat < 32)
    (hsrc : payloadStart.toNat + newLen.toNat ≤ I.calldata.size)
    (hreach : RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [⟨0⟩, ⟨128⟩, ⟨261⟩, ⟨0⟩, ⟨128⟩, ⟨0⟩, newLen, payloadStart,
        ⟨93⟩, stringStoreLiteSelWord I]
      (setPaddedMem I.calldata newLen payloadStart) (setHelperEntryAw newLen)
      ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (holdLen : oldLen = UInt256.div (currentLengthHeaderWord σ I) ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt oldLen ⟨32⟩) ≠ ⟨0⟩) :
    RDret stringStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ (clearCurrentBaseWord + ⟨0⟩) ⟨0⟩
          (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩) ⟨0⟩).toNat)
        ⟨0⟩ (setShortPackedHeader
          (setHelperPayloadWord I.calldata newLen payloadStart) newLen))
      (UInt256.toByteArray newLen) := by
  have hwriteReach := stringStoreLiteX_setShortNonemptyWriteLongValid
    (g := g) (payloadStart := payloadStart) (newLen := newLen) (oldLen := oldLen)
    hperm hnz hshort hsrc hreach hflag holdLen hvalid
  exact stringStoreLiteX_setShortNonemptyReturnFromWriteAfterClearBase
    (payloadStart := payloadStart) (len := newLen) hnz hshort hsrc hwriteReach

theorem accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_comm {σ τ : AccountMap}
    (owner : AccountAddress) (base idx slot : UInt256) :
    ∀ fuel, accountMapEquiv σ τ →
      accountMapEquiv
        (sstoreAccountMap owner
          (clearDataWordsForwardFrom owner σ base idx fuel) slot ⟨0⟩)
        (clearDataWordsForwardFrom owner
          (sstoreAccountMap owner τ slot ⟨0⟩) base idx fuel)
  | 0, hAccounts => accountMapEquiv_sstoreAccountMap owner slot ⟨0⟩ hAccounts
  | n + 1, hAccounts => by
      simp [clearDataWordsForwardFrom]
      have hdata := accountMapEquiv_sstoreAccountMap owner (base + idx) ⟨0⟩ hAccounts
      have ih := accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_comm
        owner base ((⟨1⟩ : UInt256) + idx) slot n hdata
      have hcomm₀ :=
        accountMapEquiv_sstoreAccountMap_zero_comm τ owner slot (base + idx)
      have hcomm := accountMapEquiv_clearDataWordsForwardFrom owner base
        ((⟨1⟩ : UInt256) + idx) n hcomm₀
      exact accountMapEquiv.trans ih hcomm

theorem accountMapEquiv_sstore_clearDataWordsForwardFrom_comm_ne {σ τ : AccountMap}
    (owner : AccountAddress) (base idx slot val : UInt256) :
    ∀ fuel,
      (∀ i, i < fuel → slot ≠ base + clearDataWordsLoopIndex idx i) →
      accountMapEquiv σ τ →
      accountMapEquiv
        (sstoreAccountMap owner
          (clearDataWordsForwardFrom owner σ base idx fuel) slot val)
        (clearDataWordsForwardFrom owner
          (sstoreAccountMap owner τ slot val) base idx fuel)
  | 0, _hdisjoint, hAccounts => accountMapEquiv_sstoreAccountMap owner slot val hAccounts
  | n + 1, hdisjoint, hAccounts => by
      simp [clearDataWordsForwardFrom]
      have hdata := accountMapEquiv_sstoreAccountMap owner (base + idx) ⟨0⟩ hAccounts
      have htail :
          ∀ i, i < n →
            slot ≠ base + clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) i := by
        intro i hi
        have hne := hdisjoint (i + 1) (Nat.succ_lt_succ hi)
        simpa [clearDataWordsLoopIndex, clearDataWordsLoopIndex_succ_base] using hne
      have ih := accountMapEquiv_sstore_clearDataWordsForwardFrom_comm_ne
        owner base ((⟨1⟩ : UInt256) + idx) slot val n htail hdata
      have hcomm₀ :=
        accountMapEquiv_sstoreAccountMap_erase_comm τ owner slot val (base + idx)
          (hdisjoint 0 (Nat.zero_lt_succ n))
      have hcomm := accountMapEquiv_clearDataWordsForwardFrom owner base
        ((⟨1⟩ : UInt256) + idx) n hcomm₀
      exact accountMapEquiv.trans ih hcomm

theorem accountMapEquiv_sstore_currentData_clearTail_comm {σ τ : AccountMap}
    (owner : AccountAddress) (i fuel : Nat) (val : UInt256)
    (hbound : i + fuel < 2 ^ 251) (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv
      (sstoreAccountMap owner
        (clearDataWordsForwardFrom owner σ (bytesLikeDataBase ⟨0⟩)
          (UInt256.ofNat (i + 1)) fuel)
        (bytesLikeDataBase ⟨0⟩ + UInt256.ofNat i) val)
      (clearDataWordsForwardFrom owner
        (sstoreAccountMap owner τ (bytesLikeDataBase ⟨0⟩ + UInt256.ofNat i) val)
        (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat (i + 1)) fuel) := by
  exact accountMapEquiv_sstore_clearDataWordsForwardFrom_comm_ne
    owner (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat (i + 1))
    (bytesLikeDataBase ⟨0⟩ + UInt256.ofNat i) val fuel
    (by
      intro j hj
      rw [clearDataWordsLoopIndex_ofNat (i + 1) j]
      have hi : i < 2 ^ 251 := by omega
      have hj' : i + 1 + j < 2 ^ 251 := by omega
      exact currentDataSlot_ofNat_ne hi hj' (by omega))
    hAccounts

theorem accountMapEquiv_clearDataWordsForwardFrom_succ_last
    {owner : AccountAddress} {τ : AccountMap} :
    ∀ (i fuel : Nat),
      accountMapEquiv
        (clearDataWordsForwardFrom owner τ (bytesLikeDataBase ⟨0⟩)
          (UInt256.ofNat i) (fuel + 1))
        (sstoreAccountMap owner
          (clearDataWordsForwardFrom owner τ (bytesLikeDataBase ⟨0⟩)
            (UInt256.ofNat i) fuel)
          (bytesLikeDataBase ⟨0⟩ + UInt256.ofNat (i + fuel)) ⟨0⟩)
  | i, 0 => by
      simp [clearDataWordsForwardFrom, accountMapEquiv_refl]
  | i, fuel + 1 => by
      have ih := accountMapEquiv_clearDataWordsForwardFrom_succ_last
        (owner := owner)
        (τ := sstoreAccountMap owner τ (bytesLikeDataBase ⟨0⟩ + UInt256.ofNat i) ⟨0⟩)
        (i := i + 1) (fuel := fuel)
      simpa [clearDataWordsForwardFrom, u256_one_add_ofNat,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_absorb_first
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} (fuel : Nat) :
    accountMapEquiv
      (sstoreAccountMap owner
        (clearDataWordsForwardFrom owner τ base idx (fuel + 1)) (base + idx) ⟨0⟩)
      (clearDataWordsForwardFrom owner τ base idx (fuel + 1)) := by
  simp [clearDataWordsForwardFrom]
  have hcomm := accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_comm
    owner base ((⟨1⟩ : UInt256) + idx) (base + idx) fuel
    (accountMapEquiv_refl (sstoreAccountMap owner τ (base + idx) ⟨0⟩))
  have hself := accountMapEquiv_sstoreAccountMap_self_update
    τ owner (base + idx) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
  have htailSelf := accountMapEquiv_clearDataWordsForwardFrom owner base
    ((⟨1⟩ : UInt256) + idx) fuel hself
  exact accountMapEquiv.trans hcomm (accountMapEquiv.symm htailSelf)

theorem accountMapEquiv_clearDataWordsForwardFrom_double_prefix
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} :
    ∀ oldFuel newFuel : Nat, oldFuel ≤ newFuel →
      accountMapEquiv
        (clearDataWordsForwardFrom owner
          (clearDataWordsForwardFrom owner τ base idx oldFuel) base idx newFuel)
        (clearDataWordsForwardFrom owner τ base idx newFuel)
  | 0, newFuel, _hle => by
      simp [clearDataWordsForwardFrom, accountMapEquiv_refl]
  | oldFuel + 1, 0, hle => by
      omega
  | oldFuel + 1, newFuel + 1, hle => by
      simp [clearDataWordsForwardFrom]
      have hcomm := accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_comm
        owner base ((⟨1⟩ : UInt256) + idx) (base + idx) oldFuel
        (accountMapEquiv_refl (sstoreAccountMap owner τ (base + idx) ⟨0⟩))
      have hself := accountMapEquiv_sstoreAccountMap_self_update
        τ owner (base + idx) (⟨0⟩ : UInt256) (⟨0⟩ : UInt256)
      have htailSelf := accountMapEquiv_clearDataWordsForwardFrom owner base
        ((⟨1⟩ : UInt256) + idx) oldFuel hself
      have hbase := accountMapEquiv.trans hcomm (accountMapEquiv.symm htailSelf)
      have hcong := accountMapEquiv_clearDataWordsForwardFrom owner base
        ((⟨1⟩ : UInt256) + idx) newFuel hbase
      have htail := accountMapEquiv_clearDataWordsForwardFrom_double_prefix
        (owner := owner) (τ := sstoreAccountMap owner τ (base + idx) ⟨0⟩)
        (base := base) (idx := ((⟨1⟩ : UInt256) + idx))
        oldFuel newFuel (by omega)
      exact accountMapEquiv.trans hcong htail

theorem accountMapEquiv_clearDataWordsForwardFrom_split
    {owner : AccountAddress} {τ : AccountMap} {base idx : UInt256} :
    ∀ (pref tail : Nat),
      accountMapEquiv
        (clearDataWordsForwardFrom owner τ base idx (pref + tail))
        (clearDataWordsForwardFrom owner
          (clearDataWordsForwardFrom owner τ base (clearDataWordsLoopIndex idx pref) tail)
          base idx pref)
  | 0, tail => by
      simp [clearDataWordsForwardFrom, clearDataWordsLoopIndex, accountMapEquiv_refl]
  | pref + 1, tail => by
      have hfuel : pref + 1 + tail = pref + tail + 1 := by omega
      rw [hfuel]
      simp [clearDataWordsForwardFrom]
      have ih := accountMapEquiv_clearDataWordsForwardFrom_split
        (owner := owner) (τ := sstoreAccountMap owner τ (base + idx) ⟨0⟩)
        (base := base) (idx := ((⟨1⟩ : UInt256) + idx)) pref tail
      have hcomm := accountMapEquiv_sstoreZero_clearDataWordsForwardFrom_comm
        owner base (clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) pref)
        (base + idx) tail (accountMapEquiv_refl τ)
      have htail := accountMapEquiv_clearDataWordsForwardFrom owner base
        ((⟨1⟩ : UInt256) + idx) pref (accountMapEquiv.symm hcomm)
      have hidxLoop :
          clearDataWordsLoopIndex ((⟨1⟩ : UInt256) + idx) pref =
            clearDataWordsLoopIndex idx (pref + 1) := by
        rw [clearDataWordsLoopIndex_succ_base]
        rfl
      exact accountMapEquiv.trans ih (by simpa [hidxLoop] using htail)

theorem accountMapEquiv_clearDataWordsForwardFrom_shift_current
    {owner : AccountAddress} {σ τ : AccountMap} :
    ∀ (offset : Nat) (idx : UInt256) (fuel : Nat),
      offset + fuel < 2 ^ 251 →
      accountMapEquiv σ τ →
      accountMapEquiv
        (clearDataWordsForwardFrom owner σ
          (bytesLikeDataBase ⟨0⟩ + UInt256.ofNat offset) idx fuel)
        (clearDataWordsForwardFrom owner τ
          (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat offset + idx) fuel)
  | offset, idx, 0, _hbound, hAccounts => by
      simpa [clearDataWordsForwardFrom] using hAccounts
  | offset, idx, fuel + 1, hbound, hAccounts => by
      simp [clearDataWordsForwardFrom]
      have hslot :
          (bytesLikeDataBase ⟨0⟩ + UInt256.ofNat offset) + idx =
            bytesLikeDataBase ⟨0⟩ + (UInt256.ofNat offset + idx) := by
        exact u256_add_assoc (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat offset) idx
      have hstep := accountMapEquiv_sstoreAccountMap owner
        (bytesLikeDataBase ⟨0⟩ + (UInt256.ofNat offset + idx)) (⟨0⟩ : UInt256)
        hAccounts
      have htail := accountMapEquiv_clearDataWordsForwardFrom_shift_current
        (owner := owner)
        (σ := sstoreAccountMap owner σ
          ((bytesLikeDataBase ⟨0⟩ + UInt256.ofNat offset) + idx) ⟨0⟩)
        (τ := sstoreAccountMap owner τ
          (bytesLikeDataBase ⟨0⟩ + (UInt256.ofNat offset + idx)) ⟨0⟩)
        offset ((⟨1⟩ : UInt256) + idx) fuel (by omega) (by simpa [hslot] using hstep)
      have hidx :
          UInt256.ofNat offset + ((⟨1⟩ : UInt256) + idx) =
            (⟨1⟩ : UInt256) + (UInt256.ofNat offset + idx) := by
        rw [u256_add_comm (UInt256.ofNat offset) ((⟨1⟩ : UInt256) + idx)]
        rw [u256_add_assoc]
        rw [u256_add_comm idx (UInt256.ofNat offset)]
      simpa [hidx] using htail

theorem accountMapEquiv_clearDataWordsForwardFrom_shift_clearCurrentBase
    {owner : AccountAddress} {σ τ : AccountMap}
    (offset fuel : Nat)
    (hbound : offset + fuel < 2 ^ 251)
    (hAccounts : accountMapEquiv σ τ) :
    accountMapEquiv
      (clearDataWordsForwardFrom owner σ
        (clearCurrentBaseWord + UInt256.ofNat offset) (UInt256.ofNat 0) fuel)
      (clearDataWordsForwardFrom owner τ
        (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat offset) fuel) := by
  have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_current
    (owner := owner) (σ := σ) (τ := τ)
    offset (UInt256.ofNat 0) fuel hbound hAccounts
  have hbase :
      clearCurrentBaseWord + UInt256.ofNat offset =
        bytesLikeDataBase ⟨0⟩ + UInt256.ofNat offset := by
    rw [clearCurrentBaseWord_eq_solidityBytesDataBaseSlot]
    rfl
  have hidx : UInt256.ofNat offset + UInt256.ofNat 0 = UInt256.ofNat offset := by
    simpa using uint256_add_zero_right (UInt256.ofNat offset)
  simpa [hbase, hidx] using hshift

theorem clearSolidityBytesDataWordsFrom_double_current_accountMap
    (evm : EVM.State) (oldFuel newFuel : Nat) :
    (clearSolidityBytesDataWordsFrom
        (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 oldFuel)
        ⟨0⟩ 0 newFuel).accountMap =
      clearDataWordsForwardFrom evm.executionEnv.codeOwner
        (clearDataWordsForwardFrom evm.executionEnv.codeOwner evm.accountMap
          (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) oldFuel)
        (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) newFuel := by
  calc
    (clearSolidityBytesDataWordsFrom
        (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 oldFuel)
        ⟨0⟩ 0 newFuel).accountMap =
      clearDataWordsForwardFrom
        (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 oldFuel).executionEnv.codeOwner
        (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 oldFuel).accountMap
        (solidityBytesDataBaseSlot ⟨0⟩) (UInt256.ofNat 0) newFuel := by
        simpa using
          clearSolidityBytesDataWordsFrom_accountMap
            (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0 oldFuel) ⟨0⟩ 0 newFuel
    _ =
      clearDataWordsForwardFrom evm.executionEnv.codeOwner
        (clearDataWordsForwardFrom evm.executionEnv.codeOwner evm.accountMap
          (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) oldFuel)
        (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 0) newFuel := by
        rw [clearSolidityBytesDataWordsFrom_executionEnv]
        rw [clearSolidityBytesDataWordsFrom_accountMap]
        simp [bytesLikeDataBase, solidityBytesDataBaseSlot]

theorem accountMapEquiv_longDataWordsForwardFrom_tail_zero_comm
    {owner : AccountAddress} {mem : ByteArray} :
    ∀ {τ : AccountMap} {i fuel : Nat} {aw : UInt256},
      i + fuel < 2 ^ 251 →
      accountMapEquiv
        (longDataWordsForwardFrom owner
          (sstoreAccountMap owner τ
            (bytesLikeDataBase ⟨0⟩ + UInt256.ofNat (i + fuel)) ⟨0⟩)
          (clearCurrentBaseWord + UInt256.ofNat i)
          (UInt256.ofNat (32 * (i + 1))) ⟨128⟩ aw mem fuel)
        (sstoreAccountMap owner
          (longDataWordsForwardFrom owner τ
            (clearCurrentBaseWord + UInt256.ofNat i)
            (UInt256.ofNat (32 * (i + 1))) ⟨128⟩ aw mem fuel)
          (bytesLikeDataBase ⟨0⟩ + UInt256.ofNat (i + fuel)) ⟨0⟩)
  | τ, i, 0, aw, _hbound => by
      simp [longDataWordsForwardFrom, accountMapEquiv_refl]
  | τ, i, fuel + 1, aw, hbound => by
      let slot := bytesLikeDataBase ⟨0⟩ + UInt256.ofNat i
      let tailSlot := bytesLikeDataBase ⟨0⟩ + UInt256.ofNat (i + fuel + 1)
      let stride := UInt256.ofNat (32 * (i + 1))
      let word := longDataWordsLoopWord mem aw ⟨128⟩ stride 0
      let awNext := UInt256.ofNat (MachineState.M aw.toNat (⟨128⟩ + stride).toNat 32)
      have hslot_ne_tail : slot ≠ tailSlot := by
        dsimp [slot, tailSlot]
        have hi : i < 2 ^ 251 := by omega
        have htail : i + fuel + 1 < 2 ^ 251 := by omega
        exact currentDataSlot_ofNat_ne hi htail (by omega)
      have hcomm :
          accountMapEquiv
            (sstoreAccountMap owner
              (sstoreAccountMap owner τ tailSlot ⟨0⟩) slot word)
            (sstoreAccountMap owner
              (sstoreAccountMap owner τ slot word) tailSlot ⟨0⟩) := by
        exact accountMapEquiv_sstoreAccountMap_erase_comm τ owner slot word tailSlot
          hslot_ne_tail
      have hcong :
          accountMapEquiv
            (longDataWordsForwardFrom owner
              (sstoreAccountMap owner
                (sstoreAccountMap owner τ tailSlot ⟨0⟩) slot word)
              (clearCurrentBaseWord + UInt256.ofNat (i + 1))
              (UInt256.ofNat (32 * (i + 2))) ⟨128⟩ awNext mem fuel)
            (longDataWordsForwardFrom owner
              (sstoreAccountMap owner
                (sstoreAccountMap owner τ slot word) tailSlot ⟨0⟩)
              (clearCurrentBaseWord + UInt256.ofNat (i + 1))
              (UInt256.ofNat (32 * (i + 2))) ⟨128⟩ awNext mem fuel) := by
        simpa [slot, tailSlot, stride, word, awNext] using
          accountMapEquiv_longDataWordsForwardFrom
            (owner := owner)
            (slot := clearCurrentBaseWord + UInt256.ofNat (i + 1))
            (stride := UInt256.ofNat (32 * (i + 2))) (ptr := (⟨128⟩ : UInt256))
            (aw := awNext) (mem := mem) fuel hcomm
      have ih := accountMapEquiv_longDataWordsForwardFrom_tail_zero_comm
        (owner := owner) (mem := mem)
        (τ := sstoreAccountMap owner τ slot word) (i := i + 1)
        (fuel := fuel) (aw := awNext) (by omega)
      have hih :
          accountMapEquiv
            (longDataWordsForwardFrom owner
              (sstoreAccountMap owner
                (sstoreAccountMap owner τ slot word) tailSlot ⟨0⟩)
              (clearCurrentBaseWord + UInt256.ofNat (i + 1))
              (UInt256.ofNat (32 * (i + 2))) ⟨128⟩ awNext mem fuel)
            (sstoreAccountMap owner
              (longDataWordsForwardFrom owner
                (sstoreAccountMap owner τ slot word)
                (clearCurrentBaseWord + UInt256.ofNat (i + 1))
                (UInt256.ofNat (32 * (i + 2))) ⟨128⟩ awNext mem fuel)
              tailSlot ⟨0⟩) := by
        simpa [tailSlot, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih
      have htail := accountMapEquiv.trans hcong hih
      simpa [longDataWordsForwardFrom, slot, tailSlot, stride, word, awNext,
        clearCurrentBaseWord_eq_solidityBytesDataBaseSlot, solidityBytesDataBaseSlot,
        bytesLikeDataBase, u256_base_one_add_ofNat, u256_stride32_succ_ofNat,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

theorem stringStoreLiteX_setEmptyReturnFromWriteLongMem {cA gh bl σ σ₀ A I}
    {g : Sat256} {payloadStart : UInt256} {σ' : AccountMap}
    (hreach : ∃ k C, RD stringStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨261⟩
      [⟨0⟩, ⟨128⟩, ⟨0⟩, ⟨0⟩, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      (clearCurrentBaseMemFrom currentLengthZeroReturnMem) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ') k C) :
    RDret stringStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ')
      (UInt256.toByteArray ⟨0⟩) := by
  obtain ⟨_, _, rd261⟩ := hreach
  have rd93 := evm_run rd261 with [
    jumpdest, pop, dup1,
    raw mload 0 ⟨0⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      clearCurrentBaseMemFrom_currentLengthZeroReturnMem_mload128
      (by decide) (by evm_ov),
    swap2, pop, pop, swap3, swap2, pop, pop, jump (by jump_dest)]
  have rd744 := evm_run rd93 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      clearCurrentBaseMemFrom_currentLengthZeroReturnMem_mload64
      (by decide) (by evm_ov),
    push2 ⟨106⟩, swap2, swap1, push2 ⟨744⟩, jump (by jump_dest)]
  have rd729 := evm_run rd744 with [
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨763⟩,
    push0, dup4, add, dup5, push2 ⟨729⟩, jump (by jump_dest)]
  have rd720 := evm_run rd729 with [
    jumpdest, push2 ⟨738⟩, dup2, push2 ⟨720⟩, jump (by jump_dest)]
  have rd738 := evm_run rd720 with [
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump (by jump_dest)]
  have rd763 := evm_run rd738 with [
    jumpdest, dup3,
    raw mstore 0 setEmptyReturnMemLong (UInt256.ofNat 6) (by decide)
      mem_cost
      (by
        rw [show (((⟨160⟩ : UInt256) + ⟨0⟩).toNat) = 160 from by decide]
        rfl)
      (by decide) (by evm_ov),
    pop, pop, jump (by jump_dest)]
  have rd106 := evm_run rd763 with [
    jumpdest, swap3, swap2, pop, pop, jump (by jump_dest)]
  exact evm_run rd106 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨160⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      setEmptyReturnMemLong_mload64
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray ⟨0⟩) (by decide)
      mem_cost
      (by
        rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
          show (UInt256.sub ((⟨160⟩ : UInt256) + ⟨32⟩) ⟨160⟩).toNat = 32 from by decide,
          setEmptyReturnMemLong_read160])
      (by evm_ov)]

theorem stringStoreLiteSetShortNonemptyLongValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hnewShort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat < 32)
    (hnonzero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) ≠ ⟨0⟩)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩) :
    runtimeEquivalenceFor stringStoreLiteConfig stringStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreLiteDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_some (I := I)
    hsz36 hhi hsizeSign hoffMax hlenWord hlenMax hpayload
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  let oldLen : UInt256 := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((oldLen.toNat + 31) / 32))
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0
      ((oldLen.toNat + 31) / 32)).executionEnv.codeOwner
    ⟨0⟩ (solidityShortBytesWord (setDecodedValueBytes I))
  have hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
    simpa [len] using setLengthWord_eq_abi I.calldata hoffMax
  have hshort : len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewShort
  have hnz : len.toNat ≠ 0 := by
    intro hz
    apply hnonzero
    apply u256_inj
    simpa [len] using hz
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size := by
    dsimp [payloadStart]
    rw [hlenAbi, setPayloadStart_toNat I.calldata hoffMax]
    have hle := setPayloadStartLen_le_of_payload I.calldata hlenWord hpayload
    omega
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setPayloadWord_zero_of_payload I.calldata hsize hoffMax hlenWord hlenMax hpayload
  obtain ⟨k175, C175, rd175₀⟩ := stringStoreLiteX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz36 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have rd175 : RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [len, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [len, payloadStart] using rd175₀
  obtain ⟨_, _, rd1350⟩ :=
    stringStoreLiteX_setReachStorageWriteMem (payloadStart := payloadStart) (len := len) rd175
  have hret := stringStoreLiteX_setShortNonemptyLongValidReturn
    (oldLen := oldLen) hperm hnz hshort hsrc rd1350 hflag rfl
    (by simpa [oldLen] using hvalid)
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hvalueSizeShort : (setDecodedValueBytes I).size < 32 := by
    rw [setDecodedValueBytes_size hpayload]
    simpa [hlenAbi] using hshort
  have hwrite :
      writeStorage? stringStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .string (.bytes (setDecodedValueBytes I)) = .ok evmSolm1 := by
    have hwrite₀ := writeCurrentShortFromLongPrepared (evm := evmSolm0)
      (header := currentLengthHeaderWord σ_evm I) (len := oldLen)
      (value := setDecodedValueBytes I)
      hvalueSizeShort hload hflag rfl (by simpa [oldLen] using hvalid)
    simpa [evmSolm1] using hwrite₀
  have hretEnc :
      returnEquiv (UInt256.toByteArray len) (some [.int (setDecodedValueBytes I).size])
        [(.elem (.int (.uint ⟨256, by decide⟩)))] := by
    have hlenSize : len.toNat = (setDecodedValueBytes I).size := by
      rw [setDecodedValueBytes_size hpayload, hlenAbi]
    simpa [hlenSize] using returnEquiv_of_encode (uint256ReturnEncoding len)
  have hheaderEq :
      setShortPackedHeader (setHelperPayloadWord I.calldata len payloadStart) len =
        solidityShortBytesWord (setDecodedValueBytes I) :=
    setShortPackedHeader_eq_solidityShortBytesWord (I := I) (len := len)
      (payloadStart := payloadStart) hlenAbi rfl hoffMax hnz hshort hsrc hpayload
  have holdLenLt : oldLen.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) rfl
  have hdivNat :
      (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩).toNat =
        (oldLen.toNat + 31) / 32 := by
    have hadd : (oldLen + (⟨31⟩ : UInt256)).toNat = oldLen.toNat + 31 := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      exact Nat.mod_eq_of_lt (by
        have hsize' : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  have hcountNat :
      (UInt256.sub (UInt256.div (oldLen + ⟨31⟩) ⟨32⟩) ⟨0⟩).toNat =
        (oldLen.toNat + 31) / 32 := by
    rw [uint256_sub_zero_right]
    exact hdivNat
  have hcountBound : (oldLen.toNat + 31) / 32 < 2 ^ 251 := by
    apply Nat.div_lt_of_lt_mul
    have hpow : 32 * (2 : Nat) ^ 251 = 2 ^ 256 := by norm_num [pow_succ]
    rw [hpow]
    have hgap : (2 : Nat) ^ 255 + 31 < 2 ^ 256 := by norm_num
    omega
  exact setRuntimeOfWriteAccountMapEquiv hcode hwv hret hd hdec hwrite
    (by
      simp [evmSolm1, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
        storageStore_createdAccounts, initState])
    (by
      simp [evmSolm1, evmSolm0, clearSolidityBytesDataWordsFrom_accountMap,
        clearSolidityBytesDataWordsFrom_executionEnv, storageStore_accountMap, initState, hcountNat,
        clearCurrentBaseWord_eq_solidityBytesDataBaseSlot, uint256_add_zero_right,
        hheaderEq]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
        (solidityShortBytesWord (setDecodedValueBytes I))
        (accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
          (solidityBytesDataBaseSlot ⟨0⟩) ⟨0⟩ ((oldLen.toNat + 31) / 32) hAccounts))
    hretEnc

theorem stringStoreLiteSetEmptyLongValidRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hlenZero :
      uInt256OfByteArray
        (I.calldata.readBytes
          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) = ⟨0⟩)
    (hflag : UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (currentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩) :
    runtimeEquivalenceFor stringStoreLiteConfig stringStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let len : UInt256 := UInt256.div (currentLengthHeaderWord σ_evm I) ⟨2⟩
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0 ((len.toNat + 31) / 32))
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨0⟩ 0
      ((len.toNat + 31) / 32)).executionEnv.codeOwner
    ⟨0⟩ ⟨0⟩
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
  have hlenLt : len.toNat < 2 ^ 255 :=
    clearCurrent_len_toNat_lt_sign_of_div2
      (header := currentLengthHeaderWord σ_evm I) rfl
  have hdivNat :
      (UInt256.div (len + ⟨31⟩) ⟨32⟩).toNat = (len.toNat + 31) / 32 := by
    have hadd : (len + (⟨31⟩ : UInt256)).toNat = len.toNat + 31 := by
      rw [uadd_toNat, show (⟨31⟩ : UInt256).toNat = 31 from by decide]
      exact Nat.mod_eq_of_lt (by
        have hsize' : (2 : Nat) ^ 255 + 31 < UInt256.size := by
          norm_num [UInt256.size]
        nlinarith)
    rw [udiv_toNat, hadd, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  have hcountNat :
      (UInt256.sub (UInt256.div (len + ⟨31⟩) ⟨32⟩) ⟨0⟩).toNat =
        (len.toNat + 31) / 32 := by
    rw [uint256_sub_zero_right]
    exact hdivNat
  have hsel' : ((⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreLiteDispatch_set (cd := I.calldata) hsel'
  have hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩ := by
    rw [← setLengthWord_eq_abi I.calldata hoffMax]
    exact hlenZero
  have hdec := decodeCalldata_set_empty (I := I) hsz36 hhi hsizeSign hoffMax hlenWord hlenZeroAbi
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    setLengthMaxWord_zero I.calldata hlenZero
  have hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩) +
          UInt256.mul
            (uInt256OfByteArray
              (I.calldata.readBytes
                ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) ⟨1⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    setPayloadWord_zero I.calldata hsize hoffMax hlenWord hlenZero
  obtain ⟨k175, C175, rd175₀⟩ := stringStoreLiteX_setDecoderOkCore
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax
    hstart hlenMaxWord hpayloadWord
  have rd175 : RD stringStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨175⟩
      [⟨0⟩, payloadStart, ⟨93⟩, stringStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k175 C175 := by
    simpa [payloadStart, hlenZero] using rd175₀
  obtain ⟨_, _, rd1350⟩ := stringStoreLiteX_setEmptyReachStorageWrite
    (payloadStart := payloadStart) rd175
  have hwriteEvm := stringStoreLiteX_setEmptyWriteLongValid
    (g := Sat256.ofUInt256 g) (payloadStart := payloadStart) (len := len)
    hperm rd1350 hflag rfl (by simpa [len] using hvalid)
  have hret := stringStoreLiteX_setEmptyReturnFromWriteLongMem
    (g := Sat256.ofUInt256 g) (payloadStart := payloadStart)
    (by simpa [clearCurrentHashAw6] using hwriteEvm)
  have hword := currentLengthHeaderWord_eq_of_accountMapEquiv (I := I) hAccounts
  have hslot :
      (σ_solm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) =
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) := by
    simpa [currentLengthHeaderWord] using hword.symm
  have hload :
      Solm.EVM.storageLoad evmSolm0 I.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simp [evmSolm0, Solm.EVM.storageLoad, initState, State.lookupAccount,
      Account.lookupStorage, currentLengthHeaderWord, hslot]
  have hloadBytes :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        currentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0, initState] using hload
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite :
      writeStorage? stringStoreLiteConfig evmSolm0 { base := "current", steps := [] }
        .string (.bytes ByteArray.empty) = .ok evmSolm1 := by
    have hwrite₀ := writeCurrentShortFromLongPrepared (evm := evmSolm0)
      (header := currentLengthHeaderWord σ_evm I) (len := len) (value := ByteArray.empty)
      (by decide) hloadBytes hflag rfl (by simpa [len] using hvalid)
    simpa [evmSolm1, hshortEmpty] using hwrite₀
  exact setRuntimeOfWriteAccountMapEquiv hcode hwv hret hd hdec hwrite
    (by
      simp [evmSolm1, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
        storageStore_createdAccounts, initState])
    (by
      simp [evmSolm1, evmSolm0, clearSolidityBytesDataWordsFrom_accountMap,
        clearSolidityBytesDataWordsFrom_executionEnv, storageStore_accountMap, initState, hcountNat,
        clearCurrentBaseWord_eq_solidityBytesDataBaseSlot, uint256_add_zero_right]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ ⟨0⟩
        (accountMapEquiv_clearDataWordsForwardFrom I.codeOwner
          (solidityBytesDataBaseSlot ⟨0⟩) ⟨0⟩ ((len.toNat + 31) / 32) hAccounts))
    (returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256)))

end StringStoreLite
