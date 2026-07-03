import Examples.BytesStoreLite.FullPacketTag

/-!
# BytesStoreLite — full `setByte(uint256,uint8)` runtime slice

This module keeps the byte setter work out of the already-large `FullPacketTag` proof file while
reusing its dispatcher, calldata-decoder, storage-layout, and getter scaffolding.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace BytesStoreLite

def bytesStoreLiteSetByteRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "current"
    steps := [.aindex (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat))] }

def bytesStoreLiteSetByteValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (bytesStoreLiteSetByteValueWord I).toNat)

def bytesStoreLiteSetByteShortScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetByteIndexWord I))

def bytesStoreLiteSetByteShortStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreLiteSetByteShortScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetByteShortScale I)))
      (bytesStoreLiteCurrentLengthHeaderWord σ I))

def bytesStoreLiteSetByteLongWordIndex (I : ExecutionEnv) : UInt256 :=
  UInt256.mod (bytesStoreLiteSetByteIndexWord I) ⟨32⟩

def bytesStoreLiteSetByteLongDataSlot (I : ExecutionEnv) : UInt256 :=
  bytesLikeDataBase ⟨0⟩ + UInt256.div (bytesStoreLiteSetByteIndexWord I) ⟨32⟩

def bytesStoreLiteSetByteLongScale (I : ExecutionEnv) : UInt256 :=
  UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetByteLongWordIndex I))

def bytesStoreLiteSetByteLongOldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreLiteSetByteLongDataSlot I) ⟨0⟩))

theorem bytesStoreLiteSetByteLongOldWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreLiteSetByteLongOldWord σ_evm I =
      bytesStoreLiteSetByteLongOldWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner (bytesStoreLiteSetByteLongDataSlot I) ⟨0⟩

theorem bytesStoreLiteStorageLoadSetByteLongData_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I) =
      bytesStoreLiteSetByteLongOldWord σ_evm I := by
  simpa [bytesStoreLiteSetByteLongOldWord] using
    bytesStoreLiteStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreLiteSetByteLongDataSlot I) hAccounts

def bytesStoreLiteSetByteLongStoredWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.mul
      (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (bytesStoreLiteSetByteLongScale I))
    (UInt256.land
      (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetByteLongScale I)))
      (bytesStoreLiteSetByteLongOldWord σ I))

theorem bytesStoreLiteSetByteIndex_lt31_of_short_bound {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetByteIndexWord I).toNat < 31 := by
  omega

theorem bytesStoreLiteSetByteShortExponent_pos {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    0 < (UInt256.sub ⟨31⟩ (bytesStoreLiteSetByteIndexWord I)).toNat := by
  have hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetByteIndex_lt31_of_short_bound hshort hbound
  rw [usub_toNat (a := (⟨31⟩ : UInt256)) (b := bytesStoreLiteSetByteIndexWord I) (by
    simpa using Nat.le_of_lt hidx)]
  change 0 < 31 - (bytesStoreLiteSetByteIndexWord I).toNat
  omega

theorem bytesStoreLiteSetByteShortStoredWord_load_self
    {σ : AccountMap} {I : ExecutionEnv} {acc : Account}
    (hacc : σ.find? I.codeOwner = some acc)
    (hnz : (bytesStoreLiteSetByteShortStoredWord σ I == (default : UInt256)) = false) :
    (((sstoreAccountMap I.codeOwner σ ⟨0⟩
        (bytesStoreLiteSetByteShortStoredWord σ I)).find? I.codeOwner).option
        (default : UInt256) (fun acc => acc.storage.findD ⟨0⟩ (default : UInt256))) =
      bytesStoreLiteSetByteShortStoredWord σ I := by
  exact sstoreAccountMap_storage_findD_self_of_find_some σ I.codeOwner acc ⟨0⟩
    (bytesStoreLiteSetByteShortStoredWord σ I) hacc hnz

theorem sstoreAccountMap_storage_findD_self_of_find_some_any
    (σ : AccountMap) (a : AccountAddress) (acc : Account) (slot val : UInt256)
    (hacc : σ.find? a = some acc) :
    (((sstoreAccountMap a σ slot val).find? a).option (default : UInt256)
        (fun acc => acc.storage.findD slot (default : UInt256))) = val := by
  unfold sstoreAccountMap
  by_cases hzero : (val == (default : UInt256)) = true
  · have hval : val = (default : UInt256) := eq_of_beq hzero
    simp [hacc, Option.option, accountMap_find_insert_self, hval,
      storage_findD_erase_self]
  · simp [hacc, Option.option, hzero, accountMap_find_insert_self]
    exact storage_findD_insert_self acc.storage slot val (default : UInt256)

theorem bytesStoreLiteX_returnUInt8_301 {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {val : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [val, bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land val ⟨255⟩)) := by
  obtain ⟨_, _, rd301⟩ := hreach
  have rd273 := evm_run rd301 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      solcFreePtrMem_mload64
      (by native_decide) (by evm_ov),
    push1 ⟨255⟩, swap1, swap2, and, dup2,
    raw mstore 6 (solcReturnMem (UInt256.land val ⟨255⟩)) (UInt256.ofNat 5)
      (by native_decide)
      mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨273⟩, jump (by native_decide)]
  exact evm_run rd273 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (solcReturnMem_mload64 (UInt256.land val ⟨255⟩))
      (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (UInt256.land val ⟨255⟩)) (by native_decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide,
          solcReturnMem_read128])
      (by evm_ov)]

theorem byte_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.BYTE, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stBinop s (UInt256.byteAt a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.BYTE, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_byte s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stBinop]

theorem RD.byte {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.BYTE, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.byteAt a b :: t) mem aw rdata acc
      (k + 1) (C + 3) :=
  h.stepBinop (fun _ hc hp hs => byte_xstep hc hp hdec hs hov)

theorem mod_xstep {s : State} {code : ByteArray} {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MOD, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < GasConstants.Glow then .error .OutOfGass
         else .ok ({s with
            machineState.stack := UInt256.mod a b :: t,
            machineState.gasAvailable := s.machineState.gasAvailable.subNat GasConstants.Glow,
            machineState.pc := s.machineState.pc + ⟨1⟩,
            machineState.execLength := s.machineState.execLength + 1}, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.MOD, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_mod s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Glow]

theorem RD.mod {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MOD, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.mod a b :: t) mem aw rdata acc
      (k + 1) (C + GasConstants.Glow) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have st := mod_xstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + GasConstants.Glow
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC gg))
    · refine Or.inr ⟨{s with
          machineState.stack := UInt256.mod a b :: t,
          machineState.gasAvailable := s.machineState.gasAvailable.subNat GasConstants.Glow,
          machineState.pc := s.machineState.pc + ⟨1⟩,
          machineState.execLength := s.machineState.execLength + 1},
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by
          have hGlow : GasConstants.Glow = 5 := by native_decide
          omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only; exact hcode
      · simp only; rw [hpc]
      · rfl
      · simp only; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only; exact hmem
      · simp only; exact haw
      · simp only; exact hrdata
      · simp only; exact hacc
      · exact hee
      · exact hworld

theorem bytesStoreLiteShiftLeftOne248_toNat :
    (UInt256.shiftLeft ⟨1⟩ ⟨248⟩).toNat = 2 ^ 248 := by
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨248⟩ : UInt256).val ≥ 256))]
  change (((⟨1⟩ : UInt256).val <<< (⟨248⟩ : UInt256).val) :
      Fin UInt256.size).val = 2 ^ 248
  rw [Fin.shiftLeft_val, Nat.shiftLeft_eq]
  change (1 * 2 ^ 248) % UInt256.size = 2 ^ 248
  rw [one_mul, Nat.mod_eq_of_lt]
  norm_num [UInt256.size]

theorem bytesStoreLiteSetByteValueHighShiftDiv
    {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩)
        (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) =
      bytesStoreLiteSetByteValueWord I := by
  apply u256_inj
  rw [udiv_toNat, bytesStoreLiteShiftLeftOne248_toNat]
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨248⟩ : UInt256).val ≥ 256))]
  change ((((bytesStoreLiteSetByteValueWord I).val <<< (⟨248⟩ : UInt256).val) :
      Fin UInt256.size).val) / 2 ^ 248 = (bytesStoreLiteSetByteValueWord I).toNat
  rw [Fin.shiftLeft_val, Nat.shiftLeft_eq]
  change (bytesStoreLiteSetByteValueWord I).toNat * 2 ^ 248 % UInt256.size / 2 ^ 248 =
    (bytesStoreLiteSetByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt]
  · rw [Nat.mul_comm]
    rw [Nat.mul_div_right _ (by positivity : 0 < 2 ^ 248)]
  · rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetByteValueWord I).toNat * 2 ^ 248 < 256 * 2 ^ 248 :=
        Nat.mul_lt_mul_of_pos_right hcanon (by positivity)
      _ = 2 ^ 256 := by
        rw [show (256 : Nat) = 2 ^ 8 by norm_num]
        rw [← pow_add]
        norm_num

theorem bytesStoreLiteShiftRight248_eq_div_scale (w : UInt256) :
    UInt256.shiftRight w ⟨248⟩ = UInt256.div w (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) := by
  apply u256_inj
  unfold UInt256.shiftRight UInt256.div
  rw [if_neg (by decide : ¬ ((⟨248⟩ : UInt256).val ≥ 256))]
  change ((w.val >>> (⟨248⟩ : UInt256).val) : Fin UInt256.size).val =
    w.toNat / (UInt256.shiftLeft ⟨1⟩ ⟨248⟩).toNat
  rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
  change w.toNat / 2 ^ 248 = w.toNat / (UInt256.shiftLeft ⟨1⟩ ⟨248⟩).toNat
  rw [bytesStoreLiteShiftLeftOne248_toNat]

theorem bytesStoreLiteSetByteValueHighMulDiv
    {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.div
      (UInt256.mul (bytesStoreLiteSetByteValueWord I) (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
      (UInt256.shiftLeft ⟨1⟩ ⟨248⟩) = bytesStoreLiteSetByteValueWord I := by
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat, bytesStoreLiteShiftLeftOne248_toNat]
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hlt : (bytesStoreLiteSetByteValueWord I).toNat * 2 ^ 248 < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetByteValueWord I).toNat * 2 ^ 248 < 256 * 2 ^ 248 :=
        Nat.mul_lt_mul_of_pos_right hv (by positivity)
      _ = 2 ^ 256 := by
        rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_add]
        norm_num
  rw [Nat.mod_eq_of_lt hlt]
  rw [Nat.mul_comm]
  rw [Nat.mul_div_right _ (by positivity : 0 < 2 ^ 248)]

theorem bytesStoreLiteSetByteValueHighMulShiftRight
    {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.shiftRight
      (UInt256.mul (bytesStoreLiteSetByteValueWord I) (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ =
      bytesStoreLiteSetByteValueWord I := by
  rw [bytesStoreLiteShiftRight248_eq_div_scale]
  exact bytesStoreLiteSetByteValueHighMulDiv hcanon

theorem byteAt_toNat_of_le31 {i w : UInt256} (hi : i.toNat ≤ 31) :
    (UInt256.byteAt i w).toNat =
      (w.toNat / 2 ^ ((31 - i.toNat) * 8)) % 256 := by
  unfold UInt256.byteAt
  rw [if_neg]
  · change (UInt256.land (UInt256.shiftRight w
        (UInt256.ofNat ((31 - i.toNat) * 8))) ⟨255⟩).toNat = _
    rw [u256_land_toNat]
    unfold UInt256.shiftRight
    rw [if_neg]
    · change Nat.land
          (((w.val >>> (UInt256.ofNat ((31 - i.toNat) * 8)).val) :
              Fin UInt256.size).val)
          (⟨255⟩ : UInt256).toNat % UInt256.size = _
      rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
      rw [show (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 by decide]
      rw [nat_land_mask_eq_mod]
      change w.toNat / 2 ^ (UInt256.ofNat ((31 - i.toNat) * 8)).toNat %
          2 ^ 8 % UInt256.size = _
      rw [show (UInt256.ofNat ((31 - i.toNat) * 8)).toNat =
          (31 - i.toNat) * 8 by
        apply ulit_toNat'
        have hle : (31 - i.toNat) * 8 ≤ 31 * 8 :=
          Nat.mul_le_mul_right _ (Nat.sub_le 31 i.toNat)
        norm_num [UInt256.size]
        omega]
      have hlt : (w.toNat / 2 ^ ((31 - i.toNat) * 8) % 2 ^ 8) <
          UInt256.size := by
        exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 8)) (by
          norm_num [UInt256.size])
      rw [Nat.mod_eq_of_lt hlt]
      rw [show 2 ^ 8 = 256 by norm_num]
    · change ¬ (UInt256.ofNat ((31 - i.toNat) * 8)).toNat ≥ 256
      rw [show (UInt256.ofNat ((31 - i.toNat) * 8)).toNat =
          (31 - i.toNat) * 8 by
        apply ulit_toNat'
        have hle : (31 - i.toNat) * 8 ≤ 31 * 8 :=
          Nat.mul_le_mul_right _ (Nat.sub_le 31 i.toNat)
        norm_num [UInt256.size]
        omega]
      omega
  · change ¬ (⟨31⟩ : UInt256).toNat < i.toNat
    rw [show (⟨31⟩ : UInt256).toNat = 31 by decide]
    omega

private theorem nat_clear_byte_mask_eq {k : Nat} (hk : k + 8 ≤ 256) :
    (2 : Nat) ^ 256 - 1 - 255 * 2 ^ k =
      Nat.lor (2 ^ k - 1) (((2 : Nat) ^ (256 - (k + 8)) - 1) * 2 ^ (k + 8)) := by
  have hsum : (2 : Nat) ^ 256 - 1 - 255 * 2 ^ k =
      (2 ^ k - 1) + (((2 : Nat) ^ (256 - (k + 8)) - 1) * 2 ^ (k + 8)) := by
    have hpow : (2 : Nat) ^ (256 - (k + 8)) * 2 ^ (k + 8) = 2 ^ 256 := by
      rw [← Nat.pow_add]
      congr
      omega
    have hpow2 : (2 : Nat) ^ (k + 8) = 256 * 2 ^ k := by
      rw [Nat.pow_add]
      norm_num
      ring
    rw [Nat.sub_mul, one_mul, hpow, hpow2]
    have hpk : 1 ≤ (2 : Nat) ^ k := Nat.succ_le_of_lt (Nat.two_pow_pos k)
    have hbig : 256 * 2 ^ k ≤ 2 ^ 256 := by
      rw [← hpow2]
      exact Nat.pow_le_pow_right (by norm_num) hk
    omega
  rw [hsum]
  rw [nat_lor_shift_add]
  exact lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos k) zero_lt_one) (by
    exact Nat.pow_le_pow_right (by norm_num) (by omega : k ≤ k + 8))

private theorem nat_clear_byte_mask_lane_zero {old k i : Nat}
    (hk : k + 8 ≤ 256) (hi : i < 8) :
    (((2 : Nat) ^ 256 - 1 - 255 * 2 ^ k) &&& old).testBit (k + i) = false := by
  rw [nat_clear_byte_mask_eq hk]
  rw [Nat.testBit_and]
  suffices hmask : (Nat.lor (2 ^ k - 1)
      (((2 : Nat) ^ (256 - (k + 8)) - 1) * 2 ^ (k + 8))).testBit
        (k + i) = false by
    rw [hmask]
    simp
  change ((2 ^ k - 1) ||| (((2 : Nat) ^ (256 - (k + 8)) - 1) *
      2 ^ (k + 8))).testBit (k + i) = false
  rw [Nat.testBit_or]
  have hlow : (2 ^ k - 1).testBit (k + i) = false := by
    rw [Nat.testBit_two_pow_sub_one]
    simp [show ¬ k + i < k by omega]
  have hhigh : (((2 : Nat) ^ (256 - (k + 8)) - 1) * 2 ^ (k + 8)).testBit
      (k + i) = false := by
    rw [Nat.testBit_mul_two_pow]
    simp [show ¬ k + 8 ≤ k + i by omega]
  rw [hlow, hhigh]
  simp

private theorem nat_clear_byte_mask_apply {old k : Nat}
    (hk : k + 8 ≤ 256) (hold : old < 2 ^ 256) :
    (((2 : Nat) ^ 256 - 1 - 255 * 2 ^ k) &&& old) =
      Nat.lor (old % 2 ^ k) ((old / 2 ^ (k + 8)) * 2 ^ (k + 8)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  rw [nat_clear_byte_mask_eq hk]
  change ((((2 ^ k - 1) ||| (((2 : Nat) ^ (256 - (k + 8)) - 1) *
      2 ^ (k + 8))).testBit i) && old.testBit i) =
    ((old % 2 ^ k) ||| ((old / 2 ^ (k + 8)) * 2 ^ (k + 8))).testBit i
  rw [Nat.testBit_or]
  rw [Nat.testBit_or]
  rw [Nat.testBit_mod_two_pow]
  rw [Nat.testBit_mul_two_pow]
  rw [Nat.testBit_two_pow_sub_one]
  by_cases hik : i < k
  · simp [hik]
    rw [Nat.testBit_mul_two_pow]
    simp [show ¬ k + 8 ≤ i by omega]
  · by_cases himid : i < k + 8
    · have hnotHigh : ¬ k + 8 ≤ i := by omega
      simp [hik, hnotHigh]
      rw [Nat.testBit_mul_two_pow]
      simp [hnotHigh]
    · have hge : k + 8 ≤ i := by omega
      rw [Nat.testBit_mul_two_pow]
      rw [Nat.testBit_two_pow_sub_one]
      simp [hik, hge]
      by_cases hi256 : i < 256
      · rw [decide_eq_true (by omega : i - (k + 8) < 248 - k)]
        simp
        exact (nat_div_pow_testBit old (k + 8) i hge).symm
      · have holdbit : old.testBit i = false := by
          exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hold
            (Nat.pow_le_pow_right (by norm_num) (by omega : 256 ≤ i)))
        rw [decide_eq_false (by omega : ¬ i - (k + 8) < 248 - k)]
        simp [holdbit]
        rw [nat_div_pow_testBit old (k + 8) i hge]
        rw [holdbit]

private theorem nat_or_shift_add (a b k : Nat) (ha : a < 2 ^ k) :
    a ||| (b * 2 ^ k) = a + b * 2 ^ k := by
  change Nat.lor a (b * 2 ^ k) = a + b * 2 ^ k
  exact nat_lor_shift_add a b k ha

theorem nat_byte_update_eq {old v k : Nat}
    (hv : v < 256) (hk : k + 8 ≤ 256) (hold : old < 2 ^ 256) :
    old % 2 ^ k + v * 2 ^ k + (old / 2 ^ (k + 8)) * 2 ^ (k + 8) =
      Nat.lor (v * 2 ^ k)
        (Nat.land ((2 : Nat) ^ 256 - 1 - 255 * 2 ^ k) old) := by
  change old % 2 ^ k + v * 2 ^ k + (old / 2 ^ (k + 8)) * 2 ^ (k + 8) =
      (v * 2 ^ k) ||| (((2 : Nat) ^ 256 - 1 - 255 * 2 ^ k) &&& old)
  rw [nat_clear_byte_mask_apply hk hold]
  change old % 2 ^ k + v * 2 ^ k + (old / 2 ^ (k + 8)) * 2 ^ (k + 8) =
      (v * 2 ^ k) ||| ((old % 2 ^ k) ||| ((old / 2 ^ (k + 8)) * 2 ^ (k + 8)))
  rw [Nat.lor_comm (v * 2 ^ k)]
  rw [Nat.lor_assoc]
  rw [Nat.lor_comm ((old / 2 ^ (k + 8)) * 2 ^ (k + 8)) (v * 2 ^ k)]
  rw [← Nat.lor_assoc]
  have hlow : old % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  have hblock : old % 2 ^ k + v * 2 ^ k < 2 ^ (k + 8) := by
    have hvle : v ≤ 255 := by omega
    have hpos : 0 < 2 ^ k := by positivity
    calc old % 2 ^ k + v * 2 ^ k ≤ (2 ^ k - 1) + 255 * 2 ^ k := by
          gcongr
          omega
      _ < 256 * 2 ^ k := by omega
      _ = 2 ^ (k + 8) := by
          rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_add]
          ring_nf
  rw [nat_or_shift_add (old % 2 ^ k) v k hlow]
  rw [nat_or_shift_add (old % 2 ^ k + v * 2 ^ k) (old / 2 ^ (k + 8)) (k + 8)
    hblock]

theorem nat_byte_lane_lor_clear_eq {old v k : Nat}
    (hv : v < 256) (hk : k + 8 ≤ 256) :
    (((Nat.lor (v * 2 ^ k)
        (Nat.land ((2 : Nat) ^ 256 - 1 - 255 * 2 ^ k) old)) / 2 ^ k) % 256) =
      v := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (((Nat.lor (v * 2 ^ k)
        (Nat.land ((2 : Nat) ^ 256 - 1 - 255 * 2 ^ k) old)) / 2 ^ k) %
      2 ^ 8).testBit i = v.testBit i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < 8
  · simp [hi]
    have hdiv := nat_div_pow_testBit
      (Nat.lor (v * 2 ^ k) (Nat.land ((2 : Nat) ^ 256 - 1 - 255 * 2 ^ k) old))
      k (k + i) (by omega : k ≤ k + i)
    have hidx : k + i - k = i := by omega
    rw [hidx] at hdiv
    norm_num at hdiv
    rw [hdiv]
    change ((v * 2 ^ k) ||| (((2 : Nat) ^ 256 - 1 - 255 * 2 ^ k) &&& old)).testBit
      (k + i) = v.testBit i
    rw [Nat.testBit_or]
    have hleft : (v * 2 ^ k).testBit (k + i) = v.testBit i := by
      rw [Nat.testBit_mul_two_pow]
      simp [show k ≤ k + i by omega, show k + i - k = i by omega]
    have hright := nat_clear_byte_mask_lane_zero (old := old) (k := k) (i := i) hk hi
    rw [hleft, hright]
    simp
  · simp [hi]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (by
      rw [show 256 = 2 ^ 8 by norm_num]
      exact Nat.pow_le_pow_right (by norm_num) (by omega : 8 ≤ i)))

theorem u256_lnot_toNat (a : UInt256) :
    (UInt256.lnot a).toNat = UInt256.size - 1 - a.toNat := by
  unfold UInt256.lnot
  change (UInt256.sub (UInt256.ofNat (UInt256.size - 1)) a).toNat =
    UInt256.size - 1 - a.toNat
  rw [usub_toNat]
  · rw [ulit_toNat' (UInt256.size - 1) (by norm_num [UInt256.size])]
  · rw [ulit_toNat' (UInt256.size - 1) (by norm_num [UInt256.size])]
    exact Nat.le_sub_one_of_lt a.val.isLt

theorem bytesStoreLiteSetByteShortScale_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetByteShortScale I).toNat =
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) := by
  have hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreLiteSetByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreLiteSetByteIndexWord I =
        UInt256.ofNat (bytesStoreLiteSetByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreLiteSetByteIndexWord I)).symm
    rw [bytesStoreLiteSetByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreLiteSetByteShortMaskWord_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (UInt256.mul ⟨255⟩ (bytesStoreLiteSetByteShortScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) := by
  rw [u256_mul_toNat, bytesStoreLiteSetByteShortScale_toNat (I := I) (len := len)
    hshort hbound]
  rw [show (⟨255⟩ : UInt256).toNat = 255 by decide]
  rw [Nat.mod_eq_of_lt]
  have hk : ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 31 :=
      bytesStoreLiteSetByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
    omega
  calc 255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) <
      256 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) := by
        exact Nat.mul_lt_mul_of_pos_right (by norm_num : 255 < 256) (by positivity)
    _ ≤ UInt256.size := by
      rw [show UInt256.size = 2 ^ 256 from rfl]
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem bytesStoreLiteSetByteShortClearMask_toNat {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetByteShortScale I))).toNat =
      2 ^ 256 - 1 - 255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) := by
  rw [u256_lnot_toNat, bytesStoreLiteSetByteShortMaskWord_toNat (I := I) (len := len)
    hshort hbound]
  rfl

theorem bytesStoreLiteSetByteShortStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    UInt256.byteAt (bytesStoreLiteSetByteIndexWord I)
      (bytesStoreLiteSetByteShortStoredWord σ I) = bytesStoreLiteSetByteValueWord I := by
  apply u256_inj
  have hi31 : (bytesStoreLiteSetByteIndexWord I).toNat ≤ 31 := by
    have hlt := bytesStoreLiteSetByteIndex_lt31_of_short_bound (I := I) (len := len)
      hshort hbound
    omega
  rw [byteAt_toNat_of_le31 hi31]
  rw [bytesStoreLiteSetByteShortStoredWord, bytesStoreLiteSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreLiteSetByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hk : ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 31 :=
      bytesStoreLiteSetByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreLiteSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteCurrentLengthHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size /
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) % 256 =
    (bytesStoreLiteSetByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat)
    (v := (bytesStoreLiteSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) hv hk

theorem bytesStoreLiteSetByteShortStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat %
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) *
          (bytesStoreLiteSetByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8 + 8) *
        ((bytesStoreLiteCurrentLengthHeaderWord σ I).toNat /
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8 + 8)) =
    (bytesStoreLiteSetByteShortStoredWord σ I).toNat := by
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreLiteSetByteShortStoredWord, bytesStoreLiteSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetByteShortScale_toNat (I := I) (len := len) hshort hbound]
  rw [bytesStoreLiteSetByteShortClearMask_toNat (I := I) (len := len) hshort hbound]
  have hk : ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8 ≤ 256 := by
    have hidx := bytesStoreLiteSetByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    omega
  have hleftLt : (bytesStoreLiteSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ ≤ 2 ^ 256 := by
          rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
        (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteCurrentLengthHeaderWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat %
        2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) *
        (bytesStoreLiteSetByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreLiteCurrentLengthHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8)) =
      ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
            (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)) &&&
          (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) *
        (bytesStoreLiteSetByteValueWord I).toNat =
        (bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8) *
        ((bytesStoreLiteCurrentLengthHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8)) =
      (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat)
    (v := (bytesStoreLiteSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8)
    hv hk (by exact (bytesStoreLiteCurrentLengthHeaderWord σ I).val.isLt)

theorem bytesStoreLiteSetByteLongWordIndex_toNat (I : ExecutionEnv) :
    (bytesStoreLiteSetByteLongWordIndex I).toNat =
      (bytesStoreLiteSetByteIndexWord I).toNat % 32 := by
  rw [bytesStoreLiteSetByteLongWordIndex]
  unfold UInt256.mod
  rw [if_neg (by native_decide)]
  rfl

theorem bytesStoreLiteSetByteLongWordIndex_lt32 (I : ExecutionEnv) :
    (bytesStoreLiteSetByteLongWordIndex I).toNat < 32 := by
  rw [bytesStoreLiteSetByteLongWordIndex_toNat]
  exact Nat.mod_lt _ (by decide : 0 < 32)

theorem bytesStoreLiteSetByteLongWordIndex_eq_index_of_lt32
    {I : ExecutionEnv}
    (hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 32) :
    bytesStoreLiteSetByteLongWordIndex I =
      bytesStoreLiteSetByteIndexWord I := by
  apply u256_inj
  rw [bytesStoreLiteSetByteLongWordIndex_toNat]
  exact Nat.mod_eq_of_lt hidx

theorem bytesStoreLiteSetByteLongScale_toNat {I : ExecutionEnv} :
    (bytesStoreLiteSetByteLongScale I).toNat =
      2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) := by
  have hidx : (bytesStoreLiteSetByteLongWordIndex I).toNat < 32 :=
    bytesStoreLiteSetByteLongWordIndex_lt32 I
  interval_cases hnat : (bytesStoreLiteSetByteLongWordIndex I).toNat
  all_goals
    have hword : bytesStoreLiteSetByteLongWordIndex I =
        UInt256.ofNat (bytesStoreLiteSetByteLongWordIndex I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreLiteSetByteLongWordIndex I)).symm
    rw [bytesStoreLiteSetByteLongScale, hword, hnat]
    native_decide

theorem bytesStoreLiteSetByteLongMaskWord_toNat {I : ExecutionEnv} :
    (UInt256.mul ⟨255⟩ (bytesStoreLiteSetByteLongScale I)).toNat =
      255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) := by
  rw [u256_mul_toNat, bytesStoreLiteSetByteLongScale_toNat (I := I)]
  rw [show (⟨255⟩ : UInt256).toNat = 255 by decide]
  rw [Nat.mod_eq_of_lt]
  have hk : ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    have hidx : (bytesStoreLiteSetByteLongWordIndex I).toNat < 32 :=
      bytesStoreLiteSetByteLongWordIndex_lt32 I
    omega
  calc 255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) <
      256 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) := by
        exact Nat.mul_lt_mul_of_pos_right (by norm_num : 255 < 256) (by positivity)
    _ = 2 ^ (((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8) := by
        rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_add]
        ring
    _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by norm_num) hk
    _ = UInt256.size := rfl

theorem bytesStoreLiteSetByteLongClearMask_toNat {I : ExecutionEnv} :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetByteLongScale I))).toNat =
      (2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) := by
  rw [u256_lnot_toNat, bytesStoreLiteSetByteLongMaskWord_toNat (I := I)]
  rfl

theorem bytesStoreLiteSetByteLongStoredWord_byteAt
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    UInt256.byteAt (bytesStoreLiteSetByteLongWordIndex I)
      (bytesStoreLiteSetByteLongStoredWord σ I) = bytesStoreLiteSetByteValueWord I := by
  apply u256_inj
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hidxLt : (bytesStoreLiteSetByteLongWordIndex I).toNat < 32 :=
    bytesStoreLiteSetByteLongWordIndex_lt32 I
  have hidxLe : (bytesStoreLiteSetByteLongWordIndex I).toNat ≤ 31 := by omega
  rw [byteAt_toNat_of_le31 hidxLe]
  rw [bytesStoreLiteSetByteLongStoredWord, bytesStoreLiteSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetByteLongScale_toNat (I := I)]
  rw [bytesStoreLiteSetByteLongClearMask_toNat (I := I)]
  have hk : ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreLiteSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreLiteSetByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size) /
      2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) % 256 =
    (bytesStoreLiteSetByteValueWord I).toNat
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreLiteSetByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  exact nat_byte_lane_lor_clear_eq
    (old := (bytesStoreLiteSetByteLongOldWord σ I).toNat)
    (v := (bytesStoreLiteSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) hv hk

theorem bytesStoreLiteSetByteLongStoredWord_byteAt_index_of_lt32
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 32) :
    UInt256.byteAt (bytesStoreLiteSetByteIndexWord I)
      (bytesStoreLiteSetByteLongStoredWord σ I) =
        bytesStoreLiteSetByteValueWord I := by
  have heq := bytesStoreLiteSetByteLongWordIndex_eq_index_of_lt32
    (I := I) hidx
  rw [← heq]
  exact bytesStoreLiteSetByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon

theorem bytesStoreLiteSetByteLongStoredWord_toNat_update
    {σ : AccountMap} {I : ExecutionEnv}
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    (bytesStoreLiteSetByteLongOldWord σ I).toNat %
          2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) +
        2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) *
          (bytesStoreLiteSetByteValueWord I).toNat +
      2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8 + 8) *
        ((bytesStoreLiteSetByteLongOldWord σ I).toNat /
          2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8 + 8)) =
    (bytesStoreLiteSetByteLongStoredWord σ I).toNat := by
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  rw [bytesStoreLiteSetByteLongStoredWord, bytesStoreLiteSetByteValueHighShiftDiv hcanon]
  rw [u256_lor_toNat, u256_mul_toNat, u256_land_toNat]
  rw [bytesStoreLiteSetByteLongScale_toNat (I := I)]
  rw [bytesStoreLiteSetByteLongClearMask_toNat (I := I)]
  have hidxLt : (bytesStoreLiteSetByteLongWordIndex I).toNat < 32 :=
    bytesStoreLiteSetByteLongWordIndex_lt32 I
  have hk : ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8 ≤ 256 := by
    omega
  have hleftLt : (bytesStoreLiteSetByteValueWord I).toNat *
      2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) < UInt256.size := by
    rw [show UInt256.size = 2 ^ 256 from rfl]
    calc (bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) <
          256 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (8 + (31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) := by
          rw [show 256 = 2 ^ 8 by norm_num, Nat.pow_add]
        _ ≤ 2 ^ 256 := by
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrightLt : (((2 : Nat) ^ 256 - 1 -
        255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)) &&&
        (bytesStoreLiteSetByteLongOldWord σ I).toNat) < UInt256.size := by
    exact lt_of_le_of_lt Nat.and_le_right (bytesStoreLiteSetByteLongOldWord σ I).val.isLt
  rw [Nat.mod_eq_of_lt hleftLt]
  change (bytesStoreLiteSetByteLongOldWord σ I).toNat %
        2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) +
      2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) *
        (bytesStoreLiteSetByteValueWord I).toNat +
      2 ^ (((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8)) =
      ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)).lor
        ((((2 : Nat) ^ 256 - 1 -
          255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetByteLongOldWord σ I).toNat) % UInt256.size) %
        UInt256.size
  rw [Nat.mod_eq_of_lt hrightLt]
  have hlorLt :
      ((bytesStoreLiteSetByteValueWord I).toNat *
            2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)).lor
          (((2 : Nat) ^ 256 - 1 -
              255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)) &&&
            (bytesStoreLiteSetByteLongOldWord σ I).toNat) < UInt256.size := by
    change ((bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)) |||
        (((2 : Nat) ^ 256 - 1 -
            255 * 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)) &&&
          (bytesStoreLiteSetByteLongOldWord σ I).toNat) < 2 ^ 256
    apply Nat.or_lt_two_pow
    · simpa [UInt256.size] using hleftLt
    · simpa [UInt256.size] using hrightLt
  rw [Nat.mod_eq_of_lt hlorLt]
  rw [show 2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) *
        (bytesStoreLiteSetByteValueWord I).toNat =
        (bytesStoreLiteSetByteValueWord I).toNat *
          2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) by ring]
  rw [show 2 ^ (((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8) *
        ((bytesStoreLiteSetByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8)) =
      (bytesStoreLiteSetByteLongOldWord σ I).toNat /
          2 ^ (((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8) *
        2 ^ (((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8) by ring]
  exact nat_byte_update_eq
    (old := (bytesStoreLiteSetByteLongOldWord σ I).toNat)
    (v := (bytesStoreLiteSetByteValueWord I).toNat)
    (k := (31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8)
    hv hk (by exact (bytesStoreLiteSetByteLongOldWord σ I).val.isLt)

theorem storageLocStore_oneByte_local
    (evm : EVM.State) (slot valueWord target : UInt256)
    (off : Fin 32) (typ : ABI.ElemType)
    (hbound : off.val + (1 : Fin 33).val - 1 < 32) (v : Value)
    (hval : valueToWord v = some valueWord)
    (htarget : target.toNat =
      fromBytes'
        ((EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take off.val ++
         (EVM.Word.toBytesLEWithSizeProof
              (storageLocWriteWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
                off.val none valueWord)).1.take 1 ++
         (EVM.Word.toBytesLEWithSizeProof
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop
            (off.val + 1))) :
    storageLocStore evm
      { slot := slot, offset := off, size := 1, hbound := hbound, type := typ } v =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot target) := by
  unfold storageLocStore
  simp only [hval, bind, Option.bind]
  congr 2
  apply u256_inj
  exact htarget.symm

private theorem fromBytes'_take_one_eq_mod (bs : List UInt8) :
    fromBytes' (bs.take 1) = fromBytes' bs % 256 := by
  cases bs with
  | nil => simp [fromBytes']
  | cons b bs =>
      simp [fromBytes', Nat.add_mul_mod_self_left]

theorem storageLocLoad_uint8Loc_byteAt {evm : EVM.State} {slot idx : UInt256} {off : Fin 32}
    (hoff : off.val = 31 - idx.toNat)
    (hidx : idx.toNat ≤ 31) :
    storageLocLoad evm (uint8Loc slot off) =
      .int (UInt256.byteAt idx
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat := by
  unfold storageLocLoad uint8Loc wordToElem
  simp [uint8Int]
  change fromBytes' (List.take 1 (List.drop off.val
      (EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1)) =
    (UInt256.byteAt idx
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat
  rw [fromBytes'_take_one_eq_mod]
  rw [fromBytes'_drop_wordLE]
  rw [byteAt_toNat_of_le31 hidx]
  rw [hoff]
  rw [show 256 ^ (31 - idx.toNat) = 2 ^ ((31 - idx.toNat) * 8) by
    rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
    ring]

theorem nat_mod_u256_mod_256 (n : Nat) :
    n % UInt256.size % 256 = n % 256 := by
  rw [Nat.mod_mod_of_dvd]
  norm_num [UInt256.size]

theorem nat_lor_mod_256_of_left_zero {a b : Nat}
    (ha : a % 256 = 0) :
    Nat.lor a b % 256 = b % 256 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show 256 = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow,
    Nat.testBit_mod_two_pow]
  by_cases hi : i < 8
  · have hbit := congrArg (fun n => n.testBit i) ha
    change (a % 2 ^ 8).testBit i = (0 : Nat).testBit i at hbit
    rw [Nat.testBit_mod_two_pow] at hbit
    simp [hi] at hbit
    simp [hi]
    change (a ||| b).testBit i = b.testBit i
    rw [Nat.testBit_lor, hbit]
    simp
  · simp [hi]

theorem nat_land_mod_256_of_left_255 {mask n : Nat}
    (hmask : mask % 256 = 255) :
    Nat.land mask n % 256 = n % 256 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show 256 = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow,
    Nat.testBit_mod_two_pow]
  by_cases hi : i < 8
  · have hbit := congrArg (fun n => n.testBit i) hmask
    change (mask % 2 ^ 8).testBit i = (255 : Nat).testBit i at hbit
    rw [Nat.testBit_mod_two_pow] at hbit
    have h255 : (255 : Nat).testBit i = true := by
      interval_cases i <;> native_decide
    simp [hi, h255] at hbit
    simp [hi]
    change (mask &&& n).testBit i = n.testBit i
    rw [Nat.testBit_land, hbit]
    simp
  · simp [hi]

theorem bytesStoreLiteSetByteShortScale_mod256_zero {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetByteShortScale I).toNat % 256 = 0 := by
  have hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreLiteSetByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreLiteSetByteIndexWord I =
        UInt256.ofNat (bytesStoreLiteSetByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreLiteSetByteIndexWord I)).symm
    rw [bytesStoreLiteSetByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreLiteSetByteShortClearMask_mod256_255 {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetByteShortScale I))).toNat % 256 =
      255 := by
  have hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetByteIndex_lt31_of_short_bound hshort hbound
  interval_cases hnat : (bytesStoreLiteSetByteIndexWord I).toNat
  all_goals
    have hword : bytesStoreLiteSetByteIndexWord I =
        UInt256.ofNat (bytesStoreLiteSetByteIndexWord I).toNat := by
      exact (u256_ofNat_toNat (bytesStoreLiteSetByteIndexWord I)).symm
    rw [bytesStoreLiteSetByteShortScale, hword, hnat]
    native_decide

theorem bytesStoreLiteSetByteShortStoredWord_mod256
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetByteShortStoredWord σ I).toNat % 256 =
      (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat % 256 := by
  have hscale := bytesStoreLiteSetByteShortScale_mod256_zero
    (I := I) (len := len) hshort hbound
  have hmask := bytesStoreLiteSetByteShortClearMask_mod256_255
    (I := I) (len := len) hshort hbound
  have hleft :
      (UInt256.mul
        (UInt256.div (UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        (bytesStoreLiteSetByteShortScale I)).toNat % 256 = 0 := by
    rw [u256_mul_toNat, nat_mod_u256_mod_256, Nat.mul_mod, hscale]
    simp
  have hright :
      (UInt256.land
        (UInt256.lnot (UInt256.mul ⟨255⟩ (bytesStoreLiteSetByteShortScale I)))
        (bytesStoreLiteCurrentLengthHeaderWord σ I)).toNat % 256 =
        (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat % 256 := by
    rw [u256_land_toNat, nat_mod_u256_mod_256]
    exact nat_land_mod_256_of_left_255 hmask
  rw [bytesStoreLiteSetByteShortStoredWord, u256_lor_toNat, nat_mod_u256_mod_256]
  rw [nat_lor_mod_256_of_left_zero hleft, hright]

theorem bytesStoreLiteSetByteShortStoredWord_flag_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    UInt256.land (bytesStoreLiteSetByteShortStoredWord σ I) ⟨1⟩ =
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat, uInt256_land_one_toNat]
  have hmod := bytesStoreLiteSetByteShortStoredWord_mod256
    (σ := σ) (I := I) (len := len) hshort hbound
  have hleft :
      (bytesStoreLiteSetByteShortStoredWord σ I).toNat % 2 =
        ((bytesStoreLiteSetByteShortStoredWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  have hright :
      (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat % 2 =
        ((bytesStoreLiteCurrentLengthHeaderWord σ I).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  rw [hleft, hright, hmod]

theorem nat_div_two_mod_128_eq_mod_256_div_two (n : Nat) :
    (n / 2) % 128 = (n % 256) / 2 := by
  have hsplit : n = n / 256 * 256 + n % 256 := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod n 256).symm
  conv_lhs => rw [hsplit]
  rw [show n / 256 * 256 + n % 256 =
      n % 256 + 2 * (128 * (n / 256)) by ring]
  rw [Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
  rw [show n % 256 / 2 + 128 * (n / 256) =
      n % 256 / 2 + (n / 256) * 128 by ring]
  have hsmall : n % 256 / 2 < 128 := by
    have hlt : n % 256 < 256 := Nat.mod_lt _ (by decide : 0 < 256)
    omega
  rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero]
  simp
  exact hsmall

theorem bytesStoreLiteShortLenBits_toNat (w : UInt256) :
    (UInt256.land (UInt256.div w ⟨2⟩) ⟨127⟩).toNat =
      (w.toNat % 256) / 2 := by
  rw [u256_land_toNat, udiv_toNat]
  rw [show (⟨2⟩ : UInt256).toNat = 2 by decide]
  rw [show (⟨127⟩ : UInt256).toNat = 127 by decide,
    show (127 : Nat) = 2 ^ 7 - 1 by decide, nat_land_mask_eq_mod]
  have hlt : w.toNat / 2 % 2 ^ 7 < UInt256.size := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 7)) (by
      norm_num [UInt256.size])
  rw [Nat.mod_eq_of_lt hlt]
  rw [show 2 ^ 7 = 128 by norm_num]
  exact nat_div_two_mod_128_eq_mod_256_div_two w.toNat

theorem bytesStoreLiteSetByteShortStoredWord_shortLen_eq
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    UInt256.land (UInt256.div (bytesStoreLiteSetByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
      UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩ := by
  apply u256_inj
  rw [bytesStoreLiteShortLenBits_toNat, bytesStoreLiteShortLenBits_toNat]
  rw [bytesStoreLiteSetByteShortStoredWord_mod256 (σ := σ) (I := I) (len := len)
    hshort hbound]

theorem bytesStoreLiteSetByteShortStoredWord_ne_zero
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    bytesStoreLiteSetByteShortStoredWord σ I ≠ ⟨0⟩ := by
  intro hzero
  have hshortLen := bytesStoreLiteSetByteShortStoredWord_shortLen_eq
    (σ := σ) (I := I) (len := len) hshort hbound
  rw [hzero] at hshortLen
  have hlenZero : len.toNat = 0 := by
    rw [hlen, ← hshortLen]
    native_decide
  omega

theorem bytesStoreLiteSetByteShortStoredWord_beq_zero_false
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    (bytesStoreLiteSetByteShortStoredWord σ I == (default : UInt256)) = false := by
  exact beq_false_of_ne
    (bytesStoreLiteSetByteShortStoredWord_ne_zero (σ := σ) (I := I) (len := len)
      hlen hshort hbound)

theorem bytesStoreLiteSetByte_storageTypeAt {I : ExecutionEnv} :
    storageTypeAt? bytesStoreLiteContract.storage (bytesStoreLiteSetByteRef I) =
      some uint8St := by
  simp [bytesStoreLiteSetByteRef, storageTypeAt?, bytesStoreLiteContract, storageDecls,
    bytesSt, uint8St, uint8Int, storageTypeStep?]

theorem bytesStoreLiteSetByteLayoutShort {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked ⟨0⟩ evm = true)
    (hidx : (bytesStoreLiteSetByteIndexWord I).toNat < 31) :
    bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm =
      some (uint8Loc ⟨0⟩ ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by omega⟩) := by
  simp [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, bytesStoreLiteSetByteRef, bytesLikeByteLoc?, uint8Loc,
    uint8Int, hpacked, hidx]

theorem u256_div32_eq_ofNat_toNat_div (w : UInt256) :
    UInt256.div w ⟨32⟩ = UInt256.ofNat (w.toNat / 32) := by
  apply u256_inj
  rw [udiv_toNat]
  rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  exact (ulit_toNat' (w.toNat / 32)
    (lt_of_le_of_lt (Nat.div_le_self w.toNat 32) w.val.isLt)).symm

theorem bytesStoreLiteSetByteLayoutLong {evm : EVM.State} {I : ExecutionEnv}
    (hpacked : checkBytesPacked ⟨0⟩ evm = false) :
    bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm =
      some (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
        ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
          have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
          omega⟩) := by
  rw [bytesStoreLiteSetByteLongDataSlot, u256_div32_eq_ofNat_toNat_div]
  simp [bytesStoreLiteConfig, bytesStoreLiteStorageLayout, solidityStorageLayout,
    bytesStoreLiteLayout, bytesStoreLiteSetByteRef, bytesLikeByteLoc?, uint8Loc,
    uint8Int, hpacked, bytesStoreLiteSetByteLongWordIndex_toNat]

theorem bytesStoreLiteSetByteStorageLocStoreShort
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      bytesStoreLiteCurrentLengthHeaderWord σ I)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    storageLocStore evm
      (uint8Loc ⟨0⟩ ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by
        have hidx := bytesStoreLiteSetByteIndex_lt31_of_short_bound
          (I := I) (len := len) hshort hbound
        omega⟩)
      (bytesStoreLiteSetByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (bytesStoreLiteSetByteShortStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by
      have hidx := bytesStoreLiteSetByteIndex_lt31_of_short_bound
        (I := I) (len := len) hshort hbound
      omega⟩
  have hval : valueToWord (bytesStoreLiteSetByteValue I) =
      some (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat) := by
    simp [bytesStoreLiteSetByteValue, valueToWord]
    exact bytesStoreLiteWordOfIntOfNatEq (bytesStoreLiteSetByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreLiteSetByteIndexWord I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    have hidx := bytesStoreLiteSetByteIndex_lt31_of_short_bound
      (I := I) (len := len) hshort hbound
    simp [offFin]
    omega
  have htarget :
      (bytesStoreLiteSetByteShortStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
                  offFin.val none
                  (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreLiteCurrentLengthHeaderWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat).toNat % 256 =
        (bytesStoreLiteSetByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreLiteSetByteIndexWord I).toNat) =
        (31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreLiteSetByteIndexWord I).toNat + 1) =
        2 ^ (((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreLiteCurrentLengthHeaderWord σ I).toNat %
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8) *
            (bytesStoreLiteSetByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8 + 8) *
          ((bytesStoreLiteCurrentLengthHeaderWord σ I).toNat /
            2 ^ ((31 - (bytesStoreLiteSetByteIndexWord I).toNat) * 8 + 8)) =
      (bytesStoreLiteSetByteShortStoredWord σ I).toNat
    exact bytesStoreLiteSetByteShortStoredWord_toNat_update
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  change storageLocStore evm
      { slot := ⟨0⟩, offset := offFin, size := 1, hbound := hoffBound,
        type := .int uint8Int }
      (bytesStoreLiteSetByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
        (bytesStoreLiteSetByteShortStoredWord σ I))
  exact storageLocStore_oneByte_local evm ⟨0⟩
    (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat)
    (bytesStoreLiteSetByteShortStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreLiteSetByteValue I) hval htarget

theorem bytesStoreLiteSetByteStorageLocStoreLong
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I) =
      bytesStoreLiteSetByteLongOldWord σ I)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    storageLocStore evm
      (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
        ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
          have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
          omega⟩)
      (bytesStoreLiteSetByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I)) := by
  let offFin : Fin 32 :=
    ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
      have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
      omega⟩
  have hval : valueToWord (bytesStoreLiteSetByteValue I) =
      some (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat) := by
    simp [bytesStoreLiteSetByteValue, valueToWord]
    exact bytesStoreLiteWordOfIntOfNatEq (bytesStoreLiteSetByteValueWord I).toNat
  have hoffVal : offFin.val = 31 - (bytesStoreLiteSetByteLongWordIndex I).toNat := by
    rfl
  have hoffLe : offFin.val ≤ 32 := Nat.le_of_lt offFin.isLt
  have hv : (bytesStoreLiteSetByteValueWord I).toNat < 256 := by
    simpa [EVM.twoPow] using hcanon
  have hoffBound : offFin.val + (1 : Fin 33).val - 1 < 32 := by
    simp [offFin]
    omega
  have htarget :
      (bytesStoreLiteSetByteLongStoredWord σ I).toNat =
        fromBytes'
          ((EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetByteLongDataSlot I))).1.take offFin.val ++
           (EVM.Word.toBytesLEWithSizeProof
                (storageLocWriteWord
                  (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                    (bytesStoreLiteSetByteLongDataSlot I))
                  offFin.val none
                  (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat))).1.take 1 ++
           (EVM.Word.toBytesLEWithSizeProof
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
                  (bytesStoreLiteSetByteLongDataSlot I))).1.drop
              (offFin.val + 1)) := by
    rw [hload]
    simp only [storageLocWriteWord]
    symm
    rw [fromBytes'_append, fromBytes'_append]
    rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
    have hslen := (EVM.Word.toBytesLEWithSizeProof
      (bytesStoreLiteSetByteLongOldWord σ I)).2
    have hvlen := (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat)).2
    rw [List.length_take, hslen, Nat.min_eq_left hoffLe]
    rw [List.length_append, List.length_take, hslen, Nat.min_eq_left hoffLe,
      List.length_take, hvlen, Nat.min_eq_left (by norm_num : 1 ≤ 32)]
    rw [show 8 * (offFin.val + 1) = 8 * offFin.val + 8 by ring]
    rw [show 256 ^ offFin.val = 2 ^ (8 * offFin.val) by
      rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul]]
    rw [show 256 ^ 1 = 256 by norm_num]
    rw [show (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat).toNat % 256 =
        (bytesStoreLiteSetByteValueWord I).toNat by
      rw [ulit_toNat' _ (lt_of_lt_of_le hv (by norm_num [UInt256.size]))]
      exact Nat.mod_eq_of_lt hv]
    rw [hoffVal]
    rw [show 8 * (31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) =
        (31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8 by ring]
    rw [show 256 ^ (31 - (bytesStoreLiteSetByteLongWordIndex I).toNat + 1) =
        2 ^ (((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) + 8) by
      rw [show 256 = 2 ^ 8 by norm_num, ← Nat.pow_mul]
      congr 1
      ring]
    change
      (bytesStoreLiteSetByteLongOldWord σ I).toNat %
            2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) +
          2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8) *
            (bytesStoreLiteSetByteValueWord I).toNat +
        2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8 + 8) *
          ((bytesStoreLiteSetByteLongOldWord σ I).toNat /
            2 ^ ((31 - (bytesStoreLiteSetByteLongWordIndex I).toNat) * 8 + 8)) =
      (bytesStoreLiteSetByteLongStoredWord σ I).toNat
    exact bytesStoreLiteSetByteLongStoredWord_toNat_update
      (σ := σ) (I := I) hcanon
  change storageLocStore evm
      { slot := bytesStoreLiteSetByteLongDataSlot I, offset := offFin, size := 1,
        hbound := hoffBound, type := .int uint8Int }
      (bytesStoreLiteSetByteValue I) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I))
  exact storageLocStore_oneByte_local evm (bytesStoreLiteSetByteLongDataSlot I)
    (UInt256.ofNat (bytesStoreLiteSetByteValueWord I).toNat)
    (bytesStoreLiteSetByteLongStoredWord σ I)
    offFin (.int uint8Int) hoffBound
    (bytesStoreLiteSetByteValue I) hval htarget

theorem bytesStoreLiteSetByteResolveOfLength {evm : EVM.State} {I : ExecutionEnv}
    {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
      .ok len)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
      evm (currentByteRef (.var "index")) =
        .ok (bytesStoreLiteSetByteRef I, uint8St) := by
  have hgetIndexElem :
      (bytesStoreLiteSetByteLocals I)["index"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) :=
    bytesStoreLiteSetByteLocals_getElem_index I
  have hgetCurrentElem :
      (bytesStoreLiteSetByteLocals I)["current"]? = none :=
    bytesStoreLiteSetByteLocals_getElem_current_none I
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm { base := "current", steps := [] } = .ok len := by
    simpa [bytesStoreLiteConfig] using hlen
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm (currentByteRef (.var "index")) = .ok (bytesStoreLiteSetByteRef I) := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, currentByteRef,
      bytesStoreLiteSetByteRef, hgetIndexElem, valueToKey?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig,
      bytesStoreLiteContract, storageDecls, bytesSt, hlen', hbound]
  have her' :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm { base := "current", steps := [.aindex (.var "index")] } =
          .ok (bytesStoreLiteSetByteRef I) := by
    simpa [currentByteRef] using her
  rw [resolveStorageRef?]
  simp [currentByteRef, hgetCurrentElem, her', bytesStoreLiteSetByte_storageTypeAt,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem bytesStoreLiteSetByteAssignOfLength {evm evm' : EVM.State} {I : ExecutionEnv}
    {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
      .ok len)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len)
    (hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetByteValue I)
      | none => none) = some evm') :
    assignStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
      evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
        .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }, evm') := by
  rw [assignStorageRef?]
  rw [bytesStoreLiteSetByteResolveOfLength (I := I) hlen hbound]
  cases hloc : bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm with
  | none =>
      simp [hloc] at hstore
  | some loc =>
      have hstoreLoc :
          storageLocStore evm loc
            (.int (Int.ofNat (bytesStoreLiteSetByteValueWord I).toNat)) = some evm' := by
        simpa [hloc, bytesStoreLiteSetByteValue] using hstore
      have hstoreLoc' :
          storageLocStore evm loc
            (.int ((bytesStoreLiteSetByteValueWord I).toNat : Int)) = some evm' := by
        simpa using hstoreLoc
      simp [bytesStoreLiteSetByteValue, hloc, EvalResult.ofOption, EvalResult.bind, bind, pure]
      rw [hstoreLoc']

theorem bytesStoreLiteSetByteBodyReturns {evm evm' : EVM.State} {I : ExecutionEnv}
    {ret : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm'))
    (hret :
      evalExpr? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm' (.storage (currentByteRef (.var "index"))) = .ok ret) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body
      (.returned
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm' (some ret)) := by
  let solm : Frame := { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetByteValue I) := by
    simp [solm, bytesStoreLiteSetByteValue, bytesStoreLiteSetByteLocals, evalExpr?,
      EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreLiteConfig solm evm'
        (.storage (currentByteRef (.var "index"))) = .ok ret := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLiteSetByteShortBodyReturns
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      bytesStoreLiteCurrentLengthHeaderWord σ I)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body
      (.returned
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
          (bytesStoreLiteSetByteShortStoredWord σ I))
        (some (bytesStoreLiteSetByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (bytesStoreLiteSetByteShortStoredWord σ I)
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hload, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked ⟨0⟩ evm = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hidx31 : (bytesStoreLiteSetByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetByteIndex_lt31_of_short_bound (I := I) (len := len) hshort hbound
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm =
        some (uint8Loc ⟨0⟩ ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetByteLayoutShort (evm := evm) (I := I) hpacked hidx31
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetByteStorageLocStoreShort
        (evm := evm) (σ := σ) (I := I) (len := len)
        hload hcanon hshort hbound
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm') :=
    bytesStoreLiteSetByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteSetByteShortStoredWord σ I := by
    have hloadPostOwner :
        Solm.EVM.storageLoad evm' evm.executionEnv.codeOwner ⟨0⟩ =
          bytesStoreLiteSetByteShortStoredWord σ I := by
      simpa [evm'] using
        storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc ⟨0⟩
          (bytesStoreLiteSetByteShortStoredWord σ I)
    simpa [evm', storageStore_executionEnv] using hloadPostOwner
  have hflagPost :
      UInt256.land (bytesStoreLiteSetByteShortStoredWord σ I) ⟨1⟩ = ⟨0⟩ := by
    rw [bytesStoreLiteSetByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hvalidPost :
      UInt256.sub (UInt256.land (bytesStoreLiteSetByteShortStoredWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩ := by
    rw [bytesStoreLiteSetByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound]
    rw [bytesStoreLiteSetByteShortStoredWord_shortLen_eq
      (σ := σ) (I := I) (len := len) hshort hbound]
    exact hvalid
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          { base := "current", steps := [] } =
        .ok len.toNat := by
    have hltLen : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by
        simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    have hvalidLen : UInt256.sub ⟨0⟩ (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
      rw [hltLen]
      native_decide
    have hlenPostWord :
        UInt256.land (UInt256.div (bytesStoreLiteSetByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
          len := by
      rw [bytesStoreLiteSetByteShortStoredWord_shortLen_eq
        (σ := σ) (I := I) (len := len) hshort hbound]
      exact hlen.symm
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadPost, hflagPost,
      hlenPostWord, hvalidLen]
  have hpackedPost : checkBytesPacked ⟨0⟩ evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadPost hflagPost
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm' =
        some (uint8Loc ⟨0⟩ ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hidxLe : (bytesStoreLiteSetByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm' (.storage (currentByteRef (.var "index"))) =
          .ok (bytesStoreLiteSetByteValue I) := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetByteResolveOfLength (evm := evm') (I := I) hlenPost hbound]
    simp only [bind, EvalResult.bind]
    rw [Solm.readStorage?.eq_def]
    rw [hlayoutPost]
    simp [uint8St]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := ⟨0⟩) (idx := bytesStoreLiteSetByteIndexWord I)
      (off := ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadPost]
    rw [bytesStoreLiteSetByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound]
    simp [bytesStoreLiteSetByteValue]
  simpa [evm'] using
    bytesStoreLiteSetByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreLiteSetByteLongBodyReturns_of_post_readback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len postHeaderWord : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      bytesStoreLiteCurrentLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I) =
      bytesStoreLiteSetByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hlenPost : len = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body
      (.returned
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I))
        (some (bytesStoreLiteSetByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
        .ok len.toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeader, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked ⟨0⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm') :=
    bytesStoreLiteSetByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          { base := "current", steps := [] } = .ok len.toNat := by
      have hvalidLenPost :
          UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
            (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
        simpa [hlenPost] using hvalidPost
      simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
        bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
        solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeaderPost',
        hflagPost, ← hlenPost, hvalidLenPost]
  have hpackedPost : checkBytesPacked ⟨0⟩ evm' = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeaderPost' hflagPost
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm' =
        some (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetByteLayoutLong (evm := evm') (I := I) hpackedPost
  have hloadDataPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I) =
        bytesStoreLiteSetByteLongStoredWord σ I := by
    simpa [evm', storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc
        (bytesStoreLiteSetByteLongDataSlot I) (bytesStoreLiteSetByteLongStoredWord σ I)
  have hret :
      evalExpr? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm' (.storage (currentByteRef (.var "index"))) =
          .ok (bytesStoreLiteSetByteValue I) := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetByteResolveOfLength (evm := evm') (I := I) hlenPost hbound]
    simp only [bind, EvalResult.bind]
    rw [Solm.readStorage?.eq_def]
    rw [hlayoutPost]
    simp [uint8St]
    rw [storageLocLoad_uint8Loc_byteAt
      (evm := evm') (slot := bytesStoreLiteSetByteLongDataSlot I)
      (idx := bytesStoreLiteSetByteLongWordIndex I)
      (off := ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
        have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
        omega⟩)
      (by rfl)
      (by
        have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
        omega)]
    rw [hloadDataPost]
    rw [bytesStoreLiteSetByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon]
    simp [bytesStoreLiteSetByteValue]
  simpa [evm'] using
    bytesStoreLiteSetByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreLiteSetByteLongBodyReturnsOfPostLongReadback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      bytesStoreLiteCurrentLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I) =
      bytesStoreLiteSetByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body
      (.returned
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I))
        (some (bytesStoreLiteSetByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
        .ok len.toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeader, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked ⟨0⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm') :=
    bytesStoreLiteSetByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          { base := "current", steps := [] } = .ok lenPost.toNat := by
      have hvalidLenPost :
          UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
            (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
        simpa [hlenPost] using hvalidPost
      simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
        bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
        solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeaderPost',
        hflagPost, ← hlenPost, hvalidLenPost]
  have hpackedPost : checkBytesPacked ⟨0⟩ evm' = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeaderPost' hflagPost
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm' =
        some (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetByteLayoutLong (evm := evm') (I := I) hpackedPost
  have hloadDataPost :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I) =
        bytesStoreLiteSetByteLongStoredWord σ I := by
    simpa [evm', storageStore_executionEnv] using
      storageLoad_storageStore_same_present evm evm.executionEnv.codeOwner hacc
        (bytesStoreLiteSetByteLongDataSlot I) (bytesStoreLiteSetByteLongStoredWord σ I)
  have hret :
      evalExpr? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm' (.storage (currentByteRef (.var "index"))) =
          .ok (bytesStoreLiteSetByteValue I) := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetByteResolveOfLength (evm := evm') (I := I)
      hlenPostRead hboundPost]
    simp only [bind, EvalResult.bind]
    rw [Solm.readStorage?.eq_def]
    rw [hlayoutPost]
    simp [uint8St]
    rw [storageLocLoad_uint8Loc_byteAt
      (evm := evm') (slot := bytesStoreLiteSetByteLongDataSlot I)
      (idx := bytesStoreLiteSetByteLongWordIndex I)
      (off := ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
        have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
        omega⟩)
      (by rfl)
      (by
        have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
        omega)]
    rw [hloadDataPost]
    rw [bytesStoreLiteSetByteLongStoredWord_byteAt (σ := σ) (I := I) hcanon]
    simp [bytesStoreLiteSetByteValue]
  simpa [evm'] using
    bytesStoreLiteSetByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem bytesStoreLiteSetByteLongBodyReturnsOfPostShortReadback
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256} {acc : Account}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      bytesStoreLiteCurrentLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I) =
      bytesStoreLiteSetByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord)
    (hacc : evm.accountMap.find? evm.executionEnv.codeOwner = some acc)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hbytePost :
      UInt256.byteAt (bytesStoreLiteSetByteIndexWord I) postHeaderWord =
        bytesStoreLiteSetByteValueWord I) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body
      (.returned
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I))
        (some (bytesStoreLiteSetByteValue I))) := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
        .ok len.toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeader, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked ⟨0⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm') :=
    bytesStoreLiteSetByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          { base := "current", steps := [] } = .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost, hflagPost] using hvalidPost
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeaderPost',
      hflagPost, ← hlenPost, hvalidLenPost]
  have hpackedPost : checkBytesPacked ⟨0⟩ evm' = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hloadHeaderPost' hflagPost
  have hshortPost : lenPost.toNat < 32 := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost, hflagPost] using hvalidPost
    exact solidityShortBytesValid_lt32 hvalidLenPost
  have hidx31 : (bytesStoreLiteSetByteIndexWord I).toNat < 31 :=
    bytesStoreLiteSetByteIndex_lt31_of_short_bound (I := I) (len := lenPost)
      hshortPost hboundPost
  have hlayoutPost :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm' =
        some (uint8Loc ⟨0⟩ ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by omega⟩) :=
    bytesStoreLiteSetByteLayoutShort (evm := evm') (I := I) hpackedPost hidx31
  have hidxLe : (bytesStoreLiteSetByteIndexWord I).toNat ≤ 31 := by
    omega
  have hret :
      evalExpr? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm' (.storage (currentByteRef (.var "index"))) =
          .ok (bytesStoreLiteSetByteValue I) := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetByteResolveOfLength (evm := evm') (I := I)
      hlenPostRead hboundPost]
    simp only [bind, EvalResult.bind]
    rw [Solm.readStorage?.eq_def]
    rw [hlayoutPost]
    simp [uint8St]
    rw [storageLocLoad_uint8Loc_byteAt
      (slot := ⟨0⟩) (idx := bytesStoreLiteSetByteIndexWord I)
      (off := ⟨31 - (bytesStoreLiteSetByteIndexWord I).toNat, by omega⟩)
      (hoff := by rfl) (hidx := hidxLe)]
    rw [hloadHeaderPost']
    rw [hbytePost]
    simp [bytesStoreLiteSetByteValue]
  simpa [evm'] using
    bytesStoreLiteSetByteBodyReturns (evm := evm) (evm' := evm') (I := I)
      hwv hassign hret

theorem uint8ReturnEncoding (v : UInt256) (hcanon : v.toNat < EVM.twoPow 8) :
    encodeReturnValue? uint8 (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  refine scalarReturnEncoding (t := .int uint8Int) (w := v) ?_ ?_ ?_
  · native_decide
  · native_decide
  · simp [uint8Int, encodeABIValue?, encodeABIWord?, hword, hcanon]

theorem bytesStoreLiteSetByteResolveRevertsOfLength {evm : EVM.State} {I : ExecutionEnv}
    {len : Nat}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
      .ok len)
    (hbound : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < len) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
      evm (currentByteRef (.var "index")) = .revert := by
  have hgetIndexElem :
      (bytesStoreLiteSetByteLocals I)["index"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) :=
    bytesStoreLiteSetByteLocals_getElem_index I
  have hgetCurrentElem :
      (bytesStoreLiteSetByteLocals I)["current"]? = none :=
    bytesStoreLiteSetByteLocals_getElem_current_none I
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm { base := "current", steps := [] } = .ok len := by
    simpa [bytesStoreLiteConfig] using hlen
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm (currentByteRef (.var "index")) = .revert := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, currentByteRef,
      hgetIndexElem, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, bytesSt, hlen', hbound]
  have her' :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm { base := "current", steps := [.aindex (.var "index")] } = .revert := by
    simpa [currentByteRef] using her
  rw [resolveStorageRef?]
  simp [currentByteRef, hgetCurrentElem, her']

theorem bytesStoreLiteSetByteBodyBoundsRevertsOfLength {evm : EVM.State} {I : ExecutionEnv}
    {len : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
      .ok len)
    (hbound : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < len) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
  let solm : Frame := { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetByteValue I) := by
    simp [solm, bytesStoreLiteSetByteValue, bytesStoreLiteSetByteLocals, evalExpr?,
      EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) = .revert := by
    rw [assignStorageRef?]
    rw [bytesStoreLiteSetByteResolveRevertsOfLength (I := I) hlen hbound]
    rfl
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetByteResolveRevertsOfLengthRead {evm : EVM.State} {I : ExecutionEnv}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
      .revert) :
    resolveStorageRef? bytesStoreLiteConfig
      { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
      evm (currentByteRef (.var "index")) = .revert := by
  have hgetIndexElem :
      (bytesStoreLiteSetByteLocals I)["index"]? =
        some (.int (Int.ofNat (bytesStoreLiteSetByteIndexWord I).toNat)) :=
    bytesStoreLiteSetByteLocals_getElem_index I
  have hgetCurrentElem :
      (bytesStoreLiteSetByteLocals I)["current"]? = none :=
    bytesStoreLiteSetByteLocals_getElem_current_none I
  have hlen' :
      readStorageBytesLength?
        { storage := bytesStoreLiteStorageLayout, externalABI := defaultExternalCallABI,
          selfDeployment := genSolidityConstructorDeployment [] }
        evm { base := "current", steps := [] } = .revert := by
    simpa [bytesStoreLiteConfig] using hlen
  have her :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm (currentByteRef (.var "index")) = .revert := by
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, currentByteRef,
      hgetIndexElem, valueToKey?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      arrayIndexInBounds?, storageTypeAt?, bytesStoreLiteConfig, bytesStoreLiteContract,
      storageDecls, bytesSt, hlen']
  have her' :
      evalStorageRef bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm { base := "current", steps := [.aindex (.var "index")] } = .revert := by
    simpa [currentByteRef] using her
  rw [resolveStorageRef?]
  simp [currentByteRef, hgetCurrentElem, her']

theorem bytesStoreLiteSetByteBodyRevertsOfLengthRead {evm : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
      .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
  let solm : Frame := { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetByteValue I) := by
    simp [solm, bytesStoreLiteSetByteValue, bytesStoreLiteSetByteLocals, evalExpr?,
      EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) = .revert := by
    rw [assignStorageRef?]
    rw [bytesStoreLiteSetByteResolveRevertsOfLengthRead (I := I) hlen]
    rfl
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetByteBodyReturnReverts {evm evm' : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm'))
    (hret :
      evalExpr? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm' (.storage (currentByteRef (.var "index"))) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
  let solm : Frame := { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
  have hvalue :
      evalExpr? bytesStoreLiteConfig solm evm (.var "value") =
        .ok (bytesStoreLiteSetByteValue I) := by
    simp [solm, bytesStoreLiteSetByteValue, bytesStoreLiteSetByteLocals, evalExpr?,
      EvalResult.ofOption]
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm evm .storage
        (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok (solm, evm') := by
    simpa [solm] using hassign
  have hret :
      evalExpr? bytesStoreLiteConfig solm evm'
        (.storage (currentByteRef (.var "index"))) = .revert := by
    simpa [solm] using hret
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consRevert (ExecStmt.returnRevert hret)

theorem bytesStoreLiteSetByteBodyReturnRevertsOfPostLengthRead
    {evm evm' : EVM.State} {I : ExecutionEnv}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm'))
    (hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm' { base := "current", steps := [] } =
        .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
  have hret :
      evalExpr? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm' (.storage (currentByteRef (.var "index"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetByteResolveRevertsOfLengthRead (evm := evm') (I := I) hlenPost]
    rfl
  exact bytesStoreLiteSetByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreLiteSetByteBodyReturnRevertsOfPostLongMalformed
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      bytesStoreLiteCurrentLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I) =
      bytesStoreLiteSetByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
        .ok len.toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeader, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked ⟨0⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm') :=
    bytesStoreLiteSetByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨0⟩ = postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          { base := "current", steps := [] } = .revert := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeaderPost',
      hflagPost, hbadPost]
  exact bytesStoreLiteSetByteBodyReturnRevertsOfPostLengthRead
    (evm := evm) (evm' := evm') (I := I) hwv hassign hlenPost

theorem bytesStoreLiteSetByteBodyReturnRevertsOfPostShortMalformed
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      bytesStoreLiteCurrentLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I) =
      bytesStoreLiteSetByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
        .ok len.toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeader, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked ⟨0⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm') :=
    bytesStoreLiteSetByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨0⟩ = postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hlenPost :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          { base := "current", steps := [] } = .revert := by
    have hbadPost0 :
        UInt256.sub ⟨0⟩
          (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) =
            ⟨0⟩ := by
      simpa [hflagPost] using hbadPost
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeaderPost',
      hflagPost, hbadPost0]
  exact bytesStoreLiteSetByteBodyReturnRevertsOfPostLengthRead
    (evm := evm) (evm' := evm') (I := I) hwv hassign hlenPost

theorem bytesStoreLiteSetByteLongBodyReturnRevertsOfPostShortLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      bytesStoreLiteCurrentLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I) =
      bytesStoreLiteSetByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div postHeaderWord ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
        .ok len.toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeader, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked ⟨0⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm') :=
    bytesStoreLiteSetByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          { base := "current", steps := [] } = .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost, hflagPost] using hvalidPost
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeaderPost',
      hflagPost, ← hlenPost, hvalidLenPost]
  have hret :
      evalExpr? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm' (.storage (currentByteRef (.var "index"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetByteResolveRevertsOfLength
      (evm := evm') (I := I) hlenPostRead hboundPost]
    rfl
  exact bytesStoreLiteSetByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

theorem bytesStoreLiteSetByteLongBodyReturnRevertsOfPostLongLength
    {evm : EVM.State} {σ : AccountMap} {I : ExecutionEnv}
    {len lenPost postHeaderWord : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hloadHeader : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ =
      bytesStoreLiteCurrentLengthHeaderWord σ I)
    (hloadData : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetByteLongDataSlot I) =
      bytesStoreLiteSetByteLongOldWord σ I)
    (hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I))
          evm.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hlenPost : lenPost = UInt256.div postHeaderWord ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land postHeaderWord ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
        (UInt256.lt (UInt256.div postHeaderWord ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
  let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  have hloadHeaderPost' :
      Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨0⟩ =
        postHeaderWord := by
    simpa [evm', storageStore_executionEnv] using hloadHeaderPost
  have hvalidLen :
      UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlen] using hvalid
  have hlenRead :
      readStorageBytesLength? bytesStoreLiteConfig evm { base := "current", steps := [] } =
        .ok len.toNat := by
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeader, hflag, ← hlen,
      hvalidLen]
  have hpacked : checkBytesPacked ⟨0⟩ evm = false :=
    checkBytesPacked_of_storageLoad_land_one_ne_zero hloadHeader hflag
  have hlayout :
      bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm =
        some (uint8Loc (bytesStoreLiteSetByteLongDataSlot I)
          ⟨31 - (bytesStoreLiteSetByteLongWordIndex I).toNat, by
            have hidx := bytesStoreLiteSetByteLongWordIndex_lt32 I
            omega⟩) :=
    bytesStoreLiteSetByteLayoutLong (evm := evm) (I := I) hpacked
  have hstore :
      (match bytesStoreLiteConfig.storage.layout (bytesStoreLiteSetByteRef I) evm with
      | some loc => storageLocStore evm loc (bytesStoreLiteSetByteValue I)
      | none => none) = some evm' := by
    rw [hlayout]
    simpa [evm'] using
      bytesStoreLiteSetByteStorageLocStoreLong
        (evm := evm) (σ := σ) (I := I) hloadData hcanon
  have hassign :
      assignStorageRef? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm .storage (currentByteRef (.var "index")) (bytesStoreLiteSetByteValue I) =
          .ok ({ contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I },
            evm') :=
    bytesStoreLiteSetByteAssignOfLength (evm := evm) (evm' := evm') (I := I)
      hlenRead hbound hstore
  have hlenPostRead :
      readStorageBytesLength? bytesStoreLiteConfig evm'
          { base := "current", steps := [] } = .ok lenPost.toNat := by
    have hvalidLenPost :
        UInt256.sub (UInt256.land postHeaderWord ⟨1⟩)
          (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [hlenPost] using hvalidPost
    simp [readStorageBytesLength?, storageNatResultToEval, bytesStoreLiteConfig,
      bytesStoreLiteStorageLayout, solidityStorageLayout, solidityReadBytesLength?,
      solidityDecodeBytesLengthHeader, bytesStoreLiteLayout, hloadHeaderPost',
      hflagPost, ← hlenPost, hvalidLenPost]
  have hret :
      evalExpr? bytesStoreLiteConfig
        { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
        evm' (.storage (currentByteRef (.var "index"))) = .revert := by
    rw [evalExpr?]
    rw [bytesStoreLiteSetByteResolveRevertsOfLength
      (evm := evm') (I := I) hlenPostRead hboundPost]
    rfl
  exact bytesStoreLiteSetByteBodyReturnReverts
    (evm := evm) (evm' := evm') (I := I) hwv hassign hret

private theorem bytesStoreLiteSetByteUint8CanonEqGuard {w : UInt256}
    (h : UInt256.land w ⟨255⟩ = w) :
    UInt256.eq w (UInt256.land w ⟨255⟩) = ⟨1⟩ := by
  rw [h]
  exact u256_eq_refl w

private theorem bytesStoreLiteSetByteUint8NoncanonEqGuard {w : UInt256}
    (h : UInt256.land w ⟨255⟩ ≠ w) :
    UInt256.eq w (UInt256.land w ⟨255⟩) = ⟨0⟩ := by
  exact u256_eq_of_ne (by
    intro hw
    exact h hw.symm)

private theorem bytesStoreLiteSetByteLand255_toNat (w : UInt256) :
    (UInt256.land w ⟨255⟩).toNat = w.toNat % EVM.twoPow 8 := by
  change Nat.land w.toNat (⟨255⟩ : UInt256).toNat % EVM.twoPow 256 =
    w.toNat % EVM.twoPow 8
  rw [show (⟨255⟩ : UInt256).toNat = 255 from by decide,
    show (255 : Nat) = 2 ^ 8 - 1 from by decide,
    nat_land_mask_eq_mod]
  have hlt : w.toNat % 2 ^ 8 < EVM.twoPow 256 := by
    exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 8)) (by
      norm_num [EVM.twoPow])
  rw [Nat.mod_eq_of_lt hlt]
  rw [show EVM.twoPow 8 = 2 ^ 8 from by decide]

private theorem bytesStoreLiteSetByteLand255_eq_self_of_uint8 {w : UInt256}
    (h : w.toNat < EVM.twoPow 8) :
    UInt256.land w ⟨255⟩ = w := by
  apply u256_inj
  rw [bytesStoreLiteSetByteLand255_toNat]
  exact Nat.mod_eq_of_lt h

private theorem bytesStoreLiteSetByteLand255_ne_self_of_not_uint8 {w : UInt256}
    (h : ¬ w.toNat < EVM.twoPow 8) :
    UInt256.land w ⟨255⟩ ≠ w := by
  intro hland
  apply h
  have hnat : (UInt256.land w ⟨255⟩).toNat = w.toNat := by
    rw [hland]
  rw [bytesStoreLiteSetByteLand255_toNat] at hnat
  rw [← hnat]
  exact Nat.mod_lt _ (by decide : 0 < EVM.twoPow 8)

theorem bytesStoreLiteX_setByteDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨357⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hcanon : UInt256.land (bytesStoreLiteSetByteValueWord I) ⟨255⟩ =
      bytesStoreLiteSetByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1011⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd357⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have rd1967 := evm_run rd357 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨371⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1967⟩, jump (by native_decide)]
  have rd1984 := evm_run rd1967 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1984⟩, jumpiT (by rw [hslt]; decide) (by native_decide)]
  have rd1946 := evm_run rd1984 with [
    jumpdest, dup3, calldataload, swap2, pop, push2 ⟨2000⟩, push1 ⟨32⟩,
    dup5, add, push2 ⟨1946⟩, jump (by native_decide)]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 4 32) =
      bytesStoreLiteSetByteIndexWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 36 32) =
      bytesStoreLiteSetByteValueWord I from rfl] at rd1950
  have rd2000 := evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiT (by rw [bytesStoreLiteSetByteUint8CanonEqGuard hcanon]; decide) (by native_decide),
    jumpdest, swap2, swap1, pop, jump (by native_decide)]
  exact ⟨_, _, evm_run rd2000 with [
    jumpdest, swap1, pop, swap3, pop, swap3, swap1, pop, jump (by native_decide),
    jumpdest, push2 ⟨1011⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setByteDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨357⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd357⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  have rd1967 := evm_run rd357 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨371⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1967⟩, jump (by native_decide)]
  exact evm_run rd1967 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1984⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setByteDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨357⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd357⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  have rd1967 := evm_run rd357 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨371⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1967⟩, jump (by native_decide)]
  exact evm_run rd1967 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1984⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setByteDecodeNoncanonValue {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨357⟩ [bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hnc : UInt256.land (bytesStoreLiteSetByteValueWord I) ⟨255⟩ ≠
      bytesStoreLiteSetByteValueWord I) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd357⟩ := hreach
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have rd1967 := evm_run rd357 with [
    jumpdest, push2 ⟨301⟩, push2 ⟨371⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨1967⟩, jump (by native_decide)]
  have rd1984 := evm_run rd1967 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero,
    push2 ⟨1984⟩, jumpiT (by rw [hslt]; decide) (by native_decide)]
  have rd1946 := evm_run rd1984 with [
    jumpdest, dup3, calldataload, swap2, pop, push2 ⟨2000⟩, push1 ⟨32⟩,
    dup5, add, push2 ⟨1946⟩, jump (by native_decide)]
  rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 4 32) =
      bytesStoreLiteSetByteIndexWord I from rfl,
    show (⟨4⟩ + ⟨32⟩ : UInt256) = ⟨36⟩ from by native_decide] at rd1946
  have rd1950 := evm_run rd1946 with [
    jumpdest, dup1, calldataload]
  rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide,
    show uInt256OfByteArray (I.calldata.readBytes 36 32) =
      bytesStoreLiteSetByteValueWord I from rfl] at rd1950
  exact evm_run rd1950 with [
    push1 ⟨255⟩, dup2, and, dup2, eq,
    push2 ⟨1962⟩,
    jumpiNT (by rw [bytesStoreLiteSetByteUint8NoncanonEqGuard hnc]),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setByteReachLengthDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1011⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteCurrentLengthHeaderWord σ I, ⟨1029⟩,
        bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1011⟩ := hreach
  have rd1020 := evm_run rd1011 with [
    jumpdest, push0, dup2, push1 ⟨248⟩, shl, push0, dup5, dup2]
  obtain ⟨_, _, rd1021₀⟩ := rd1020.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1021⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1021⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1021₀⟩
  exact ⟨_, _, evm_run rd1021 with [
    push2 ⟨1029⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setByteOobAfterLength {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1029⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd1029 with [
    jumpdest, dup2, lt, push2 ⟨1043⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨1043⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreLiteX_panic32Mem ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_panic32MemFromReachSetByte
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {stk : List UInt256} {mem : ByteArray}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2579⟩ stk
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hov : stk.length + 3 ≤ 1024) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd2579⟩ := hreach
  have hsel :
      UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
        bytesStoreLiteFullPanicSelectorWord := by
    decide
  have rd2591₀ := evm_run rd2579 with [
    jumpdest, push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl, push0]
  have rd2591 := rd2591₀
  rw [hsel] at rd2591
  exact evm_run rd2591 with [
    raw mstore 0 (bytesStoreLiteFullPanic22Mem1From mem) (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨0x32⟩, push1 ⟨4⟩,
    raw mstore 0 (bytesStoreLiteFullPanicMemFrom ⟨0x32⟩ mem) (UInt256.ofNat 3)
      (by native_decide)
      mem_cost
      (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; rfl)
      (by decide) (by evm_ov),
    push1 ⟨36⟩, push0,
    raw rev 0 (by native_decide) mem_cost
      (by evm_ov)]

theorem bytesStoreLiteX_setByteReturnOobLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨709⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σinit σ₀ g A I) := by
  obtain ⟨_, _, rd709⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨0⟩ :=
    ult_zero (by omega)
  have rd2579 := evm_run rd709 with [
    jumpdest, dup2, lt, push2 ⟨723⟩,
    jumpiNT (by simpa using hlt),
    push2 ⟨723⟩, push2 ⟨2579⟩, jump (by native_decide)]
  exact bytesStoreLiteX_panic32MemFromReachSetByte ⟨_, _, rd2579⟩
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem u256_land_one_eq_one_of_ne_zero {header : UInt256}
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩) :
    UInt256.land header ⟨1⟩ = ⟨1⟩ := by
  have hbit := uInt256_land_one_toNat header
  have hlt : (UInt256.land header ⟨1⟩).toNat < 2 := by
    rw [hbit]
    exact Nat.mod_lt _ (by decide)
  have hnz : (UInt256.land header ⟨1⟩).toNat ≠ 0 := by
    intro hzero
    apply hflag
    rw [← u256_ofNat_toNat (UInt256.land header ⟨1⟩), hzero]
    rfl
  have hone : (UInt256.land header ⟨1⟩).toNat = 1 := by
    omega
  rw [← u256_ofNat_toNat (UInt256.land header ⟨1⟩), hone]
  rfl

theorem bytesStoreLiteSetByteLongBaseHash :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem (⟨0⟩ : UInt256) solcFreePtrMem).readWithPadding 0 32))) =
      bytesLikeDataBase ⟨0⟩ := by
  rw [wordAt0Mem_read0]
  simpa [bytesLikeDataBase] using keccakSlot_eq (UInt256.toByteArray (⟨0⟩ : UInt256))

theorem wordAt0Mem_zero_solcFreePtrMem :
    wordAt0Mem (⟨0⟩ : UInt256) solcFreePtrMem = solcFreePtrMem := by
  unfold wordAt0Mem solcFreePtrMem
  native_decide

theorem bytesStoreLiteX_setByteLongReachStoreCommon {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1072⟩
      [bytesStoreLiteSetByteLongWordIndex I, bytesStoreLiteSetByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1029⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne :
      UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreLiteSetByteLongBaseHash
  have rd1043 := evm_run rd1029 with [
    jumpdest, dup2, lt, push2 ⟨1043⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd1045 := evm_run rd1043 with [jumpdest, dup2]
  obtain ⟨_, _, rd1046₀⟩ := rd1045.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1046⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1046⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1046₀⟩
  have rd1071 := evm_run rd1046 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨1072⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (⟨0⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd1072 := RD.mod rd1071 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by
    simpa [bytesStoreLiteSetByteLongWordIndex, bytesStoreLiteSetByteLongDataSlot,
      wordAt0Mem_zero_solcFreePtrMem,
      u256_add_comm (UInt256.div (bytesStoreLiteSetByteIndexWord I) ⟨32⟩)
        (bytesLikeDataBase ⟨0⟩)] using rd1072⟩

theorem bytesStoreLiteX_setByteShortReachStoreCommon {cA gh bl σ σ₀ A I} {g : Sat256}
    {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1072⟩
      [bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1029⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd1043 := evm_run rd1029 with [
    jumpdest, dup2, lt, push2 ⟨1043⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd1045 := evm_run rd1043 with [jumpdest, dup2]
  obtain ⟨_, _, rd1046₀⟩ := rd1045.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1046⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1046⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1046₀⟩
  have rd1072 := evm_run rd1046 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨1072⟩,
    jumpiT (by
      rw [u256_land_comm, hflag]
      decide)
      (by native_decide)]
  exact ⟨_, _, rd1072⟩

theorem bytesStoreLiteX_setByteShortStoreCurrent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1072⟩
      [bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1101⟩
      [⟨0⟩, bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
        (bytesStoreLiteSetByteShortStoredWord σ I)) k C := by
  obtain ⟨_, _, rd1072⟩ := hreach
  have rd1081 := evm_run rd1072 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd1082₀⟩ := rd1081.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1082⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1082⟩
        [bytesStoreLiteCurrentLengthHeaderWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetByteIndexWord I)),
          ⟨0⟩, UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteCurrentLengthHeaderWord, initState] using rd1082₀⟩
  have rd1099 := evm_run rd1082 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd1099'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1099⟩
        [⟨0⟩,
          bytesStoreLiteSetByteShortStoredWord σ I,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetByteShortStoredWord, bytesStoreLiteSetByteShortScale] using rd1099⟩
  obtain ⟨_, _, rd1100₀⟩ := rd1099'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1100⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1100⟩
        [UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
          (bytesStoreLiteSetByteShortStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd1100₀⟩
  exact ⟨_, _, evm_run rd1100 with [pop]⟩

theorem bytesStoreLiteX_setByteLongStoreCurrent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1072⟩
      [bytesStoreLiteSetByteLongWordIndex I, bytesStoreLiteSetByteLongDataSlot I,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1101⟩
      [⟨0⟩, bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I)) k C := by
  obtain ⟨_, _, rd1072⟩ := hreach
  have rd1081 := evm_run rd1072 with [
    jumpdest, push1 ⟨31⟩, sub, push2 ⟨256⟩, exp, dup2]
  obtain ⟨_, _, rd1082₀⟩ := rd1081.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1082⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1082⟩
        [bytesStoreLiteSetByteLongOldWord σ I,
          UInt256.exp ⟨256⟩ (UInt256.sub ⟨31⟩ (bytesStoreLiteSetByteLongWordIndex I)),
          bytesStoreLiteSetByteLongDataSlot I,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetByteLongOldWord, initState] using rd1082₀⟩
  have rd1099 := evm_run rd1082 with [
    dup2, push1 ⟨255⟩, mul, not, and, swap1,
    push1 ⟨1⟩, push1 ⟨248⟩, shl, dup5, div, mul, lor, swap1]
  obtain ⟨_, _, rd1099'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1099⟩
        [bytesStoreLiteSetByteLongDataSlot I,
          bytesStoreLiteSetByteLongStoredWord σ I,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetByteLongStoredWord, bytesStoreLiteSetByteLongScale] using rd1099⟩
  obtain ⟨_, _, rd1100₀⟩ := rd1099'.sstore hperm (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1100⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1100⟩
        [UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) k C := by
    exact ⟨_, _, by simpa [sstoreAccountMap, initState] using rd1100₀⟩
  exact ⟨_, _, evm_run rd1100 with [pop]⟩

theorem bytesStoreLiteX_setByteReturnReachLengthDecoder {cA gh bl σinit σ σ₀ A I}
    {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1101⟩
      [⟨0⟩, bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨0⟩ ⟨0⟩)
          (Batteries.RBMap.find? σ I.codeOwner),
        ⟨709⟩,
        bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1101⟩ := hreach
  have rd1104 := evm_run rd1101 with [push0, dup4, dup2]
  obtain ⟨_, _, rd1105₀⟩ := rd1104.sload (by native_decide) (by evm_ov)
  have rd2246 := evm_run rd1105₀ with [
    push2 ⟨709⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]
  exact ⟨_, _, rd2246⟩

theorem bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried {cA gh bl σinit τ σ₀ A I}
    {g : Sat256} {header ret : UInt256} {rest : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      (header :: ret :: rest) mem aw rdata (cA, τ) k C)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : rest.length + 6 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret
      (UInt256.div header ⟨2⟩ :: rest)
      mem aw rdata (cA, τ) k C := by
  obtain ⟨_, _, rd2246⟩ := hreach
  have rd2259 := evm_run rd2246 with [
    jumpdest, push1 ⟨1⟩, dup2, dup2, shr, swap1, dup3, and, dup1, push2 ⟨2266⟩]
  have rd2266 := rd2259.jumpiT (by native_decide) hflag (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2288 := evm_run rd2266 with [
    jumpdest, push1 ⟨32⟩, dup3, lt, dup2, sub, push2 ⟨2296⟩]
  rw [bytesStoreLite_shiftRight_one_eq_div_two] at rd2288
  have rd2296 := rd2288.jumpiT (by native_decide) hvalid (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd2296 with [
    jumpdest, pop, swap2, swap1, pop, raw jump (by native_decide) hret
      (by simp only [List.length_cons]; omega)]⟩

theorem bytesStoreLiteX_setByteShortWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨0⟩ ⟨0⟩)
          (Batteries.RBMap.find?
            (sstoreAccountMap I.codeOwner σ ⟨0⟩
              (bytesStoreLiteSetByteShortStoredWord σ I)) I.codeOwner),
        ⟨709⟩, bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
        (bytesStoreLiteSetByteShortStoredWord σ I)) k C := by
  have h1072 := bytesStoreLiteX_setByteShortReachStoreCommon
    (g := g) hreach hbound hflag
  have h1101 := bytesStoreLiteX_setByteShortStoreCurrent
    (g := g) h1072 hperm
  exact bytesStoreLiteX_setByteReturnReachLengthDecoder
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨0⟩
      (bytesStoreLiteSetByteShortStoredWord σ I))
    h1101

theorem bytesStoreLiteX_setByteShortWriteReturnDecodedLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨709⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
        (bytesStoreLiteSetByteShortStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ ⟨0⟩
    (bytesStoreLiteSetByteShortStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨0⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setByteShortWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hnz := bytesStoreLiteSetByteShortStoredWord_beq_zero_false
    (σ := σ) (I := I) (len := len) hlen hshort hbound
  have hheader : header' = bytesStoreLiteSetByteShortStoredWord σ I := by
    simpa [header', σ'] using
      bytesStoreLiteSetByteShortStoredWord_load_self (σ := σ) (I := I) (acc := acc)
        hacc hnz
  have hflag' : UInt256.land header' ⟨1⟩ = ⟨0⟩ := by
    rw [hheader, bytesStoreLiteSetByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hvalid' : UInt256.sub (UInt256.land header' ⟨1⟩)
      (UInt256.lt (UInt256.land (UInt256.div header' ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    rw [hheader, bytesStoreLiteSetByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound,
      bytesStoreLiteSetByteShortStoredWord_shortLen_eq
        (σ := σ) (I := I) (len := len) hshort hbound]
    exact hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
      bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header', σ'] using hdec) hflag' hvalid' (by native_decide)
    (by simp)
  have hlen' :
      UInt256.land (UInt256.div (bytesStoreLiteSetByteShortStoredWord σ I) ⟨2⟩) ⟨127⟩ =
        len := by
    rw [bytesStoreLiteSetByteShortStoredWord_shortLen_eq
      (σ := σ) (I := I) (len := len) hshort hbound, ← hlen]
  simpa [σ', header', hheader, hlen'] using hdecoded

theorem bytesStoreLiteX_setByteLongWriteReturnReachLengthDecoder
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      [Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨0⟩ ⟨0⟩)
          (Batteries.RBMap.find?
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I.codeOwner),
        ⟨709⟩, bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I)) k C := by
  have h1072 := bytesStoreLiteX_setByteLongReachStoreCommon
    (g := g) hreach hbound hflag
  have h1101 := bytesStoreLiteX_setByteLongStoreCurrent
    (g := g) h1072 hperm
  exact bytesStoreLiteX_setByteReturnReachLengthDecoder
    (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
      (bytesStoreLiteSetByteLongStoredWord σ I))
    h1101

theorem bytesStoreLiteX_setByteLongWriteReturnDecodedLength_of_post_header
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlenPost : len = UInt256.div
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨709⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨0⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
      bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header', σ'] using hdec)
    (by simpa [header', σ', bytesStoreLiteCurrentLengthHeaderWord] using hflagPost)
    (by simpa [header', σ', bytesStoreLiteCurrentLengthHeaderWord] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ', header', bytesStoreLiteCurrentLengthHeaderWord, hlenPost] using hdecoded

theorem bytesStoreLiteX_setByteLongWriteReturnDecodedPostLongLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨709⟩
      [lenPost, bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨0⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hdec := bytesStoreLiteX_setByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
      bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header', σ'] using hdec)
    (by simpa [header', σ', bytesStoreLiteCurrentLengthHeaderWord] using hflagPost)
    (by simpa [header', σ', bytesStoreLiteCurrentLengthHeaderWord] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ', header', bytesStoreLiteCurrentLengthHeaderWord, hlenPost] using hdecoded

theorem bytesStoreLiteX_setByteLongWriteReturnLongMalformed
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) = ⟨0⟩)
    (hperm : I.perm = true) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  have hdec := bytesStoreLiteX_setByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreLiteCurrentLengthHeaderWord σ' I) (ret := ⟨709⟩)
    (rest := [bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
      bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hbadPost)
    (by simp)

theorem bytesStoreLiteX_setByteLongWriteReturnShortMalformed
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div
            (bytesStoreLiteCurrentLengthHeaderWord
              (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
                (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩)
    (hperm : I.perm = true) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  have hdec := bytesStoreLiteX_setByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreLiteCurrentLengthHeaderWord σ' I) (ret := ⟨709⟩)
    (rest := [bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
      bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem)
    (by simpa [σ'] using hdec)
    (by simpa [σ'] using hflagPost)
    (by simpa [σ'] using hbadPost)
    (by simp)

theorem bytesStoreLiteX_setByteShortReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨709⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetByteIndexWord I) header)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd709⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have rd723 := evm_run rd709 with [
    jumpdest, dup2, lt, push2 ⟨723⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd725 := evm_run rd723 with [jumpdest, dup2]
  obtain ⟨_, _, rd725'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨726⟩
        [header, bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    obtain ⟨_, _, rd725₀⟩ := rd725.sload (by native_decide) (by evm_ov)
    exact ⟨_, _, by simpa [initState, hheader] using rd725₀⟩
  have rd752 := evm_run rd725' with [
    push1 ⟨1⟩, and, iszero, push2 ⟨752⟩,
    jumpiT (by
      rw [u256_land_comm, hflag]
      decide)
      (by native_decide)]
  have rd771 := evm_run rd752 with [
    jumpdest, swap1]
  obtain ⟨_, _, rd755'⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨755⟩
        [header, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    obtain ⟨_, _, rd755₀⟩ := rd771.sload (by native_decide) (by evm_ov)
    exact ⟨_, _, by simpa [initState, hheader] using rd755₀⟩
  have rd761 := evm_run rd755' with [
    push1 ⟨1⟩, push1 ⟨248⟩, shl, swap2]
  have rd762 := RD.byte rd761 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := evm_run rd762 with [
    mul, push1 ⟨248⟩, shr,
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  exact ⟨_, _, by simpa [hbyte] using rd301⟩

theorem bytesStoreLiteX_setByteLongReadReturnToWrapper
    {cA gh bl σinit τ σ₀ A I} {g : Sat256} {len header dataWord : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨709⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hheader :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hdata :
      ((τ.find? I.codeOwner).option ⟨0⟩
        (fun acc => acc.storage.findD (bytesStoreLiteSetByteLongDataSlot I) ⟨0⟩)) = dataWord)
    (hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetByteLongWordIndex I) dataWord)
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetByteValueWord I) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨301⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
  obtain ⟨_, _, rd709⟩ := hreach
  have hlt : UInt256.lt (bytesStoreLiteSetByteIndexWord I) len = ⟨1⟩ :=
    ult_one hbound
  have hflagOne : UInt256.land header ⟨1⟩ = ⟨1⟩ :=
    u256_land_one_eq_one_of_ne_zero hflag
  have hslot := bytesStoreLiteSetByteLongBaseHash
  have rd723 := evm_run rd709 with [
    jumpdest, dup2, lt, push2 ⟨723⟩,
    jumpiT (by rw [hlt]; decide) (by native_decide)]
  have rd725 := evm_run rd723 with [jumpdest, dup2]
  obtain ⟨_, _, rd726₀⟩ := rd725.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd726⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨726⟩
        [header, bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hheader] using rd726₀⟩
  have rd751 := evm_run rd726 with [
    push1 ⟨1⟩, and, iszero, push2 ⟨752⟩,
    jumpiNT (by
      rw [u256_land_comm, hflagOne]
      decide),
    swap1, push0,
    raw mstore 0 (wordAt0Mem (⟨0⟩ : UInt256) solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, push0,
    raw keccak256 0 (bytesLikeDataBase ⟨0⟩) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    swap1, push1 ⟨32⟩, swap2, dup3, dup3, div, add, swap2, swap1]
  have rd752raw := RD.mod rd751 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd752⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨752⟩
        [bytesStoreLiteSetByteLongWordIndex I, bytesStoreLiteSetByteLongDataSlot I, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by
      simpa [bytesStoreLiteSetByteLongWordIndex, bytesStoreLiteSetByteLongDataSlot,
        wordAt0Mem_zero_solcFreePtrMem,
        u256_add_comm (UInt256.div (bytesStoreLiteSetByteIndexWord I) ⟨32⟩)
          (bytesLikeDataBase ⟨0⟩)] using rd752raw⟩
  have rd754 := evm_run rd752 with [jumpdest, swap1]
  obtain ⟨_, _, rd755₀⟩ := rd754.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd755⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨755⟩
        [dataWord, bytesStoreLiteSetByteLongWordIndex I, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, τ) k C := by
    exact ⟨_, _, by simpa [initState, hdata] using rd755₀⟩
  have rd761 := evm_run rd755 with [
    push1 ⟨1⟩, push1 ⟨248⟩, shl, swap2]
  have rd762 := RD.byte rd761 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := evm_run rd762 with [
    mul, push1 ⟨248⟩, shr,
    swap4, swap3, pop, pop, pop, jump (by native_decide)]
  exact ⟨_, _, by simpa [hbyte] using rd301⟩

theorem bytesStoreLiteX_setByteShortSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨0⟩
        (bytesStoreLiteSetByteShortStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ ⟨0⟩
    (bytesStoreLiteSetByteShortStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨0⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hread := bytesStoreLiteX_setByteShortWriteReturnDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (acc := acc) hreach hlen hshort hbound
    hflag hvalid hperm hacc
  have hnz := bytesStoreLiteSetByteShortStoredWord_beq_zero_false
    (σ := σ) (I := I) (len := len) hlen hshort hbound
  have hheader : header' = bytesStoreLiteSetByteShortStoredWord σ I := by
    simpa [header', σ'] using
      bytesStoreLiteSetByteShortStoredWord_load_self (σ := σ) (I := I) (acc := acc)
        hacc hnz
  have hflag' : UInt256.land header' ⟨1⟩ = ⟨0⟩ := by
    rw [hheader, bytesStoreLiteSetByteShortStoredWord_flag_eq
      (σ := σ) (I := I) (len := len) hshort hbound, hflag]
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetByteIndexWord I) header' =
        bytesStoreLiteSetByteValueWord I := by
    rw [hheader]
    exact bytesStoreLiteSetByteShortStoredWord_byteAt
      (σ := σ) (I := I) (len := len) hcanon hshort hbound
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetByteIndexWord I) header')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetByteValueHighMulShiftRight hcanon
  have h301 := bytesStoreLiteX_setByteShortReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header') hread hbound
    (by rfl) hflag' hbyte
  have hret := bytesStoreLiteX_returnUInt8_301
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetByteValueWord I) h301
  simpa [σ', bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreLiteX_setByteLongWriteReturnDecodedShortLength
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hperm : I.perm = true) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨709⟩
      [UInt256.land (UInt256.div
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩,
        bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I)) k C := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  let header' := bytesStoreLiteCurrentLengthHeaderWord σ' I
  have hdec := bytesStoreLiteX_setByteLongWriteReturnReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hperm
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header') (ret := ⟨709⟩)
    (rest := [bytesStoreLiteSetByteIndexWord I, ⟨0⟩, ⟨0⟩,
      bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [σ', header'] using hdec)
    (by simpa [σ', header'] using hflagPost)
    (by simpa [σ', header'] using hvalidPost)
    (by native_decide)
    (by simp)
  simpa [σ', header'] using hdecoded

theorem bytesStoreLiteX_setByteLongShortSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨0⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hread := bytesStoreLiteX_setByteLongWriteReturnDecodedShortLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len)
    hreach hbound hflag hflagPost hvalidPost hperm
  have hheaderStored : header' = bytesStoreLiteSetByteLongStoredWord σ I := by
    by_cases hEq : (⟨0⟩ : UInt256) = bytesStoreLiteSetByteLongDataSlot I
    · simpa [header', σ', bytesStoreLiteCurrentLengthHeaderWord, hEq.symm] using
        sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
          (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I) hacc
    · have hheaderOld :
          bytesStoreLiteCurrentLengthHeaderWord σ' I =
            bytesStoreLiteCurrentLengthHeaderWord σ I := by
        simpa [σ', bytesStoreLiteCurrentLengthHeaderWord, bytesStoreLiteSetByteLongDataSlot] using
          bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
            (σ := σ) (I := I) (baseSlot := ⟨0⟩)
            (idx := bytesStoreLiteSetByteIndexWord I)
            (val := bytesStoreLiteSetByteLongStoredWord σ I) hEq (by rfl)
      have hzeroOld :
          UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩ := by
        rw [← hheaderOld]
        simpa [σ', header', bytesStoreLiteCurrentLengthHeaderWord] using hflagPost
      exact False.elim (hflag hzeroOld)
  have hvalid0 :
      UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlenPost, hflagPost] using hvalidPost
  have hshortPost : lenPost.toNat < 32 :=
    solidityShortBytesValid_lt32 hvalid0
  have hidxLt32 : (bytesStoreLiteSetByteIndexWord I).toNat < 32 :=
    lt_trans hboundPost hshortPost
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetByteIndexWord I) header' =
        bytesStoreLiteSetByteValueWord I := by
    rw [hheaderStored]
    exact bytesStoreLiteSetByteLongStoredWord_byteAt_index_of_lt32
      (σ := σ) (I := I) hcanon hidxLt32
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetByteIndexWord I) header')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetByteValueHighMulShiftRight hcanon
  have h301 := bytesStoreLiteX_setByteShortReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := lenPost) (header := header')
    (by simpa [hlenPost] using hread) hboundPost (by rfl)
    (by simpa [header', σ'] using hflagPost) hbyte
  have hret := bytesStoreLiteX_returnUInt8_301
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetByteValueWord I) h301
  simpa [σ', bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreLiteX_setByteLongLongSuccessReturn
    {cA gh bl σ σ₀ A I} {g : Sat256} {len lenPost : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨0⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  let dataWord' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreLiteSetByteLongDataSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hread := bytesStoreLiteX_setByteLongWriteReturnDecodedPostLongLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (lenPost := lenPost)
    hreach hbound hflag hlenPost hflagPost hvalidPost hperm
  have hheader : header' = bytesStoreLiteCurrentLengthHeaderWord σ' I := by
    rfl
  have hdata : dataWord' = bytesStoreLiteSetByteLongStoredWord σ I := by
    simpa [dataWord', σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetByteLongWordIndex I) dataWord' =
        bytesStoreLiteSetByteValueWord I := by
    rw [hdata]
    exact bytesStoreLiteSetByteLongStoredWord_byteAt
      (σ := σ) (I := I) hcanon
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetByteLongWordIndex I) dataWord')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetByteValueHighMulShiftRight hcanon
  have h301 := bytesStoreLiteX_setByteLongReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := lenPost) (header := header')
    (dataWord := dataWord') hread hboundPost (by rfl)
    (by simpa [hheader, σ'] using hflagPost) (by rfl) hbyte
  have hret := bytesStoreLiteX_returnUInt8_301
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetByteValueWord I) h301
  simpa [σ', bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreLiteX_setByteLongSuccessReturn_of_post_header
    {cA gh bl σ σ₀ A I} {g : Sat256} {len : UInt256} {acc : Account}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1029⟩
      [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
        UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
        bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hlenPost : len = UInt256.div
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I))
      (UInt256.toByteArray (bytesStoreLiteSetByteValueWord I)) := by
  let σ' := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
    (bytesStoreLiteSetByteLongStoredWord σ I)
  let header' : UInt256 :=
    Option.option ⟨0⟩ (fun ac => Batteries.RBMap.findD ac.storage ⟨0⟩ ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  let dataWord' : UInt256 :=
    Option.option ⟨0⟩
      (fun ac => Batteries.RBMap.findD ac.storage (bytesStoreLiteSetByteLongDataSlot I) ⟨0⟩)
      (Batteries.RBMap.find? σ' I.codeOwner)
  have hread := bytesStoreLiteX_setByteLongWriteReturnDecodedLength_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) hreach hbound hflag hlenPost hflagPost
    hvalidPost hperm
  have hdata : dataWord' = bytesStoreLiteSetByteLongStoredWord σ I := by
    simpa [dataWord', σ'] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I) hacc
  have hbyteAt :
      UInt256.byteAt (bytesStoreLiteSetByteLongWordIndex I) dataWord' =
        bytesStoreLiteSetByteValueWord I := by
    rw [hdata]
    exact bytesStoreLiteSetByteLongStoredWord_byteAt
      (σ := σ) (I := I) hcanon
  have hbyte :
      UInt256.shiftRight
        (UInt256.mul (UInt256.byteAt (bytesStoreLiteSetByteLongWordIndex I) dataWord')
          (UInt256.shiftLeft ⟨1⟩ ⟨248⟩))
        ⟨248⟩ = bytesStoreLiteSetByteValueWord I := by
    rw [hbyteAt]
    exact bytesStoreLiteSetByteValueHighMulShiftRight hcanon
  have h301 := bytesStoreLiteX_setByteLongReadReturnToWrapper
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (len := len) (header := header')
    (dataWord := dataWord') hread hbound (by rfl)
    (by simpa [header', σ', bytesStoreLiteCurrentLengthHeaderWord] using hflagPost)
    (by rfl) hbyte
  have hret := bytesStoreLiteX_returnUInt8_301
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := bytesStoreLiteSetByteValueWord I) h301
  simpa [σ', bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon] using hret

theorem bytesStoreLiteX_setByteOobLong {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1011⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetByteIndexWord I).toNat <
        (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setByteReachLengthDecoder hreach
  have hlen := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_setByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreLiteX_setByteOobShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1011⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setByteReachLengthDecoder hreach
  have hlen := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := g) hdec hflag hvalid (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_setByteOobAfterLength (g := g) hlen hbound

theorem bytesStoreLiteX_setByteLongMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1011⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setByteReachLengthDecoder (g := g) hreach
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMem
    hdec hflag hbad (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setByteShortMalformed {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1011⟩
      [bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
        bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdec := bytesStoreLiteX_setByteReachLengthDecoder (g := g) hreach
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMem
    hdec hflag hbad (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteSetByteDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 68) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte_none_short (I := I) hshort
  exact (bytesStoreLiteX_setByteDecodeShort
      (g := Sat256.ofUInt256 g) hreachPc hsz hshort hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetByteDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte_none_huge (I := I) hbig
  exact (bytesStoreLiteX_setByteDecodeHuge
      (g := Sat256.ofUInt256 g) hreachPc hbig hsize)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetByteDecodeNoncanonValueRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte_none_noncanon_value (I := I) hsz68 hhi hnc
  exact (bytesStoreLiteX_setByteDecodeNoncanonValue
      (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
      (bytesStoreLiteSetByteLand255_ne_self_of_not_uint8 hnc))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetByteShortSuccessRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len =
      UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
    (hshort : len.toNat < 32)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  have hreachLen := bytesStoreLiteX_setByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have hreach1029Raw := bytesStoreLiteX_bytesLengthDecoderShortValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hreachLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have hreach1029 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1029⟩
        [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using hreach1029Raw
  have hret := bytesStoreLiteX_setByteShortSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (acc := accEvm)
    hreach1029 hcanon hlen hshort hbound hflag hvalid hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩
    (bytesStoreLiteSetByteShortStoredWord σ_evm I)
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetByteLocals I) setByteTransition.body
        (.returned
          { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
          evmSolm1 (some (bytesStoreLiteSetByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreLiteSetByteShortBodyReturns
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len) (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hload
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hshort hbound hflag hvalid
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩
          (bytesStoreLiteSetByteShortStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
      (bytesStoreLiteSetByteShortStoredWord σ_evm I) hAccounts
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetByteValueWord I) hcanon))
  
theorem bytesStoreLiteSetByteLongSuccessRuntime_of_post_header
    {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256} {len : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenPost : len = UInt256.div
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  have hreachLen := bytesStoreLiteX_setByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have hreach1029Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hreachLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have hreach1029 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1029⟩
        [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using hreach1029Raw
  have hret := bytesStoreLiteX_setByteLongSuccessReturn_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (acc := accEvm)
    hreach1029 hcanon hbound hflag hlenPost hflagPost hvalidPost hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I) (bytesStoreLiteSetByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I) =
        bytesStoreLiteSetByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetByteLongDataSlot I)
      (bytesStoreLiteSetByteLongStoredWord σ_evm I) hAccounts
  have hloadHeaderPost :
      Solm.EVM.storageLoad evmSolm1 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I := by
    have hword :
        bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I =
          bytesStoreLiteCurrentLengthHeaderWord evmSolm1.accountMap I :=
      accountMapEquiv_storage_findD hpostAccounts I.codeOwner ⟨0⟩ ⟨0⟩
    simpa [evmSolm1, evmSolm0, initState, bytesStoreLiteCurrentLengthHeaderWord,
      Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using hword.symm
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetByteLocals I) setByteTransition.body
        (.returned
          { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
          evmSolm1 (some (bytesStoreLiteSetByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreLiteSetByteLongBodyReturns_of_post_readback
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len)
        (postHeaderWord := bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I)
        (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData
        (by
          simpa [evmSolm1, evmSolm0, initState] using hloadHeaderPost)
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hlenPost hbound hflag hvalid hflagPost hvalidPost
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetByteValueWord I) hcanon))

theorem bytesStoreLiteSetByteLongReturnLongMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hreachLen := bytesStoreLiteX_setByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have hreach1029Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hreachLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have hreach1029 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1029⟩
        [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using hreach1029Raw
  have hrev := bytesStoreLiteX_setByteLongWriteReturnLongMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    hreach1029 hbound hflag hflagPost hbadPost hperm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I) (bytesStoreLiteSetByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I) =
        bytesStoreLiteSetByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetByteLongDataSlot I)
      (bytesStoreLiteSetByteLongStoredWord σ_evm I) hAccounts
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I := by
    have hword :
        bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I =
          bytesStoreLiteCurrentLengthHeaderWord evmSolm1.accountMap I :=
      accountMapEquiv_storage_findD hpostAccounts I.codeOwner ⟨0⟩ ⟨0⟩
    simpa [evmSolm1, evmSolm0, initState, bytesStoreLiteCurrentLengthHeaderWord,
      Solm.EVM.storageLoad, Solm.EVM.storageStore, State.lookupAccount, Account.lookupStorage]
      using hword.symm
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteSetByteBodyReturnRevertsOfPostLongMalformed
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len)
        (postHeaderWord := bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hbound hflag hvalid
        hflagPost hbadPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetByteLongReturnShortMalformedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hbadPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div
            (bytesStoreLiteCurrentLengthHeaderWord
              (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
                (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) =
          ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hreachLen := bytesStoreLiteX_setByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have hreach1029Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hreachLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have hreach1029 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1029⟩
        [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using hreach1029Raw
  have hrev := bytesStoreLiteX_setByteLongWriteReturnShortMalformed
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    hreach1029 hbound hflag hflagPost hbadPost hperm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I) (bytesStoreLiteSetByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I) =
        bytesStoreLiteSetByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetByteLongDataSlot I)
      (bytesStoreLiteSetByteLongStoredWord σ_evm I) hAccounts
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I := by
    have hword :
        bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I =
          bytesStoreLiteCurrentLengthHeaderWord evmSolm1.accountMap I :=
      accountMapEquiv_storage_findD hpostAccounts I.codeOwner ⟨0⟩ ⟨0⟩
    simpa [evmSolm1, evmSolm0, initState, bytesStoreLiteCurrentLengthHeaderWord,
      Solm.EVM.storageLoad, Solm.EVM.storageStore, State.lookupAccount, Account.lookupStorage]
      using hword.symm
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteSetByteBodyReturnRevertsOfPostShortMalformed
        (evm := evmSolm0) (σ := σ_evm) (I := I) (len := len)
        (postHeaderWord := bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hbound hflag hvalid
        hflagPost hbadPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetByteLongReturnShortOobLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hreachLen := bytesStoreLiteX_setByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have hreach1029Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hreachLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have hreach1029 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1029⟩
        [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using hreach1029Raw
  have hread := bytesStoreLiteX_setByteLongWriteReturnDecodedShortLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len)
    hreach1029 hbound hflag hflagPost hvalidPost hperm
  have hrev := bytesStoreLiteX_setByteReturnOobLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
    (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
      (bytesStoreLiteSetByteLongStoredWord σ_evm I))
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := lenPost)
    (by simpa [hlenPost] using hread) hboundPost
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I) (bytesStoreLiteSetByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I) =
        bytesStoreLiteSetByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetByteLongDataSlot I)
      (bytesStoreLiteSetByteLongStoredWord σ_evm I) hAccounts
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I := by
    have hword :
        bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I =
          bytesStoreLiteCurrentLengthHeaderWord evmSolm1.accountMap I :=
      accountMapEquiv_storage_findD hpostAccounts I.codeOwner ⟨0⟩ ⟨0⟩
    simpa [evmSolm1, evmSolm0, initState, bytesStoreLiteCurrentLengthHeaderWord,
      Solm.EVM.storageLoad, Solm.EVM.storageStore, State.lookupAccount, Account.lookupStorage]
      using hword.symm
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteSetByteLongBodyReturnRevertsOfPostShortLength
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hlenPost hbound hboundPost
        hflag hvalid hflagPost hvalidPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetByteLongReturnShortSuccessRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.land (UInt256.div
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩ = ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hreachLen := bytesStoreLiteX_setByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have hreach1029Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hreachLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have hreach1029 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1029⟩
        [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using hreach1029Raw
  have hret := bytesStoreLiteX_setByteLongShortSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    (acc := accEvm)
    hreach1029 hcanon hlenPost hflagPost hvalidPost hlen hbound hboundPost
    hflag hvalid hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I) (bytesStoreLiteSetByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I) =
        bytesStoreLiteSetByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetByteLongDataSlot I)
      (bytesStoreLiteSetByteLongStoredWord σ_evm I) hAccounts
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I := by
    have hword :
        bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I =
          bytesStoreLiteCurrentLengthHeaderWord evmSolm1.accountMap I :=
      accountMapEquiv_storage_findD hpostAccounts I.codeOwner ⟨0⟩ ⟨0⟩
    simpa [evmSolm1, evmSolm0, initState, bytesStoreLiteCurrentLengthHeaderWord,
      Solm.EVM.storageLoad, Solm.EVM.storageStore, State.lookupAccount, Account.lookupStorage]
      using hword.symm
  have hvalid0 :
      UInt256.sub ⟨0⟩ (UInt256.lt lenPost ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [hlenPost, hflagPost] using hvalidPost
  have hshortPost : lenPost.toNat < 32 :=
    solidityShortBytesValid_lt32 hvalid0
  have hidxLt32 : (bytesStoreLiteSetByteIndexWord I).toNat < 32 :=
    lt_trans hboundPost hshortPost
  have hbytePost :
      UInt256.byteAt (bytesStoreLiteSetByteIndexWord I)
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) =
        bytesStoreLiteSetByteValueWord I := by
    by_cases hEq : (⟨0⟩ : UInt256) = bytesStoreLiteSetByteLongDataSlot I
    · have hheaderPostStored :
          bytesStoreLiteCurrentLengthHeaderWord
              (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
                (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I =
            bytesStoreLiteSetByteLongStoredWord σ_evm I := by
        simpa [bytesStoreLiteCurrentLengthHeaderWord, hEq.symm] using
          sstoreAccountMap_storage_findD_self_of_find_some_any σ_evm I.codeOwner accEvm
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I) haccEvm
      rw [hheaderPostStored]
      exact bytesStoreLiteSetByteLongStoredWord_byteAt_index_of_lt32
        (σ := σ_evm) (I := I) hcanon hidxLt32
    · have hheaderOld :
          bytesStoreLiteCurrentLengthHeaderWord
              (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
                (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I =
            bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
        simpa [bytesStoreLiteCurrentLengthHeaderWord, bytesStoreLiteSetByteLongDataSlot] using
          bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
            (σ := σ_evm) (I := I) (baseSlot := ⟨0⟩)
            (idx := bytesStoreLiteSetByteIndexWord I)
            (val := bytesStoreLiteSetByteLongStoredWord σ_evm I) hEq (by rfl)
      have hflagOldZero :
          UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
        rw [← hheaderOld]
        exact hflagPost
      exact False.elim (hflag hflagOldZero)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetByteLocals I) setByteTransition.body
        (.returned
          { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
          evmSolm1 (some (bytesStoreLiteSetByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreLiteSetByteLongBodyReturnsOfPostShortReadback
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I)
        (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hlenPost hbound hboundPost hflag hvalid hflagPost hvalidPost
        hbytePost
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetByteValueWord I) hcanon))

theorem bytesStoreLiteSetByteLongReturnLongOobLengthRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : ¬ (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hreachLen := bytesStoreLiteX_setByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have hreach1029Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hreachLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have hreach1029 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1029⟩
        [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using hreach1029Raw
  have hread := bytesStoreLiteX_setByteLongWriteReturnDecodedPostLongLength
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    hreach1029 hbound hflag hlenPost hflagPost hvalidPost hperm
  have hrev := bytesStoreLiteX_setByteReturnOobLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ_evm)
    (σ := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
      (bytesStoreLiteSetByteLongStoredWord σ_evm I))
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (len := lenPost)
    hread hboundPost
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I) (bytesStoreLiteSetByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I) =
        bytesStoreLiteSetByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetByteLongDataSlot I)
      (bytesStoreLiteSetByteLongStoredWord σ_evm I) hAccounts
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I := by
    have hword :
        bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I =
          bytesStoreLiteCurrentLengthHeaderWord evmSolm1.accountMap I :=
      accountMapEquiv_storage_findD hpostAccounts I.codeOwner ⟨0⟩ ⟨0⟩
    simpa [evmSolm1, evmSolm0, initState, bytesStoreLiteCurrentLengthHeaderWord,
      Solm.EVM.storageLoad, Solm.EVM.storageStore, State.lookupAccount, Account.lookupStorage]
      using hword.symm
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
    simpa [evmSolm0, initState] using
      bytesStoreLiteSetByteLongBodyReturnRevertsOfPostLongLength
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost hcanon hlen hlenPost hbound hboundPost
        hflag hvalid hflagPost hvalidPost
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetByteLongReturnLongSuccessRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {len lenPost : UInt256}
    {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hlenPost : lenPost = UInt256.div
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩)
    (hflagPost : UInt256.land
      (bytesStoreLiteCurrentLengthHeaderWord
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalidPost : UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
    (hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat)
    (hboundPost : (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hreachLen := bytesStoreLiteX_setByteReachLengthDecoder
    (g := Sat256.ofUInt256 g) hreachBody
  have hreach1029Raw := bytesStoreLiteX_bytesLengthDecoderLongValidMem
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hreachLen hflag hvalid
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)
  have hreach1029 :
      ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1029⟩
        [len, bytesStoreLiteSetByteIndexWord I, ⟨0⟩,
          UInt256.shiftLeft (bytesStoreLiteSetByteValueWord I) ⟨248⟩, ⟨0⟩,
          bytesStoreLiteSetByteValueWord I, bytesStoreLiteSetByteIndexWord I, ⟨301⟩,
          bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    simpa [hlen] using hreach1029Raw
  have hret := bytesStoreLiteX_setByteLongLongSuccessReturn
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g) (len := len) (lenPost := lenPost)
    (acc := accEvm)
    hreach1029 hcanon hlenPost hflagPost hvalidPost hlen hbound hboundPost
    hflag hvalid hperm haccEvm
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetByteLongDataSlot I) (bytesStoreLiteSetByteLongStoredWord σ_evm I)
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadCurrentLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hloadData :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetByteLongDataSlot I) =
        bytesStoreLiteSetByteLongOldWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetByteLongData_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hpostAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
          (bytesStoreLiteSetByteLongStoredWord σ_evm I))
        evmSolm1.accountMap := by
    simp [evmSolm1, evmSolm0, initState, storageStore_accountMap]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner (bytesStoreLiteSetByteLongDataSlot I)
      (bytesStoreLiteSetByteLongStoredWord σ_evm I) hAccounts
  have hloadHeaderPost :
      Solm.EVM.storageLoad
          (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
            (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I))
          evmSolm0.executionEnv.codeOwner ⟨0⟩ =
        bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I := by
    have hword :
        bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I =
          bytesStoreLiteCurrentLengthHeaderWord evmSolm1.accountMap I :=
      accountMapEquiv_storage_findD hpostAccounts I.codeOwner ⟨0⟩ ⟨0⟩
    simpa [evmSolm1, evmSolm0, initState, bytesStoreLiteCurrentLengthHeaderWord,
      Solm.EVM.storageLoad, Solm.EVM.storageStore, State.lookupAccount, Account.lookupStorage]
      using hword.symm
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetByteLocals I) setByteTransition.body
        (.returned
          { contract := bytesStoreLiteContract, locals := bytesStoreLiteSetByteLocals I }
          evmSolm1 (some (bytesStoreLiteSetByteValue I))) := by
    simpa [evmSolm0, evmSolm1, initState] using
      bytesStoreLiteSetByteLongBodyReturnsOfPostLongReadback
        (evm := evmSolm0) (σ := σ_evm) (I := I)
        (len := len) (lenPost := lenPost)
        (postHeaderWord := bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I)
        (acc := accSolm)
        (by simp [evmSolm0, initState]; exact hwv)
        hloadHeader hloadData hloadHeaderPost
        (by simpa [evmSolm0, initState] using haccSolm)
        hcanon hlen hlenPost hbound hboundPost hflag hvalid hflagPost hvalidPost
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    (by simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts])
    hpostAccounts
    (returnEquiv_of_encode (uint8ReturnEncoding (bytesStoreLiteSetByteValueWord I) hcanon))

theorem bytesStoreLiteSetByteLongHeaderPost_of_collision_cases
    {σ : AccountMap} {I : ExecutionEnv} {len : UInt256} {acc : Account}
    (hacc : σ.find? I.codeOwner = some acc)
    (hlen : len = UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hcollisionLen :
      (⟨0⟩ : UInt256) = bytesStoreLiteSetByteLongDataSlot I →
        len = UInt256.div (bytesStoreLiteSetByteLongStoredWord σ I) ⟨2⟩)
    (hcollisionFlag :
      (⟨0⟩ : UInt256) = bytesStoreLiteSetByteLongDataSlot I →
        UInt256.land (bytesStoreLiteSetByteLongStoredWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hcollisionValid :
      (⟨0⟩ : UInt256) = bytesStoreLiteSetByteLongDataSlot I →
        UInt256.sub (UInt256.land (bytesStoreLiteSetByteLongStoredWord σ I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLiteSetByteLongStoredWord σ I) ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩) :
    len = UInt256.div
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩ ∧
      UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩ ≠ ⟨0⟩ ∧
      UInt256.sub (UInt256.land
        (bytesStoreLiteCurrentLengthHeaderWord
          (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
            (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨1⟩)
        (UInt256.lt (UInt256.div
          (bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
  by_cases hEq : (⟨0⟩ : UInt256) = bytesStoreLiteSetByteLongDataSlot I
  · have hheaderPost :
        bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I =
          bytesStoreLiteSetByteLongStoredWord σ I := by
      simpa [bytesStoreLiteCurrentLengthHeaderWord, hEq.symm] using
        sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetByteLongDataSlot I)
        (bytesStoreLiteSetByteLongStoredWord σ I) hacc
    refine ⟨?_, ?_, ?_⟩
    · rw [hheaderPost]
      exact hcollisionLen hEq
    · rw [hheaderPost]
      exact hcollisionFlag hEq
    · rw [hheaderPost]
      exact hcollisionValid hEq
  · have hheaderPost :
        bytesStoreLiteCurrentLengthHeaderWord
            (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetByteLongDataSlot I)
              (bytesStoreLiteSetByteLongStoredWord σ I)) I =
          bytesStoreLiteCurrentLengthHeaderWord σ I := by
      simpa [bytesStoreLiteCurrentLengthHeaderWord, bytesStoreLiteSetByteLongDataSlot] using
        bytesStoreLiteBytesHeaderWordAfterDataSstore_eq_of_before_of_ne
          (σ := σ) (I := I) (baseSlot := ⟨0⟩)
          (idx := bytesStoreLiteSetByteIndexWord I)
          (val := bytesStoreLiteSetByteLongStoredWord σ I) hEq (by rfl)
    refine ⟨?_, ?_, ?_⟩
    · rw [hheaderPost]
      exact hlen
    · rw [hheaderPost]
      exact hflag
    · rw [hheaderPost]
      exact hvalid

theorem bytesStoreLiteSetByteOobLongRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetByteIndexWord I).toNat <
        (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩).toNat :=
    bytesStoreLiteReadCurrentLengthLong_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hvalid
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
    exact bytesStoreLiteSetByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hlen hbound
  exact (bytesStoreLiteX_setByteOobLong
      (g := Sat256.ofUInt256 g) hreachBody hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetByteOobShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hbound :
      ¬ (bytesStoreLiteSetByteIndexWord I).toNat <
        (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .ok (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩).toNat :=
    bytesStoreLiteReadCurrentLengthShort_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hvalid
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
    exact bytesStoreLiteSetByteBodyBoundsRevertsOfLength
      (by simp only [initState]; exact hwv) hlen hbound
  exact (bytesStoreLiteX_setByteOobShort
      (g := Sat256.ofUInt256 g) hreachBody hflag hvalid hbound)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetByteLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert :=
    bytesStoreLiteReadCurrentLengthLongMalformed_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
    exact bytesStoreLiteSetByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_setByteLongMalformed
      (g := Sat256.ofUInt256 g) hreachBody hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetByteShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8)
    (hflag : UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetByteSelector_size hsel
  have hreach := bytesStoreLiteReachSetByte (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz hsize hsel
  have hreachPc : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨357⟩
      [bytesStoreLiteSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ_evm) k C := by
    simpa [bytesStoreLiteSetByteEntryPc] using hreach
  have hreachBody := bytesStoreLiteX_setByteDecodeValid
    (g := Sat256.ofUInt256 g) hreachPc hsz68 hhi hsize
    (bytesStoreLiteSetByteLand255_eq_self_of_uint8 hcanon)
  have hd := bytesStoreLiteDispatch_setByte (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setByte (I := I) hsz68 hhi hcanon
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) { base := "current" } =
          .revert :=
    bytesStoreLiteReadCurrentLengthShortMalformed_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (bytesStoreLiteSetByteLocals I) setByteTransition.body .reverted := by
    exact bytesStoreLiteSetByteBodyRevertsOfLengthRead
      (by simp only [initState]; exact hwv) hlen
  exact (bytesStoreLiteX_setByteShortMalformed
      (g := Sat256.ofUInt256 g) hreachBody hflag hbad)
    |>.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetByteRuntime_of_post_header {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (bytesStoreLiteSetByteValueWord I).toNat < EVM.twoPow 8
      · by_cases hflagLong :
          UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩
        · by_cases hvalidLong :
            UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
              (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
                ⟨32⟩) ≠ ⟨0⟩
          · let len := UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩
            by_cases hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat
            · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
              · obtain ⟨accEvm, haccEq⟩ := haccSome
                by_cases hflagPost :
                    UInt256.land
                      (bytesStoreLiteCurrentLengthHeaderWord
                        (sstoreAccountMap I.codeOwner σ_evm
                          (bytesStoreLiteSetByteLongDataSlot I)
                          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩ ≠ ⟨0⟩
                · by_cases hvalidPost :
                      UInt256.sub (UInt256.land
                        (bytesStoreLiteCurrentLengthHeaderWord
                          (sstoreAccountMap I.codeOwner σ_evm
                            (bytesStoreLiteSetByteLongDataSlot I)
                            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
                        (UInt256.lt (UInt256.div
                          (bytesStoreLiteCurrentLengthHeaderWord
                            (sstoreAccountMap I.codeOwner σ_evm
                              (bytesStoreLiteSetByteLongDataSlot I)
                              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩)
                          ⟨32⟩) ≠ ⟨0⟩
                  · let lenPost := UInt256.div
                        (bytesStoreLiteCurrentLengthHeaderWord
                          (sstoreAccountMap I.codeOwner σ_evm
                            (bytesStoreLiteSetByteLongDataSlot I)
                            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩
                    by_cases hboundPost :
                        (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat
                    · exact bytesStoreLiteSetByteLongReturnLongSuccessRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost) (accEvm := accEvm)
                        hcode hsize hperm hwv hsel hAccounts haccEq hsz68 hhi hcanon
                        (by rfl) hflagPost hvalidPost (by rfl) hbound hboundPost
                        hflagLong hvalidLong
                    · exact bytesStoreLiteSetByteLongReturnLongOobLengthRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost)
                        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon
                        (by rfl) hflagPost hvalidPost (by rfl) hbound hboundPost
                        hflagLong hvalidLong
                  · have hbadPost :
                        UInt256.sub (UInt256.land
                          (bytesStoreLiteCurrentLengthHeaderWord
                            (sstoreAccountMap I.codeOwner σ_evm
                              (bytesStoreLiteSetByteLongDataSlot I)
                              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
                          (UInt256.lt (UInt256.div
                            (bytesStoreLiteCurrentLengthHeaderWord
                              (sstoreAccountMap I.codeOwner σ_evm
                                (bytesStoreLiteSetByteLongDataSlot I)
                                (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩)
                            ⟨32⟩) = ⟨0⟩ := by
                      by_contra hne
                      exact hvalidPost hne
                    exact bytesStoreLiteSetByteLongReturnLongMalformedRuntime
                      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (len := len)
                      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon
                      (by rfl) hbound hflagLong hvalidLong hflagPost hbadPost
                · have hflagPostZero :
                      UInt256.land
                        (bytesStoreLiteCurrentLengthHeaderWord
                          (sstoreAccountMap I.codeOwner σ_evm
                            (bytesStoreLiteSetByteLongDataSlot I)
                            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩ =
                        ⟨0⟩ := by
                    by_contra hne
                    exact hflagPost hne
                  by_cases hvalidShortPost :
                      UInt256.sub (UInt256.land
                        (bytesStoreLiteCurrentLengthHeaderWord
                          (sstoreAccountMap I.codeOwner σ_evm
                            (bytesStoreLiteSetByteLongDataSlot I)
                            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
                        (UInt256.lt (UInt256.land (UInt256.div
                          (bytesStoreLiteCurrentLengthHeaderWord
                            (sstoreAccountMap I.codeOwner σ_evm
                          (bytesStoreLiteSetByteLongDataSlot I)
                          (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩)
                          ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
                  · let lenPost := UInt256.land (UInt256.div
                        (bytesStoreLiteCurrentLengthHeaderWord
                          (sstoreAccountMap I.codeOwner σ_evm
                            (bytesStoreLiteSetByteLongDataSlot I)
                            (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩)
                        ⟨127⟩
                    by_cases hboundPost :
                        (bytesStoreLiteSetByteIndexWord I).toNat < lenPost.toNat
                    · exact bytesStoreLiteSetByteLongReturnShortSuccessRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost) (accEvm := accEvm)
                        hcode hsize hperm hwv hsel hAccounts haccEq hsz68 hhi hcanon
                        (by rfl) hflagPostZero hvalidShortPost (by rfl) hbound hboundPost
                        hflagLong hvalidLong
                    · exact bytesStoreLiteSetByteLongReturnShortOobLengthRuntime
                        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                        (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        (len := len) (lenPost := lenPost)
                        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon
                        (by rfl) hflagPostZero hvalidShortPost (by rfl) hbound hboundPost
                        hflagLong hvalidLong
                  · have hbadPost :
                        UInt256.sub (UInt256.land
                          (bytesStoreLiteCurrentLengthHeaderWord
                            (sstoreAccountMap I.codeOwner σ_evm
                              (bytesStoreLiteSetByteLongDataSlot I)
                              (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨1⟩)
                          (UInt256.lt (UInt256.land (UInt256.div
                            (bytesStoreLiteCurrentLengthHeaderWord
                              (sstoreAccountMap I.codeOwner σ_evm
                                (bytesStoreLiteSetByteLongDataSlot I)
                                (bytesStoreLiteSetByteLongStoredWord σ_evm I)) I) ⟨2⟩)
                            ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
                      by_contra hne
                      exact hvalidShortPost hne
                    exact bytesStoreLiteSetByteLongReturnShortMalformedRuntime
                      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (len := len)
                      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon
                      (by rfl) hbound hflagLong hvalidLong hflagPostZero hbadPost
              · have haccNone : σ_evm.find? I.codeOwner = none := by
                  cases haccEq : σ_evm.find? I.codeOwner with
                  | none => rfl
                  | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                have hhdr :
                    bytesStoreLiteCurrentLengthHeaderWord σ_evm I = ⟨0⟩ := by
                  simp [bytesStoreLiteCurrentLengthHeaderWord, haccNone, Option.option]
                have hflag0 :
                    UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ =
                      ⟨0⟩ := by
                  rw [hhdr]
                  native_decide
                exact False.elim (hflagLong hflag0)
            · exact bytesStoreLiteSetByteOobLongRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagLong
                hvalidLong hbound
          · have hbad :
              UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
                  ⟨32⟩) = ⟨0⟩ := by
              by_contra hne
              exact hvalidLong hne
            exact bytesStoreLiteSetByteLongMalformedRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagLong hbad
        · have hflagShort :
            UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
            by_contra hne
            exact hflagLong hne
          by_cases hvalidShort :
              UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
          · let len :=
              UInt256.land
                (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
            have hltNe : UInt256.lt len ⟨32⟩ ≠ ⟨0⟩ := by
              intro hlt0
              have hzero : UInt256.sub ⟨0⟩ ⟨0⟩ = (⟨0⟩ : UInt256) := by
                native_decide
              exact hvalidShort (by simpa [len, hflagShort, hlt0] using hzero)
            have hshort : len.toNat < 32 := by
              have hlt := ult_ne_zero_toNat_lt hltNe
              simpa using hlt
            by_cases hbound : (bytesStoreLiteSetByteIndexWord I).toNat < len.toNat
            · by_cases haccSome : ∃ accEvm, σ_evm.find? I.codeOwner = some accEvm
              · obtain ⟨accEvm, haccEq⟩ := haccSome
                exact bytesStoreLiteSetByteShortSuccessRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  (len := len) (accEvm := accEvm)
                  hcode hsize hperm hwv hsel hAccounts haccEq hsz68 hhi hcanon
                  (by rfl) hshort hbound hflagShort hvalidShort
              · have haccNone : σ_evm.find? I.codeOwner = none := by
                  cases haccEq : σ_evm.find? I.codeOwner with
                  | none => rfl
                  | some accEvm => exact False.elim (haccSome ⟨accEvm, haccEq⟩)
                have hhdr :
                    bytesStoreLiteCurrentLengthHeaderWord σ_evm I = ⟨0⟩ := by
                  simp [bytesStoreLiteCurrentLengthHeaderWord, haccNone, Option.option]
                have hlenZero : len = ⟨0⟩ := by
                  change
                    UInt256.land
                      (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
                      ⟨127⟩ = ⟨0⟩
                  rw [hhdr]
                  native_decide
                have hlen0 : len.toNat = 0 := by
                  simp [hlenZero]
                have hbadBound : (bytesStoreLiteSetByteIndexWord I).toNat < 0 := by
                  simpa [hlen0] using hbound
                exact False.elim (Nat.not_lt_zero _ hbadBound)
            · exact bytesStoreLiteSetByteOobShortRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagShort
                hvalidShort hbound
          · have hbad :
              UInt256.sub (UInt256.land (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨1⟩)
                (UInt256.lt
                  (UInt256.land
                    (UInt256.div (bytesStoreLiteCurrentLengthHeaderWord σ_evm I) ⟨2⟩)
                    ⟨127⟩) ⟨32⟩) = ⟨0⟩ := by
              by_contra hne
              exact hvalidShort hne
            exact bytesStoreLiteSetByteShortMalformedRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon hflagShort hbad
      · exact bytesStoreLiteSetByteDecodeNoncanonValueRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hcanon
    · exact bytesStoreLiteSetByteDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts (by omega)
  · exact bytesStoreLiteSetByteDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts (by omega)

theorem bytesStoreLiteSetByteRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x1c, 0x52, 0x47, 0x7d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact bytesStoreLiteSetByteRuntime_of_post_header
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hsize hperm hwv hsel hAccounts

end BytesStoreLite
