import Benchmarks.EAS.Attester.Common
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

/-! ## `attest(bytes32,uint256)` -/

def attesterAttestSchemaBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

def attesterAttestSchemaWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def attesterAttestInputWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def attesterAttestStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "schema" (.fixedBytes bytes32Width (attesterAttestSchemaBytes I))).insert
    "input" (.int (Int.ofNat (attesterAttestInputWord I).toNat))

def attesterAttestDataValue (I : ExecutionEnv) : Value :=
  .tuple
    [.address (AccountAddress.ofNat 0), .int 0, .bool true,
      .fixedBytes bytes32Width ((EVM.Word.ofNat 0).toBytesBE.drop (32 - (bytes32Width.val + 1))),
      .bytes (UInt256.toByteArray (attesterAttestInputWord I)), .int 0]

def attesterAttestRequestValue (I : ExecutionEnv) : Value :=
  .tuple [.fixedBytes bytes32Width (attesterAttestSchemaBytes I), attesterAttestDataValue I]

def attesterAttestArgVals (I : ExecutionEnv) : List Value :=
  [attesterAttestRequestValue I]

/-! Local reachability support for `MCOPY`.

The shared `Reasoning.Reach` layer has copy combinators for calldata/code/returndata, but not for
EIP-5656 `MCOPY`.  The runtime generated for `attest` uses `MCOPY` while ABI-encoding the nested
request tuple, so we prove the same wrapper locally from evmlean's `step_mcopy` theorem. -/

private def stMcopy (s : State) (a b c : UInt256) (t : List UInt256) : State :=
  { s with machineState := { s.machineState with
      pc := s.machineState.pc + ⟨1⟩,
      stack := t,
      memory := s.machineState.memory.write b.toNat s.machineState.memory a.toNat c.toNat,
      activeWords := UInt256.ofNat
        (MachineState.M s.machineState.activeWords.toNat (max a.toNat b.toNat) c.toNat),
      execLength := s.machineState.execLength + 1,
      gasAvailable :=
        (s.machineState.gasAvailable.subNat (memoryExpansionCost s .MCOPY)).subNat
          (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) } }

private theorem mcopy_xstep {s : State} {code : ByteArray} {pcv a b c : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MCOPY, .none))
    (hstk : s.machineState.stack = a :: b :: c :: t)
    (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .MCOPY
         then .error .OutOfGass
         else if (s.machineState.gasAvailable.subNat (memoryExpansionCost s .MCOPY)).toNat
                < GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
              then .error .OutOfGass
              else .ok (stMcopy s a b c t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.MCOPY, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_mcopy s hd, hstk]
  by_cases hg1 : s.machineState.gasAvailable.toNat < memoryExpansionCost s .MCOPY
  · simp only [hg1, if_true]
  · by_cases hg2 : (s.machineState.gasAvailable.subNat (memoryExpansionCost s .MCOPY)).toNat
        < GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)
    · simp only [hg1, hg2, if_true, if_false]
    · have hov' : ¬ ((a :: b :: c :: t).length - 3 + 0 > 1024) := by
        simp only [List.length_cons]
        omega
      simp only [hg1, hg2, hov', if_false, stMcopy]

private theorem RD.mcopyLocal {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c : UInt256} {t : List UInt256} (mcost : ℕ)
    (memout : ByteArray) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MCOPY, .none))
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: t →
        memoryExpansionCost s .MCOPY = mcost)
    (hmemout : mem.write b.toNat mem a.toNat c.toNat = memout)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat (max a.toNat b.toNat) c.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t memout awout rdata acc
      (k + 1)
      (C + (mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
    hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .MCOPY = mcost := hmc s haw hstk
    have st := mcopy_xstep hcode hpc hdec hstk hov
    rw [hmcS] at st
    rw [collapse_two_stage] at st
    by_cases gg :
        g.toNat < C + (mcost +
          (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · have hcost_pos :
          0 < mcost + (GasConstants.Gverylow + GasConstants.Gcopy * ((c.toNat + 31) / 32)) := by
        simp [GasConstants.Gverylow]
      refine Or.inr ⟨stMcopy s a b c t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stMcopy]
        exact hcode
      · simp only [stMcopy]
        rw [hpc]
      · rfl
      · simp only [stMcopy, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stMcopy]
        rw [hmem, hmemout]
      · simp only [stMcopy]
        rw [haw, hawout]
      · simp only [stMcopy]
        exact hrdata
      · simp only [stMcopy]
        exact hacc
      · exact hee
      · exact hworld

private theorem byteArray_toList_toByteArray (b : ByteArray) :
    b.toList.toByteArray = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [byteArray_toList_eq]
  simp

private theorem toByteArray_uInt256OfByteArray_of_size {arr : ByteArray}
    (hsize : arr.size = 32) :
    UInt256.toByteArray (uInt256OfByteArray arr) = arr := by
  rw [← word_toBytesBE_toByteArray_eq_toByteArray (uInt256OfByteArray arr),
    toBytesBE_uInt256OfByteArray_of_size hsize, byteArray_toList_toByteArray]

def attesterAttestExternalCalldata (I : ExecutionEnv) : ByteArray :=
  attestSelector ++
    UInt256.toByteArray ⟨32⟩ ++
    UInt256.toByteArray (attesterAttestSchemaWord I) ++
    UInt256.toByteArray ⟨64⟩ ++
    UInt256.toByteArray ⟨0⟩ ++
    UInt256.toByteArray ⟨0⟩ ++
    UInt256.toByteArray ⟨1⟩ ++
    UInt256.toByteArray ⟨0⟩ ++
    UInt256.toByteArray ⟨192⟩ ++
    UInt256.toByteArray ⟨0⟩ ++
    UInt256.toByteArray ⟨32⟩ ++
    UInt256.toByteArray (attesterAttestInputWord I)

private abbrev attesterWriteWord (mem : ByteArray) (off : Nat) (w : UInt256) : ByteArray :=
  (UInt256.toByteArray w).write 0 mem off 32

def attesterAttestEasWord (v : AttesterImmutables) : UInt256 :=
  EVM.Word.ofNat v.eas.toNat

def attesterAttestTargetWord (v : AttesterImmutables) : UInt256 :=
  UInt256.land solcAddrMask (attesterAttestEasWord v)

theorem attesterAttestEasWord_canonical (v : AttesterImmutables) :
    (attesterAttestEasWord v).toNat < EVM.addressModulus := by
  change (UInt256.ofNat v.eas.val).toNat < EVM.addressModulus
  rw [UInt256.toNat_ofNat_of_lt]
  · change v.eas.val < AccountAddress.size
    exact v.eas.isLt
  · exact lt_of_lt_of_le v.eas.isLt (by decide)

theorem attesterAttestEasWord_clean (v : AttesterImmutables) :
    UInt256.land solcAddrMask (attesterAttestEasWord v) =
      attesterAttestEasWord v :=
  solcAddrMask_clean_left (attesterAttestEasWord_canonical v)

theorem attesterAttestTargetWord_eq_easWord (v : AttesterImmutables) :
    attesterAttestTargetWord v = attesterAttestEasWord v := by
  unfold attesterAttestTargetWord
  rw [attesterAttestEasWord_clean]

theorem attesterAttestTarget_eq (v : AttesterImmutables) :
    EVM.address v.eas = AccountAddress.ofUInt256 (attesterAttestTargetWord v) := by
  rw [attesterAttestTargetWord_eq_easWord]
  have hleft : EVM.address (v.eas : Nat) = v.eas := by
    apply Fin.ext
    simp [EVM.address, EVM.uintN]
    exact Nat.mod_eq_of_lt v.eas.isLt
  have hright : AccountAddress.ofUInt256 (attesterAttestEasWord v) = v.eas := by
    change AccountAddress.ofUInt256 (UInt256.ofNat v.eas.val) = v.eas
    have hv : (UInt256.ofNat v.eas.val).val = v.eas.val := by
      show (Fin.ofNat UInt256.size v.eas.val).val = v.eas.val
      simp only [Fin.ofNat]
      exact Nat.mod_eq_of_lt (lt_of_lt_of_le v.eas.isLt (by decide))
    apply Fin.ext
    simp [AccountAddress.ofUInt256, hv]
    exact Nat.mod_eq_of_lt v.eas.isLt
  rw [hleft, hright]

def attesterAttestMem192 : ByteArray :=
  attesterWriteWord solcFreePtrMem 64 ⟨192⟩

def attesterAttestMemSchema (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord attesterAttestMem192 128 (attesterAttestSchemaWord I)

def attesterAttestMem384 (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMemSchema I) 64 ⟨384⟩

def attesterAttestMemRecipient (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMem384 I) 192 ⟨0⟩

def attesterAttestMemExpiration (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMemRecipient I) 224 ⟨0⟩

def attesterAttestMemRevocable (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMemExpiration I) 256 ⟨1⟩

def attesterAttestMemRefUID (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMemRevocable I) 288 ⟨0⟩

def attesterAttestMemInputWord (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMemRefUID I) 416 (attesterAttestInputWord I)

def attesterAttestMemBytesLen (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMemInputWord I) 384 ⟨32⟩

def attesterAttestMem448 (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMemBytesLen I) 64 ⟨448⟩

def attesterAttestMemDataOffset (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMem448 I) 320 ⟨384⟩

def attesterAttestMemDataPad (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMemDataOffset I) 352 ⟨0⟩

def attesterAttestSourceMem (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestMemDataPad I) 160 ⟨192⟩

def attesterAttestSelectorWord : UInt256 :=
  UInt256.shiftLeft (UInt256.land ⟨0xffffffff⟩ ⟨0xf17325e7⟩) ⟨224⟩

def attesterAttestCallMemSelector (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestSourceMem I) 448 attesterAttestSelectorWord

def attesterAttestCallMemArgOffset (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemSelector I) 452 ⟨32⟩

def attesterAttestCallMemSchema (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemArgOffset I) 484 (attesterAttestSchemaWord I)

def attesterAttestCallMemDataOffset (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemSchema I) 516 ⟨64⟩

def attesterAttestCallMemRecipient (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemDataOffset I) 548 ⟨0⟩

def attesterAttestCallMemExpiration (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemRecipient I) 580 ⟨0⟩

def attesterAttestCallMemRevocable (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemExpiration I) 612 ⟨1⟩

def attesterAttestCallMemRefUID (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemRevocable I) 644 ⟨0⟩

def attesterAttestCallMemBytesOffset (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemRefUID I) 676 ⟨192⟩

def attesterAttestCallMemBytesLen (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemBytesOffset I) 740 ⟨32⟩

def attesterAttestCallMemBytesData (I : ExecutionEnv) : ByteArray :=
  (attesterAttestCallMemBytesLen I).write 416 (attesterAttestCallMemBytesLen I) 772 32

def attesterAttestCallMemPad (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemBytesData I) 804 ⟨0⟩

def attesterAttestCallMemValue (I : ExecutionEnv) : ByteArray :=
  attesterWriteWord (attesterAttestCallMemPad I) 708 ⟨0⟩

def attesterAttestCallMem (I : ExecutionEnv) : ByteArray :=
  attesterAttestCallMemValue I

private theorem attesterWriteWord_size_eq_max (mem : ByteArray) (off : Nat) (w : UInt256)
    (hgap : off - mem.size < USize.size) :
    (attesterWriteWord mem off w).size = max mem.size (off + 32) := by
  unfold attesterWriteWord
  by_cases hoff : off ≤ mem.size
  · rw [toByteArray_write32_size_of_le mem w off mem.size (max mem.size (off + 32)) rfl
      hoff rfl]
  · have hge : mem.size ≤ off := by omega
    rw [toByteArray_write32_size_of_ge mem w off mem.size (off + 32) rfl hge hgap rfl]
    rw [max_eq_right (by omega)]

private theorem attesterWriteWord_read_below_len (mem : ByteArray) (off : Nat)
    (w : UInt256) (read len : Nat)
    (hread : read + len ≤ mem.size) (hbelow : read + len ≤ off)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hgap : off - mem.size < USize.size) :
    (attesterWriteWord mem off w).readWithPadding read len =
      mem.readWithPadding read len := by
  exact toByteArray_write_read_below_len_of_gap w mem off read len hread hbelow hpos hlen64 hgap

private theorem attesterWriteWord_read_above_len (mem : ByteArray) (off : Nat)
    (w : UInt256) (read len : Nat)
    (hoff : off ≤ mem.size) (habove : off + 32 ≤ read) (hin : read + len ≤ mem.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (attesterWriteWord mem off w).readWithPadding read len =
      mem.readWithPadding read len := by
  unfold attesterWriteWord
  exact write32_read_above_len _ _ off read len (by rw [toByteArray_size]) hoff habove hin
    hpos hlen64

private theorem attesterWriteWord_read_back (mem : ByteArray) (off : Nat) (w : UInt256)
    (hgap : off - mem.size < USize.size) :
    (attesterWriteWord mem off w).readWithPadding off 32 = UInt256.toByteArray w := by
  exact toByteArray_write_read_back_of_gap w mem off hgap

private theorem attesterToByteArray_write_eq_nat (v : UInt256) (mem : ByteArray) (off : ℕ)
    (hoff : mem.size ≤ off) :
    (UInt256.toByteArray v).write 0 mem off 32 =
      mem ++ ffi.ByteArray.zeroes (off - mem.size) ++ UInt256.toByteArray v := by
  have hsz : (UInt256.toByteArray v).data.size = 32 := UInt256.toByteArrayWithSizeProof v |>.2
  have hpz : (ffi.ByteArray.zeroes (off - mem.size)).data.size = off - mem.size := by
    rw [show (ffi.ByteArray.zeroes (off - mem.size)).data.size =
        (ffi.ByteArray.zeroes (off - mem.size)).size from rfl, ByteArray_zeroes_size]
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg (by decide : ¬ ((32 : ℕ) = 0)),
    if_neg (show ¬ (0 ≥ (UInt256.toByteArray v).size) from by
      rw [show (UInt256.toByteArray v).size = 32 from hsz]; omega)]
  simp only [ByteArray.data_copySlice, ByteArray.data_append]
  have hv : v.toByteArray.size = 32 := hsz
  have hDsz : (mem.data ++ (ffi.ByteArray.zeroes (off - mem.size)).data).size = off := by
    rw [Array.size_append, hpz]
    show mem.size + (off - mem.size) = off
    omega
  rw [hv, show (min 32 (32 - 0) : ℕ) = 32 from rfl,
    show min mem.size (off + 32) - (off + 32) = 0 from by omega,
    show (ffi.ByteArray.zeroes 0).data = (#[] : Array UInt8) from by
      rw [zeroes_zero (n := 0) (by rfl)]
      rfl]
  rw [Array.append_empty]
  rw [Array.extract_eq_self_of_le (by rw [hDsz]),
    Array.extract_eq_self_of_le (show v.toByteArray.data.size ≤ 0 + (32 + 0) from by rw [hsz]),
    Array.extract_eq_empty_of_le (by rw [hDsz]; omega),
    Array.append_empty]

private theorem attesterWriteWord_size_eq_max_nat (mem : ByteArray) (off : Nat) (w : UInt256) :
    (attesterWriteWord mem off w).size = max mem.size (off + 32) := by
  unfold attesterWriteWord
  by_cases hoff : off ≤ mem.size
  · rw [toByteArray_write32_size_of_le mem w off mem.size (max mem.size (off + 32)) rfl
      hoff rfl]
  · have hge : mem.size ≤ off := by omega
    rw [attesterToByteArray_write_eq_nat w mem off hge]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
    rw [max_eq_right (by omega)]
    omega

private theorem attesterWriteWord_read_back_nat (mem : ByteArray) (off : Nat) (w : UInt256) :
    (attesterWriteWord mem off w).readWithPadding off 32 = UInt256.toByteArray w := by
  unfold attesterWriteWord
  by_cases hle : off ≤ mem.size
  · rw [write32_read_back _ _ off (by rw [toByteArray_size]) hle]
    rw [show 32 = (UInt256.toByteArray w).size by rw [toByteArray_size]]
    exact byteArray_extract_self _
  · have hge : mem.size ≤ off := by omega
    rw [attesterToByteArray_write_eq_nat w mem off hge]
    rw [readWithPadding_eq_extract _ off (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega)]
    rw [extract_append_right_window
      (mem ++ ffi.ByteArray.zeroes (off - mem.size))
      (UInt256.toByteArray w) off (off + 32) (by
        rw [ByteArray.size_append, ByteArray_zeroes_size]
        omega)]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    rw [show off - (mem.size + (off - mem.size)) = 0 by omega,
      show off + 32 - (mem.size + (off - mem.size)) = 32 by omega]
    rw [show (UInt256.toByteArray w).extract 0 32 = UInt256.toByteArray w from by
      rw [show 32 = (UInt256.toByteArray w).size by rw [toByteArray_size]]
      exact byteArray_extract_self _]

private theorem attesterWriteWord_read_below_len_nat (mem : ByteArray) (off : Nat)
    (w : UInt256) (read len : Nat)
    (hread : read + len ≤ mem.size) (hbelow : read + len ≤ off)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (attesterWriteWord mem off w).readWithPadding read len =
      mem.readWithPadding read len := by
  unfold attesterWriteWord
  by_cases hle : off ≤ mem.size
  · exact write32_read_below_len _ _ off read len (by rw [toByteArray_size]) hle
      hbelow hread hpos hlen64
  · have hge : mem.size ≤ off := by omega
    rw [attesterToByteArray_write_eq_nat w mem off hge]
    rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray_zeroes_size]
      omega)]
    rw [extract_append_left _ _ _ _ hread]
    exact (readWithPadding_eq_extract' _ read len hpos hlen64 hread).symm

private theorem write_read_below_end_from_len (src base : ByteArray)
    (srcAddr writeLen read len : Nat)
    (hwrite : writeLen ≠ 0) (hsrc : srcAddr + writeLen ≤ src.size)
    (hread : read + len ≤ base.size) (hbelow : read + len ≤ base.size)
    (hpos : 0 < len) (hlen64 : len < 2 ^ 64) :
    (src.write srcAddr base base.size writeLen).readWithPadding read len =
      base.readWithPadding read len := by
  rw [write_at_end_eq_from src base srcAddr writeLen hwrite hsrc]
  rw [readWithPadding_eq_extract' _ read len hpos hlen64 (by
    rw [ByteArray.size_append, ByteArray.size_extract]
    omega)]
  rw [extract_append_left _ _ _ _ hbelow]
  exact (readWithPadding_eq_extract' base read len hpos hlen64 hread).symm

theorem attesterAttestMem192_size : attesterAttestMem192.size = 96 := by
  unfold attesterAttestMem192
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [solcFreePtrMem_size]
      exact lt_usize _ (by norm_num)),
    solcFreePtrMem_size]
  norm_num

theorem attesterAttestMemSchema_size (I : ExecutionEnv) :
    (attesterAttestMemSchema I).size = 160 := by
  unfold attesterAttestMemSchema
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMem192_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMem192_size]
  norm_num

theorem attesterAttestMem384_size (I : ExecutionEnv) :
    (attesterAttestMem384 I).size = 160 := by
  unfold attesterAttestMem384
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMemSchema_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMemSchema_size]
  norm_num

theorem attesterAttestMemRecipient_size (I : ExecutionEnv) :
    (attesterAttestMemRecipient I).size = 224 := by
  unfold attesterAttestMemRecipient
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMem384_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMem384_size]
  norm_num

theorem attesterAttestMemExpiration_size (I : ExecutionEnv) :
    (attesterAttestMemExpiration I).size = 256 := by
  unfold attesterAttestMemExpiration
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMemRecipient_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMemRecipient_size]
  norm_num

theorem attesterAttestMemRevocable_size (I : ExecutionEnv) :
    (attesterAttestMemRevocable I).size = 288 := by
  unfold attesterAttestMemRevocable
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMemExpiration_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMemExpiration_size]
  norm_num

theorem attesterAttestMemRefUID_size (I : ExecutionEnv) :
    (attesterAttestMemRefUID I).size = 320 := by
  unfold attesterAttestMemRefUID
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMemRevocable_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMemRevocable_size]
  norm_num

theorem attesterAttestMemInputWord_size (I : ExecutionEnv) :
    (attesterAttestMemInputWord I).size = 448 := by
  unfold attesterAttestMemInputWord
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMemRefUID_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMemRefUID_size]
  norm_num

theorem attesterAttestMemBytesLen_size (I : ExecutionEnv) :
    (attesterAttestMemBytesLen I).size = 448 := by
  unfold attesterAttestMemBytesLen
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMemInputWord_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMemInputWord_size]
  norm_num

theorem attesterAttestMem448_size (I : ExecutionEnv) :
    (attesterAttestMem448 I).size = 448 := by
  unfold attesterAttestMem448
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMemBytesLen_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMemBytesLen_size]
  norm_num

theorem attesterAttestMemDataOffset_size (I : ExecutionEnv) :
    (attesterAttestMemDataOffset I).size = 448 := by
  unfold attesterAttestMemDataOffset
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMem448_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMem448_size]
  norm_num

theorem attesterAttestMemDataPad_size (I : ExecutionEnv) :
    (attesterAttestMemDataPad I).size = 448 := by
  unfold attesterAttestMemDataPad
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMemDataOffset_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMemDataOffset_size]
  norm_num

theorem attesterAttestSourceMem_size (I : ExecutionEnv) :
    (attesterAttestSourceMem I).size = 448 := by
  unfold attesterAttestSourceMem
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestMemDataPad_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestMemDataPad_size]
  norm_num

theorem attesterAttestMem192_read64 :
    attesterAttestMem192.readWithPadding 64 32 = UInt256.toByteArray ⟨192⟩ := by
  unfold attesterAttestMem192
  exact attesterWriteWord_read_back _ _ _ (by
    rw [solcFreePtrMem_size]
    exact lt_usize _ (by norm_num))

theorem attesterAttestMemSchema_read64 (I : ExecutionEnv) :
    (attesterAttestMemSchema I).readWithPadding 64 32 = UInt256.toByteArray ⟨192⟩ := by
  unfold attesterAttestMemSchema
  rw [attesterWriteWord_read_below_len _ 128 _ 64 32
    (by rw [attesterAttestMem192_size]) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestMem192_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestMem192_read64

theorem attesterAttestMem384_read64 (I : ExecutionEnv) :
    (attesterAttestMem384 I).readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold attesterAttestMem384
  exact attesterWriteWord_read_back _ _ _ (by
    rw [attesterAttestMemSchema_size]
    exact lt_usize _ (by norm_num))

theorem attesterAttestMemRecipient_read64 (I : ExecutionEnv) :
    (attesterAttestMemRecipient I).readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold attesterAttestMemRecipient
  rw [attesterWriteWord_read_below_len _ 192 _ 64 32
    (by rw [attesterAttestMem384_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestMem384_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestMem384_read64 I

theorem attesterAttestMemExpiration_read64 (I : ExecutionEnv) :
    (attesterAttestMemExpiration I).readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold attesterAttestMemExpiration
  rw [attesterWriteWord_read_below_len _ 224 _ 64 32
    (by rw [attesterAttestMemRecipient_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestMemRecipient_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestMemRecipient_read64 I

theorem attesterAttestMemRevocable_read64 (I : ExecutionEnv) :
    (attesterAttestMemRevocable I).readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold attesterAttestMemRevocable
  rw [attesterWriteWord_read_below_len _ 256 _ 64 32
    (by rw [attesterAttestMemExpiration_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestMemExpiration_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestMemExpiration_read64 I

theorem attesterAttestMemRefUID_read64 (I : ExecutionEnv) :
    (attesterAttestMemRefUID I).readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold attesterAttestMemRefUID
  rw [attesterWriteWord_read_below_len _ 288 _ 64 32
    (by rw [attesterAttestMemRevocable_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestMemRevocable_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestMemRevocable_read64 I

theorem attesterAttestMemInputWord_read64 (I : ExecutionEnv) :
    (attesterAttestMemInputWord I).readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold attesterAttestMemInputWord
  rw [attesterWriteWord_read_below_len _ 416 _ 64 32
    (by rw [attesterAttestMemRefUID_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestMemRefUID_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestMemRefUID_read64 I

theorem attesterAttestMem448_read64 (I : ExecutionEnv) :
    (attesterAttestMem448 I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestMem448
  exact attesterWriteWord_read_back _ _ _ (by
    rw [attesterAttestMemBytesLen_size]
    exact lt_usize _ (by norm_num))

theorem attesterAttestMemDataOffset_read64 (I : ExecutionEnv) :
    (attesterAttestMemDataOffset I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestMemDataOffset
  rw [attesterWriteWord_read_below_len _ 320 _ 64 32
    (by rw [attesterAttestMem448_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestMem448_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestMem448_read64 I

theorem attesterAttestMemDataPad_read64 (I : ExecutionEnv) :
    (attesterAttestMemDataPad I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestMemDataPad
  rw [attesterWriteWord_read_below_len _ 352 _ 64 32
    (by rw [attesterAttestMemDataOffset_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestMemDataOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestMemDataOffset_read64 I

theorem attesterAttestSourceMem_read64 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestSourceMem
  rw [attesterWriteWord_read_below_len _ 160 _ 64 32
    (by rw [attesterAttestMemDataPad_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestMemDataPad_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestMemDataPad_read64 I

theorem attesterAttestSourceMem_read128 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 128 32 =
      UInt256.toByteArray (attesterAttestSchemaWord I) := by
  change (writeCascade attesterAttestMem192
      [(128, attesterAttestSchemaWord I), (64, (⟨384⟩ : UInt256)), (192, (⟨0⟩ : UInt256)),
        (224, (⟨0⟩ : UInt256)), (256, (⟨1⟩ : UInt256)), (288, (⟨0⟩ : UInt256)),
        (416, attesterAttestInputWord I), (384, (⟨32⟩ : UInt256)), (64, (⟨448⟩ : UInt256)),
        (320, (⟨384⟩ : UInt256)), (352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))]).readWithPadding
      128 32 = UInt256.toByteArray (attesterAttestSchemaWord I)
  exact writeCascade_read_word_of_head_of_base attesterAttestMem192
    (word := attesterAttestSchemaWord I)
    (rest := [(64, (⟨384⟩ : UInt256)), (192, (⟨0⟩ : UInt256)),
      (224, (⟨0⟩ : UInt256)), (256, (⟨1⟩ : UInt256)), (288, (⟨0⟩ : UInt256)),
      (416, attesterAttestInputWord I), (384, (⟨32⟩ : UInt256)), (64, (⟨448⟩ : UInt256)),
      (320, (⟨384⟩ : UInt256)), (352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))])
    (hbase := attesterAttestMem192_size) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestSourceMem_read160 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 160 32 = UInt256.toByteArray ⟨192⟩ := by
  unfold attesterAttestSourceMem
  exact attesterWriteWord_read_back _ _ _ (by
    rw [attesterAttestMemDataPad_size]
    exact lt_usize _ (by norm_num))

theorem attesterAttestSourceMem_read192 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 192 32 = UInt256.toByteArray ⟨0⟩ := by
  change (writeCascade (attesterAttestMem384 I)
      [(192, (⟨0⟩ : UInt256)), (224, (⟨0⟩ : UInt256)), (256, (⟨1⟩ : UInt256)),
        (288, (⟨0⟩ : UInt256)), (416, attesterAttestInputWord I),
        (384, (⟨32⟩ : UInt256)), (64, (⟨448⟩ : UInt256)),
        (320, (⟨384⟩ : UInt256)), (352, (⟨0⟩ : UInt256)),
        (160, (⟨192⟩ : UInt256))]).readWithPadding 192 32 =
      UInt256.toByteArray ⟨0⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestMem384 I)
    (word := (⟨0⟩ : UInt256))
    (rest := [(224, (⟨0⟩ : UInt256)), (256, (⟨1⟩ : UInt256)),
      (288, (⟨0⟩ : UInt256)), (416, attesterAttestInputWord I),
      (384, (⟨32⟩ : UInt256)), (64, (⟨448⟩ : UInt256)),
      (320, (⟨384⟩ : UInt256)), (352, (⟨0⟩ : UInt256)),
      (160, (⟨192⟩ : UInt256))])
    (hbase := attesterAttestMem384_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestSourceMem_read224 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 224 32 = UInt256.toByteArray ⟨0⟩ := by
  change (writeCascade (attesterAttestMemRecipient I)
      [(224, (⟨0⟩ : UInt256)), (256, (⟨1⟩ : UInt256)), (288, (⟨0⟩ : UInt256)),
        (416, attesterAttestInputWord I), (384, (⟨32⟩ : UInt256)),
        (64, (⟨448⟩ : UInt256)), (320, (⟨384⟩ : UInt256)),
        (352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))]).readWithPadding 224 32 =
      UInt256.toByteArray ⟨0⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestMemRecipient I)
    (word := (⟨0⟩ : UInt256))
    (rest := [(256, (⟨1⟩ : UInt256)), (288, (⟨0⟩ : UInt256)),
      (416, attesterAttestInputWord I), (384, (⟨32⟩ : UInt256)),
      (64, (⟨448⟩ : UInt256)), (320, (⟨384⟩ : UInt256)),
      (352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))])
    (hbase := attesterAttestMemRecipient_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestSourceMem_read256 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 256 32 = UInt256.toByteArray ⟨1⟩ := by
  change (writeCascade (attesterAttestMemExpiration I)
      [(256, (⟨1⟩ : UInt256)), (288, (⟨0⟩ : UInt256)),
        (416, attesterAttestInputWord I), (384, (⟨32⟩ : UInt256)),
        (64, (⟨448⟩ : UInt256)), (320, (⟨384⟩ : UInt256)),
        (352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))]).readWithPadding 256 32 =
      UInt256.toByteArray ⟨1⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestMemExpiration I)
    (word := (⟨1⟩ : UInt256))
    (rest := [(288, (⟨0⟩ : UInt256)), (416, attesterAttestInputWord I),
      (384, (⟨32⟩ : UInt256)), (64, (⟨448⟩ : UInt256)),
      (320, (⟨384⟩ : UInt256)), (352, (⟨0⟩ : UInt256)),
      (160, (⟨192⟩ : UInt256))])
    (hbase := attesterAttestMemExpiration_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestSourceMem_read288 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 288 32 = UInt256.toByteArray ⟨0⟩ := by
  change (writeCascade (attesterAttestMemRevocable I)
      [(288, (⟨0⟩ : UInt256)), (416, attesterAttestInputWord I),
        (384, (⟨32⟩ : UInt256)), (64, (⟨448⟩ : UInt256)),
        (320, (⟨384⟩ : UInt256)), (352, (⟨0⟩ : UInt256)),
        (160, (⟨192⟩ : UInt256))]).readWithPadding 288 32 = UInt256.toByteArray ⟨0⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestMemRevocable I)
    (word := (⟨0⟩ : UInt256))
    (rest := [(416, attesterAttestInputWord I), (384, (⟨32⟩ : UInt256)),
      (64, (⟨448⟩ : UInt256)), (320, (⟨384⟩ : UInt256)),
      (352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))])
    (hbase := attesterAttestMemRevocable_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestSourceMem_read320 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 320 32 = UInt256.toByteArray ⟨384⟩ := by
  change (writeCascade (attesterAttestMem448 I)
      [(320, (⟨384⟩ : UInt256)), (352, (⟨0⟩ : UInt256)),
        (160, (⟨192⟩ : UInt256))]).readWithPadding 320 32 = UInt256.toByteArray ⟨384⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestMem448 I)
    (word := (⟨384⟩ : UInt256))
    (rest := [(352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))])
    (hbase := attesterAttestMem448_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites])

theorem attesterAttestSourceMem_read352 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 352 32 = UInt256.toByteArray ⟨0⟩ := by
  change (writeCascade (attesterAttestMemDataOffset I)
      [(352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))]).readWithPadding 352 32 =
      UInt256.toByteArray ⟨0⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestMemDataOffset I)
    (word := (⟨0⟩ : UInt256)) (rest := [(160, (⟨192⟩ : UInt256))])
    (hbase := attesterAttestMemDataOffset_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites])

theorem attesterAttestSourceMem_read384 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 384 32 = UInt256.toByteArray ⟨32⟩ := by
  change (writeCascade (attesterAttestMemInputWord I)
      [(384, (⟨32⟩ : UInt256)), (64, (⟨448⟩ : UInt256)),
        (320, (⟨384⟩ : UInt256)), (352, (⟨0⟩ : UInt256)),
        (160, (⟨192⟩ : UInt256))]).readWithPadding 384 32 = UInt256.toByteArray ⟨32⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestMemInputWord I)
    (word := (⟨32⟩ : UInt256))
    (rest := [(64, (⟨448⟩ : UInt256)), (320, (⟨384⟩ : UInt256)),
      (352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))])
    (hbase := attesterAttestMemInputWord_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites])

theorem attesterAttestSourceMem_read416 (I : ExecutionEnv) :
    (attesterAttestSourceMem I).readWithPadding 416 32 =
      UInt256.toByteArray (attesterAttestInputWord I) := by
  change (writeCascade (attesterAttestMemRefUID I)
      [(416, attesterAttestInputWord I), (384, (⟨32⟩ : UInt256)),
        (64, (⟨448⟩ : UInt256)), (320, (⟨384⟩ : UInt256)),
        (352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))]).readWithPadding
      416 32 = UInt256.toByteArray (attesterAttestInputWord I)
  exact writeCascade_read_word_of_head_of_base (attesterAttestMemRefUID I)
    (word := attesterAttestInputWord I)
    (rest := [(384, (⟨32⟩ : UInt256)), (64, (⟨448⟩ : UInt256)),
      (320, (⟨384⟩ : UInt256)), (352, (⟨0⟩ : UInt256)), (160, (⟨192⟩ : UInt256))])
    (hbase := attesterAttestMemRefUID_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites])

theorem attesterAttestCallMemSelector_size (I : ExecutionEnv) :
    (attesterAttestCallMemSelector I).size = 480 := by
  unfold attesterAttestCallMemSelector
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestSourceMem_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestSourceMem_size]
  norm_num

theorem attesterAttestCallMemArgOffset_size (I : ExecutionEnv) :
    (attesterAttestCallMemArgOffset I).size = 484 := by
  unfold attesterAttestCallMemArgOffset
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemSelector_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemSelector_size]
  norm_num

theorem attesterAttestCallMemSchema_size (I : ExecutionEnv) :
    (attesterAttestCallMemSchema I).size = 516 := by
  unfold attesterAttestCallMemSchema
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemArgOffset_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemArgOffset_size]
  norm_num

theorem attesterAttestCallMemDataOffset_size (I : ExecutionEnv) :
    (attesterAttestCallMemDataOffset I).size = 548 := by
  unfold attesterAttestCallMemDataOffset
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemSchema_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemSchema_size]
  norm_num

theorem attesterAttestCallMemRecipient_size (I : ExecutionEnv) :
    (attesterAttestCallMemRecipient I).size = 580 := by
  unfold attesterAttestCallMemRecipient
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemDataOffset_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemDataOffset_size]
  norm_num

theorem attesterAttestCallMemExpiration_size (I : ExecutionEnv) :
    (attesterAttestCallMemExpiration I).size = 612 := by
  unfold attesterAttestCallMemExpiration
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemRecipient_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemRecipient_size]
  norm_num

theorem attesterAttestCallMemRevocable_size (I : ExecutionEnv) :
    (attesterAttestCallMemRevocable I).size = 644 := by
  unfold attesterAttestCallMemRevocable
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemExpiration_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemExpiration_size]
  norm_num

theorem attesterAttestCallMemRefUID_size (I : ExecutionEnv) :
    (attesterAttestCallMemRefUID I).size = 676 := by
  unfold attesterAttestCallMemRefUID
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemRevocable_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemRevocable_size]
  norm_num

theorem attesterAttestCallMemBytesOffset_size (I : ExecutionEnv) :
    (attesterAttestCallMemBytesOffset I).size = 708 := by
  unfold attesterAttestCallMemBytesOffset
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemRefUID_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemRefUID_size]
  norm_num

theorem attesterAttestCallMemBytesLen_size (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).size = 772 := by
  unfold attesterAttestCallMemBytesLen
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemBytesOffset_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemBytesOffset_size]
  norm_num

theorem attesterAttestCallMemBytesData_size (I : ExecutionEnv) :
    (attesterAttestCallMemBytesData I).size = 804 := by
  unfold attesterAttestCallMemBytesData
  rw [show (772 : Nat) = (attesterAttestCallMemBytesLen I).size by
      rw [attesterAttestCallMemBytesLen_size]]
  rw [write_end_size_from (attesterAttestCallMemBytesLen I)
    (attesterAttestCallMemBytesLen I) 416 32 (by norm_num)
    (by rw [attesterAttestCallMemBytesLen_size]; norm_num)]
  rw [attesterAttestCallMemBytesLen_size]

theorem attesterAttestCallMemPad_size (I : ExecutionEnv) :
    (attesterAttestCallMemPad I).size = 836 := by
  unfold attesterAttestCallMemPad
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemBytesData_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemBytesData_size]
  norm_num

theorem attesterAttestCallMemValue_size (I : ExecutionEnv) :
    (attesterAttestCallMemValue I).size = 836 := by
  unfold attesterAttestCallMemValue
  rw [attesterWriteWord_size_eq_max _ _ _ (by
      rw [attesterAttestCallMemPad_size]
      exact lt_usize _ (by norm_num)),
    attesterAttestCallMemPad_size]
  norm_num

theorem attesterAttestCallMem_size (I : ExecutionEnv) :
    (attesterAttestCallMem I).size = 836 := by
  unfold attesterAttestCallMem
  exact attesterAttestCallMemValue_size I

theorem attesterAttestCallMemSelector_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemSelector I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemSelector
  rw [attesterWriteWord_read_below_len _ 448 _ 64 32
    (by rw [attesterAttestSourceMem_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestSourceMem_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestSourceMem_read64 I

theorem attesterAttestCallMemArgOffset_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemArgOffset I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemArgOffset
  rw [attesterWriteWord_read_below_len _ 452 _ 64 32
    (by rw [attesterAttestCallMemSelector_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemSelector_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemSelector_read64 I

theorem attesterAttestCallMemSelector_read128 (I : ExecutionEnv) :
    (attesterAttestCallMemSelector I).readWithPadding 128 32 =
      UInt256.toByteArray (attesterAttestSchemaWord I) := by
  unfold attesterAttestCallMemSelector
  rw [attesterWriteWord_read_below_len _ 448 _ 128 32
    (by rw [attesterAttestSourceMem_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestSourceMem_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestSourceMem_read128 I

theorem attesterAttestCallMemArgOffset_read128 (I : ExecutionEnv) :
    (attesterAttestCallMemArgOffset I).readWithPadding 128 32 =
      UInt256.toByteArray (attesterAttestSchemaWord I) := by
  unfold attesterAttestCallMemArgOffset
  rw [attesterWriteWord_read_below_len _ 452 _ 128 32
    (by rw [attesterAttestCallMemSelector_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemSelector_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemSelector_read128 I

theorem attesterAttestCallMemSelector_read160 (I : ExecutionEnv) :
    (attesterAttestCallMemSelector I).readWithPadding 160 32 = UInt256.toByteArray ⟨192⟩ := by
  unfold attesterAttestCallMemSelector
  rw [attesterWriteWord_read_below_len _ 448 _ 160 32
    (by rw [attesterAttestSourceMem_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestSourceMem_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestSourceMem_read160 I

theorem attesterAttestCallMemArgOffset_read160 (I : ExecutionEnv) :
    (attesterAttestCallMemArgOffset I).readWithPadding 160 32 = UInt256.toByteArray ⟨192⟩ := by
  unfold attesterAttestCallMemArgOffset
  rw [attesterWriteWord_read_below_len _ 452 _ 160 32
    (by rw [attesterAttestCallMemSelector_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemSelector_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemSelector_read160 I

theorem attesterAttestCallMemSelector_read320 (I : ExecutionEnv) :
    (attesterAttestCallMemSelector I).readWithPadding 320 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold attesterAttestCallMemSelector
  rw [attesterWriteWord_read_below_len _ 448 _ 320 32
    (by rw [attesterAttestSourceMem_size]; norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestSourceMem_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestSourceMem_read320 I

theorem attesterAttestCallMemArgOffset_read320 (I : ExecutionEnv) :
    (attesterAttestCallMemArgOffset I).readWithPadding 320 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold attesterAttestCallMemArgOffset
  rw [attesterWriteWord_read_below_len _ 452 _ 320 32
    (by rw [attesterAttestCallMemSelector_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemSelector_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemSelector_read320 I

theorem attesterAttestCallMemSchema_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemSchema I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemSchema
  rw [attesterWriteWord_read_below_len _ 484 _ 64 32
    (by rw [attesterAttestCallMemArgOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemArgOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemArgOffset_read64 I

theorem attesterAttestCallMemSchema_read160 (I : ExecutionEnv) :
    (attesterAttestCallMemSchema I).readWithPadding 160 32 = UInt256.toByteArray ⟨192⟩ := by
  unfold attesterAttestCallMemSchema
  rw [attesterWriteWord_read_below_len _ 484 _ 160 32
    (by rw [attesterAttestCallMemArgOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemArgOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemArgOffset_read160 I

theorem attesterAttestCallMemSchema_read320 (I : ExecutionEnv) :
    (attesterAttestCallMemSchema I).readWithPadding 320 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold attesterAttestCallMemSchema
  rw [attesterWriteWord_read_below_len _ 484 _ 320 32
    (by rw [attesterAttestCallMemArgOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemArgOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemArgOffset_read320 I

theorem attesterAttestCallMemDataOffset_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemDataOffset I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemDataOffset
  rw [attesterWriteWord_read_below_len _ 516 _ 64 32
    (by rw [attesterAttestCallMemSchema_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemSchema_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemSchema_read64 I

private theorem attesterAttestCallMemDataOffset_read_source (I : ExecutionEnv)
    {read : Nat} {w : UInt256} (hbelow : read + 32 ≤ 448)
    (hsrc : (attesterAttestSourceMem I).readWithPadding read 32 = UInt256.toByteArray w) :
    (attesterAttestCallMemDataOffset I).readWithPadding read 32 = UInt256.toByteArray w := by
  unfold attesterAttestCallMemDataOffset
  rw [attesterWriteWord_read_below_len _ 516 _ read 32
    (by rw [attesterAttestCallMemSchema_size]; omega) (by omega) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemSchema_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemSchema
  rw [attesterWriteWord_read_below_len _ 484 _ read 32
    (by rw [attesterAttestCallMemArgOffset_size]; omega) (by omega) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemArgOffset_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemArgOffset
  rw [attesterWriteWord_read_below_len _ 452 _ read 32
    (by rw [attesterAttestCallMemSelector_size]; omega) (by omega) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemSelector_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemSelector
  rw [attesterWriteWord_read_below_len _ 448 _ read 32
    (by rw [attesterAttestSourceMem_size]; omega) (by omega) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestSourceMem_size]; exact lt_usize _ (by norm_num))]
  exact hsrc

theorem attesterAttestCallMemDataOffset_read192 (I : ExecutionEnv) :
    (attesterAttestCallMemDataOffset I).readWithPadding 192 32 = UInt256.toByteArray ⟨0⟩ := by
  exact attesterAttestCallMemDataOffset_read_source I (by norm_num)
    (attesterAttestSourceMem_read192 I)

theorem attesterAttestCallMemDataOffset_read224 (I : ExecutionEnv) :
    (attesterAttestCallMemDataOffset I).readWithPadding 224 32 = UInt256.toByteArray ⟨0⟩ := by
  exact attesterAttestCallMemDataOffset_read_source I (by norm_num)
    (attesterAttestSourceMem_read224 I)

theorem attesterAttestCallMemDataOffset_read256 (I : ExecutionEnv) :
    (attesterAttestCallMemDataOffset I).readWithPadding 256 32 = UInt256.toByteArray ⟨1⟩ := by
  exact attesterAttestCallMemDataOffset_read_source I (by norm_num)
    (attesterAttestSourceMem_read256 I)

theorem attesterAttestCallMemDataOffset_read288 (I : ExecutionEnv) :
    (attesterAttestCallMemDataOffset I).readWithPadding 288 32 = UInt256.toByteArray ⟨0⟩ := by
  exact attesterAttestCallMemDataOffset_read_source I (by norm_num)
    (attesterAttestSourceMem_read288 I)

theorem attesterAttestCallMemDataOffset_read320 (I : ExecutionEnv) :
    (attesterAttestCallMemDataOffset I).readWithPadding 320 32 = UInt256.toByteArray ⟨384⟩ := by
  exact attesterAttestCallMemDataOffset_read_source I (by norm_num)
    (attesterAttestSourceMem_read320 I)

theorem attesterAttestCallMemDataOffset_read352 (I : ExecutionEnv) :
    (attesterAttestCallMemDataOffset I).readWithPadding 352 32 = UInt256.toByteArray ⟨0⟩ := by
  exact attesterAttestCallMemDataOffset_read_source I (by norm_num)
    (attesterAttestSourceMem_read352 I)

theorem attesterAttestCallMemDataOffset_read384 (I : ExecutionEnv) :
    (attesterAttestCallMemDataOffset I).readWithPadding 384 32 = UInt256.toByteArray ⟨32⟩ := by
  exact attesterAttestCallMemDataOffset_read_source I (by norm_num)
    (attesterAttestSourceMem_read384 I)

theorem attesterAttestCallMemRecipient_read224 (I : ExecutionEnv) :
    (attesterAttestCallMemRecipient I).readWithPadding 224 32 = UInt256.toByteArray ⟨0⟩ := by
  unfold attesterAttestCallMemRecipient
  rw [attesterWriteWord_read_below_len _ 548 _ 224 32
    (by rw [attesterAttestCallMemDataOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemDataOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemDataOffset_read224 I

theorem attesterAttestCallMemExpiration_read256 (I : ExecutionEnv) :
    (attesterAttestCallMemExpiration I).readWithPadding 256 32 = UInt256.toByteArray ⟨1⟩ := by
  unfold attesterAttestCallMemExpiration
  rw [attesterWriteWord_read_below_len _ 580 _ 256 32
    (by rw [attesterAttestCallMemRecipient_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRecipient_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemRecipient
  rw [attesterWriteWord_read_below_len _ 548 _ 256 32
    (by rw [attesterAttestCallMemDataOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemDataOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemDataOffset_read256 I

theorem attesterAttestCallMemRevocable_read288 (I : ExecutionEnv) :
    (attesterAttestCallMemRevocable I).readWithPadding 288 32 = UInt256.toByteArray ⟨0⟩ := by
  unfold attesterAttestCallMemRevocable
  rw [attesterWriteWord_read_below_len _ 612 _ 288 32
    (by rw [attesterAttestCallMemExpiration_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemExpiration_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemExpiration
  rw [attesterWriteWord_read_below_len _ 580 _ 288 32
    (by rw [attesterAttestCallMemRecipient_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRecipient_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemRecipient
  rw [attesterWriteWord_read_below_len _ 548 _ 288 32
    (by rw [attesterAttestCallMemDataOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemDataOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemDataOffset_read288 I

theorem attesterAttestCallMemRefUID_read320 (I : ExecutionEnv) :
    (attesterAttestCallMemRefUID I).readWithPadding 320 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold attesterAttestCallMemRefUID
  rw [attesterWriteWord_read_below_len _ 644 _ 320 32
    (by rw [attesterAttestCallMemRevocable_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRevocable_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemRevocable
  rw [attesterWriteWord_read_below_len _ 612 _ 320 32
    (by rw [attesterAttestCallMemExpiration_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemExpiration_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemExpiration
  rw [attesterWriteWord_read_below_len _ 580 _ 320 32
    (by rw [attesterAttestCallMemRecipient_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRecipient_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemRecipient
  rw [attesterWriteWord_read_below_len _ 548 _ 320 32
    (by rw [attesterAttestCallMemDataOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemDataOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemDataOffset_read320 I

theorem attesterAttestCallMemBytesOffset_read384 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesOffset I).readWithPadding 384 32 = UInt256.toByteArray ⟨32⟩ := by
  unfold attesterAttestCallMemBytesOffset
  rw [attesterWriteWord_read_below_len _ 676 _ 384 32
    (by rw [attesterAttestCallMemRefUID_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRefUID_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemRefUID
  rw [attesterWriteWord_read_below_len _ 644 _ 384 32
    (by rw [attesterAttestCallMemRevocable_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRevocable_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemRevocable
  rw [attesterWriteWord_read_below_len _ 612 _ 384 32
    (by rw [attesterAttestCallMemExpiration_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemExpiration_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemExpiration
  rw [attesterWriteWord_read_below_len _ 580 _ 384 32
    (by rw [attesterAttestCallMemRecipient_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRecipient_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemRecipient
  rw [attesterWriteWord_read_below_len _ 548 _ 384 32
    (by rw [attesterAttestCallMemDataOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemDataOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemDataOffset_read384 I

theorem attesterAttestCallMemPad_read352 (I : ExecutionEnv) :
    (attesterAttestCallMemPad I).readWithPadding 352 32 = UInt256.toByteArray ⟨0⟩ := by
  unfold attesterAttestCallMemPad
  rw [attesterWriteWord_read_below_len _ 804 _ 352 32
    (by rw [attesterAttestCallMemBytesData_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemBytesData_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemBytesData
  rw [show (772 : Nat) = (attesterAttestCallMemBytesLen I).size by
      rw [attesterAttestCallMemBytesLen_size]]
  rw [write_read_below_end_from (attesterAttestCallMemBytesLen I)
    (attesterAttestCallMemBytesLen I) 416 32 352 (by norm_num)
    (by rw [attesterAttestCallMemBytesLen_size]; norm_num)
    (by rw [attesterAttestCallMemBytesLen_size]; norm_num)]
  unfold attesterAttestCallMemBytesLen
  rw [attesterWriteWord_read_below_len _ 740 _ 352 32
    (by rw [attesterAttestCallMemBytesOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemBytesOffset_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemBytesOffset
  rw [attesterWriteWord_read_below_len _ 676 _ 352 32
    (by rw [attesterAttestCallMemRefUID_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRefUID_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemRefUID
  rw [attesterWriteWord_read_below_len _ 644 _ 352 32
    (by rw [attesterAttestCallMemRevocable_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRevocable_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemRevocable
  rw [attesterWriteWord_read_below_len _ 612 _ 352 32
    (by rw [attesterAttestCallMemExpiration_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemExpiration_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemExpiration
  rw [attesterWriteWord_read_below_len _ 580 _ 352 32
    (by rw [attesterAttestCallMemRecipient_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRecipient_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemRecipient
  rw [attesterWriteWord_read_below_len _ 548 _ 352 32
    (by rw [attesterAttestCallMemDataOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemDataOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemDataOffset_read352 I

theorem attesterAttestCallMemRecipient_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemRecipient I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemRecipient
  rw [attesterWriteWord_read_below_len _ 548 _ 64 32
    (by rw [attesterAttestCallMemDataOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemDataOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemDataOffset_read64 I

theorem attesterAttestCallMemExpiration_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemExpiration I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemExpiration
  rw [attesterWriteWord_read_below_len _ 580 _ 64 32
    (by rw [attesterAttestCallMemRecipient_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRecipient_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemRecipient_read64 I

theorem attesterAttestCallMemRevocable_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemRevocable I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemRevocable
  rw [attesterWriteWord_read_below_len _ 612 _ 64 32
    (by rw [attesterAttestCallMemExpiration_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemExpiration_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemExpiration_read64 I

theorem attesterAttestCallMemRefUID_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemRefUID I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemRefUID
  rw [attesterWriteWord_read_below_len _ 644 _ 64 32
    (by rw [attesterAttestCallMemRevocable_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRevocable_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemRevocable_read64 I

theorem attesterAttestCallMemBytesOffset_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesOffset I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemBytesOffset
  rw [attesterWriteWord_read_below_len _ 676 _ 64 32
    (by rw [attesterAttestCallMemRefUID_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemRefUID_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemRefUID_read64 I

theorem attesterAttestCallMemBytesLen_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemBytesLen
  rw [attesterWriteWord_read_below_len _ 740 _ 64 32
    (by rw [attesterAttestCallMemBytesOffset_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemBytesOffset_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemBytesOffset_read64 I

theorem attesterAttestCallMemBytesData_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesData I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemBytesData
  rw [show (772 : Nat) = (attesterAttestCallMemBytesLen I).size by
      rw [attesterAttestCallMemBytesLen_size]]
  rw [write_read_below_end_from (attesterAttestCallMemBytesLen I)
    (attesterAttestCallMemBytesLen I) 416 32 64 (by norm_num)
    (by rw [attesterAttestCallMemBytesLen_size]; norm_num)
    (by rw [attesterAttestCallMemBytesLen_size]; norm_num)]
  exact attesterAttestCallMemBytesLen_read64 I

theorem attesterAttestCallMemPad_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemPad I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemPad
  rw [attesterWriteWord_read_below_len _ 804 _ 64 32
    (by rw [attesterAttestCallMemBytesData_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemBytesData_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemBytesData_read64 I

theorem attesterAttestCallMemValue_read64 (I : ExecutionEnv) :
    (attesterAttestCallMemValue I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMemValue
  rw [attesterWriteWord_read_below_len _ 708 _ 64 32
    (by rw [attesterAttestCallMemPad_size]; norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [attesterAttestCallMemPad_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemPad_read64 I

theorem attesterAttestCallMem_read64 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨448⟩ := by
  unfold attesterAttestCallMem
  exact attesterAttestCallMemValue_read64 I

theorem attesterAttestMin32_toNat_of_ge {n : ℕ}
    (h32 : 32 ≤ n) (hsize : n < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat n)).toNat = 32 :=
  umin_ofNat_right_toNat_of_ge (c := 32) (n := n) (by norm_num [UInt256.size]) h32 hsize

theorem attesterAttestMin32_toNat_of_lt {n : ℕ}
    (h : n < 32) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat n)).toNat = n := by
  have hsize : n < UInt256.size := by
    have h32 : 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  exact umin_ofNat_right_toNat_of_lt (c := 32) (n := n)
    (by norm_num [UInt256.size]) h hsize

theorem attesterAttestReturnWrite_size (I : ExecutionEnv) (o : ByteArray)
    (ho32 : 32 ≤ o.size) :
    (o.write 0 (attesterAttestCallMem I) 448 32).size = 836 := by
  rw [write_eq_gen o (attesterAttestCallMem I) 448 32 (by norm_num) ho32
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, attesterAttestCallMem_size]
  omega

theorem attesterAttestReturnWrite_read64 (I : ExecutionEnv) (o : ByteArray)
    (ho32 : 32 ≤ o.size) :
    (o.write 0 (attesterAttestCallMem I) 448 32).readWithPadding 64 32 =
      UInt256.toByteArray ⟨448⟩ := by
  rw [write_read_below_gen o (attesterAttestCallMem I) 448 32 64
    (by norm_num) ho32 (by rw [attesterAttestCallMem_size]; norm_num) (by norm_num)]
  exact attesterAttestCallMem_read64 I

theorem attesterAttestReturnWrite_read64_of_len (I : ExecutionEnv) (o : ByteArray)
    {len : ℕ} (hlenSrc : len ≤ o.size) (hlenMax : len ≤ 32) :
    (o.write 0 (attesterAttestCallMem I) 448 len).readWithPadding 64 32 =
      UInt256.toByteArray ⟨448⟩ := by
  by_cases hlen : len = 0
  · subst len
    rw [byteArray_write_len_zero]
    exact attesterAttestCallMem_read64 I
  · rw [write_read_below_gen o (attesterAttestCallMem I) 448 len 64
      hlen hlenSrc (by rw [attesterAttestCallMem_size]; omega) (by norm_num)]
    exact attesterAttestCallMem_read64 I

theorem attesterAttestReturnWrite_size_of_len (I : ExecutionEnv) (o : ByteArray)
    {len : ℕ} (hlenSrc : len ≤ o.size) (hlenMax : len ≤ 32) :
    (o.write 0 (attesterAttestCallMem I) 448 len).size = 836 := by
  by_cases hlen : len = 0
  · subst len
    rw [byteArray_write_len_zero, attesterAttestCallMem_size]
  · rw [write_eq_gen o (attesterAttestCallMem I) 448 len hlen hlenSrc
      (by rw [attesterAttestCallMem_size]; omega)]
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, attesterAttestCallMem_size]
    omega

theorem attesterAttestReturnWrite_mload64_of_len (I : ExecutionEnv) (o : ByteArray)
    {len : ℕ} (hlenSrc : len ≤ o.size) (hlenMax : len ≤ 32) :
    (if (⟨64⟩ : UInt256).toNat ≥ (o.write 0 (attesterAttestCallMem I) 448 len).size ∨
        (⟨64⟩ : UInt256) ≥ ⟨27⟩ * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((o.write 0 (attesterAttestCallMem I) 448 len).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨448⟩ := by
  exact mloadWordValue_of_readWithPadding
    (by rw [attesterAttestReturnWrite_size_of_len I o hlenSrc hlenMax]; decide)
    (by decide)
    (by simpa using attesterAttestReturnWrite_read64_of_len I o hlenSrc hlenMax)

theorem attesterAttestReturnWrite_read448_word (I : ExecutionEnv) (o : ByteArray)
    (ho32 : 32 ≤ o.size) :
    (o.write 0 (attesterAttestCallMem I) 448 32).readWithPadding 448 32 =
      UInt256.toByteArray (uInt256OfByteArray (o.extract 0 32)) := by
  rw [write32_read_back o (attesterAttestCallMem I) 448 ho32
    (by rw [attesterAttestCallMem_size]; norm_num)]
  exact (toByteArray_uInt256OfByteArray_of_size
    (by rw [ByteArray.size_extract]; omega)).symm

def attesterAttestReturnDecodeFreePtr (o : ByteArray) : UInt256 :=
  UInt256.add ⟨448⟩
    (UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩) (UInt256.lnot ⟨31⟩))

noncomputable def attesterAttestReturnDecodeMem (I : ExecutionEnv) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray (attesterAttestReturnDecodeFreePtr o)).write 0
    (o.write 0 (attesterAttestCallMem I) 448 32) 64 32

theorem attesterAttestReturnDecodeMem_size (I : ExecutionEnv) (o : ByteArray)
    (ho32 : 32 ≤ o.size) :
    (attesterAttestReturnDecodeMem I o).size = 836 := by
  unfold attesterAttestReturnDecodeMem
  rw [write32_eq _ _ 64 (by rw [toByteArray_size])
    (by rw [attesterAttestReturnWrite_size I o ho32]; norm_num)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size,
    attesterAttestReturnWrite_size I o ho32]
  omega

theorem attesterAttestReturnDecodeMem_read64 (I : ExecutionEnv) (o : ByteArray)
    (ho32 : 32 ≤ o.size) :
    (attesterAttestReturnDecodeMem I o).readWithPadding 64 32 =
      UInt256.toByteArray (attesterAttestReturnDecodeFreePtr o) := by
  unfold attesterAttestReturnDecodeMem
  exact toByteArray_write32_read_back _ _ 64
    (by rw [attesterAttestReturnWrite_size I o ho32]; norm_num)

theorem attesterAttestReturnDecodeMem_read448_word (I : ExecutionEnv) (o : ByteArray)
    (ho32 : 32 ≤ o.size) :
    (attesterAttestReturnDecodeMem I o).readWithPadding 448 32 =
      UInt256.toByteArray (uInt256OfByteArray (o.extract 0 32)) := by
  unfold attesterAttestReturnDecodeMem
  rw [write32_read_above (UInt256.toByteArray (attesterAttestReturnDecodeFreePtr o))
    (o.write 0 (attesterAttestCallMem I) 448 32) 64 448
    (by rw [toByteArray_size])
    (by rw [attesterAttestReturnWrite_size I o ho32]; norm_num)
    (by norm_num)
    (by rw [attesterAttestReturnWrite_size I o ho32]; norm_num)]
  exact attesterAttestReturnWrite_read448_word I o ho32

private theorem attesterAttestReturnDecodeRounded_le (o : ByteArray)
    (ho255 : o.size < 2 ^ 255) :
    (UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩) (UInt256.lnot ⟨31⟩)).toNat
      ≤ o.size + 31 := by
  have hosz : (UInt256.ofNat o.size).toNat = o.size :=
    ulit_toNat' o.size (lt_size_of_lt_sign ho255)
  have hadd :
      (UInt256.add (UInt256.ofNat o.size) (⟨31⟩ : UInt256)).toNat = o.size + 31 := by
    change (((UInt256.ofNat o.size) + (⟨31⟩ : UInt256)).toNat = o.size + 31)
    rw [uadd_toNat, hosz, show (⟨31⟩ : UInt256).toNat = 31 by decide]
    rw [Nat.mod_eq_of_lt]
    have hcap : 2 ^ 255 + 31 < UInt256.size := by norm_num [UInt256.size]
    omega
  rw [uland_toNat, hadd]
  exact Nat.and_le_left

theorem attesterAttestReturnDecodeFreePtr_toNat (o : ByteArray)
    (ho255 : o.size < 2 ^ 255) :
    (attesterAttestReturnDecodeFreePtr o).toNat =
      448 +
        (UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)
          (UInt256.lnot ⟨31⟩)).toNat := by
  unfold attesterAttestReturnDecodeFreePtr
  change (((⟨448⟩ : UInt256) +
      UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)
        (UInt256.lnot ⟨31⟩)).toNat =
    448 +
      (UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)
        (UInt256.lnot ⟨31⟩)).toNat)
  rw [uadd_toNat, show (⟨448⟩ : UInt256).toNat = 448 by decide]
  rw [Nat.mod_eq_of_lt]
  have hround := attesterAttestReturnDecodeRounded_le o ho255
  have hcap : 448 + (o.size + 31) < UInt256.size := by
    have hsign : 2 ^ 255 + 479 < UInt256.size := by norm_num [UInt256.size]
    omega
  omega

theorem attesterAttestReturnDecodeFreePtr_ge448 (o : ByteArray)
    (ho255 : o.size < 2 ^ 255) :
    448 ≤ (attesterAttestReturnDecodeFreePtr o).toNat := by
  rw [attesterAttestReturnDecodeFreePtr_toNat o ho255]
  omega

theorem attesterAttestReturnDecodeFreePtr_add32_lt (o : ByteArray)
    (ho255 : o.size < 2 ^ 255) :
    (attesterAttestReturnDecodeFreePtr o).toNat + 32 < UInt256.size := by
  rw [attesterAttestReturnDecodeFreePtr_toNat o ho255]
  have hround := attesterAttestReturnDecodeRounded_le o ho255
  have hcap : 448 + (o.size + 31) + 32 < UInt256.size := by
    have hsign : 2 ^ 255 + 511 < UInt256.size := by norm_num [UInt256.size]
    omega
  omega

theorem attesterAttestReturnDecodeFreePtr_add63_lt (o : ByteArray)
    (ho255 : o.size < 2 ^ 255) :
    (attesterAttestReturnDecodeFreePtr o).toNat + 63 < UInt256.size := by
  rw [attesterAttestReturnDecodeFreePtr_toNat o ho255]
  have hround := attesterAttestReturnDecodeRounded_le o ho255
  have hcap : 448 + (o.size + 31) + 63 < UInt256.size := by
    have hsign : 2 ^ 255 + 542 < UInt256.size := by norm_num [UInt256.size]
    omega
  omega

theorem attesterAttestReturnDecodeFreePtr_add32_sub (o : ByteArray)
    (ho255 : o.size < 2 ^ 255) :
    UInt256.sub (UInt256.add ⟨32⟩ (attesterAttestReturnDecodeFreePtr o))
        (attesterAttestReturnDecodeFreePtr o) = ⟨32⟩ := by
  let fp := attesterAttestReturnDecodeFreePtr o
  have hfit : fp.toNat + 32 < UInt256.size :=
    attesterAttestReturnDecodeFreePtr_add32_lt o ho255
  apply u256_inj
  change (UInt256.sub ((⟨32⟩ : UInt256) + fp) fp).toNat = (⟨32⟩ : UInt256).toNat
  rw [usub_toNat]
  · rw [uadd_lit32_toNat fp hfit]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    omega
  · rw [uadd_lit32_toNat fp hfit]
    omega

theorem solcDecodeEndLenCheckOk_448_32 {len : ℕ}
    (hlen : 32 ≤ len) (hhi : len < 2 ^ 255) :
    UInt256.slt (UInt256.sub (UInt256.add ⟨448⟩ (UInt256.ofNat len)) ⟨448⟩) ⟨32⟩ =
      ⟨0⟩ := by
  exact solcReturnStaticLenCheckOk (base := 448) (words := 1) (by simpa using hlen) hhi
    (by norm_num [UInt256.size])
    (by
      have hcap : 2 ^ 255 + 448 < UInt256.size := by norm_num [UInt256.size]
      omega)

theorem solcDecodeEndLenCheckShort_448_32 {len : ℕ}
    (hshort : len < 32) :
    UInt256.slt (UInt256.sub (UInt256.add ⟨448⟩ (UInt256.ofNat len)) ⟨448⟩) ⟨32⟩ =
      ⟨1⟩ := by
  exact solcReturnStaticLenCheckShort (base := 448) (words := 1) (by simpa using hshort)
    (by norm_num [UInt256.size])
    (by
      have hcap : 448 + 32 < UInt256.size := by norm_num [UInt256.size]
      omega)
    (by norm_num)

theorem solcDecodeEndLenCheckHuge_448_32 {len : ℕ}
    (hhi : 2 ^ 255 ≤ len) (hlo : len < UInt256.size) :
    UInt256.slt (UInt256.sub (UInt256.add ⟨448⟩ (UInt256.ofNat len)) ⟨448⟩) ⟨32⟩ =
      ⟨1⟩ := by
  exact solcReturnStaticLenCheckHuge (base := 448) (words := 1) hhi hlo
    (by norm_num [UInt256.size]) (by norm_num)

theorem attesterAttestCallMemBytesLen_read448_4 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 448 4 = attestSelector := by
  change (writeCascade (attesterAttestSourceMem I)
      [(448, attesterAttestSelectorWord), (452, (⟨32⟩ : UInt256)),
        (484, attesterAttestSchemaWord I), (516, (⟨64⟩ : UInt256)),
        (548, (⟨0⟩ : UInt256)), (580, (⟨0⟩ : UInt256)),
        (612, (⟨1⟩ : UInt256)), (644, (⟨0⟩ : UInt256)),
        (676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))]).readWithPadding
      448 4 = attestSelector
  rw [writeCascade_read_window_of_head (attesterAttestSourceMem I) 448 0 4
      attesterAttestSelectorWord
      [(452, (⟨32⟩ : UInt256)), (484, attesterAttestSchemaWord I),
        (516, (⟨64⟩ : UInt256)), (548, (⟨0⟩ : UInt256)),
        (580, (⟨0⟩ : UInt256)), (612, (⟨1⟩ : UInt256)),
        (644, (⟨0⟩ : UInt256)), (676, (⟨192⟩ : UInt256)),
        (740, (⟨32⟩ : UInt256))]
      (by rw [attesterAttestSourceMem_size]; native_decide)
      (by
        rw [attesterAttestSourceMem_size]
        simp [WindowDisjointFromWrites]
        native_decide)
      (by norm_num) (by norm_num) (by norm_num)]
  unfold attesterAttestSelectorWord attestSelector selectorBytes
  native_decide

theorem attesterAttestCallMemBytesLen_read416 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 416 32 =
      UInt256.toByteArray (attesterAttestInputWord I) := by
  change (writeCascade (attesterAttestSourceMem I)
      [(448, attesterAttestSelectorWord), (452, (⟨32⟩ : UInt256)),
        (484, attesterAttestSchemaWord I), (516, (⟨64⟩ : UInt256)),
        (548, (⟨0⟩ : UInt256)), (580, (⟨0⟩ : UInt256)),
        (612, (⟨1⟩ : UInt256)), (644, (⟨0⟩ : UInt256)),
        (676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))]).readWithPadding
      416 32 = UInt256.toByteArray (attesterAttestInputWord I)
  rw [writeCascade_read_preserved_of_base (attesterAttestSourceMem I)
      [(448, attesterAttestSelectorWord), (452, (⟨32⟩ : UInt256)),
        (484, attesterAttestSchemaWord I), (516, (⟨64⟩ : UInt256)),
        (548, (⟨0⟩ : UInt256)), (580, (⟨0⟩ : UInt256)),
        (612, (⟨1⟩ : UInt256)), (644, (⟨0⟩ : UInt256)),
        (676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))]
      (hbase := attesterAttestSourceMem_size I)
      (hwin := by
        simp [WindowDisjointFromWrites]
        native_decide)]
  exact attesterAttestSourceMem_read416 I

theorem attesterAttestCallMemBytesLen_read452 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 452 32 =
      UInt256.toByteArray ⟨32⟩ := by
  change (writeCascade (attesterAttestCallMemSelector I)
      [(452, (⟨32⟩ : UInt256)), (484, attesterAttestSchemaWord I),
        (516, (⟨64⟩ : UInt256)), (548, (⟨0⟩ : UInt256)),
        (580, (⟨0⟩ : UInt256)), (612, (⟨1⟩ : UInt256)),
        (644, (⟨0⟩ : UInt256)), (676, (⟨192⟩ : UInt256)),
        (740, (⟨32⟩ : UInt256))]).readWithPadding 452 32 = UInt256.toByteArray ⟨32⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestCallMemSelector I)
    (word := (⟨32⟩ : UInt256))
    (rest := [(484, attesterAttestSchemaWord I), (516, (⟨64⟩ : UInt256)),
      (548, (⟨0⟩ : UInt256)), (580, (⟨0⟩ : UInt256)),
      (612, (⟨1⟩ : UInt256)), (644, (⟨0⟩ : UInt256)),
      (676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))])
    (hbase := attesterAttestCallMemSelector_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestCallMemBytesLen_read484 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 484 32 =
      UInt256.toByteArray (attesterAttestSchemaWord I) := by
  change (writeCascade (attesterAttestCallMemArgOffset I)
      [(484, attesterAttestSchemaWord I), (516, (⟨64⟩ : UInt256)),
        (548, (⟨0⟩ : UInt256)), (580, (⟨0⟩ : UInt256)),
        (612, (⟨1⟩ : UInt256)), (644, (⟨0⟩ : UInt256)),
        (676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))]).readWithPadding
      484 32 = UInt256.toByteArray (attesterAttestSchemaWord I)
  exact writeCascade_read_word_of_head_of_base (attesterAttestCallMemArgOffset I)
    (word := attesterAttestSchemaWord I)
    (rest := [(516, (⟨64⟩ : UInt256)), (548, (⟨0⟩ : UInt256)),
      (580, (⟨0⟩ : UInt256)), (612, (⟨1⟩ : UInt256)),
      (644, (⟨0⟩ : UInt256)), (676, (⟨192⟩ : UInt256)),
      (740, (⟨32⟩ : UInt256))])
    (hbase := attesterAttestCallMemArgOffset_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestCallMemBytesLen_read516 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 516 32 =
      UInt256.toByteArray ⟨64⟩ := by
  change (writeCascade (attesterAttestCallMemSchema I)
      [(516, (⟨64⟩ : UInt256)), (548, (⟨0⟩ : UInt256)),
        (580, (⟨0⟩ : UInt256)), (612, (⟨1⟩ : UInt256)),
        (644, (⟨0⟩ : UInt256)), (676, (⟨192⟩ : UInt256)),
        (740, (⟨32⟩ : UInt256))]).readWithPadding 516 32 = UInt256.toByteArray ⟨64⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestCallMemSchema I)
    (word := (⟨64⟩ : UInt256))
    (rest := [(548, (⟨0⟩ : UInt256)), (580, (⟨0⟩ : UInt256)),
      (612, (⟨1⟩ : UInt256)), (644, (⟨0⟩ : UInt256)),
      (676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))])
    (hbase := attesterAttestCallMemSchema_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestCallMemBytesLen_read548 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 548 32 =
      UInt256.toByteArray ⟨0⟩ := by
  change (writeCascade (attesterAttestCallMemDataOffset I)
      [(548, (⟨0⟩ : UInt256)), (580, (⟨0⟩ : UInt256)),
        (612, (⟨1⟩ : UInt256)), (644, (⟨0⟩ : UInt256)),
        (676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))]).readWithPadding
      548 32 = UInt256.toByteArray ⟨0⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestCallMemDataOffset I)
    (word := (⟨0⟩ : UInt256))
    (rest := [(580, (⟨0⟩ : UInt256)), (612, (⟨1⟩ : UInt256)),
      (644, (⟨0⟩ : UInt256)), (676, (⟨192⟩ : UInt256)),
      (740, (⟨32⟩ : UInt256))])
    (hbase := attesterAttestCallMemDataOffset_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestCallMemBytesLen_read580 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 580 32 =
      UInt256.toByteArray ⟨0⟩ := by
  change (writeCascade (attesterAttestCallMemRecipient I)
      [(580, (⟨0⟩ : UInt256)), (612, (⟨1⟩ : UInt256)),
        (644, (⟨0⟩ : UInt256)), (676, (⟨192⟩ : UInt256)),
        (740, (⟨32⟩ : UInt256))]).readWithPadding 580 32 = UInt256.toByteArray ⟨0⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestCallMemRecipient I)
    (word := (⟨0⟩ : UInt256))
    (rest := [(612, (⟨1⟩ : UInt256)), (644, (⟨0⟩ : UInt256)),
      (676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))])
    (hbase := attesterAttestCallMemRecipient_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestCallMemBytesLen_read612 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 612 32 =
      UInt256.toByteArray ⟨1⟩ := by
  change (writeCascade (attesterAttestCallMemExpiration I)
      [(612, (⟨1⟩ : UInt256)), (644, (⟨0⟩ : UInt256)),
        (676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))]).readWithPadding
      612 32 = UInt256.toByteArray ⟨1⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestCallMemExpiration I)
    (word := (⟨1⟩ : UInt256))
    (rest := [(644, (⟨0⟩ : UInt256)), (676, (⟨192⟩ : UInt256)),
      (740, (⟨32⟩ : UInt256))])
    (hbase := attesterAttestCallMemExpiration_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestCallMemBytesLen_read644 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 644 32 =
      UInt256.toByteArray ⟨0⟩ := by
  change (writeCascade (attesterAttestCallMemRevocable I)
      [(644, (⟨0⟩ : UInt256)), (676, (⟨192⟩ : UInt256)),
        (740, (⟨32⟩ : UInt256))]).readWithPadding 644 32 = UInt256.toByteArray ⟨0⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestCallMemRevocable I)
    (word := (⟨0⟩ : UInt256))
    (rest := [(676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))])
    (hbase := attesterAttestCallMemRevocable_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestCallMemBytesLen_read676 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 676 32 =
      UInt256.toByteArray ⟨192⟩ := by
  change (writeCascade (attesterAttestCallMemRefUID I)
      [(676, (⟨192⟩ : UInt256)), (740, (⟨32⟩ : UInt256))]).readWithPadding
      676 32 = UInt256.toByteArray ⟨192⟩
  exact writeCascade_read_word_of_head_of_base (attesterAttestCallMemRefUID I)
    (word := (⟨192⟩ : UInt256))
    (rest := [(740, (⟨32⟩ : UInt256))])
    (hbase := attesterAttestCallMemRefUID_size I) (hgap := by native_decide +revert)
    (hlater := by
      simp [WindowDisjointFromWrites]
      native_decide)

theorem attesterAttestCallMemBytesLen_read740 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesLen I).readWithPadding 740 32 =
      UInt256.toByteArray ⟨32⟩ := by
  unfold attesterAttestCallMemBytesLen
  exact attesterWriteWord_read_back _ _ _ (by
    rw [attesterAttestCallMemBytesOffset_size]
    exact lt_usize _ (by norm_num))

private theorem attesterAttestCallMem_read_before_value_len (I : ExecutionEnv)
    {read len : Nat} {bytes : ByteArray}
    (hbelowValue : read + len ≤ 708) (hpos : 0 < len) (hlen64 : len < 2 ^ 64)
    (hpre : (attesterAttestCallMemBytesLen I).readWithPadding read len = bytes) :
    (attesterAttestCallMem I).readWithPadding read len = bytes := by
  unfold attesterAttestCallMem attesterAttestCallMemValue
  rw [attesterWriteWord_read_below_len _ 708 _ read len
    (by rw [attesterAttestCallMemPad_size]; omega) hbelowValue hpos hlen64
    (by rw [attesterAttestCallMemPad_size]; exact lt_usize _ (by omega))]
  unfold attesterAttestCallMemPad
  rw [attesterWriteWord_read_below_len _ 804 _ read len
    (by rw [attesterAttestCallMemBytesData_size]; omega) (by omega) hpos hlen64
    (by rw [attesterAttestCallMemBytesData_size]; exact lt_usize _ (by omega))]
  unfold attesterAttestCallMemBytesData
  rw [show (772 : Nat) = (attesterAttestCallMemBytesLen I).size by
      rw [attesterAttestCallMemBytesLen_size]]
  rw [write_read_below_end_from_len (attesterAttestCallMemBytesLen I)
    (attesterAttestCallMemBytesLen I) 416 32 read len (by norm_num)
    (by rw [attesterAttestCallMemBytesLen_size]; norm_num)
    (by rw [attesterAttestCallMemBytesLen_size]; omega)
    (by rw [attesterAttestCallMemBytesLen_size]; omega)
    hpos hlen64]
  exact hpre

theorem attesterAttestCallMem_read448_4 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 448 4 = attestSelector := by
  exact attesterAttestCallMem_read_before_value_len I (by norm_num) (by norm_num)
    (by norm_num) (attesterAttestCallMemBytesLen_read448_4 I)

theorem attesterAttestCallMem_read452 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 452 32 = UInt256.toByteArray ⟨32⟩ := by
  exact attesterAttestCallMem_read_before_value_len I (by norm_num) (by norm_num)
    (by norm_num) (attesterAttestCallMemBytesLen_read452 I)

theorem attesterAttestCallMem_read484 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 484 32 =
      UInt256.toByteArray (attesterAttestSchemaWord I) := by
  exact attesterAttestCallMem_read_before_value_len I (by norm_num) (by norm_num)
    (by norm_num) (attesterAttestCallMemBytesLen_read484 I)

theorem attesterAttestCallMem_read516 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 516 32 = UInt256.toByteArray ⟨64⟩ := by
  exact attesterAttestCallMem_read_before_value_len I (by norm_num) (by norm_num)
    (by norm_num) (attesterAttestCallMemBytesLen_read516 I)

theorem attesterAttestCallMem_read548 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 548 32 = UInt256.toByteArray ⟨0⟩ := by
  exact attesterAttestCallMem_read_before_value_len I (by norm_num) (by norm_num)
    (by norm_num) (attesterAttestCallMemBytesLen_read548 I)

theorem attesterAttestCallMem_read580 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 580 32 = UInt256.toByteArray ⟨0⟩ := by
  exact attesterAttestCallMem_read_before_value_len I (by norm_num) (by norm_num)
    (by norm_num) (attesterAttestCallMemBytesLen_read580 I)

theorem attesterAttestCallMem_read612 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 612 32 = UInt256.toByteArray ⟨1⟩ := by
  exact attesterAttestCallMem_read_before_value_len I (by norm_num) (by norm_num)
    (by norm_num) (attesterAttestCallMemBytesLen_read612 I)

theorem attesterAttestCallMem_read644 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 644 32 = UInt256.toByteArray ⟨0⟩ := by
  exact attesterAttestCallMem_read_before_value_len I (by norm_num) (by norm_num)
    (by norm_num) (attesterAttestCallMemBytesLen_read644 I)

theorem attesterAttestCallMem_read676 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 676 32 = UInt256.toByteArray ⟨192⟩ := by
  exact attesterAttestCallMem_read_before_value_len I (by norm_num) (by norm_num)
    (by norm_num) (attesterAttestCallMemBytesLen_read676 I)

theorem attesterAttestCallMem_read708 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 708 32 = UInt256.toByteArray ⟨0⟩ := by
  unfold attesterAttestCallMem attesterAttestCallMemValue
  exact attesterWriteWord_read_back _ _ _ (by
    rw [attesterAttestCallMemPad_size]
    exact lt_usize _ (by norm_num))

theorem attesterAttestCallMem_read740 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 740 32 = UInt256.toByteArray ⟨32⟩ := by
  unfold attesterAttestCallMem attesterAttestCallMemValue
  rw [attesterWriteWord_read_above_len _ 708 _ 740 32
    (by rw [attesterAttestCallMemPad_size]; norm_num) (by norm_num)
    (by rw [attesterAttestCallMemPad_size]; norm_num) (by norm_num) (by norm_num)]
  unfold attesterAttestCallMemPad
  rw [attesterWriteWord_read_below_len _ 804 _ 740 32
    (by rw [attesterAttestCallMemBytesData_size]; norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMemBytesData_size]; exact lt_usize _ (by norm_num))]
  unfold attesterAttestCallMemBytesData
  rw [show (772 : Nat) = (attesterAttestCallMemBytesLen I).size by
      rw [attesterAttestCallMemBytesLen_size]]
  rw [write_read_below_end_from (attesterAttestCallMemBytesLen I)
    (attesterAttestCallMemBytesLen I) 416 32 740 (by norm_num)
    (by rw [attesterAttestCallMemBytesLen_size]; norm_num)
    (by rw [attesterAttestCallMemBytesLen_size])]
  exact attesterAttestCallMemBytesLen_read740 I

theorem attesterAttestCallMemBytesData_read772 (I : ExecutionEnv) :
    (attesterAttestCallMemBytesData I).readWithPadding 772 32 =
      UInt256.toByteArray (attesterAttestInputWord I) := by
  unfold attesterAttestCallMemBytesData
  rw [show (772 : Nat) = (attesterAttestCallMemBytesLen I).size by
      rw [attesterAttestCallMemBytesLen_size]]
  rw [readWithPadding_eq_extract' _ (attesterAttestCallMemBytesLen I).size 32
    (by norm_num) (by norm_num) (by
      rw [write_end_size_from (attesterAttestCallMemBytesLen I)
        (attesterAttestCallMemBytesLen I) 416 32 (by norm_num)
        (by rw [attesterAttestCallMemBytesLen_size]; norm_num)])]
  rw [write_end_extract_tail_from (attesterAttestCallMemBytesLen I)
    (attesterAttestCallMemBytesLen I) 416 32 (by norm_num)
    (by rw [attesterAttestCallMemBytesLen_size]; norm_num)]
  rw [← readWithPadding_eq_extract' (attesterAttestCallMemBytesLen I) 416 32
    (by norm_num) (by norm_num) (by rw [attesterAttestCallMemBytesLen_size]; norm_num)]
  exact attesterAttestCallMemBytesLen_read416 I

theorem attesterAttestCallMem_read772 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 772 32 =
      UInt256.toByteArray (attesterAttestInputWord I) := by
  unfold attesterAttestCallMem attesterAttestCallMemValue
  rw [attesterWriteWord_read_above_len _ 708 _ 772 32
    (by rw [attesterAttestCallMemPad_size]; norm_num) (by norm_num)
    (by rw [attesterAttestCallMemPad_size]; norm_num) (by norm_num) (by norm_num)]
  unfold attesterAttestCallMemPad
  rw [attesterWriteWord_read_below_len _ 804 _ 772 32
    (by rw [attesterAttestCallMemBytesData_size]) (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMemBytesData_size]; exact lt_usize _ (by norm_num))]
  exact attesterAttestCallMemBytesData_read772 I

theorem attesterAttestCallMem_read448_356 (I : ExecutionEnv) :
    (attesterAttestCallMem I).readWithPadding 448 356 =
      attesterAttestExternalCalldata I := by
  rw [show (356 : Nat) = 4 + 352 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 448 4 352
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read448_4]
  rw [show (352 : Nat) = 32 + 320 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 452 32 320
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read452]
  rw [show (320 : Nat) = 32 + 288 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 484 32 288
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read484]
  rw [show (288 : Nat) = 32 + 256 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 516 32 256
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read516]
  rw [show (256 : Nat) = 32 + 224 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 548 32 224
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read548]
  rw [show (224 : Nat) = 32 + 192 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 580 32 192
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read580]
  rw [show (192 : Nat) = 32 + 160 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 612 32 160
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read612]
  rw [show (160 : Nat) = 32 + 128 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 644 32 128
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read644]
  rw [show (128 : Nat) = 32 + 96 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 676 32 96
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read676]
  rw [show (96 : Nat) = 32 + 64 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 708 32 64
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read708]
  rw [show (64 : Nat) = 32 + 32 by norm_num]
  rw [byteArray_readWithPadding_split (attesterAttestCallMem I) 740 32 32
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by rw [attesterAttestCallMem_size]; norm_num)]
  rw [attesterAttestCallMem_read740, attesterAttestCallMem_read772]
  unfold attesterAttestExternalCalldata
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem attesterAttestSchemaBytes_eq_toBytesBE {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    attesterAttestSchemaBytes I = EVM.Word.toBytesBE (attesterAttestSchemaWord I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hlen : (attesterAttestSchemaBytes I).length = 32 := by
    simp [attesterAttestSchemaBytes, List.length_take, List.length_drop, htlen]
    omega
  have hword : ABI.bytesToWord (attesterAttestSchemaBytes I) =
      attesterAttestSchemaWord I := by
    simpa [attesterAttestSchemaBytes, attesterAttestSchemaWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [← hword]
  exact (toBytesBE_bytesToWord_of_length hlen).symm

theorem attesterEncodeAttest_eq (v : AttesterImmutables) {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    (config v).externalABI.encode? "attest" (attesterAttestArgVals I) =
      some (attesterAttestExternalCalldata I) := by
  have hschema := attesterAttestSchemaBytes_eq_toBytesBE (I := I) hsz68
  have hschemaLen : (EVM.Word.toBytesBE (attesterAttestSchemaWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (attesterAttestSchemaWord I)
  have hinputSize : (UInt256.toByteArray (attesterAttestInputWord I)).size = 32 :=
    toByteArray_size _
  have hinputListLen :
      (UInt256.toByteArray (attesterAttestInputWord I)).toList.length = 32 := by
    rw [byteArray_toList_eq, Array.length_toList]
    exact hinputSize
  have hpow64 : 0 < EVM.twoPow 64 := by norm_num [EVM.twoPow]
  have hpow256 : 0 < EVM.twoPow 256 := by norm_num [EVM.twoPow]
  have hzeroLen : (EVM.Word.ofNat 0).toBytesBE.length = 32 := by
    simpa [list_toByteArray_size] using word_toBytesBE_toByteArray_size (EVM.Word.ofNat 0)
  have hword32 : EVM.Word.ofNat 32 = (⟨32⟩ : UInt256) := by native_decide
  have hword64 : EVM.Word.ofNat 64 = (⟨64⟩ : UInt256) := by native_decide
  have hword192 : EVM.Word.ofNat 192 = (⟨192⟩ : UInt256) := by native_decide
  have hwordNat0 : EVM.Word.ofNat 0 = (⟨0⟩ : UInt256) := by native_decide
  have hword0 : EVM.word 0 = (⟨0⟩ : UInt256) := rfl
  have haddr0Word : EVM.word ↑(AccountAddress.ofNat 0) = (⟨0⟩ : UInt256) := by native_decide
  have honeWord : UInt256.ofNat 1 = (⟨1⟩ : UInt256) := UInt256_ofNat_1
  simp [config, attesterExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIArrayElems?,
    ABI.encodeABIStaticArrayElems?, ABI.encodeABIDynamicArrayElemsFrom?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.staticABIEncodedSizeList?,
    ABI.isDynamicABIType, ABI.isDynamicABITypeList,
    attesterAttestArgVals, attesterAttestRequestValue, attesterAttestDataValue,
    attesterAttestExternalCalldata, attestationRequestTy, attestationRequestDataTy,
    addr, uint64, uint64Int, boolTy, bytes32, bytes32Width, bytesTy, uint256, uint256Int,
    attestSelector, selectorBytes, hschema, hschemaLen, hinputSize, hinputListLen, hpow64,
    hpow256, hzeroLen, ABI.natBytes,
    ABI.padRightToWord, ABI.paddedSize, ABI.zeroBytes,
    word_toBytesBE_toByteArray_eq_toByteArray, list_toByteArray_append]
  apply ByteArray.ext
  simp [ByteArray.data_append, ByteArray.append_assoc, byteArray_toList_toByteArray,
    hword32, hword64, hword192, hwordNat0, hword0, haddr0Word, honeWord]

@[simp] theorem attesterAbiEncodeUint256Call (w : UInt256) :
    attesterExternalABI.encode? "__abi_encode_uint256" [.int (Int.ofNat w.toNat)] =
      some (abiEncodeUint256Selector ++ UInt256.toByteArray w) := by
  have hword : EVM.word w.toNat = w := by
    show UInt256.ofNat w.toNat = w
    exact u256_ofNat_toNat w
  have hlt : w.toNat < EVM.twoPow 256 := by
    change w.val.val < EVM.twoPow 256
    exact w.val.isLt
  simp [attesterExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    abiEncodeUint256Selector, selectorBytes, uint256, uint256Int, hword, hlt,
    word_toBytesBE_toByteArray_eq_toByteArray]

@[simp] theorem attesterAbiEncodeUint256Slice (w : UInt256) :
    sliceBytes? (abiEncodeUint256Selector ++ UInt256.toByteArray w) 4 36 =
      .ok (.bytes (UInt256.toByteArray w)) := by
  unfold sliceBytes?
  simp [abiEncodeUint256Selector, selectorBytes]
  rw [show ({ data := #[0, 0, 0, 0] } : ByteArray).size = 4 by rfl]
  simp
  rw [extract_append_right']
  · rfl
  · rw [show ({ data := #[0, 0, 0, 0] } : ByteArray).size = 4 by rfl, toByteArray_size]

@[simp] theorem attesterEvalAbiEncodeUint256Input (v : AttesterImmutables)
    (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v)
        { contract := contract v, locals := attesterAttestStore I } evm
        (abiEncodeUint256 (.var "input")) =
      .ok (.bytes (UInt256.toByteArray (attesterAttestInputWord I))) := by
  simp [abiEncodeUint256, evalExpr?, evalExprList?, EvalResult.bind, bind, pure,
    EvalResult.ofOption, attesterAttestStore, config]
  have hcall :
      attesterExternalABI.encode? "__abi_encode_uint256"
          [Value.int ↑(attesterAttestInputWord I).toNat] =
        some (abiEncodeUint256Selector ++ UInt256.toByteArray (attesterAttestInputWord I)) := by
    simpa using attesterAbiEncodeUint256Call (attesterAttestInputWord I)
  rw [hcall]
  simp [attesterAbiEncodeUint256Slice]

theorem attesterEvalAttestArgs (v : AttesterImmutables) (evm : EVM.State)
    (I : ExecutionEnv) :
    evalExprs? (config v)
        { contract := contract v, locals := attesterAttestStore I } evm
        [attestationRequest (.var "schema") (.var "input")] =
      .ok (attesterAttestArgVals I) := by
  have habi := attesterEvalAbiEncodeUint256Input v evm I
  simp [attesterAttestStore, attesterAttestInputWord] at habi
  simp [attesterAttestArgVals, attesterAttestRequestValue, attesterAttestDataValue,
    attestationRequest, attestationData, attesterAttestStore,
    attesterAttestInputWord, evalExprs?, evalExprList?, evalExpr?, EvalResult.bind,
    bind, pure, EvalResult.ofOption, castValue?, zeroAddr, zeroBytes32, addrSt, bytes32St,
    selectorBytes, abiEncodeUint256Selector, uint256, uint256Int, habi,
    Std.HashMap.getElem_insert]

theorem attesterDecodeABIValues_bytes32_uint256_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [bytes32, uint256] bytes 0 0 64 64 =
      some ([.fixedBytes bytes32Width (bytes.take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, bytes32, bytes32Width, uint256, uint256Int, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  rw [if_pos]
  · simp [UInt256.toNat]
  · exact (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt

theorem attesterDecodeABIValues_bytes32_uint256_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [bytes32, uint256] bytes 0 0 64 64 = none := by
  simp only [decodeABIValues?, bytes32, bytes32Width, uint256, uint256Int, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, zeroPadding?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp [decodeABIValue?, readBytes?, zeroPadding?, htake0]
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [readWord?, readBytes?, hnot]

theorem attesterDecodeABIValues_bytes32_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32) :
    decodeABIValues? [bytes32] bytes 0 0 32 32 =
      some ([.fixedBytes bytes32Width (bytes.take 32)], 32) := by
  simp [decodeABIValues?, bytes32, bytes32Width, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hlen0]

theorem attesterDecodeABIValues_bytes32_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeABIValues? [bytes32] bytes 0 0 32 32 = none := by
  have hnot : ¬ 32 ≤ bytes.length := by omega
  simp [decodeABIValues?, bytes32, bytes32Width, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, zeroPadding?, hnot]

theorem attesterDecodeReturnValue_bytes32_ok {returndata : ByteArray}
    (hlo : 32 ≤ returndata.size) (hhi : returndata.size < 2 ^ 255) :
    ABI.decodeReturnValue? bytes32 returndata =
      some (.fixedBytes bytes32Width
        (EVM.Word.toBytesBE (uInt256OfByteArray (returndata.extract 0 32)))) := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : (returndata.toList.take 32).length = 32 := by
    rw [List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := returndata)
  have hword : ABI.bytesToWord (returndata.toList.take 32) =
      uInt256OfByteArray (returndata.extract 0 32) := by
    rw [hwordList, uInt256OfByteArray_eq]
  have hbytes :
      EVM.Word.toBytesBE (uInt256OfByteArray (returndata.extract 0 32)) =
        returndata.toList.take 32 := by
    rw [← hword]
    exact toBytesBE_bytesToWord_of_length htake0
  rw [hbytes]
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues?
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  rw [show ABI.abiTupleHeadSize? [bytes32] = some 32 by native_decide]
  simp only [bind, Option.bind]
  rw [attesterDecodeABIValues_bytes32_ok (bytes := returndata.toList) htake0]

theorem attesterDecodeReturnValue_bytes32_none_short {returndata : ByteArray}
    (hshort : returndata.size < 32) :
    ABI.decodeReturnValue? bytes32 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues?
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [hlen] at hhuge
    omega)]
  rw [show ABI.abiTupleHeadSize? [bytes32] = some 32 by native_decide]
  simp only [bind, Option.bind]
  rw [attesterDecodeABIValues_bytes32_none_short (bytes := returndata.toList) (by rw [hlen]; omega)]

theorem attesterDecodeReturnValue_bytes32_none_huge {returndata : ByteArray}
    (hhuge : 2 ^ 255 ≤ returndata.size) :
    ABI.decodeReturnValue? bytes32 returndata = none := by
  have hlen : returndata.toList.length = returndata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues?
  rw [if_pos (by exact ⟨by simp, by rw [hlen]; exact hhuge⟩)]

theorem attesterDecode_attest_return_ok (v : AttesterImmutables) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (ho255 : o.size < 2 ^ 255) :
    (config v).externalABI.decode? "attest" o =
      some [.fixedBytes bytes32Width
        (EVM.Word.toBytesBE (uInt256OfByteArray (o.extract 0 32)))] := by
  change decodeReturn? bytes32 o =
    some [.fixedBytes bytes32Width
      (EVM.Word.toBytesBE (uInt256OfByteArray (o.extract 0 32)))]
  unfold decodeReturn?
  rw [attesterDecodeReturnValue_bytes32_ok ho32 ho255]
  rfl

theorem attesterDecode_attest_return_none_short (v : AttesterImmutables) {o : ByteArray}
    (hshort : o.size < 32) :
    (config v).externalABI.decode? "attest" o = none := by
  change decodeReturn? bytes32 o = none
  unfold decodeReturn?
  rw [attesterDecodeReturnValue_bytes32_none_short hshort]
  rfl

theorem attesterDecode_attest_return_none_huge (v : AttesterImmutables) {o : ByteArray}
    (hhuge : 2 ^ 255 ≤ o.size) :
    (config v).externalABI.decode? "attest" o = none := by
  change decodeReturn? bytes32 o = none
  unfold decodeReturn?
  rw [attesterDecodeReturnValue_bytes32_none_huge hhuge]
  rfl

theorem attesterDecode_attest_ok (v : AttesterImmutables) {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((attestTransition v).params.map Param.name)
        (transitionSignature (attestTransition v)).paramTypes I.calldata =
      some (attesterAttestStore I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      calldataWord I.calldata 36 := by
    exact decode_word_at_eq I.calldata 36 (by omega) (by norm_num)
  show decodeCalldata ["schema", "input"] [bytes32, uint256] I.calldata =
    some (attesterAttestStore I)
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, uint256, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, uint256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [attesterDecodeABIValues_bytes32_uint256_ok (bytes := I.calldata.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (I.calldata.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues, attesterAttestStore, attesterAttestSchemaBytes,
    attesterAttestInputWord]
  rw [hword36]

theorem attesterDecode_attest_none_short (v : AttesterImmutables) {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((attestTransition v).params.map Param.name)
        (transitionSignature (attestTransition v)).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["schema", "input"] [bytes32, uint256] I.calldata = none
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, uint256, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, uint256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [attesterDecodeABIValues_bytes32_uint256_none_short
    (bytes := I.calldata.toList.drop 4) (by rw [List.length_drop, htlen]; omega)]
  rw [if_pos (by rw [List.length_drop, htlen]; omega :
    (I.calldata.toList.drop 4).length < 64)]

theorem attesterDecode_attest_none_huge (v : AttesterImmutables) {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
        ((attestTransition v).params.map Param.name)
        (transitionSignature (attestTransition v)).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["schema", "input"] [bytes32, uint256] I.calldata = none
  unfold decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by simp [bytes32, uint256, isDynamicABIType])]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem attesterAttestBodySuccess (v : AttesterImmutables)
    (evm evm' : EVM.State) (locals : Store) {argVals : List Value}
    {out : ByteArray} {uid : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hargs : evalExprs? (config v) { contract := contract v, locals := locals } evm
      [attestationRequest (.var "schema") (.var "input")] = .ok argVals)
    (hcall : typedCallViaEVM (config v) evm (EVM.address v.eas) "attest" 0 argVals
      (true, evm', out))
    (hdec : (config v).externalABI.decode? "attest" out = some [uid]) :
    ExecTransitionBody (config v) (contract v) evm locals (attestTransition v).body
      (.returned { contract := contract v, locals := locals.insert "uid" uid } evm'
        (some [uid])) := by
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.externalCallSuccess
          (attesterEvalEasExpr v { contract := contract v, locals := locals } evm)
          (by simp [evalExpr?, pure]) hargs hcall hdec) <|
        ExecBlock.consReturn (ExecStmt.return (by
          simp [evalExprs?, evalExpr?, EvalResult.bind, bind, pure, collapseReturns,
            EvalResult.ofOption]))

theorem attesterAttestBodyCallFailure (v : AttesterImmutables)
    (evm evm' : EVM.State) (locals : Store) {argVals : List Value}
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hargs : evalExprs? (config v) { contract := contract v, locals := locals } evm
      [attestationRequest (.var "schema") (.var "input")] = .ok argVals)
    (hcall : typedCallViaEVM (config v) evm (EVM.address v.eas) "attest" 0 argVals
      (false, evm', out)) :
    ExecTransitionBody (config v) (contract v) evm locals (attestTransition v).body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.externalCallFailure
          (attesterEvalEasExpr v { contract := contract v, locals := locals } evm)
          (by simp [evalExpr?, pure]) hargs hcall)

theorem attesterAttestBodyDecodeRevert (v : AttesterImmutables)
    (evm evm' : EVM.State) (locals : Store) {argVals : List Value}
    {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hargs : evalExprs? (config v) { contract := contract v, locals := locals } evm
      [attestationRequest (.var "schema") (.var "input")] = .ok argVals)
    (hcall : typedCallViaEVM (config v) evm (EVM.address v.eas) "attest" 0 argVals
      (true, evm', out))
    (hdec : (config v).externalABI.decode? "attest" out = none) :
    ExecTransitionBody (config v) (contract v) evm locals (attestTransition v).body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert
        (ExecStmt.externalCallReturnDecodeRevert
          (attesterEvalEasExpr v { contract := contract v, locals := locals } evm)
          (by simp [evalExpr?, pure]) hargs hcall hdec)

theorem attesterX_attestWrapper {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = true) :
    ∃ k C, RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨140⟩ : UInt256)
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
    (by attester_decode) (by attester_decode) (by attester_decode)
    (by attester_decode) (by attester_decode) (by attester_decode)
  obtain ⟨_, _, h17⟩ := solcGuardCallvalueZero
    (ctgt := (⟨15⟩ : UInt256)) (opC := .PUSH2) (wC := 2)
    h0 hwv (by decide) (by attester_decode)
    (by attester_decode) (by attester_decode)
    (by attester_decode) (attesterGuardJumpdest v)
  obtain ⟨k25, C25, h25raw⟩ := solcCalldataOk
    (bodyPc := (⟨17⟩ : UInt256)) (selLoadTgt := attesterDispatchRevertPc)
    (opR := .PUSH2) (wR := 2)
    h17 hsz hsize (by attester_decode) (by attester_decode) (by attester_decode)
    (by decide) (by attester_decode) (by attester_decode)
  have h25 :
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) (⟨25⟩ : UInt256)
        [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k25 C25 := by
    simpa using h25raw
  obtain ⟨k30, C30, h30raw⟩ := solcSelectorLoad h25
    (by attester_decode) (by attester_decode) (by attester_decode) (by attester_decode) (by simp)
  have h30 :
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) attesterFirstArmPc
        [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k30 C30 := by
    simpa [attesterFirstArmPc, solcSelectorWord] using h30raw
  have heqMultiRevoke := attesterMultiRevokeEqZero I hsz hmultiRevoke
  have heqMultiAttest := attesterMultiAttestEqZero I hsz hmultiAttest
  have heqAttest := attesterAttestEqNonzero I hsz hattest
  exact ⟨_, _, h30
    |>.selectorArmNotTaken (selNat := (⟨0x13fde550⟩ : UInt256))
      (tgt := (⟨78⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqMultiRevoke (by simp)
    |>.selectorArmNotTaken (selNat := (⟨0x54e1db35⟩ : UInt256))
      (tgt := (⟨99⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqMultiAttest (by simp)
    |>.selectorArmTaken (selNat := (⟨0x72b9966d⟩ : UInt256))
      (tgt := (⟨140⟩ : UInt256)) (width := 2) (op := .PUSH2)
      (by attester_decode) (by attester_decode) (by attester_decode)
      (by decide) (by attester_decode) (by attester_decode) heqAttest
      (attesterAttestWrapperJumpdest v) (by simp)⟩

theorem attesterX_attestToDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨140⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2281⟩ : UInt256)
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨154⟩, ⟨159⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd140⟩ := hreach
  exact ⟨_, _, evm_run rd140 with [
    raw jumpdest (by attester_decode) (by evm_ov),
    raw push2 ⟨159⟩ (by attester_decode) (by evm_ov),
    raw push2 ⟨154⟩ (by attester_decode) (by evm_ov),
    raw calldatasize (by attester_decode) (by evm_ov),
    raw push1 ⟨4⟩ (by attester_decode) (by evm_ov),
    raw push2 ⟨2281⟩ (by attester_decode) (by evm_ov),
    raw jump (by attester_decode) (attesterAttestDecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_attestDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨140⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd2281⟩ := attesterX_attestToDecoder (v := v) hreach
  exact evm_run rd2281 with [
    raw jumpdest (by attester_decode_at v, ⟨2281⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2282⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2283⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2284⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2286⟩, 0x83, .DUP4) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2287⟩, 0x85, .DUP6) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2288⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2289⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2290⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2298⟩ (by attester_decode_at v, ⟨2291⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2294⟩, 0x57, .JUMPI) (by rw [hslt]; decide)
      (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2295⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2296⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2297⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_attestDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = true) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  exact attesterX_attestDecodeRevert (v := v) hslt
    (attesterX_attestWrapper (g := g) v hcode hwv hsz4 hsize hmultiRevoke hmultiAttest hattest)

theorem attesterX_attestDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = true) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  exact attesterX_attestDecodeRevert (v := v) hslt
    (attesterX_attestWrapper (g := g) v hcode hwv hsz4 hsize hmultiRevoke hmultiAttest hattest)

theorem attesterX_attestDecoded {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨140⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1595⟩ : UInt256)
      [attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hsmall hsize
  obtain ⟨_, _, rd2281⟩ := attesterX_attestToDecoder (v := v) hreach
  have rd154 := evm_run rd2281 with [
    raw jumpdest (by attester_decode_at v, ⟨2281⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2282⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2283⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2284⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2286⟩, 0x83, .DUP4) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2287⟩, 0x85, .DUP6) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2288⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2289⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2290⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2298⟩ (by attester_decode_at v, ⟨2291⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2294⟩, 0x57, .JUMPI)
      (by rw [hslt]; decide) (attesterAttestDecodeOkJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨2298⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2299⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2300⟩, 0x50, .POP) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2301⟩, 0x80, .DUP1) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2302⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2303⟩, 0x92, .SWAP3) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2304⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2306⟩, 0x90, .SWAP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2307⟩, 0x91, .SWAP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2308⟩, 0x01, .ADD) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2309⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2310⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2311⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2312⟩, 0x56, .JUMP)
      (attesterAttestDecodedJumpdest v) (by evm_ov)]
  have rd1595 := evm_run rd154 with [
    raw jumpdest (by attester_decode_at v, ⟨154⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push2 ⟨1595⟩ (by attester_decode_at v, ⟨155⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨158⟩, 0x56, .JUMP)
      (attesterAttestBodyJumpdest v) (by evm_ov)]
  exact ⟨_, _, by
    simpa [attesterAttestInputWord, attesterAttestSchemaWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide] using rd1595⟩

set_option maxRecDepth 10000 in
theorem attesterX_attestToEncodeTail {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨140⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1737⟩ : UInt256)
      [⟨448⟩, ⟨320⟩, ⟨192⟩, ⟨160⟩, ⟨128⟩, ⟨0xf17325e7⟩,
        attesterAttestTargetWord v, ⟨0⟩, attesterAttestInputWord I,
        attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      (attesterAttestMemInputWord I) (UInt256.ofNat 14) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1595⟩ := attesterX_attestDecoded (v := v) hsz68 hsize hsmall hreach
  have rd1597 := evm_run rd1595 with [
    raw jumpdest (by attester_decode_at v, ⟨1595⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1596⟩, 0x5f, .PUSH0) (by evm_ov)]
  have rd1630 := rd1597.pushConst (attesterAttestEasWord v) (width := 32) (op := .PUSH32)
    (by decide) (attesterDecodeEasWord1597 v) (by evm_ov)
  have rd1737 := evm_run rd1630 with [
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1630⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1632⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨160⟩ (by attester_decode_at v, ⟨1634⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨1636⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨1637⟩, 0x03, .SUB) (by evm_ov),
    raw and (by attester_decode_at v, ⟨1638⟩, 0x16, .AND) (by evm_ov),
    raw push4 ⟨0xf17325e7⟩ (by attester_decode_at v, ⟨1639⟩, 0x63, (.Push .PUSH4))
      (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1644⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by attester_decode_at v, ⟨1646⟩, 0x51, .MLOAD)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1647⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1648⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1650⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1651⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mstore 0 attesterAttestMem192 (UInt256.ofNat 3)
      (by attester_decode_at v, ⟨1653⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1654⟩, 0x80, .DUP1) (by evm_ov),
    raw dup7 (by attester_decode_at v, ⟨1655⟩, 0x86, .DUP7) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1656⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 (attesterAttestMemSchema I) (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨1657⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1658⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1660⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1661⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨192⟩ (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨1663⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestMemSchema_size I]; decide) (by decide)
        (attesterAttestMemSchema_read64 I))
      (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1664⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨192⟩ (by attester_decode_at v, ⟨1665⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1667⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1668⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mstore 0 (attesterAttestMem384 I) (UInt256.ofNat 5)
      (by attester_decode_at v, ⟨1670⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1671⟩, 0x80, .DUP1) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1672⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1673⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1675⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨160⟩ (by attester_decode_at v, ⟨1677⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨1679⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨1680⟩, 0x03, .SUB) (by evm_ov),
    raw and (by attester_decode_at v, ⟨1681⟩, 0x16, .AND) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1682⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 6 (attesterAttestMemRecipient I) (UInt256.ofNat 7)
      (by attester_decode_at v, ⟨1683⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask by decide]
        rw [show UInt256.land solcAddrMask (⟨0⟩ : UInt256) = ⟨0⟩ by decide]
        rw [show (⟨192⟩ : UInt256).toNat = 192 by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1684⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1686⟩, 0x01, .ADD) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1687⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1688⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1690⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1692⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨1694⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨1695⟩, 0x03, .SUB) (by evm_ov),
    raw and (by attester_decode_at v, ⟨1696⟩, 0x16, .AND) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1697⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 3 (attesterAttestMemExpiration I) (UInt256.ofNat 8)
      (by attester_decode_at v, ⟨1698⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩ =
            (⟨18446744073709551615⟩ : UInt256) by decide]
        rw [show UInt256.land (⟨18446744073709551615⟩ : UInt256) ⟨0⟩ = ⟨0⟩ by decide]
        rw [show ((⟨32⟩ : UInt256) + ⟨192⟩).toNat = 224 by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1699⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1701⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨1702⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨1704⟩, 0x15, .ISZERO) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨1705⟩, 0x15, .ISZERO) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1706⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 3 (attesterAttestMemRevocable I) (UInt256.ofNat 9)
      (by attester_decode_at v, ⟨1707⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1708⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1710⟩, 0x01, .ADD) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1711⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1712⟩, 0x80, .DUP1) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨1713⟩, 0x1b, .SHL) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1714⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 3 (attesterAttestMemRefUID I) (UInt256.ofNat 10)
      (by attester_decode_at v, ⟨1715⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1716⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1718⟩, 0x01, .ADD) (by evm_ov),
    raw dup8 (by attester_decode_at v, ⟨1719⟩, 0x87, .DUP8) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1720⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 10)
      (by attester_decode_at v, ⟨1722⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestMemRefUID_size I]; decide) (by decide)
        (attesterAttestMemRefUID_read64 I))
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1723⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1725⟩, 0x01, .ADD) (by evm_ov),
    raw push2 ⟨1737⟩ (by attester_decode_at v, ⟨1726⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨1729⟩, 0x91, .SWAP2) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1730⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 12 (attesterAttestMemInputWord I) (UInt256.ofNat 14)
      (by attester_decode_at v, ⟨1731⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1732⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1734⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1735⟩, 0x90, .SWAP1) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨1736⟩, 0x56, .JUMP)
      (attesterAttestEncodeTailJumpdest v) (by evm_ov)]
  exact ⟨_, _, by
    simpa [attesterAttestTargetWord, attesterAttestEasWord,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd1737⟩

set_option maxRecDepth 10000 in
theorem attesterX_attestToEncodeRequest {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨140⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨3106⟩ : UInt256)
      [⟨452⟩, ⟨128⟩, ⟨1792⟩, ⟨0xf17325e7⟩, attesterAttestTargetWord v, ⟨0⟩,
        attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      (attesterAttestCallMemSelector I) (UInt256.ofNat 15) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1737⟩ :=
    attesterX_attestToEncodeTail (v := v) hsz68 hsize hsmall hreach
  have rd3106 := evm_run rd1737 with [
    raw jumpdest (by attester_decode_at v, ⟨1737⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1738⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 14)
      (by attester_decode_at v, ⟨1740⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestMemInputWord_size I]; decide) (by decide)
        (attesterAttestMemInputWord_read64 I))
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1741⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1743⟩, 0x81, .DUP2) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1744⟩, 0x83, .DUP4) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨1745⟩, 0x03, .SUB) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨1746⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1747⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 0 (attesterAttestMemBytesLen I) (UInt256.ofNat 14)
      (by attester_decode_at v, ⟨1748⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1749⟩, 0x90, .SWAP1) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1750⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mstore 0 (attesterAttestMem448 I) (UInt256.ofNat 14)
      (by attester_decode_at v, ⟨1752⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1753⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 0 (attesterAttestMemDataOffset I) (UInt256.ofNat 14)
      (by attester_decode_at v, ⟨1754⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1755⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1757⟩, 0x01, .ADD) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1758⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1759⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 0 (attesterAttestMemDataPad I) (UInt256.ofNat 14)
      (by attester_decode_at v, ⟨1760⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1761⟩, 0x50, .POP) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1762⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 0 (attesterAttestSourceMem I) (UInt256.ofNat 14)
      (by attester_decode_at v, ⟨1763⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1764⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1765⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨448⟩ (UInt256.ofNat 14)
      (by attester_decode_at v, ⟨1767⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestSourceMem_size I]; decide) (by decide)
        (attesterAttestSourceMem_read64 I))
      (by decide) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨1768⟩, 0x82, .DUP3) (by evm_ov),
    raw push4 ⟨0xffffffff⟩ (by attester_decode_at v, ⟨1769⟩, 0x63, (.Push .PUSH4))
      (by evm_ov),
    raw and (by attester_decode_at v, ⟨1774⟩, 0x16, .AND) (by evm_ov),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨1775⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨1777⟩, 0x1b, .SHL) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1778⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 3 (attesterAttestCallMemSelector I) (UInt256.ofNat 15)
      (by attester_decode_at v, ⟨1779⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show UInt256.land (⟨0xffffffff⟩ : UInt256) ⟨0xf17325e7⟩ = ⟨0xf17325e7⟩
          by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by attester_decode_at v, ⟨1780⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨1782⟩, 0x01, .ADD) (by evm_ov),
    raw push2 ⟨1792⟩ (by attester_decode_at v, ⟨1783⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨1786⟩, 0x91, .SWAP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨1787⟩, 0x90, .SWAP1) (by evm_ov),
    raw push2 ⟨3106⟩ (by attester_decode_at v, ⟨1788⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨1791⟩, 0x56, .JUMP)
      (attesterAttestEncodeRequestJumpdest v) (by evm_ov)]
  exact ⟨_, _, rd3106⟩

set_option maxRecDepth 10000 in
theorem attesterX_attestToTupleEncoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨140⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2604⟩ : UInt256)
      [⟨192⟩, ⟨548⟩, ⟨3142⟩, ⟨192⟩, ⟨0⟩, ⟨452⟩, ⟨128⟩, ⟨1792⟩,
        ⟨0xf17325e7⟩, attesterAttestTargetWord v, ⟨0⟩, attesterAttestInputWord I,
        attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      (attesterAttestCallMemDataOffset I) (UInt256.ofNat 18) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3106⟩ :=
    attesterX_attestToEncodeRequest (v := v) hsz68 hsize hsmall hreach
  have rd2604 := evm_run rd3106 with [
    raw jumpdest (by attester_decode_at v, ⟨3106⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨3107⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨3109⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore 3 (attesterAttestCallMemArgOffset I) (UInt256.ofNat 16)
      (by attester_decode_at v, ⟨3110⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨3111⟩, 0x81, .DUP2) (by evm_ov),
    raw mload 0 (attesterAttestSchemaWord I) (UInt256.ofNat 16)
      (by attester_decode_at v, ⟨3112⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestCallMemArgOffset_size I]; decide) (by decide)
        (attesterAttestCallMemArgOffset_read128 I))
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨3113⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨3115⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨3116⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 (attesterAttestCallMemSchema I) (UInt256.ofNat 17)
      (by attester_decode_at v, ⟨3117⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨3118⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨3119⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨3121⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨3122⟩, 0x01, .ADD) (by evm_ov),
    raw mload 0 ⟨192⟩ (UInt256.ofNat 17)
      (by attester_decode_at v, ⟨3123⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestCallMemSchema_size I]; decide) (by decide)
        (by
          rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 by decide]
          exact attesterAttestCallMemSchema_read160 I))
      (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨3124⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨3126⟩, 0x80, .DUP1) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨3127⟩, 0x84, .DUP5) (by evm_ov),
    raw add (by attester_decode_at v, ⟨3128⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 (attesterAttestCallMemDataOffset I) (UInt256.ofNat 18)
      (by attester_decode_at v, ⟨3129⟩, 0x52, .MSTORE) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push2 ⟨3142⟩ (by attester_decode_at v, ⟨3130⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨3133⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨3135⟩, 0x84, .DUP5) (by evm_ov),
    raw add (by attester_decode_at v, ⟨3136⟩, 0x01, .ADD) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨3137⟩, 0x82, .DUP3) (by evm_ov),
    raw push2 ⟨2604⟩ (by attester_decode_at v, ⟨3138⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨3141⟩, 0x56, .JUMP)
      (attesterAttestEncodeTupleJumpdest v) (by evm_ov)]
  exact ⟨_, _, by
    simpa [show ((⟨452⟩ : UInt256) + ⟨96⟩) = (⟨548⟩ : UInt256) by decide]
      using rd2604⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem attesterX_attestEncodeTuple {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨140⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨3142⟩ : UInt256)
      [⟨804⟩, ⟨192⟩, ⟨0⟩, ⟨452⟩, ⟨128⟩, ⟨1792⟩, ⟨0xf17325e7⟩,
        attesterAttestTargetWord v, ⟨0⟩, attesterAttestInputWord I,
        attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      (attesterAttestCallMem I) (UInt256.ofNat 27) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd2604⟩ :=
    attesterX_attestToTupleEncoder (v := v) hsz68 hsize hsmall hreach
  have rd2688_raw := evm_run rd2604 with [
    raw jumpdest (by attester_decode_at v, ⟨2604⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2605⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2607⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨160⟩ (by attester_decode_at v, ⟨2608⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2610⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2611⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2612⟩, 0x81, .DUP2) (by evm_ov),
    raw mload 0 ⟨0⟩ (UInt256.ofNat 18)
      (by attester_decode_at v, ⟨2613⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestCallMemDataOffset_size I]; decide) (by decide)
        (attesterAttestCallMemDataOffset_read192 I))
      (by decide) (by evm_ov),
    raw and (by attester_decode_at v, ⟨2614⟩, 0x16, .AND) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2615⟩, 0x82, .DUP3) (by evm_ov),
    raw mstore 3 (attesterAttestCallMemRecipient I) (UInt256.ofNat 19)
      (by attester_decode_at v, ⟨2616⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask by decide]
        rw [show UInt256.land (⟨0⟩ : UInt256) solcAddrMask = ⟨0⟩ by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2617⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2619⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2621⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2623⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2624⟩, 0x03, .SUB) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2625⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2627⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2628⟩, 0x01, .ADD) (by evm_ov),
    raw mload 0 ⟨0⟩ (UInt256.ofNat 19)
      (by attester_decode_at v, ⟨2629⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestCallMemRecipient_size I]; decide) (by decide)
        (by
          rw [show ((⟨192⟩ : UInt256) + ⟨32⟩).toNat = 224 by decide]
          exact attesterAttestCallMemRecipient_read224 I))
      (by decide) (by evm_ov),
    raw and (by attester_decode_at v, ⟨2630⟩, 0x16, .AND) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2631⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2633⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2634⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 (attesterAttestCallMemExpiration I) (UInt256.ofNat 20)
      (by attester_decode_at v, ⟨2635⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩ =
            (⟨18446744073709551615⟩ : UInt256) by decide]
        rw [show UInt256.land (⟨0⟩ : UInt256) (⟨18446744073709551615⟩ : UInt256) =
            ⟨0⟩ by decide]
        rw [show ((⟨548⟩ : UInt256) + ⟨32⟩).toNat = 580 by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2636⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2638⟩, 0x81, .DUP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2639⟩, 0x01, .ADD) (by evm_ov),
    raw mload 0 ⟨1⟩ (UInt256.ofNat 20)
      (by attester_decode_at v, ⟨2640⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestCallMemExpiration_size I]; decide) (by decide)
        (by
          rw [show ((⟨192⟩ : UInt256) + ⟨64⟩).toNat = 256 by decide]
          exact attesterAttestCallMemExpiration_read256 I))
      (by decide) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2641⟩, 0x15, .ISZERO) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2642⟩, 0x15, .ISZERO) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2643⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2645⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2646⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 (attesterAttestCallMemRevocable I) (UInt256.ofNat 21)
      (by attester_decode_at v, ⟨2647⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show ((⟨548⟩ : UInt256) + ⟨64⟩).toNat = 612 by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨2648⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2650⟩, 0x81, .DUP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2651⟩, 0x01, .ADD) (by evm_ov),
    raw mload 0 ⟨0⟩ (UInt256.ofNat 21)
      (by attester_decode_at v, ⟨2652⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestCallMemRevocable_size I]; decide) (by decide)
        (by
          rw [show ((⟨192⟩ : UInt256) + ⟨96⟩).toNat = 288 by decide]
          exact attesterAttestCallMemRevocable_read288 I))
      (by decide) (by evm_ov),
    raw push1 ⟨96⟩ (by attester_decode_at v, ⟨2653⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2655⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2656⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 (attesterAttestCallMemRefUID I) (UInt256.ofNat 22)
      (by attester_decode_at v, ⟨2657⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show ((⟨548⟩ : UInt256) + ⟨96⟩).toNat = 644 by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2658⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨128⟩ (by attester_decode_at v, ⟨2659⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2661⟩, 0x82, .DUP3) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2662⟩, 0x01, .ADD) (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 22)
      (by attester_decode_at v, ⟨2663⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestCallMemRefUID_size I]; decide) (by decide)
        (by
          rw [show ((⟨192⟩ : UInt256) + ⟨128⟩).toNat = 320 by decide]
          exact attesterAttestCallMemRefUID_read320 I))
      (by decide) (by evm_ov),
    raw push1 ⟨192⟩ (by attester_decode_at v, ⟨2664⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨128⟩ (by attester_decode_at v, ⟨2666⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup6 (by attester_decode_at v, ⟨2668⟩, 0x85, .DUP6) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2669⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 4 (attesterAttestCallMemBytesOffset I) (UInt256.ofNat 23)
      (by attester_decode_at v, ⟨2670⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show ((⟨548⟩ : UInt256) + ⟨128⟩).toNat = 676 by decide]
        rfl)
      (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2671⟩, 0x80, .DUP1) (by evm_ov),
    raw mload 0 ⟨32⟩ (UInt256.ofNat 23)
      (by attester_decode_at v, ⟨2672⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestCallMemBytesOffset_size I]; decide) (by decide)
        (attesterAttestCallMemBytesOffset_read384 I))
      (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2673⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨192⟩ (by attester_decode_at v, ⟨2674⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup7 (by attester_decode_at v, ⟨2676⟩, 0x86, .DUP7) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2677⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 6 (attesterAttestCallMemBytesLen I) (UInt256.ofNat 25)
      (by attester_decode_at v, ⟨2678⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show ((⟨548⟩ : UInt256) + ⟨192⟩).toNat = 740 by decide]
        rfl)
      (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2679⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2680⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2682⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2683⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨2684⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup8 (by attester_decode_at v, ⟨2686⟩, 0x87, .DUP8) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2687⟩, 0x01, .ADD) (by evm_ov)]
  have hrd2688 :
      ∃ k C, RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨2688⟩ : UInt256)
        [⟨772⟩, ⟨416⟩, ⟨32⟩, ⟨32⟩, ⟨384⟩, ⟨0⟩, ⟨192⟩, ⟨548⟩,
          ⟨3142⟩, ⟨192⟩, ⟨0⟩, ⟨452⟩, ⟨128⟩, ⟨1792⟩, ⟨0xf17325e7⟩,
          attesterAttestTargetWord v, ⟨0⟩, attesterAttestInputWord I,
          attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
        (attesterAttestCallMemBytesLen I) (UInt256.ofNat 25) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [
        show ((⟨192⟩ : UInt256) + ⟨32⟩) = (⟨224⟩ : UInt256) by decide,
        show ((⟨548⟩ : UInt256) + ⟨32⟩) = (⟨580⟩ : UInt256) by decide,
        show ((⟨192⟩ : UInt256) + ⟨64⟩) = (⟨256⟩ : UInt256) by decide,
        show ((⟨548⟩ : UInt256) + ⟨64⟩) = (⟨612⟩ : UInt256) by decide,
        show ((⟨192⟩ : UInt256) + ⟨96⟩) = (⟨288⟩ : UInt256) by decide,
        show ((⟨548⟩ : UInt256) + ⟨96⟩) = (⟨644⟩ : UInt256) by decide,
        show ((⟨192⟩ : UInt256) + ⟨128⟩) = (⟨320⟩ : UInt256) by decide,
        show ((⟨548⟩ : UInt256) + ⟨128⟩) = (⟨676⟩ : UInt256) by decide,
        show ((⟨548⟩ : UInt256) + ⟨192⟩) = (⟨740⟩ : UInt256) by decide,
        show ((⟨384⟩ : UInt256) + ⟨32⟩) = (⟨416⟩ : UInt256) by decide,
        show ((⟨548⟩ : UInt256) + ⟨224⟩) = (⟨772⟩ : UInt256) by decide,
        show UInt256.isZero (⟨1⟩ : UInt256) = (⟨0⟩ : UInt256) by decide,
        show UInt256.isZero (⟨0⟩ : UInt256) = (⟨1⟩ : UInt256) by decide,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask by decide,
        show UInt256.land (⟨0⟩ : UInt256) solcAddrMask = (⟨0⟩ : UInt256) by decide,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩ =
          (⟨18446744073709551615⟩ : UInt256) by decide,
        show UInt256.land (⟨0⟩ : UInt256) (⟨18446744073709551615⟩ : UInt256) =
          (⟨0⟩ : UInt256) by decide] using rd2688_raw⟩
  obtain ⟨_, _, rd2688⟩ := hrd2688
  have rd2689_raw := RD.mcopyLocal 3 (attesterAttestCallMemBytesData I) (UInt256.ofNat 26)
    rd2688
    (by attester_decode_at v, ⟨2688⟩, 0x5e, .MCOPY)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    (by rfl)
    (by decide)
    (by evm_ov)
  have hrd2689 :
      ∃ k C, RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨2689⟩ : UInt256)
        [⟨32⟩, ⟨384⟩, ⟨0⟩, ⟨192⟩, ⟨548⟩, ⟨3142⟩, ⟨192⟩, ⟨0⟩,
          ⟨452⟩, ⟨128⟩, ⟨1792⟩, ⟨0xf17325e7⟩, attesterAttestTargetWord v,
          ⟨0⟩, attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩,
          solcSelectorWord I]
        (attesterAttestCallMemBytesData I) (UInt256.ofNat 26) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [show ((⟨2688⟩ : UInt256) + ⟨1⟩) = (⟨2689⟩ : UInt256) by decide]
        using rd2689_raw⟩
  obtain ⟨_, _, rd2689⟩ := hrd2689
  have rd2701_raw := evm_run rd2689 with [
    raw push0 (by attester_decode_at v, ⟨2689⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨2690⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2692⟩, 0x82, .DUP3) (by evm_ov),
    raw dup8 (by attester_decode_at v, ⟨2693⟩, 0x87, .DUP8) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2694⟩, 0x01, .ADD) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2695⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 3 (attesterAttestCallMemPad I) (UInt256.ofNat 27)
      (by attester_decode_at v, ⟨2696⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show (((⟨548⟩ : UInt256) + ⟨32⟩) + ⟨224⟩).toNat = 804 by decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨160⟩ (by attester_decode_at v, ⟨2697⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2699⟩, 0x84, .DUP5) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2700⟩, 0x01, .ADD) (by evm_ov)]
  have hrd2701 :
      ∃ k C, RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨2701⟩ : UInt256)
        [⟨352⟩, ⟨32⟩, ⟨384⟩, ⟨0⟩, ⟨192⟩, ⟨548⟩, ⟨3142⟩, ⟨192⟩,
          ⟨0⟩, ⟨452⟩, ⟨128⟩, ⟨1792⟩, ⟨0xf17325e7⟩,
          attesterAttestTargetWord v, ⟨0⟩, attesterAttestInputWord I,
          attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
        (attesterAttestCallMemPad I) (UInt256.ofNat 27) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [
        show (((⟨548⟩ : UInt256) + ⟨32⟩) + ⟨224⟩) = (⟨804⟩ : UInt256) by decide,
        show ((⟨192⟩ : UInt256) + ⟨160⟩) = (⟨352⟩ : UInt256) by decide]
        using rd2701_raw⟩
  obtain ⟨_, _, rd2701⟩ := hrd2701
  have rd2707_raw := evm_run rd2701 with [
    raw mload 0 ⟨0⟩ (UInt256.ofNat 27)
      (by attester_decode_at v, ⟨2701⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestCallMemPad_size I]; decide) (by decide)
        (by simpa using attesterAttestCallMemPad_read352 I))
      (by decide) (by evm_ov),
    raw push1 ⟨160⟩ (by attester_decode_at v, ⟨2702⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup7 (by attester_decode_at v, ⟨2704⟩, 0x86, .DUP7) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2705⟩, 0x01, .ADD) (by evm_ov),
    raw mstore 0 (attesterAttestCallMemValue I) (UInt256.ofNat 27)
      (by attester_decode_at v, ⟨2706⟩, 0x52, .MSTORE) mem_cost
      (by
        rw [show ((⟨548⟩ : UInt256) + ⟨160⟩).toNat = 708 by decide]
        rfl)
      (by decide) (by evm_ov)]
  have hrd2707 :
      ∃ k C, RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨2707⟩ : UInt256)
        [⟨32⟩, ⟨384⟩, ⟨0⟩, ⟨192⟩, ⟨548⟩, ⟨3142⟩, ⟨192⟩, ⟨0⟩,
          ⟨452⟩, ⟨128⟩, ⟨1792⟩, ⟨0xf17325e7⟩, attesterAttestTargetWord v,
          ⟨0⟩, attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩,
          solcSelectorWord I]
        (attesterAttestCallMemValue I) (UInt256.ofNat 27) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [show ((⟨548⟩ : UInt256) + ⟨160⟩) = (⟨708⟩ : UInt256) by decide]
        using rd2707_raw⟩
  obtain ⟨_, _, rd2707⟩ := hrd2707
  have rd3142 := evm_run rd2707 with [
    raw push1 ⟨224⟩ (by attester_decode_at v, ⟨2707⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨31⟩ (by attester_decode_at v, ⟨2709⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw not (by attester_decode_at v, ⟨2711⟩, 0x19, .NOT) (by evm_ov),
    raw push1 ⟨31⟩ (by attester_decode_at v, ⟨2712⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2714⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2715⟩, 0x01, .ADD) (by evm_ov),
    raw and (by attester_decode_at v, ⟨2716⟩, 0x16, .AND) (by evm_ov),
    raw dup7 (by attester_decode_at v, ⟨2717⟩, 0x86, .DUP7) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2718⟩, 0x01, .ADD) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2719⟩, 0x01, .ADD) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2720⟩, 0x92, .SWAP3) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2721⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2722⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2723⟩, 0x50, .POP) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2724⟩, 0x92, .SWAP3) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2725⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2726⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2727⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2728⟩, 0x56, .JUMP)
      (attesterAttestEncodeTupleReturnJumpdest v) (by evm_ov)]
  exact ⟨_, _, by
    simpa [attesterAttestCallMem,
      show UInt256.land ((⟨32⟩ : UInt256) + ⟨31⟩) (UInt256.lnot ⟨31⟩) =
        (⟨32⟩ : UInt256) by decide,
      show ((⟨548⟩ : UInt256) + ⟨32⟩) = (⟨580⟩ : UInt256) by decide,
      show ((⟨580⟩ : UInt256) + ⟨224⟩) = (⟨804⟩ : UInt256) by decide]
      using rd3142⟩

set_option maxRecDepth 10000 in
theorem attesterX_attestToExternalCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨140⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨1804⟩ : UInt256)
      [attesterAttestTargetWord v, ⟨0⟩, ⟨448⟩, ⟨356⟩, ⟨448⟩, ⟨32⟩,
        ⟨804⟩, ⟨0xf17325e7⟩, attesterAttestTargetWord v, ⟨0⟩,
        attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      (attesterAttestCallMem I) (UInt256.ofNat 27) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3142⟩ :=
    attesterX_attestEncodeTuple (v := v) hsz68 hsize hsmall hreach
  have rd1804 := evm_run rd3142 with [
    raw jumpdest (by attester_decode_at v, ⟨3142⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap5 (by attester_decode_at v, ⟨3143⟩, 0x94, .SWAP5) (by evm_ov),
    raw swap4 (by attester_decode_at v, ⟨3144⟩, 0x93, .SWAP4) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨3145⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨3146⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨3147⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨3148⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨3149⟩, 0x56, .JUMP)
      (attesterAttestCallDataEncodedJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨1792⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨1793⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1795⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨448⟩ (UInt256.ofNat 27)
      (by attester_decode_at v, ⟨1797⟩, 0x51, .MLOAD)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestCallMem_size I]; decide) (by decide)
        (attesterAttestCallMem_read64 I))
      (by decide) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1798⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨1799⟩, 0x83, .DUP4) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨1800⟩, 0x03, .SUB) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨1801⟩, 0x81, .DUP2) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨1802⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup8 (by attester_decode_at v, ⟨1803⟩, 0x87, .DUP8) (by evm_ov)]
  exact ⟨_, _, by
    simpa [show UInt256.sub (⟨804⟩ : UInt256) ⟨448⟩ = (⟨356⟩ : UInt256) by decide]
      using rd1804⟩

theorem attesterX_attestPostCall {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hreach : ∃ k C, RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨140⟩ : UInt256)
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
        (⟨1804⟩ + ⟨1⟩ + ⟨1⟩)
        ((if z then ⟨1⟩ else ⟨0⟩) ::
          ⟨804⟩ :: ⟨0xf17325e7⟩ :: attesterAttestTargetWord v :: ⟨0⟩ ::
          attesterAttestInputWord I :: attesterAttestSchemaWord I :: ⟨159⟩ ::
          solcSelectorWord I :: [])
        (o.write 0 (attesterAttestCallMem I) 448
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        ⟨27⟩ o (cA', σ') k' C'
    ∧ typedCallViaEVM (config v) (initState cA gh bl σ σ₀ g A I)
        (EVM.address v.eas) "attest" 0 (attesterAttestArgVals I)
        (z, { initState cA gh bl σ σ₀ g A I with
                accountMap := σ', substate := A', createdAccounts := cA' }, o) true
    ∧ o.size < UInt256.size := by
  obtain ⟨_, _, rd1804⟩ :=
    attesterX_attestToExternalCall (v := v) hsz68 hsize hsmall hreach
  obtain ⟨gv, rd1805⟩ :=
    rd1804.gas (by attester_decode_at v, ⟨1804⟩, 0x5a, .GAS) (by evm_ov)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hTheta, rd1806, hosz⟩ :=
    rd1805.call (by attester_decode_at v, ⟨1805⟩, 0xf1, .CALL) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hTheta
  refine ⟨cA', σ', z, o, A', k', C', ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 27).toNat
          (⟨448⟩ : UInt256).toNat (⟨356⟩ : UInt256).toNat)
          (⟨448⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) = (⟨27⟩ : UInt256) := by
        decide
    exact haw ▸ rd1806
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := attesterAttestTargetWord v)
      (mem := attesterAttestCallMem I) (inOff := ⟨448⟩) (inSize := ⟨356⟩)
      (hdepth := fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (htgt := attesterAttestTarget_eq v) (hcd := ?_) (hΘ := ?_)
    · rw [show (⟨448⟩ : UInt256).toNat = 448 by decide,
          show (⟨356⟩ : UInt256).toNat = 356 by decide,
          attesterAttestCallMem_read448_356]
      exact attesterEncodeAttest_eq v hsz68
    · simpa [initState, hperm] using hΘ

theorem attesterX_attestPostRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ} {rest : List UInt256}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨1804⟩ + ⟨1⟩ + ⟨1⟩) (⟨0⟩ :: rest) mem aw rdata acc k C)
    (hov : rest.length + 4 ≤ 1024) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  have rd1813 : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨1804⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩)
      (UInt256.isZero ⟨0⟩ :: rest) mem aw rdata acc _ _ :=
    evm_run rd with [
      raw iszero (by attester_decode_at v, ⟨1806⟩, 0x15, .ISZERO) (by evm_ov),
      raw dup1 (by attester_decode_at v, ⟨1807⟩, 0x80, .DUP1) (by evm_ov),
      raw iszero (by attester_decode_at v, ⟨1808⟩, 0x15, .ISZERO) (by evm_ov),
      raw push2 ⟨1820⟩ (by attester_decode_at v, ⟨1809⟩, 0x61, (.Push .PUSH2))
        (by evm_ov),
      raw jumpiNT (by attester_decode_at v, ⟨1812⟩, 0x57, .JUMPI) (by decide)
        (by evm_ov)]
  have rd1814 := RD.returndatasize rd1813
    (by
      rw [show (⟨1804⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩)
        = (⟨1813⟩ : UInt256) by decide]
      attester_decode_at v, ⟨1813⟩, 0x3d, .RETURNDATASIZE)
    (by simp only [List.length_cons]; omega)
  have rd1815 := RD.push0 rd1814
    (by
      rw [show (⟨1804⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩)
        = (⟨1814⟩ : UInt256) by decide]
      attester_decode_at v, ⟨1814⟩, 0x5f, .PUSH0)
    (by simp only [List.length_cons]; omega)
  have rd1816 := RD.dup1 rd1815
    (by
      rw [show (⟨1804⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
        = (⟨1815⟩ : UInt256) by decide]
      attester_decode_at v, ⟨1815⟩, 0x80, .DUP1)
    (by simp only [List.length_cons]; omega)
  have rd1817 : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨1804⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
      (UInt256.isZero ⟨0⟩ :: rest)
      (rdata.write 0 mem 0 (UInt256.ofNat rdata.size).toNat)
      (UInt256.ofNat (MachineState.M aw.toNat 0 (UInt256.ofNat rdata.size).toNat))
      rdata acc _ _ :=
    RD.returndatacopy
      (Cₘ (UInt256.ofNat (MachineState.M aw.toNat 0 (UInt256.ofNat rdata.size).toNat)) - Cₘ aw)
      (rdata.write 0 mem 0 (UInt256.ofNat rdata.size).toNat)
      (UInt256.ofNat (MachineState.M aw.toNat 0 (UInt256.ofNat rdata.size).toNat))
      rd1816
      (by
        rw [show (⟨1804⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
          = (⟨1816⟩ : UInt256) by decide]
        attester_decode_at v, ⟨1816⟩, 0x3e, .RETURNDATACOPY)
      (by
        rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_add]
        rw [show (UInt256.ofNat rdata.size).toNat = rdata.size % UInt256.size from rfl]
        exact Nat.mod_le _ _)
      (by
        intro s haws hstks
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', hstks, haws,
          List.getElem!_cons_zero, List.getElem!_cons_succ,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl])
      rfl rfl (by simp only [List.length_cons]; omega)
  have rd1818 := RD.returndatasize rd1817
    (by
      rw [show (⟨1804⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
        = (⟨1817⟩ : UInt256) by decide]
      attester_decode_at v, ⟨1817⟩, 0x3d, .RETURNDATASIZE)
    (by simp only [List.length_cons]; omega)
  have rd1819 := RD.push0 rd1818
    (by
      rw [show (⟨1804⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
        = (⟨1818⟩ : UInt256) by decide]
      attester_decode_at v, ⟨1818⟩, 0x5f, .PUSH0)
    (by simp only [List.length_cons]; omega)
  exact RD.rev _ rd1819
    (by
      rw [show (⟨1804⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
        = (⟨1819⟩ : UInt256) by decide]
      attester_decode_at v, ⟨1819⟩, 0xfd, .REVERT)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by simp only [List.length_cons]; omega)

theorem attesterX_attestCallDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    (hcode : I.code = patchedRuntime v) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hsmall : I.calldata.size < 2 ^ 255 + 4)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = true)
    (hdepth : I.depth = 1024) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd1804⟩ :=
    attesterX_attestToExternalCall (v := v) hsz68 hsize hsmall
      (attesterX_attestWrapper (g := g) v hcode hwv hsz4 hsize
        hmultiRevoke hmultiAttest hattest)
  obtain ⟨_, rd1805⟩ :=
    rd1804.gas (by attester_decode_at v, ⟨1804⟩, 0x5a, .GAS) (by evm_ov)
  obtain ⟨_, _, rd1806⟩ :=
    rd1805.callDepthLimit (by attester_decode_at v, ⟨1805⟩, 0xf1, .CALL)
      hdepth (by evm_ov)
  exact attesterX_attestPostRevert (v := v) rd1806 (by simp)

theorem attesterX_attestCallSuccessToReturnDecodeMem {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨1804⟩ + ⟨1⟩ + ⟨1⟩)
      [⟨1⟩, ⟨804⟩, ⟨0xf17325e7⟩, attesterAttestTargetWord v, ⟨0⟩,
        attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      mem ⟨27⟩ o acc k C)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨
        (⟨64⟩ : UInt256) ≥ ⟨27⟩ * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨448⟩) :
    ∃ k' C', RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨3150⟩
      [⟨448⟩, UInt256.add ⟨448⟩ (UInt256.ofNat o.size), ⟨1856⟩, ⟨0⟩,
        attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      ((UInt256.toByteArray (attesterAttestReturnDecodeFreePtr o)).write 0 mem 64 32)
      ⟨27⟩ o acc k' C' := by
  have rd1828 := evm_run rd with [
    raw iszero (by attester_decode_at v, ⟨1806⟩, 0x15, .ISZERO) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨1807⟩, 0x80, .DUP1) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨1808⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨1820⟩ (by attester_decode_at v, ⟨1809⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨1812⟩, 0x57, .JUMPI) (by decide)
      (attesterAttestCallOkJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨1820⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1821⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1822⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1823⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨1824⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1825⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload 0 ⟨448⟩ ⟨27⟩ (by attester_decode_at v, ⟨1827⟩, 0x51, .MLOAD)
      mem_cost hfp (by decide) (by evm_ov)]
  refine ⟨_, _, by
    simpa [attesterAttestReturnDecodeFreePtr] using evm_run rd1828 with [
      raw returndatasize (by attester_decode_at v, ⟨1828⟩, 0x3d, .RETURNDATASIZE)
        (by evm_ov),
      raw push1 ⟨31⟩ (by attester_decode_at v, ⟨1829⟩, 0x60, (.Push .PUSH1))
        (by evm_ov),
      raw not (by attester_decode_at v, ⟨1831⟩, 0x19, .NOT) (by evm_ov),
      raw push1 ⟨31⟩ (by attester_decode_at v, ⟨1832⟩, 0x60, (.Push .PUSH1))
        (by evm_ov),
      raw dup3 (by attester_decode_at v, ⟨1834⟩, 0x82, .DUP3) (by evm_ov),
      raw add (by attester_decode_at v, ⟨1835⟩, 0x01, .ADD) (by evm_ov),
      raw and (by attester_decode_at v, ⟨1836⟩, 0x16, .AND) (by evm_ov),
      raw dup3 (by attester_decode_at v, ⟨1837⟩, 0x82, .DUP3) (by evm_ov),
      raw add (by attester_decode_at v, ⟨1838⟩, 0x01, .ADD) (by evm_ov),
      raw dup1 (by attester_decode_at v, ⟨1839⟩, 0x80, .DUP1) (by evm_ov),
      raw push1 ⟨64⟩ (by attester_decode_at v, ⟨1840⟩, 0x60, (.Push .PUSH1))
        (by evm_ov),
      raw mstore 0 ((UInt256.toByteArray (attesterAttestReturnDecodeFreePtr o)).write 0 mem 64 32)
        ⟨27⟩ (by attester_decode_at v, ⟨1842⟩, 0x52, .MSTORE) mem_cost
        (by rfl) (by decide) (by evm_ov),
      raw pop (by attester_decode_at v, ⟨1843⟩, 0x50, .POP) (by evm_ov),
      raw dup2 (by attester_decode_at v, ⟨1844⟩, 0x81, .DUP2) (by evm_ov),
      raw add (by attester_decode_at v, ⟨1845⟩, 0x01, .ADD) (by evm_ov),
      raw swap1 (by attester_decode_at v, ⟨1846⟩, 0x90, .SWAP1) (by evm_ov),
      raw push2 ⟨1856⟩ (by attester_decode_at v, ⟨1847⟩, 0x61, (.Push .PUSH2))
        (by evm_ov),
      raw swap2 (by attester_decode_at v, ⟨1850⟩, 0x91, .SWAP2) (by evm_ov),
      raw swap1 (by attester_decode_at v, ⟨1851⟩, 0x90, .SWAP1) (by evm_ov),
      raw push2 ⟨3150⟩ (by attester_decode_at v, ⟨1852⟩, 0x61, (.Push .PUSH2))
        (by evm_ov),
      raw jump (by attester_decode_at v, ⟨1855⟩, 0x56, .JUMP)
        (attesterAttestReturnDecodeJumpdest v) (by evm_ov)]⟩

theorem attesterX_attestCallSuccessToReturnDecode {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {o : ByteArray} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I)
      (⟨1804⟩ + ⟨1⟩ + ⟨1⟩)
      [⟨1⟩, ⟨804⟩, ⟨0xf17325e7⟩, attesterAttestTargetWord v, ⟨0⟩,
        attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      (o.write 0 (attesterAttestCallMem I) 448 32) ⟨27⟩ o acc k C)
    (ho32 : 32 ≤ o.size) :
    ∃ k' C', RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨3150⟩
      [⟨448⟩, UInt256.add ⟨448⟩ (UInt256.ofNat o.size), ⟨1856⟩, ⟨0⟩,
        attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      (attesterAttestReturnDecodeMem I o) ⟨27⟩ o acc k' C' := by
  have hfp :
      (if (⟨64⟩ : UInt256).toNat ≥ (o.write 0 (attesterAttestCallMem I) 448 32).size ∨
          (⟨64⟩ : UInt256) ≥ ⟨27⟩ * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat (fromByteArrayBigEndian
          ((o.write 0 (attesterAttestCallMem I) 448 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨448⟩ :=
    mloadWordValue_of_readWithPadding
      (by rw [attesterAttestReturnWrite_size I o ho32]; decide)
      (by decide)
      (by simpa using attesterAttestReturnWrite_read64 I o ho32)
  obtain ⟨k', C', rd3150⟩ := attesterX_attestCallSuccessToReturnDecodeMem
    (v := v) rd hfp
  exact ⟨k', C', by simpa [attesterAttestReturnDecodeMem] using rd3150⟩

theorem attesterX_attestReturnDecodeOk {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {o : ByteArray} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨3150⟩
      [⟨448⟩, UInt256.add ⟨448⟩ (UInt256.ofNat o.size), ⟨1856⟩, ⟨0⟩,
        attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      (attesterAttestReturnDecodeMem I o) ⟨27⟩ o acc k C)
    (ho32 : 32 ≤ o.size) (ho255 : o.size < 2 ^ 255) :
    ∃ k' C', RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨1856⟩
      [uInt256OfByteArray (o.extract 0 32), ⟨0⟩, attesterAttestInputWord I,
        attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      (attesterAttestReturnDecodeMem I o) ⟨27⟩ o acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    raw jumpdest (by attester_decode_at v, ⟨3150⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨3151⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨3152⟩, 0x60, (.Push .PUSH1))
      (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨3154⟩, 0x82, .DUP3) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨3155⟩, 0x84, .DUP5) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨3156⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨3157⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨3158⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨3166⟩ (by attester_decode_at v, ⟨3159⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨3162⟩, 0x57, .JUMPI)
      (by rw [solcDecodeEndLenCheckOk_448_32 ho32 ho255]; decide)
      (attesterAttestReturnDecodeOkJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨3166⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨3167⟩, 0x50, .POP) (by evm_ov),
    raw mload 0 (uInt256OfByteArray (o.extract 0 32)) ⟨27⟩
      (by attester_decode_at v, ⟨3168⟩, 0x51, .MLOAD) mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [attesterAttestReturnDecodeMem_size I o ho32]; decide)
        (by decide)
        (attesterAttestReturnDecodeMem_read448_word I o ho32))
      (by decide) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨3169⟩, 0x91, .SWAP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨3170⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨3171⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨3172⟩, 0x56, .JUMP)
      (attesterAttestAfterReturnDecodeJumpdest v) (by evm_ov)]⟩

theorem attesterX_attestReturnDecodeShortReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨3150⟩
      [⟨448⟩, UInt256.add ⟨448⟩ (UInt256.ofNat o.size), ⟨1856⟩, ⟨0⟩,
        attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      mem aw o acc k C)
    (ho : o.size < 32) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run rd with [
    raw jumpdest (by attester_decode_at v, ⟨3150⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨3151⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨3152⟩, 0x60, (.Push .PUSH1))
      (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨3154⟩, 0x82, .DUP3) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨3155⟩, 0x84, .DUP5) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨3156⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨3157⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨3158⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨3166⟩ (by attester_decode_at v, ⟨3159⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨3162⟩, 0x57, .JUMPI)
      (by rw [solcDecodeEndLenCheckShort_448_32 ho]; decide) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨3163⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨3164⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨3165⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_attestReturnDecodeHugeReverts {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨3150⟩
      [⟨448⟩, UInt256.add ⟨448⟩ (UInt256.ofNat o.size), ⟨1856⟩, ⟨0⟩,
        attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩, solcSelectorWord I]
      mem aw o acc k C)
    (hhi : 2 ^ 255 ≤ o.size) (hlo : o.size < UInt256.size) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run rd with [
    raw jumpdest (by attester_decode_at v, ⟨3150⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨3151⟩, 0x5f, .PUSH0) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨3152⟩, 0x60, (.Push .PUSH1))
      (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨3154⟩, 0x82, .DUP3) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨3155⟩, 0x84, .DUP5) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨3156⟩, 0x03, .SUB) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨3157⟩, 0x12, .SLT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨3158⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨3166⟩ (by attester_decode_at v, ⟨3159⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨3162⟩, 0x57, .JUMPI)
      (by rw [solcDecodeEndLenCheckHuge_448_32 hhi hlo]; decide) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨3163⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨3164⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨3165⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

noncomputable def attesterAttestPublicReturnMem (I : ExecutionEnv) (o : ByteArray)
    (uid : UInt256) : ByteArray :=
  attesterWriteWord (attesterAttestReturnDecodeMem I o)
    (attesterAttestReturnDecodeFreePtr o).toNat uid

def attesterAttestPublicReturnAw (o : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (⟨27⟩ : UInt256).toNat
    (attesterAttestReturnDecodeFreePtr o).toNat 32)

def attesterAttestPublicReturnAwAfterMload (o : ByteArray) : UInt256 :=
  UInt256.ofNat (MachineState.M (attesterAttestPublicReturnAw o).toNat
    (⟨64⟩ : UInt256).toNat 32)

theorem attesterAttestPublicReturnMem_size (I : ExecutionEnv) (o : ByteArray)
    (uid : UInt256) (ho32 : 32 ≤ o.size) :
    (attesterAttestPublicReturnMem I o uid).size =
      max 836 ((attesterAttestReturnDecodeFreePtr o).toNat + 32) := by
  unfold attesterAttestPublicReturnMem
  rw [attesterWriteWord_size_eq_max_nat, attesterAttestReturnDecodeMem_size I o ho32]

theorem attesterAttestPublicReturnMem_read64 (I : ExecutionEnv) (o : ByteArray)
    (uid : UInt256) (ho32 : 32 ≤ o.size) (ho255 : o.size < 2 ^ 255) :
    (attesterAttestPublicReturnMem I o uid).readWithPadding 64 32 =
      UInt256.toByteArray (attesterAttestReturnDecodeFreePtr o) := by
  unfold attesterAttestPublicReturnMem
  rw [attesterWriteWord_read_below_len_nat]
  · exact attesterAttestReturnDecodeMem_read64 I o ho32
  · rw [attesterAttestReturnDecodeMem_size I o ho32]
    norm_num
  · exact le_trans (by norm_num : 64 + 32 ≤ 448)
      (attesterAttestReturnDecodeFreePtr_ge448 o ho255)
  · norm_num
  · norm_num

theorem attesterAttestPublicReturnMem_readUid (I : ExecutionEnv) (o : ByteArray)
    (uid : UInt256) :
    (attesterAttestPublicReturnMem I o uid).readWithPadding
        (attesterAttestReturnDecodeFreePtr o).toNat 32 =
      UInt256.toByteArray uid := by
  unfold attesterAttestPublicReturnMem
  exact attesterWriteWord_read_back_nat _ _ _

theorem attesterAttestReturnDecodeMem_mload64 (I : ExecutionEnv) (o : ByteArray)
    (ho32 : 32 ≤ o.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (attesterAttestReturnDecodeMem I o).size ∨
        (⟨64⟩ : UInt256) ≥ ⟨27⟩ * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((attesterAttestReturnDecodeMem I o).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      attesterAttestReturnDecodeFreePtr o := by
  exact mloadWordValue_of_readWithPadding
    (by rw [attesterAttestReturnDecodeMem_size I o ho32]; decide)
    (by decide)
    (by simpa using attesterAttestReturnDecodeMem_read64 I o ho32)

private theorem attesterAttestPublicReturnAw_toNat (o : ByteArray)
    (ho255 : o.size < 2 ^ 255) :
    (attesterAttestPublicReturnAw o).toNat =
      MachineState.M 27 (attesterAttestReturnDecodeFreePtr o).toNat 32 := by
  unfold attesterAttestPublicReturnAw
  exact ulit_toNat' _ (by
    simp [MachineState.M]
    have hfp := attesterAttestReturnDecodeFreePtr_add63_lt o ho255
    have hdivle :
        ((attesterAttestReturnDecodeFreePtr o).toNat + 32 + 31) / 32
          ≤ (attesterAttestReturnDecodeFreePtr o).toNat + 32 + 31 :=
      Nat.div_le_self _ _
    constructor
    · rw [show (⟨27⟩ : UInt256).toNat = 27 by decide]
      norm_num [UInt256.size]
    · omega)

private theorem attesterAttestPublicReturnAw_ge27 (o : ByteArray)
    (ho255 : o.size < 2 ^ 255) :
    27 ≤ (attesterAttestPublicReturnAw o).toNat := by
  rw [attesterAttestPublicReturnAw_toNat o ho255]
  simp [MachineState.M]

private theorem attesterAttestPublicReturnAw_mul32_toNat (o : ByteArray)
    (ho255 : o.size < 2 ^ 255) :
    (attesterAttestPublicReturnAw o * (⟨32⟩ : UInt256)).toNat =
      (attesterAttestPublicReturnAw o).toNat * 32 := by
  apply umul_toNat
  rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
  rw [attesterAttestPublicReturnAw_toNat o ho255]
  simp [MachineState.M]
  have hfp := attesterAttestReturnDecodeFreePtr_add63_lt o ho255
  have hdiv : ((attesterAttestReturnDecodeFreePtr o).toNat + 32 + 31) / 32 * 32
      ≤ (attesterAttestReturnDecodeFreePtr o).toNat + 32 + 31 :=
    Nat.div_mul_le_self _ _
  by_cases hle : 27 ≤ ((attesterAttestReturnDecodeFreePtr o).toNat + 32 + 31) / 32
  · rw [max_eq_right hle]
    omega
  · rw [max_eq_left (by omega)]
    norm_num [UInt256.size]

private theorem attesterAttestPublicReturnAw_mload64 (o : ByteArray)
    (ho255 : o.size < 2 ^ 255) :
    ¬ (⟨64⟩ : UInt256) ≥ attesterAttestPublicReturnAw o * ⟨32⟩ := by
  intro h
  have hle : (attesterAttestPublicReturnAw o * (⟨32⟩ : UInt256)).toNat ≤ 64 := by
    exact h
  rw [attesterAttestPublicReturnAw_mul32_toNat o ho255] at hle
  have hge := attesterAttestPublicReturnAw_ge27 o ho255
  omega

theorem attesterAttestPublicReturnMem_mload64 (I : ExecutionEnv) (o : ByteArray)
    (uid : UInt256) (ho32 : 32 ≤ o.size) (ho255 : o.size < 2 ^ 255) :
    (if (⟨64⟩ : UInt256).toNat ≥ (attesterAttestPublicReturnMem I o uid).size ∨
        (⟨64⟩ : UInt256) ≥ attesterAttestPublicReturnAw o * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((attesterAttestPublicReturnMem I o uid).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      attesterAttestReturnDecodeFreePtr o := by
  exact mloadWordValue_of_readWithPadding
    (by
      rw [attesterAttestPublicReturnMem_size I o uid ho32]
      rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
      exact lt_of_lt_of_le (by norm_num : 64 < 836)
        (le_max_left _ _))
    (attesterAttestPublicReturnAw_mload64 o ho255)
    (by simpa using attesterAttestPublicReturnMem_read64 I o uid ho32 ho255)

theorem attesterX_attestPublicReturnWith {cA gh bl σ σ₀ A I} {g : Sat256}
    (v : AttesterImmutables)
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {o : ByteArray} {uid : UInt256} {k C : ℕ}
    (rd : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨1856⟩
      [uid, ⟨0⟩, attesterAttestInputWord I, attesterAttestSchemaWord I, ⟨159⟩,
        solcSelectorWord I]
      (attesterAttestReturnDecodeMem I o) ⟨27⟩ o acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (attesterAttestReturnDecodeMem I o).size ∨
          (⟨64⟩ : UInt256) ≥ ⟨27⟩ * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((attesterAttestReturnDecodeMem I o).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        attesterAttestReturnDecodeFreePtr o)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (attesterAttestPublicReturnMem I o uid).size ∨
          (⟨64⟩ : UInt256) ≥ attesterAttestPublicReturnAw o * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((attesterAttestPublicReturnMem I o uid).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        attesterAttestReturnDecodeFreePtr o)
    (hsub :
      UInt256.sub (UInt256.add ⟨32⟩ (attesterAttestReturnDecodeFreePtr o))
          (attesterAttestReturnDecodeFreePtr o) = ⟨32⟩)
    (hread :
      (attesterAttestPublicReturnMem I o uid).readWithPadding
        (attesterAttestReturnDecodeFreePtr o).toNat 32 =
        UInt256.toByteArray uid) :
    RDret (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) acc
      (UInt256.toByteArray uid) := by
  have rd159 : RD (patchedRuntime v) I g (initState cA gh bl σ σ₀ g A I) ⟨159⟩
      [uid, solcSelectorWord I] (attesterAttestReturnDecodeMem I o) ⟨27⟩ o acc _ _ :=
    evm_run rd with [
      raw jumpdest (by attester_decode_at v, ⟨1856⟩, 0x5b, .JUMPDEST) (by evm_ov),
      raw swap4 (by attester_decode_at v, ⟨1857⟩, 0x93, .SWAP4) (by evm_ov),
      raw swap3 (by attester_decode_at v, ⟨1858⟩, 0x92, .SWAP3) (by evm_ov),
      raw pop (by attester_decode_at v, ⟨1859⟩, 0x50, .POP) (by evm_ov),
      raw pop (by attester_decode_at v, ⟨1860⟩, 0x50, .POP) (by evm_ov),
      raw pop (by attester_decode_at v, ⟨1861⟩, 0x50, .POP) (by evm_ov),
      raw jump (by attester_decode_at v, ⟨1862⟩, 0x56, .JUMP)
        (attesterAttestPublicReturnJumpdest v) (by evm_ov)]
  exact evm_run rd159 with [
    raw jumpdest (by attester_decode_at v, ⟨159⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨160⟩, 0x60, (.Push .PUSH1))
      (by evm_ov),
    raw mload 0 (attesterAttestReturnDecodeFreePtr o) ⟨27⟩
      (by attester_decode_at v, ⟨162⟩, 0x51, .MLOAD) mem_cost hmload64
      (by decide) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨163⟩, 0x90, .SWAP1) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨164⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore
      (Cₘ (attesterAttestPublicReturnAw o) - Cₘ (⟨27⟩ : UInt256))
      (attesterAttestPublicReturnMem I o uid) (attesterAttestPublicReturnAw o)
      (by attester_decode_at v, ⟨165⟩, 0x52, .MSTORE)
      (by
        intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero, List.getElem!_cons_succ,
          attesterAttestPublicReturnAw])
      (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨166⟩, 0x60, (.Push .PUSH1))
      (by evm_ov),
    raw add (by attester_decode_at v, ⟨168⟩, 0x01, .ADD) (by evm_ov),
    raw push2 ⟨131⟩ (by attester_decode_at v, ⟨169⟩, 0x61, (.Push .PUSH2))
      (by evm_ov),
    raw jump (by attester_decode_at v, ⟨172⟩, 0x56, .JUMP)
      (attesterAttestFinalReturnJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨131⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨132⟩, 0x60, (.Push .PUSH1))
      (by evm_ov),
    raw mload
      (Cₘ (attesterAttestPublicReturnAwAfterMload o) -
        Cₘ (attesterAttestPublicReturnAw o))
      (attesterAttestReturnDecodeFreePtr o) (attesterAttestPublicReturnAwAfterMload o)
      (by attester_decode_at v, ⟨134⟩, 0x51, .MLOAD)
      (by
        intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero, List.getElem!_cons_succ,
          attesterAttestPublicReturnAwAfterMload])
      hmemoutLoad64 (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨135⟩, 0x80, .DUP1) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨136⟩, 0x91, .SWAP2) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨137⟩, 0x03, .SUB) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨138⟩, 0x90, .SWAP1) (by evm_ov),
    raw ret
      (Cₘ (UInt256.ofNat (MachineState.M (attesterAttestPublicReturnAwAfterMload o).toNat
          (attesterAttestReturnDecodeFreePtr o).toNat
          (UInt256.sub (UInt256.add ⟨32⟩ (attesterAttestReturnDecodeFreePtr o))
            (attesterAttestReturnDecodeFreePtr o)).toNat)) -
        Cₘ (attesterAttestPublicReturnAwAfterMload o))
      (UInt256.toByteArray uid)
      (by attester_decode_at v, ⟨139⟩, 0xf3, .RETURN)
      (by
        intro s haw hstk
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        rfl)
      (by
        change (attesterAttestPublicReturnMem I o uid).readWithPadding
          (attesterAttestReturnDecodeFreePtr o).toNat
          (UInt256.sub (UInt256.add ⟨32⟩ (attesterAttestReturnDecodeFreePtr o))
            (attesterAttestReturnDecodeFreePtr o)).toNat =
            UInt256.toByteArray uid
        rw [hsub]
        exact hread)
      (by evm_ov)]

theorem attesterAttestBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (v : AttesterImmutables) {code : ByteArray}
    (hpatch : patchRuntime attesterBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hmultiRevoke : (attesterMultiRevokeSelBytes == I.calldata.extract 0 4) = false)
    (hmultiAttest : (attesterMultiAttestSelBytes == I.calldata.extract 0 4) = false)
    (hattest : (attesterAttestSelBytes == I.calldata.extract 0 4) = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hpatched : code = patchedRuntime v := code_eq_patchedRuntime_of_patch hpatch
  have hIcode : I.code = patchedRuntime v := hcode.trans hpatched
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I attesterAttestSelBytes attesterAttestSelBytes_size hattest
  have hd := attesterDispatch_attest v hattest
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hsmall : I.calldata.size < 2 ^ 255 + 4
    · let gS : Sat256 := Sat256.ofUInt256 g
      let evmEvm : EVM.State := initState cA gh bl σ_evm σ₀ gS A I
      let evmSolm : EVM.State := initState cA gh bl σ_solm σ₀ gS A I
      have hdec := attesterDecode_attest_ok v hsz68 hsmall
      have hwvSolm : evmSolm.executionEnv.weiValue = ⟨0⟩ := by
        simp [evmSolm, initState, hwv]
      have hargsSolm :
          evalExprs? (config v)
              { contract := contract v, locals := attesterAttestStore I } evmSolm
              [attestationRequest (.var "schema") (.var "input")] =
            .ok (attesterAttestArgVals I) :=
        attesterEvalAttestArgs v evmSolm I
      by_cases hdepth : I.depth.val < 1024
      · have hreach :=
          attesterX_attestWrapper (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
            (σ₀ := σ₀) (A := A) (I := I) (g := gS) v hIcode hwv hsz4 hsize
            hmultiRevoke hmultiAttest hattest
        obtain ⟨cA', σ', z, o, A', k', C', rd1806, hcallEvm, hosize⟩ :=
          attesterX_attestPostCall (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
            (σ₀ := σ₀) (A := A) (I := I) (g := gS) v hsz68 hsize hsmall hreach
            hperm hdepth
        let evmPostEvm : EVM.State :=
          { evmEvm with accountMap := σ', substate := A', createdAccounts := cA' }
        have hcallEvm' :
            typedCallViaEVM (config v) evmEvm (EVM.address v.eas) "attest" 0
              (attesterAttestArgVals I) (z, evmPostEvm, o) true := by
          simpa [evmEvm, evmPostEvm] using hcallEvm
        obtain ⟨σSolmPost, ASolmPost, hcallSolm, hStateCall⟩ :=
          typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallEvm')
            (by simp [evmEvm, evmSolm, evmPostEvm, initState]) hAccounts
        let evmPostSolm : EVM.State :=
          { evmSolm with accountMap := σSolmPost, substate := ASolmPost, createdAccounts := cA' }
        have hcallSolm' :
            typedCallViaEVM (config v) evmSolm (EVM.address v.eas) "attest" 0
              (attesterAttestArgVals I) (z, evmPostSolm, o) true := by
          simpa [evmPostSolm] using hcallSolm
        have hStateCall' : EVMStateEquiv evmPostEvm evmPostSolm := by
          simpa [evmPostSolm] using hStateCall
        cases z
        · simp only [Bool.false_eq_true, if_false] at rd1806 hcallSolm'
          have hrdrev := attesterX_attestPostRevert (v := v) rd1806 (by simp)
          have hbody :=
            attesterAttestBodyCallFailure v evmSolm evmPostSolm
              (attesterAttestStore I) hwvSolm hargsSolm hcallSolm'
          exact hrdrev.reEquivExecutionRevert hIcode hd hdec hbody
        · simp only [Bool.true_eq_false, if_true] at rd1806 hcallSolm'
          by_cases ho255 : o.size < 2 ^ 255
          · by_cases ho32 : 32 ≤ o.size
            · rw [attesterAttestMin32_toNat_of_ge ho32 hosize] at rd1806
              obtain ⟨_, _, rd3150⟩ :=
                attesterX_attestCallSuccessToReturnDecode (v := v) rd1806 ho32
              obtain ⟨_, _, rd1856⟩ :=
                attesterX_attestReturnDecodeOk (v := v) rd3150 ho32 ho255
              have hrdret :=
                attesterX_attestPublicReturnWith (v := v) rd1856
                  (attesterAttestReturnDecodeMem_mload64 I o ho32)
                  (attesterAttestPublicReturnMem_mload64 I o
                    (uInt256OfByteArray (o.extract 0 32)) ho32 ho255)
                  (attesterAttestReturnDecodeFreePtr_add32_sub o ho255)
                  (attesterAttestPublicReturnMem_readUid I o
                    (uInt256OfByteArray (o.extract 0 32)))
              have hretdec := attesterDecode_attest_return_ok v ho32 ho255
              have hbody :=
                attesterAttestBodySuccess v evmSolm evmPostSolm
                  (attesterAttestStore I) hwvSolm hargsSolm hcallSolm' hretdec
              have henc :
                  returnEquiv
                    (UInt256.toByteArray (uInt256OfByteArray (o.extract 0 32)))
                    (some [.fixedBytes bytes32Width
                      (EVM.Word.toBytesBE (uInt256OfByteArray (o.extract 0 32)))])
                    (attestTransition v).returnType := by
                simpa [attestTransition, bytes32, bytes32Width] using
                  returnEquiv_of_encode
                    (bytes32ReturnEncoding (uInt256OfByteArray (o.extract 0 32)))
              exact hrdret.reEquivExecutionGenEVMStateEquiv hIcode hd hdec hbody
                rfl (accountMapEquiv.refl σ') hStateCall' henc
            · have ho32lt : o.size < 32 := by omega
              rw [attesterAttestMin32_toNat_of_lt ho32lt] at rd1806
              have hfp :=
                attesterAttestReturnWrite_mload64_of_len I o
                  (by omega : o.size ≤ o.size)
                  (by omega : o.size ≤ 32)
              obtain ⟨_, _, rd3150⟩ :=
                attesterX_attestCallSuccessToReturnDecodeMem (v := v) rd1806 hfp
              have hrdrev :=
                attesterX_attestReturnDecodeShortReverts (v := v) rd3150 ho32lt
              have hretdec := attesterDecode_attest_return_none_short v ho32lt
              have hbody :=
                attesterAttestBodyDecodeRevert v evmSolm evmPostSolm
                  (attesterAttestStore I) hwvSolm hargsSolm hcallSolm' hretdec
              exact hrdrev.reEquivExecutionRevert hIcode hd hdec hbody
          · have hhi : 2 ^ 255 ≤ o.size := by omega
            have ho32 : 32 ≤ o.size := by omega
            rw [attesterAttestMin32_toNat_of_ge ho32 hosize] at rd1806
            obtain ⟨_, _, rd3150⟩ :=
              attesterX_attestCallSuccessToReturnDecode (v := v) rd1806 ho32
            have hrdrev :=
              attesterX_attestReturnDecodeHugeReverts (v := v) rd3150 hhi hosize
            have hretdec := attesterDecode_attest_return_none_huge v hhi
            have hbody :=
              attesterAttestBodyDecodeRevert v evmSolm evmPostSolm
                (attesterAttestStore I) hwvSolm hargsSolm hcallSolm' hretdec
            exact hrdrev.reEquivExecutionRevert hIcode hd hdec hbody
      · have hdepth1024 : I.depth = 1024 := by
          apply Fin.ext
          have hlt := I.depth.isLt
          rw [not_lt] at hdepth
          omega
        have hrdrev :=
          attesterX_attestCallDepthLimit (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := gS) v hIcode hwv
            hsz4 hsize hsz68 hsmall hmultiRevoke hmultiAttest hattest hdepth1024
        have hdepthInit : evmSolm.executionEnv.depth = 1024 := by
          simpa [evmSolm, initState] using hdepth1024
        have hcallSolm :
            typedCallViaEVM (config v) evmSolm (EVM.address v.eas) "attest" 0
              (attesterAttestArgVals I)
              (false,
                { evmSolm with
                  substate := (evmSolm.addAccessedAccount (EVM.address v.eas)).substate },
                ByteArray.empty)
              true :=
          callNotMade_depthLimit
            (cfg := config v) (evm := evmSolm) (tgt := EVM.address v.eas)
            (name := "attest") (args := attesterAttestArgVals I) (callPerm := true)
            (attesterEncodeAttest_eq v hsz68) hdepthInit
        have hbody :=
          attesterAttestBodyCallFailure v evmSolm
            ({ evmSolm with
              substate := (evmSolm.addAccessedAccount (EVM.address v.eas)).substate })
            (attesterAttestStore I) hwvSolm hargsSolm hcallSolm
        exact hrdrev.reEquivExecutionRevert hIcode hd hdec hbody
    · have hbig : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
      have hdec := attesterDecode_attest_none_huge v hbig
      exact (attesterX_attestDecodeHuge (g := Sat256.ofUInt256 g) v hIcode hwv hsz4 hsize hbig
          hmultiRevoke hmultiAttest hattest)
        |>.reEquivDecodingFailed hIcode hd hdec
  · have hshort : I.calldata.size < 68 := by omega
    have hdec := attesterDecode_attest_none_short v hsz4 hshort
    exact (attesterX_attestDecodeShort (g := Sat256.ofUInt256 g) v hIcode hwv hsz4 hsize hshort
        hmultiRevoke hmultiAttest hattest)
      |>.reEquivDecodingFailed hIcode hd hdec

end Benchmarks.EAS.Attester
