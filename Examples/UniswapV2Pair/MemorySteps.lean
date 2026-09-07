import Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair

abbrev memoryWordActiveWords (aw offset : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat offset.toNat 32)

noncomputable abbrev memoryWordLoad (mem : ByteArray) (aw offset : UInt256) : UInt256 :=
  if offset.toNat ≥ mem.size ∨ offset ≥ aw * ⟨32⟩ then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding offset.toNat 32))

-- GENERALIZES Reasoning.Reach.RD.mstore: derive memory, active words, and gas cost.
theorem RD.mstoreWord
    {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc offset value aw : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {R : List UInt256} {k C : Nat}
    (rd : RD code I g s0 pc (offset :: value :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MSTORE, .none)) (hov : R.length ≤ 1024) :
    RD code I g s0 (pc + ⟨1⟩) R (value.toByteArray.write 0 mem offset.toNat 32)
      (memoryWordActiveWords aw offset) rdata acc (k + 1)
      (C + (Cₘ (memoryWordActiveWords aw offset) - Cₘ aw + 3)) := by
  exact RD.mstore _ _ _ rd hdec
    (fun _ haw hstk ↦ mstoreCost_of_stack haw hstk rfl) rfl rfl hov

-- GENERALIZES Reasoning.Reach.RD.mload: derive the expansion and gas witnesses.
theorem RD.mloadWord
    {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc offset aw value : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {R : List UInt256} {k C : Nat}
    (rd : RD code I g s0 pc (offset :: R) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MLOAD, .none))
    (hvalue : memoryWordLoad mem aw offset = value) (hov : R.length + 1 ≤ 1024) :
    RD code I g s0 (pc + ⟨1⟩) (value :: R) mem (memoryWordActiveWords aw offset) rdata acc
      (k + 1) (C + (Cₘ (memoryWordActiveWords aw offset) - Cₘ aw + 3)) := by
  exact RD.mload _ _ _ rd hdec
    (fun s haw hstk ↦ by
      simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk,
        List.getElem!_cons_zero, memoryWordActiveWords]) hvalue rfl hov

-- LIBRARY CANDIDATES: bounds and read coverage for active memory words.
theorem MachineState_M_mul32_lt_of_bounds {s f l : Nat}
    (hs : s * 32 < UInt256.size) (hf : f + l + 31 < UInt256.size) :
    MachineState.M s f l * 32 < UInt256.size := by
  unfold MachineState.M
  split
  · exact hs
  · by_cases hle : s ≤ (f + l + 31) / 32
    · rw [Nat.max_eq_right hle]
      have hdiv := Nat.div_mul_le_self (f + l + 31) 32
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hle)]
      exact hs

theorem MachineState_M_ge_left (s f l : Nat) : s ≤ MachineState.M s f l := by
  unfold MachineState.M
  split
  · rfl
  · exact Nat.le_max_left _ _

theorem UInt256_ofNat_M_mul32_lt (aw off : UInt256)
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + 32 + 31 < UInt256.size) :
    (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)).toNat * 32 <
      UInt256.size := by
  have hMmul := MachineState_M_mul32_lt_of_bounds haw hoff
  have hMlt : MachineState.M aw.toNat off.toNat 32 < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact hMmul

theorem UInt256_ofNat_M_toNat_ge (aw off : UInt256) {n : Nat}
    (hn : n ≤ aw.toNat)
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + 32 + 31 < UInt256.size) :
    n ≤ (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)).toNat := by
  have hMmul := MachineState_M_mul32_lt_of_bounds haw hoff
  have hMlt : MachineState.M aw.toNat off.toNat 32 < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  exact le_trans hn (MachineState_M_ge_left _ _ _)

theorem UInt256_ofNat_M_covers (aw off : UInt256)
    (haw : aw.toNat * 32 < UInt256.size)
    (hoff : off.toNat + 32 + 31 < UInt256.size) :
    off.toNat + 32 ≤
      (UInt256.ofNat (MachineState.M aw.toNat off.toNat 32)).toNat * 32 := by
  have hMmul := MachineState_M_mul32_lt_of_bounds haw hoff
  have hMlt : MachineState.M aw.toNat off.toNat 32 < UInt256.size := by
    omega
  rw [UInt256.toNat_ofNat_of_lt hMlt]
  unfold MachineState.M
  have hceil : off.toNat + 32 ≤ ((off.toNat + 32 + 31) / 32) * 32 := by
    have hmod := Nat.mod_lt (off.toNat + 32 + 31) (by norm_num : 0 < 32)
    have hdm := Nat.div_add_mod (off.toNat + 32 + 31) 32
    omega
  split
  · omega
  · exact le_trans hceil (Nat.mul_le_mul_right 32 (Nat.le_max_right _ _))

-- LIBRARY CANDIDATE: covered memory accesses do not expand active words.
theorem MachineState_M_eq_of_cover (aw off len : Nat) (hcover : off + len ≤ aw * 32) :
    MachineState.M aw off len = aw := by
  unfold MachineState.M
  split
  · rfl
  · rw [Nat.max_eq_left]
    have hdivlt : (off + len + 31) / 32 < aw + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 32)]
      omega
    omega

-- GENERALIZES UInt256_M_same_of_cover: arbitrary access length.
theorem UInt256_M_same_of_cover_len (aw off : UInt256) (len : Nat)
    (hcover : off.toNat + len ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off.toNat len) = aw := by
  rw [MachineState_M_eq_of_cover _ _ _ hcover]
  exact u256_ofNat_toNat aw

theorem UInt256_M_same_of_cover (aw off : UInt256)
    (_haw : aw.toNat * 32 < UInt256.size)
    (hcover : off.toNat + 32 ≤ aw.toNat * 32) :
    UInt256.ofNat (MachineState.M aw.toNat off.toNat 32) = aw :=
  UInt256_M_same_of_cover_len aw off 32 hcover

theorem UInt256_mload_haw_of_cover (aw off : UInt256)
    (haw : aw.toNat * 32 < UInt256.size)
    (hcover : off.toNat + 32 ≤ aw.toNat * 32) :
    ¬ off ≥ aw * ⟨32⟩ := by
  intro h
  have hle : (aw * ⟨32⟩).toNat ≤ off.toNat := h
  rw [u256_mul_op_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt haw] at hle
  omega


-- GENERALIZES Reasoning.Theory.uadd_word_lit32_toNat: arbitrary natural increment.
theorem uadd_word_ofNat_toNat (word : UInt256) (n : Nat) (hfit : word.toNat + n < UInt256.size) :
    (word + UInt256.ofNat n).toNat = word.toNat + n := by
  rw [uadd_toNat, UInt256.toNat_ofNat_of_lt (by omega), Nat.mod_eq_of_lt hfit]

-- LIBRARY CANDIDATE: decoding and encoding a 32-byte memory word.
theorem toByteArray_ofNat_fromByteArrayBigEndian_of_size {arr : ByteArray}
    (hsize : arr.size = 32) :
    UInt256.toByteArray (UInt256.ofNat (fromByteArrayBigEndian arr)) = arr := by
  rw [← uInt256OfByteArray_eq arr]
  rw [← word_toBytesBE_toByteArray_eq_toByteArray (uInt256OfByteArray arr)]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [List.toList_data_toByteArray]
  simpa [byteArray_toList_eq] using toBytesBE_uInt256OfByteArray_of_size hsize

-- LIBRARY CANDIDATE: extracting bytes from a decoded memory word.
theorem toByteArray_readWord_extract (mem : ByteArray) (off start len : Nat)
    (hfull : off + 32 ≤ mem.size) (hwithin : start + len ≤ 32) (hpos : 0 < len) :
    (UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off 32))).toByteArray.extract start (start + len) =
      mem.readWithPadding (off + start) len := by
  have hreadSize : (mem.readWithPadding off 32).size = 32 := by
    rw [readWithPadding_eq_extract mem off hfull, ByteArray.size_extract]
    omega
  rw [toByteArray_ofNat_fromByteArrayBigEndian_of_size hreadSize,
    readWithPadding_eq_extract mem off hfull, extract_extract_BA,
    readWithPadding_eq_extract' mem (off + start) len hpos (by omega) (by omega)]
  congr 1
  omega

end UniswapV2Pair
