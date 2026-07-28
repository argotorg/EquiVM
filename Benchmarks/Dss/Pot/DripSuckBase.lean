import Benchmarks.Dss.Pot.DripEVMArith

/-!
# Pot `drip()` — `vat.suck(vow, this, rad)` calldata / return memory helpers

Mirrors the Jug `dripVatFold*` calldata-memory defs (`Benchmarks/Dss/Jug/DripBase.lean`).
The `suck` call encodes selector `0xf24e23eb` + `[address vow, address this, uint256 rad]`
(100-byte calldata) built at the free pointer `0x80` on top of the initial `solcFreePtrMem`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-! ## Constants -/

abbrev potSuckSelectorWord : UInt256 := ⟨0xf24e23eb⟩
abbrev potSuckSelectorShifted : UInt256 := UInt256.shiftLeft potSuckSelectorWord ⟨224⟩
abbrev potSuckOutPtr : UInt256 := ⟨128⟩
abbrev potSuckInSize : UInt256 := ⟨100⟩
abbrev potSuckEndPtr : UInt256 := ⟨228⟩

/-- `this` (the executing Pot contract's own address) as a machine word (from `ADDRESS`). -/
abbrev dripThisWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.codeOwner.val

/-! ## Calldata memory (four 32-byte writes at `0x80`, `0x84`, `0xa4`, `0xc4`) -/

noncomputable def potSuckSelectorMem (mem : ByteArray) : ByteArray :=
  potSuckSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def potSuckVowMem (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (dripVowTargetWord σ I).toByteArray.write 0 (potSuckSelectorMem mem) 132 32

noncomputable def potSuckThisMem (σ : AccountMap) (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (dripThisWord I).toByteArray.write 0 (potSuckVowMem σ I mem) 164 32

noncomputable def potSuckCalldataMem (σ : AccountMap) (I : ExecutionEnv) (rad : UInt256)
    (mem : ByteArray) : ByteArray :=
  rad.toByteArray.write 0 (potSuckThisMem σ I mem) 196 32

/-- Return memory: solc writes the return word `tmp` at `0x80` before `RETURN`. -/
noncomputable def potSuckReturnMem (mem : ByteArray) (tmp : UInt256) : ByteArray :=
  (UInt256.toByteArray tmp).write 0 mem 128 32

/-! ## Canonicality of the two address arguments -/

theorem dripVowTargetWord_canonical (σ : AccountMap) (I : ExecutionEnv) :
    (dripVowTargetWord σ I).toNat < EVM.addressModulus := by
  simpa [dripVowTargetWord, potAddressReturnWord] using
    solcAddrMask_result_canonical (potSlotWord ⟨6⟩ σ I)

theorem dripThisWord_canonical (I : ExecutionEnv) :
    (dripThisWord I).toNat < EVM.addressModulus := by
  have hcw : I.codeOwner.val < EVM.addressModulus :=
    Nat.lt_of_lt_of_le I.codeOwner.isLt (le_of_eq (by native_decide))
  have hlt : I.codeOwner.val < UInt256.size := lt_trans hcw (by decide)
  show (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus
  rw [ulit_toNat' I.codeOwner.val hlt]
  exact hcw

theorem dripVowTargetWord_mask_clean (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      (dripVowTargetWord σ I) = dripVowTargetWord σ I := by
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask from by
    native_decide]
  exact solcAddrMask_clean_left (dripVowTargetWord_canonical σ I)

theorem dripThisWord_mask_clean (I : ExecutionEnv) :
    UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      (dripThisWord I) = dripThisWord I := by
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask from by
    native_decide]
  exact solcAddrMask_clean_left (dripThisWord_canonical I)

/-! ## Sizes -/

theorem potSuckSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (potSuckSelectorMem mem).size = 160 := by
  unfold potSuckSelectorMem
  exact toByteArray_write32_size_of_ge mem potSuckSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem potSuckVowMem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (potSuckVowMem σ I mem).size = 164 := by
  unfold potSuckVowMem
  exact toByteArray_write32_size_of_le (potSuckSelectorMem mem) (dripVowTargetWord σ I)
    132 160 164 (potSuckSelectorMem_size hmem)
    (by rw [potSuckSelectorMem_size hmem]; omega) (by omega)

theorem potSuckThisMem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (potSuckThisMem σ I mem).size = 196 := by
  unfold potSuckThisMem
  exact toByteArray_write32_size_of_le (potSuckVowMem σ I mem) (dripThisWord I)
    164 164 196 (potSuckVowMem_size σ I hmem)
    (by rw [potSuckVowMem_size σ I hmem]) (by omega)

theorem potSuckCalldataMem_size (σ : AccountMap) (I : ExecutionEnv) (rad : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (potSuckCalldataMem σ I rad mem).size = 228 := by
  unfold potSuckCalldataMem
  exact toByteArray_write32_size_of_le (potSuckThisMem σ I mem) rad
    196 196 228 (potSuckThisMem_size σ I hmem)
    (by rw [potSuckThisMem_size σ I hmem]) (by omega)

theorem potSuckReturnMem_size {mem : ByteArray} (tmp : UInt256) (hmem : mem.size = 228) :
    (potSuckReturnMem mem tmp).size = 228 := by
  unfold potSuckReturnMem
  exact toByteArray_write32_size_of_le mem tmp 128 228 228 hmem
    (by rw [hmem]; omega) (by omega)

/-! ## Free-pointer reads (`mem[0x40] = 0x80` preserved by every write above `0x60`) -/

theorem potSuckSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (potSuckSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold potSuckSelectorMem
  rw [toByteArray_write_read_below_of_gap potSuckSelectorShifted mem 128 64
    (by omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

theorem potSuckVowMem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (potSuckVowMem σ I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold potSuckVowMem
  rw [toByteArray_write_read_below_of_gap (dripVowTargetWord σ I) (potSuckSelectorMem mem) 132 64
    (by rw [potSuckSelectorMem_size hmem]; omega) (by omega)
    (by rw [potSuckSelectorMem_size hmem]; native_decide)]
  exact potSuckSelectorMem_read64 hmem hread64

theorem potSuckThisMem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (potSuckThisMem σ I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold potSuckThisMem
  rw [toByteArray_write_read_below_of_gap (dripThisWord I) (potSuckVowMem σ I mem) 164 64
    (by rw [potSuckVowMem_size σ I hmem]; omega) (by omega)
    (by rw [potSuckVowMem_size σ I hmem]; native_decide)]
  exact potSuckVowMem_read64 σ I hmem hread64

theorem potSuckCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv) (rad : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (potSuckCalldataMem σ I rad mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold potSuckCalldataMem
  rw [toByteArray_write_read_below_of_gap rad (potSuckThisMem σ I mem) 196 64
    (by rw [potSuckThisMem_size σ I hmem]; omega) (by omega)
    (by rw [potSuckThisMem_size σ I hmem]; native_decide)]
  exact potSuckThisMem_read64 σ I hmem hread64

theorem potSuckReturnMem_read64 {mem : ByteArray} (tmp : UInt256) (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (potSuckReturnMem mem tmp).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold potSuckReturnMem
  rw [toByteArray_write_read_below_of_gap tmp mem 128 64
    (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

/-- The return word `tmp` read back at `0x80`. -/
theorem potSuckReturnMem_read128 {mem : ByteArray} (tmp : UInt256) (hmem : mem.size = 228) :
    (potSuckReturnMem mem tmp).readWithPadding 128 32 = UInt256.toByteArray tmp := by
  unfold potSuckReturnMem
  exact toByteArray_write_read_back_of_gap tmp mem 128 (by rw [hmem]; native_decide)

/-! ## `MLOAD 0x40` values (free pointer) at the two active-word snapshots used in the trace -/

theorem potSuckCalldataMem_mload64 (σ : AccountMap) (I : ExecutionEnv) (rad : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (potSuckCalldataMem σ I rad mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((potSuckCalldataMem σ I rad mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [potSuckCalldataMem_size σ I rad hmem]; decide)
    (by decide) (potSuckCalldataMem_read64 σ I rad hmem hread64)

theorem potSuckReturnMem_mload64 {mem : ByteArray} (tmp : UInt256) (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (potSuckReturnMem mem tmp).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((potSuckReturnMem mem tmp).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [potSuckReturnMem_size tmp hmem]; decide)
    (by decide) (potSuckReturnMem_read64 tmp hmem hread64)

end Benchmarks.Dss.Pot
