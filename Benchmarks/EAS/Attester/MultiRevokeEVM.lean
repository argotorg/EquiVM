import Benchmarks.EAS.Attester.MultiRevokeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables

namespace Benchmarks.EAS.Attester

set_option linter.unnecessarySimpa false

abbrev attesterMultiRevokePostCopyFreeWord
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMloadWord mem aw ⟨64⟩

abbrev attesterMultiRevokePostCopyAwAfterMload
    (aw : UInt256) : UInt256 :=
  attesterMloadAw aw ⟨64⟩

abbrev attesterMultiRevokePostCopyFreeBumpWord
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  (⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw

abbrev attesterMultiRevokePostCopyFreeMem
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray
      (attesterMultiRevokePostCopyFreeBumpWord mem aw)).write 0 mem 64 32

abbrev attesterMultiRevokePostCopyFreeAw
    (_mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiRevokePostCopyAwAfterMload aw).toNat 64 32)

abbrev attesterMultiRevokePostCopySchemaCalldataOffset
    (schemaPayload idx : UInt256) : UInt256 :=
  UInt256.mul (⟨32⟩ : UInt256) idx + schemaPayload

abbrev attesterMultiRevokePostCopySchemaWord
    (I : ExecutionEnv) (schemaPayload idx : UInt256) : UInt256 :=
  calldataWord I.calldata
    (attesterMultiRevokePostCopySchemaCalldataOffset schemaPayload idx).toNat

abbrev attesterMultiRevokePostCopySchemaMem
    (I : ExecutionEnv) (schemaPayload idx : UInt256) (mem : ByteArray) (aw : UInt256) :
    ByteArray :=
  (UInt256.toByteArray
      (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).write 0
    (attesterMultiRevokePostCopyFreeMem mem aw)
    (attesterMultiRevokePostCopyFreeWord mem aw).toNat 32

abbrev attesterMultiRevokePostCopySchemaAw
    (_I : ExecutionEnv) (_schemaPayload _idx : UInt256) (mem : ByteArray) (aw : UInt256) :
    UInt256 :=
  UInt256.ofNat
    (MachineState.M (attesterMultiRevokePostCopyFreeAw mem aw).toNat
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat 32)

abbrev attesterMultiRevokePostCopyDataOffsetWord
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  (⟨32⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw

abbrev attesterMultiRevokePostCopyDataMem
    (base : UInt256) (I : ExecutionEnv) (schemaPayload idx : UInt256)
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray base).write 0
    (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
    (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat 32

abbrev attesterMultiRevokePostCopyDataAw
    (_base : UInt256) (I : ExecutionEnv) (schemaPayload idx : UInt256)
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M
      (attesterMultiRevokePostCopySchemaAw I schemaPayload idx mem aw).toNat
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat 32)

abbrev attesterMultiRevokePostCopyOuterArrayAwAfterMload
    (outerBase : UInt256) (I : ExecutionEnv) (schemaPayload idx : UInt256)
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  attesterMloadAw
    (attesterMultiRevokePostCopyDataAw outerBase I schemaPayload idx mem aw) outerBase

abbrev attesterMultiRevokePostCopyOuterSlotWord
    (outerBase idx : UInt256) : UInt256 :=
  ((⟨32⟩ : UInt256) + UInt256.mul (⟨32⟩ : UInt256) idx) + outerBase

abbrev attesterMultiRevokePostCopyOuterMem
    (base outerBase : UInt256) (I : ExecutionEnv) (schemaPayload idx : UInt256)
    (mem : ByteArray) (aw : UInt256) : ByteArray :=
  (UInt256.toByteArray (attesterMultiRevokePostCopyFreeWord mem aw)).write 0
    (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
    (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat 32

abbrev attesterMultiRevokePostCopyOuterAw
    (_base outerBase : UInt256) (I : ExecutionEnv) (schemaPayload idx : UInt256)
    (mem : ByteArray) (aw : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M
      (attesterMultiRevokePostCopyOuterArrayAwAfterMload outerBase I schemaPayload idx mem aw).toNat
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat 32)

abbrev attesterMultiRevokePostCopyNextIdx (idx : UInt256) : UInt256 :=
  (⟨1⟩ : UInt256) + idx

theorem attesterMultiRevokePostCopyOuterSlotWord_toNat
    {outerBase idx : UInt256}
    (hbound : outerBase.toNat + 32 + 32 * idx.toNat < UInt256.size) :
    (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat =
      outerBase.toNat + 32 + 32 * idx.toNat := by
  unfold attesterMultiRevokePostCopyOuterSlotWord
  have hmul :
      (UInt256.mul (⟨32⟩ : UInt256) idx).toNat = 32 * idx.toNat := by
    rw [u256_mul_toNat]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  have hinner :
      (((⟨32⟩ : UInt256) + UInt256.mul (⟨32⟩ : UInt256) idx).toNat) =
        32 + 32 * idx.toNat := by
    rw [uadd_toNat, hmul]
    rw [show (⟨32⟩ : UInt256).toNat = 32 by decide]
    exact Nat.mod_eq_of_lt (by omega)
  rw [uadd_toNat, hinner]
  rw [show 32 + 32 * idx.toNat + outerBase.toNat =
      outerBase.toNat + 32 + 32 * idx.toNat by omega]
  exact Nat.mod_eq_of_lt hbound

theorem attesterMultiRevokePostCopyDataMem_readOuter_and_size
    {base outerBase len schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : outerBase.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding outerBase.toNat 32 = UInt256.toByteArray len)
    (houter64 : 64 + 32 ≤ outerBase.toNat)
    (hbase : outerBase.toNat + 32 ≤ base.toNat)
    (hfree : base.toNat + 32 ≤ (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
    (hfree96 :
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 96 < UInt256.size) :
    (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).readWithPadding
        outerBase.toNat 32 =
      UInt256.toByteArray len ∧
    outerBase.toNat + 32 ≤
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).size := by
  let free := attesterMultiRevokePostCopyFreeWord mem aw
  let dataOff := attesterMultiRevokePostCopyDataOffsetWord mem aw
  have hfreeGe : base.toNat + 32 ≤ free.toNat := by
    simpa [free] using hfree
  have hfree32 : free.toNat + 32 < UInt256.size := by
    have hfree96' : free.toNat + 96 < UInt256.size := by
      simpa [free] using hfree96
    omega
  have hdataToNat : dataOff.toNat = free.toNat + 32 := by
    unfold dataOff attesterMultiRevokePostCopyDataOffsetWord
    exact uadd_lit32_toNat free hfree32
  have hread1 :
      (attesterMultiRevokePostCopyFreeMem mem aw).readWithPadding outerBase.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord mem 64
      (attesterMultiRevokePostCopyFreeBumpWord mem aw)).readWithPadding
        outerBase.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := mem) (base := outerBase.toNat) (writeOff := 64)
      (len := len) (writeVal := attesterMultiRevokePostCopyFreeBumpWord mem aw)
      hmem houter64 hread
  have hmem1 :
      outerBase.toNat + 32 ≤ (attesterMultiRevokePostCopyFreeMem mem aw).size := by
    change outerBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        (attesterMultiRevokePostCopyFreeBumpWord mem aw)).size
    exact le_trans hmem
      (attesterWriteWord_size_ge_nat mem 64
        (attesterMultiRevokePostCopyFreeBumpWord mem aw))
  have hread2 :
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw).readWithPadding
          outerBase.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyFreeMem mem aw)
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat
      (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).readWithPadding
        outerBase.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopyFreeMem mem aw)
      (base := outerBase.toNat)
      (writeOff := (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
      (len := len) (writeVal := attesterMultiRevokePostCopySchemaWord I schemaPayload idx)
      hmem1 (by simpa [free] using (by omega : outerBase.toNat + 32 ≤ free.toNat))
      hread1
  have hmem2 :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw).size := by
    change outerBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopyFreeMem mem aw)
        (attesterMultiRevokePostCopyFreeWord mem aw).toNat
        (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).size
    exact le_trans hmem1
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokePostCopyFreeMem mem aw)
        (attesterMultiRevokePostCopyFreeWord mem aw).toNat
        (attesterMultiRevokePostCopySchemaWord I schemaPayload idx))
  have hread3 :
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).readWithPadding
          outerBase.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base).readWithPadding
        outerBase.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (base := outerBase.toNat)
      (writeOff := (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat)
      (len := len) (writeVal := base)
      hmem2 (by rw [hdataToNat]; omega) hread2
  have hmem3 :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).size := by
    change outerBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base).size
    exact le_trans hmem2
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base)
  exact ⟨hread3, hmem3⟩

theorem attesterMultiRevokePostCopyOuterMem_readOuter_and_size
    {base outerBase len schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : outerBase.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding outerBase.toNat 32 = UInt256.toByteArray len)
    (houter64 : 64 + 32 ≤ outerBase.toNat)
    (hbase : outerBase.toNat + 32 ≤ base.toNat)
    (hfree : base.toNat + 32 ≤ (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
    (hfree96 :
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 96 < UInt256.size)
    (hslotBound : outerBase.toNat + 32 + 32 * idx.toNat < UInt256.size) :
    (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).readWithPadding
        outerBase.toNat 32 =
      UInt256.toByteArray len ∧
    outerBase.toNat + 32 ≤
      (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).size := by
  obtain ⟨hreadData, hmemData⟩ :=
    attesterMultiRevokePostCopyDataMem_readOuter_and_size
      (base := base) (outerBase := outerBase) (len := len)
      (schemaPayload := schemaPayload) (idx := idx) (mem := mem) (aw := aw)
      hmem hread houter64 hbase hfree hfree96
  have hslotToNat :
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat =
        outerBase.toNat + 32 + 32 * idx.toNat :=
    attesterMultiRevokePostCopyOuterSlotWord_toNat hslotBound
  have hreadOuter :
      (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).readWithPadding
          outerBase.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
      (attesterMultiRevokePostCopyFreeWord mem aw)).readWithPadding
        outerBase.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (base := outerBase.toNat)
      (writeOff := (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat)
      (len := len) (writeVal := attesterMultiRevokePostCopyFreeWord mem aw)
      hmemData (by rw [hslotToNat]; omega) hreadData
  have hmemOuter :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).size := by
    change outerBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
        (attesterMultiRevokePostCopyFreeWord mem aw)).size
    exact le_trans hmemData
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
        (attesterMultiRevokePostCopyFreeWord mem aw))
  exact ⟨hreadOuter, hmemOuter⟩

theorem attesterMultiRevokePostCopyDataMem_mloadOuter
    {base outerBase len schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hmem : outerBase.toNat + 32 ≤ mem.size)
    (hread : mem.readWithPadding outerBase.toNat 32 = UInt256.toByteArray len)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (houter64 : 64 + 32 ≤ outerBase.toNat)
    (hbase : outerBase.toNat + 32 ≤ base.toNat)
    (hfree : base.toNat + 32 ≤ (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
    (hfree96 :
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 96 < UInt256.size) :
    attesterMloadWord
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyDataAw base I schemaPayload idx mem aw)
      outerBase = len := by
  let free := attesterMultiRevokePostCopyFreeWord mem aw
  let dataOff := attesterMultiRevokePostCopyDataOffsetWord mem aw
  have hfreeGe : base.toNat + 32 ≤ free.toNat := by
    simpa [free] using hfree
  have hfree96' : free.toNat + 96 < UInt256.size := by
    simpa [free] using hfree96
  have hfree32 : free.toNat + 32 < UInt256.size := by
    omega
  have hfree63 : free.toNat + 63 < UInt256.size := by
    omega
  have hdataToNat : dataOff.toNat = free.toNat + 32 := by
    unfold dataOff attesterMultiRevokePostCopyDataOffsetWord
    exact uadd_lit32_toNat free hfree32
  have hdata63 : dataOff.toNat + 63 < UInt256.size := by
    rw [hdataToNat]
    omega
  have hread1 :
      (attesterMultiRevokePostCopyFreeMem mem aw).readWithPadding outerBase.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord mem 64
      (attesterMultiRevokePostCopyFreeBumpWord mem aw)).readWithPadding
        outerBase.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_below_nat
      (mem := mem) (base := outerBase.toNat) (writeOff := 64)
      (len := len) (writeVal := attesterMultiRevokePostCopyFreeBumpWord mem aw)
      hmem houter64 hread
  have hmem1 :
      outerBase.toNat + 32 ≤ (attesterMultiRevokePostCopyFreeMem mem aw).size := by
    change outerBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        (attesterMultiRevokePostCopyFreeBumpWord mem aw)).size
    exact le_trans hmem
      (attesterWriteWord_size_ge_nat mem 64
        (attesterMultiRevokePostCopyFreeBumpWord mem aw))
  have hread2 :
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw).readWithPadding
          outerBase.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyFreeMem mem aw)
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat
      (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).readWithPadding
        outerBase.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopyFreeMem mem aw)
      (base := outerBase.toNat)
      (writeOff := (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
      (len := len) (writeVal := attesterMultiRevokePostCopySchemaWord I schemaPayload idx)
      hmem1 (by simpa [free] using (by omega : outerBase.toNat + 32 ≤ free.toNat)) hread1
  have hmem2 :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw).size := by
    change outerBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopyFreeMem mem aw)
        (attesterMultiRevokePostCopyFreeWord mem aw).toNat
        (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).size
    exact le_trans hmem1
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokePostCopyFreeMem mem aw)
        (attesterMultiRevokePostCopyFreeWord mem aw).toNat
        (attesterMultiRevokePostCopySchemaWord I schemaPayload idx))
  have hread3 :
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).readWithPadding
          outerBase.toNat 32 =
        UInt256.toByteArray len := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base).readWithPadding
        outerBase.toNat 32 = UInt256.toByteArray len
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (base := outerBase.toNat)
      (writeOff := (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat)
      (len := len) (writeVal := base)
      hmem2 (by rw [hdataToNat]; omega) hread2
  have hmem3 :
      outerBase.toNat + 32 ≤
        (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).size := by
    change outerBase.toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base).size
    exact le_trans hmem2
      (attesterWriteWord_size_ge_nat
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base)
  let aw1 := attesterMultiRevokePostCopyAwAfterMload aw
  let aw2 := attesterMultiRevokePostCopyFreeAw mem aw
  let aw3 := attesterMultiRevokePostCopySchemaAw I schemaPayload idx mem aw
  let aw4 := attesterMultiRevokePostCopyDataAw base I schemaPayload idx mem aw
  have hM1 : MachineState.M aw.toNat 64 32 < UInt256.size :=
    attesterMachineStateM32_lt hawMul (by norm_num [UInt256.size])
  have haw1ToNat : aw1.toNat = MachineState.M aw.toNat 64 32 := by
    unfold aw1 attesterMultiRevokePostCopyAwAfterMload attesterMloadAw
    rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
    exact ulit_toNat' _ hM1
  have haw1Mul : aw1.toNat * 32 < UInt256.size := by
    rw [haw1ToNat]
    exact attesterMachineStateM32_mul32_lt hawMul (by norm_num [UInt256.size])
  have hM2 : MachineState.M aw1.toNat 64 32 < UInt256.size :=
    attesterMachineStateM32_lt haw1Mul (by norm_num [UInt256.size])
  have haw2ToNat : aw2.toNat = MachineState.M aw1.toNat 64 32 := by
    unfold aw2 attesterMultiRevokePostCopyFreeAw
    change (UInt256.ofNat (MachineState.M aw1.toNat 64 32)).toNat =
      MachineState.M aw1.toNat 64 32
    exact ulit_toNat' _ hM2
  have haw2Mul : aw2.toNat * 32 < UInt256.size := by
    rw [haw2ToNat]
    exact attesterMachineStateM32_mul32_lt haw1Mul (by norm_num [UInt256.size])
  have hM3 : MachineState.M aw2.toNat free.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt haw2Mul hfree63
  have haw3ToNat : aw3.toNat = MachineState.M aw2.toNat free.toNat 32 := by
    unfold aw3 attesterMultiRevokePostCopySchemaAw
    change (UInt256.ofNat (MachineState.M aw2.toNat free.toNat 32)).toNat =
      MachineState.M aw2.toNat free.toNat 32
    exact ulit_toNat' _ hM3
  have haw3Mul : aw3.toNat * 32 < UInt256.size := by
    rw [haw3ToNat]
    exact attesterMachineStateM32_mul32_lt haw2Mul hfree63
  have hM4 : MachineState.M aw3.toNat dataOff.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt haw3Mul hdata63
  have haw4ToNat : aw4.toNat = MachineState.M aw3.toNat dataOff.toNat 32 := by
    unfold aw4 attesterMultiRevokePostCopyDataAw
    change (UInt256.ofNat (MachineState.M aw3.toNat dataOff.toNat 32)).toNat =
      MachineState.M aw3.toNat dataOff.toNat 32
    exact ulit_toNat' _ hM4
  have haw4Mul : aw4.toNat * 32 < UInt256.size := by
    rw [haw4ToNat]
    exact attesterMachineStateM32_mul32_lt haw3Mul hdata63
  have hdataCovered : dataOff.toNat + 32 ≤ aw4.toNat * 32 := by
    have hcover := attesterMachineStateM_covers_word32 aw3.toNat dataOff.toNat
    rw [haw4ToNat]
    nlinarith
  have houterCovered : outerBase.toNat + 32 ≤ aw4.toNat * 32 := by
    exact le_trans (by rw [hdataToNat]; omega) hdataCovered
  have haw :
      ¬ outerBase ≥
        (attesterMultiRevokePostCopyDataAw base I schemaPayload idx mem aw) *
          (⟨32⟩ : UInt256) := by
    exact attesterMloadActiveWordsCovers
      (base := outerBase)
      (aw := attesterMultiRevokePostCopyDataAw base I schemaPayload idx mem aw)
      (by simpa [aw4] using haw4Mul)
      (by simpa [aw4] using houterCovered)
  exact attesterMloadWord_of_readWithPadding hmem3 haw hread3

theorem attesterMultiRevokePostCopyOuterMem_read64
    {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
    (hdata : 64 + 32 ≤ (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat)
    (hslot : 64 + 32 ≤ (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat) :
    (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).readWithPadding
        64 32 =
      UInt256.toByteArray
        ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw) := by
  have hread1 :
      (attesterMultiRevokePostCopyFreeMem mem aw).readWithPadding 64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord mem 64
      ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw)).readWithPadding
        64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw)
    exact attesterWriteWord_read_back_nat mem 64
      ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw)
  have hmem1 : 64 + 32 ≤ (attesterMultiRevokePostCopyFreeMem mem aw).size := by
    have hsize := attesterWriteWord_size_nat mem 64
      ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord mem 64
        ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw)).size
    rw [hsize]
    change 96 ≤ max mem.size (64 + 32)
    exact Nat.le_max_right _ _
  have hread2 :
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw).readWithPadding
          64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopyFreeMem mem aw)
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat
      (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).readWithPadding
        64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw)
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopyFreeMem mem aw)
      (base := 64)
      (writeOff := (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
      (len := ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw))
      (writeVal := attesterMultiRevokePostCopySchemaWord I schemaPayload idx)
      hmem1 hfree hread1
  have hmem2 :
      64 + 32 ≤ (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat (attesterMultiRevokePostCopyFreeMem mem aw)
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat
      (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord (attesterMultiRevokePostCopyFreeMem mem aw)
        (attesterMultiRevokePostCopyFreeWord mem aw).toNat
        (attesterMultiRevokePostCopySchemaWord I schemaPayload idx)).size
    rw [hsize]
    exact le_trans hmem1 (Nat.le_max_left _ _)
  have hread3 :
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).readWithPadding
          64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw) := by
    change (Reasoning.Theory.writeWord
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base).readWithPadding
        64 32 =
        UInt256.toByteArray
          ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw)
    exact attesterReadWithPadding_writeWord_preserved_above_nat
      (mem := attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (base := 64)
      (writeOff := (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat)
      (len := ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw))
      (writeVal := base)
      hmem2 hdata hread2
  have hmem3 :
      64 + 32 ≤ (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat
      (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base
    change 64 + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat base).size
    rw [hsize]
    exact le_trans hmem2 (Nat.le_max_left _ _)
  change (Reasoning.Theory.writeWord
    (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
    (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
    (attesterMultiRevokePostCopyFreeWord mem aw)).readWithPadding 64 32 =
      UInt256.toByteArray
        ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw)
  exact attesterReadWithPadding_writeWord_preserved_above_nat
    (mem := attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
    (base := 64)
    (writeOff := (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat)
    (len := ((⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw))
    (writeVal := attesterMultiRevokePostCopyFreeWord mem aw)
    hmem3 hslot hread3

theorem attesterMultiRevokePostCopyOuterAw_bounds
    {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hawGe : 3 ≤ aw.toNat)
    (hawMul : aw.toNat * 32 < UInt256.size)
    (hfree95 : (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 95 < UInt256.size)
    (houter63 : outerBase.toNat + 63 < UInt256.size)
    (hslot63 : (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 63 <
      UInt256.size) :
    3 ≤ (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw).toNat ∧
      (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw).toNat *
          32 < UInt256.size := by
  let free := attesterMultiRevokePostCopyFreeWord mem aw
  let dataOff := attesterMultiRevokePostCopyDataOffsetWord mem aw
  let aw1 := attesterMultiRevokePostCopyAwAfterMload aw
  let aw2 := attesterMultiRevokePostCopyFreeAw mem aw
  let aw3 := attesterMultiRevokePostCopySchemaAw I schemaPayload idx mem aw
  let aw4 := attesterMultiRevokePostCopyDataAw base I schemaPayload idx mem aw
  let aw5 := attesterMultiRevokePostCopyOuterArrayAwAfterMload
    outerBase I schemaPayload idx mem aw
  let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase idx
  have hfree63 : free.toNat + 63 < UInt256.size := by
    simpa [free] using (by
      have h := hfree95
      omega)
  have hfree32 : free.toNat + 32 < UInt256.size := by
    simpa [free] using (by
      have h := hfree95
      omega)
  have hdataToNat : dataOff.toNat = free.toNat + 32 := by
    unfold dataOff attesterMultiRevokePostCopyDataOffsetWord
    exact uadd_lit32_toNat free hfree32
  have hdata63 : dataOff.toNat + 63 < UInt256.size := by
    rw [hdataToNat]
    simpa [free] using hfree95
  have hM1 : MachineState.M aw.toNat 64 32 < UInt256.size :=
    attesterMachineStateM32_lt hawMul (by norm_num [UInt256.size])
  have hM1Mul : MachineState.M aw.toNat 64 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt hawMul (by norm_num [UInt256.size])
  have haw1Ge : 3 ≤ aw1.toNat := by
    unfold aw1 attesterMultiRevokePostCopyAwAfterMload attesterMloadAw
    rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
    rw [ulit_toNat' _ hM1]
    exact le_trans hawGe (attesterMachineStateM_ge aw.toNat 64 32)
  have haw1Mul : aw1.toNat * 32 < UInt256.size := by
    unfold aw1 attesterMultiRevokePostCopyAwAfterMload attesterMloadAw
    rw [show (⟨64⟩ : UInt256).toNat = 64 by decide]
    rw [ulit_toNat' _ hM1]
    exact hM1Mul
  have hM2 : MachineState.M aw1.toNat 64 32 < UInt256.size :=
    attesterMachineStateM32_lt haw1Mul (by norm_num [UInt256.size])
  have hM2Mul : MachineState.M aw1.toNat 64 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt haw1Mul (by norm_num [UInt256.size])
  have haw2Ge : 3 ≤ aw2.toNat := by
    unfold aw2 attesterMultiRevokePostCopyFreeAw
    rw [ulit_toNat' _ hM2]
    exact le_trans haw1Ge (attesterMachineStateM_ge aw1.toNat 64 32)
  have haw2Mul : aw2.toNat * 32 < UInt256.size := by
    unfold aw2 attesterMultiRevokePostCopyFreeAw
    rw [ulit_toNat' _ hM2]
    exact hM2Mul
  have hM3 : MachineState.M aw2.toNat free.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt haw2Mul hfree63
  have hM3Mul : MachineState.M aw2.toNat free.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt haw2Mul hfree63
  have haw3Ge : 3 ≤ aw3.toNat := by
    unfold aw3 attesterMultiRevokePostCopySchemaAw
    rw [ulit_toNat' _ hM3]
    exact le_trans haw2Ge
      (attesterMachineStateM_ge
        (attesterMultiRevokePostCopyFreeAw mem aw).toNat
        (attesterMultiRevokePostCopyFreeWord mem aw).toNat 32)
  have haw3Mul : aw3.toNat * 32 < UInt256.size := by
    unfold aw3 attesterMultiRevokePostCopySchemaAw
    rw [ulit_toNat' _ hM3]
    exact hM3Mul
  have hM4 : MachineState.M aw3.toNat dataOff.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt haw3Mul hdata63
  have hM4Mul : MachineState.M aw3.toNat dataOff.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt haw3Mul hdata63
  have haw4Ge : 3 ≤ aw4.toNat := by
    unfold aw4 attesterMultiRevokePostCopyDataAw
    rw [ulit_toNat' _ hM4]
    exact le_trans haw3Ge
      (attesterMachineStateM_ge
        (attesterMultiRevokePostCopySchemaAw I schemaPayload idx mem aw).toNat
        (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat 32)
  have haw4Mul : aw4.toNat * 32 < UInt256.size := by
    unfold aw4 attesterMultiRevokePostCopyDataAw
    rw [ulit_toNat' _ hM4]
    exact hM4Mul
  have hM5 : MachineState.M aw4.toNat outerBase.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt haw4Mul houter63
  have hM5Mul : MachineState.M aw4.toNat outerBase.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt haw4Mul houter63
  have haw5Ge : 3 ≤ aw5.toNat := by
    unfold aw5 attesterMultiRevokePostCopyOuterArrayAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM5]
    exact le_trans haw4Ge
      (attesterMachineStateM_ge
        (attesterMultiRevokePostCopyDataAw base I schemaPayload idx mem aw).toNat
        outerBase.toNat 32)
  have haw5Mul : aw5.toNat * 32 < UInt256.size := by
    unfold aw5 attesterMultiRevokePostCopyOuterArrayAwAfterMload attesterMloadAw
    rw [ulit_toNat' _ hM5]
    exact hM5Mul
  have hM6 : MachineState.M aw5.toNat slot.toNat 32 < UInt256.size :=
    attesterMachineStateM32_lt haw5Mul (by simpa [slot] using hslot63)
  have hM6Mul : MachineState.M aw5.toNat slot.toNat 32 * 32 < UInt256.size :=
    attesterMachineStateM32_mul32_lt haw5Mul (by simpa [slot] using hslot63)
  constructor
  · unfold attesterMultiRevokePostCopyOuterAw
    rw [ulit_toNat' _ hM6]
    exact le_trans haw5Ge
      (attesterMachineStateM_ge
        (attesterMultiRevokePostCopyOuterArrayAwAfterMload
          outerBase I schemaPayload idx mem aw).toNat
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat 32)
  · unfold attesterMultiRevokePostCopyOuterAw
    rw [ulit_toNat' _ hM6]
    exact hM6Mul

theorem attesterMultiRevokePostCopyOuterMem_mload64
    {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
    (hdata : 64 + 32 ≤ (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat)
    (hslot : 64 + 32 ≤ (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat)
    (haw :
      ¬ (⟨64⟩ : UInt256) ≥
        attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw *
          (⟨32⟩ : UInt256)) :
    attesterInnerArrayAllocFreeWord
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw) =
      (⟨64⟩ : UInt256) + attesterMultiRevokePostCopyFreeWord mem aw := by
  have hread := attesterMultiRevokePostCopyOuterMem_read64
    (I := I) (base := base) (outerBase := outerBase)
    (schemaPayload := schemaPayload) (idx := idx) (mem := mem) (aw := aw)
    hfree hdata hslot
  have hmem : (⟨64⟩ : UInt256).toNat + 32 ≤
      (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw).size := by
    have hsize := attesterWriteWord_size_nat
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
      (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
      (attesterMultiRevokePostCopyFreeWord mem aw)
    change (⟨64⟩ : UInt256).toNat + 32 ≤
      (Reasoning.Theory.writeWord
        (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat
        (attesterMultiRevokePostCopyFreeWord mem aw)).size
    rw [hsize]
    change 96 ≤ max
      (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw).size
      ((attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat + 32)
    exact le_trans (by omega) (Nat.le_max_right _ _)
  exact attesterMloadWord_of_readWithPadding hmem haw hread

theorem attesterMultiRevokePostCopyOuterMem_freeWord_toNat
    {base outerBase schemaPayload idx : UInt256}
    {mem : ByteArray} {aw : UInt256}
    (hfree : 64 + 32 ≤ (attesterMultiRevokePostCopyFreeWord mem aw).toNat)
    (hdata : 64 + 32 ≤ (attesterMultiRevokePostCopyDataOffsetWord mem aw).toNat)
    (hslot : 64 + 32 ≤ (attesterMultiRevokePostCopyOuterSlotWord outerBase idx).toNat)
    (hawMul :
      (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw).toNat *
          32 < UInt256.size)
    (hawGe :
      3 ≤ (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw).toNat)
    (hfreeBound : (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 64 < UInt256.size) :
    (attesterInnerArrayAllocFreeWord
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw)).toNat =
      (attesterMultiRevokePostCopyFreeWord mem aw).toNat + 64 := by
  rw [attesterMultiRevokePostCopyOuterMem_mload64
    (I := I) (base := base) (outerBase := outerBase)
    (schemaPayload := schemaPayload) (idx := idx) (mem := mem) (aw := aw)
    hfree hdata hslot (attesterMload64ActiveWordsGe3 hawMul hawGe)]
  exact attester_uadd_lit64_toNat (attesterMultiRevokePostCopyFreeWord mem aw) hfreeBound

abbrev attesterMultiRevokeInnerArrayHeadWord
    (payload idx : UInt256) : UInt256 :=
  payload + UInt256.mul (⟨32⟩ : UInt256) idx

abbrev attesterMultiRevokeInnerArrayOffsetWord
    (I : ExecutionEnv) (head : UInt256) : UInt256 :=
  calldataWord I.calldata head.toNat

abbrev attesterMultiRevokeInnerArrayStartWord
    (I : ExecutionEnv) (base head : UInt256) : UInt256 :=
  base + attesterMultiRevokeInnerArrayOffsetWord I head

abbrev attesterMultiRevokeInnerArrayLengthWord
    (I : ExecutionEnv) (base head : UInt256) : UInt256 :=
  calldataWord I.calldata
    (attesterMultiRevokeInnerArrayStartWord I base head).toNat

abbrev attesterMultiRevokeInnerArrayPayloadWord
    (I : ExecutionEnv) (base head : UInt256) : UInt256 :=
  attesterMultiRevokeInnerArrayStartWord I base head + ⟨32⟩

private theorem attester_inner_start_add32_comm
    (I : ExecutionEnv) (base head : UInt256) :
    (⟨32⟩ : UInt256) + attesterMultiRevokeInnerArrayStartWord I base head =
      attesterMultiRevokeInnerArrayStartWord I base head + ⟨32⟩ := by
  exact u256_add_comm _ _

private theorem attester_pc363_after_inner_setup_at :
    ((((((((((((⟨363⟩ : UInt256) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) +
                      UInt256.ofNat 2) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) + ⟨1⟩) +
                  UInt256.ofNat 3) + ⟨1⟩) + ⟨1⟩) + UInt256.ofNat 3 =
      (⟨380⟩ : UInt256) := by
  native_decide

theorem attesterMultiRevokePostCopySchemaOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨638⟩ : UInt256) = true := by
  let A := attesterBytecode.extract 0 722
  let B := (patchedRuntime v).extract 722 (patchedRuntime v).size
  have hprefix : (patchedRuntime v).extract 0 722 = A := by
    unfold A
    rw [patchedRuntime_extract_preserved_len v 0 722
      (by simp [runtimeWrites, WindowDisjointFromWrites])
      (by norm_num)
      (by norm_num)
      (by norm_num)]
  have hsplit : patchedRuntime v = A ++ B := by
    unfold B
    have h := ByteArray.extract_append_extract (a := patchedRuntime v)
      (i := 0) (j := 722) (k := (patchedRuntime v).size)
    rw [← hprefix]
    have hsize : 722 ≤ (patchedRuntime v).size := by
      rw [patchedRuntime_size v]
      norm_num
    have hmax : max 722 (patchedRuntime v).size = (patchedRuntime v).size :=
      Nat.max_eq_right hsize
    have hmin : min 0 722 = 0 := by omega
    simpa [hmin, hmax, ByteArray.extract_zero_size] using h.symm
  rw [hsplit]
  apply Reasoning.Theory.D_J_contains_append_left
  unfold A
  native_decide

theorem attesterMultiRevokeOuterSourceLoopJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨335⟩ : UInt256) = true := by
  let A := attesterBytecode.extract 0 722
  let B := (patchedRuntime v).extract 722 (patchedRuntime v).size
  have hprefix : (patchedRuntime v).extract 0 722 = A := by
    unfold A
    rw [patchedRuntime_extract_preserved_len v 0 722
      (by simp [runtimeWrites, WindowDisjointFromWrites])
      (by norm_num)
      (by norm_num)
      (by norm_num)]
  have hsplit : patchedRuntime v = A ++ B := by
    unfold B
    have h := ByteArray.extract_append_extract (a := patchedRuntime v)
      (i := 0) (j := 722) (k := (patchedRuntime v).size)
    rw [← hprefix]
    have hsize : 722 ≤ (patchedRuntime v).size := by
      rw [patchedRuntime_size v]
      norm_num
    have hmax : max 722 (patchedRuntime v).size = (patchedRuntime v).size :=
      Nat.max_eq_right hsize
    have hmin : min 0 722 = 0 := by omega
    simpa [hmin, hmax, ByteArray.extract_zero_size] using h.symm
  rw [hsplit]
  apply Reasoning.Theory.D_J_contains_append_left
  unfold A
  native_decide

theorem attesterMultiRevokePostCopyOuterStoreOkJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨672⟩ : UInt256) = true := by
  let A := attesterBytecode.extract 0 722
  let B := (patchedRuntime v).extract 722 (patchedRuntime v).size
  have hprefix : (patchedRuntime v).extract 0 722 = A := by
    unfold A
    rw [patchedRuntime_extract_preserved_len v 0 722
      (by simp [runtimeWrites, WindowDisjointFromWrites])
      (by norm_num)
      (by norm_num)
      (by norm_num)]
  have hsplit : patchedRuntime v = A ++ B := by
    unfold B
    have h := ByteArray.extract_append_extract (a := patchedRuntime v)
      (i := 0) (j := 722) (k := (patchedRuntime v).size)
    rw [← hprefix]
    have hsize : 722 ≤ (patchedRuntime v).size := by
      rw [patchedRuntime_size v]
      norm_num
    have hmax : max 722 (patchedRuntime v).size = (patchedRuntime v).size :=
      Nat.max_eq_right hsize
    have hmin : min 0 722 = 0 := by omega
    simpa [hmin, hmax, ByteArray.extract_zero_size] using h.symm
  rw [hsplit]
  apply Reasoning.Theory.D_J_contains_append_left
  unfold A
  native_decide

theorem attesterMultiRevokeExternalCallEntryJumpdest (v : AttesterImmutables) :
    (D_J (patchedRuntime v) 0).contains (⟨698⟩ : UInt256) = true := by
  let A := attesterBytecode.extract 0 722
  let B := (patchedRuntime v).extract 722 (patchedRuntime v).size
  have hprefix : (patchedRuntime v).extract 0 722 = A := by
    unfold A
    rw [patchedRuntime_extract_preserved_len v 0 722
      (by simp [runtimeWrites, WindowDisjointFromWrites])
      (by norm_num)
      (by norm_num)
      (by norm_num)]
  have hsplit : patchedRuntime v = A ++ B := by
    unfold B
    have h := ByteArray.extract_append_extract (a := patchedRuntime v)
      (i := 0) (j := 722) (k := (patchedRuntime v).size)
    rw [← hprefix]
    have hsize : 722 ≤ (patchedRuntime v).size := by
      rw [patchedRuntime_size v]
      norm_num
    have hmax : max 722 (patchedRuntime v).size = (patchedRuntime v).size :=
      Nat.max_eq_right hsize
    have hmin : min 0 722 = 0 := by omega
    simpa [hmin, hmax, ByteArray.extract_zero_size] using h.symm
  rw [hsplit]
  apply Reasoning.Theory.D_J_contains_append_left
  unfold A
  native_decide

theorem attesterX_multiRevokeOuterSourceLoopExit
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hge : UInt256.lt idx schemaLen = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen, schemaPayload,
        ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨698⟩ : UInt256)
        [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen, schemaPayload,
          ret, selector]
        mem aw ByteArray.empty (cA, σ) k' C' := by
  have hcond : UInt256.isZero (UInt256.lt idx schemaLen) ≠ ⟨0⟩ := by
    rw [hge]
    decide
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨335⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨336⟩, 0x82, .DUP3) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨337⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨338⟩, 0x10, .LT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨339⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨698⟩ (by attester_decode_at v, ⟨340⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨343⟩, 0x57, .JUMPI)
      hcond (attesterMultiRevokeExternalCallEntryJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeOuterSourceLoopGuard
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hlt : UInt256.lt idx schemaLen = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen, schemaPayload,
        ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨344⟩ : UInt256)
        [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen, schemaPayload,
          ret, selector]
        mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨335⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨336⟩, 0x82, .DUP3) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨337⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨338⟩, 0x10, .LT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨339⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨698⟩ (by attester_decode_at v, ⟨340⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨343⟩, 0x57, .JUMPI)
      (by rw [hlt]; decide) (by evm_ov)]⟩

theorem attesterX_multiRevokeOuterSecondArrayAccessCheckAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hltSecond : UInt256.lt idx secondLen = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨344⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen, schemaPayload,
        ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨355⟩ : UInt256)
        [⟨363⟩, ⟨1⟩, idx, secondLen, secondPayload, ⟨0⟩,
          UInt256.ofNat I.calldata.size, idx, outerBase, schemaLen, secondLen,
          secondPayload, schemaLen, schemaPayload, ret, selector]
        mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, by
    simpa [hltSecond] using
      (evm_run hreach with [
        raw calldatasize (by attester_decode_at v, ⟨344⟩, 0x36, .CALLDATASIZE) (by evm_ov),
        raw push0 (by attester_decode_at v, ⟨345⟩, 0x5f, .PUSH0) (by evm_ov),
        raw dup7 (by attester_decode_at v, ⟨346⟩, 0x86, .DUP7) (by evm_ov),
        raw dup7 (by attester_decode_at v, ⟨347⟩, 0x86, .DUP7) (by evm_ov),
        raw dup5 (by attester_decode_at v, ⟨348⟩, 0x84, .DUP5) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨349⟩, 0x81, .DUP2) (by evm_ov),
        raw dup2 (by attester_decode_at v, ⟨350⟩, 0x81, .DUP2) (by evm_ov),
        raw lt (by attester_decode_at v, ⟨351⟩, 0x10, .LT) (by evm_ov),
        raw push2 ⟨363⟩ (by attester_decode_at v, ⟨352⟩, 0x61, (.Push .PUSH2))
          (by evm_ov)])⟩

theorem attesterX_multiRevokeOuterSecondArrayAccessOkAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx outerBase schemaLen secondLen secondPayload schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hltSecond : UInt256.lt idx secondLen = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨344⟩ : UInt256)
      [idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen, schemaPayload,
        ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨363⟩ : UInt256)
        [idx, secondLen, secondPayload, ⟨0⟩, UInt256.ofNat I.calldata.size,
          idx, outerBase, schemaLen, secondLen, secondPayload, schemaLen,
          schemaPayload, ret, selector]
        mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd0⟩ :=
    attesterX_multiRevokeOuterSecondArrayAccessCheckAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (outerBase := outerBase) (schemaLen := schemaLen)
      (secondLen := secondLen) (secondPayload := secondPayload)
      (schemaPayload := schemaPayload) (ret := ret) (selector := selector)
      (mem := mem) (aw := aw) (k := k) (C := C) hltSecond hreach
  exact ⟨_, _, evm_run rd0 with [
    raw jumpiT (by attester_decode_at v, ⟨355⟩, 0x57, .JUMPI)
      (by decide) (attesterMultiRevokeOuterSourceElementOkJumpdest v)
      (by evm_ov)]⟩

theorem attesterX_multiRevokeInnerArrayDecoderSetupAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx l p sz base len fp ret sel : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨363⟩ : UInt256)
      [idx, l, p, ⟨0⟩, sz, idx, base, len, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨380⟩ : UInt256)
      [⟨2353⟩, p, attesterMultiRevokeInnerArrayHeadWord p idx, ⟨381⟩,
        ⟨0⟩, sz, idx, base, len, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, by
    simpa [attesterMultiRevokeInnerArrayHeadWord, attester_pc363_after_inner_setup_at] using
      (evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨363⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨364⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨365⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨366⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨368⟩, 0x02, .MUL) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨369⟩, 0x81, .DUP2) (by evm_ov),
    raw add (by attester_decode_at v, ⟨370⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨371⟩, 0x90, .SWAP1) (by evm_ov),
    raw push2 ⟨381⟩ (by attester_decode_at v, ⟨372⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨375⟩, 0x91, .SWAP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨376⟩, 0x90, .SWAP1) (by evm_ov),
    raw push2 ⟨2353⟩ (by attester_decode_at v, ⟨377⟩, 0x61, (.Push .PUSH2)) (by evm_ov)])⟩

theorem attesterX_multiRevokeInnerArrayDecoderEntryAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {idx l p sz base len fp ret sel : UInt256} {mem : ByteArray} {aw : UInt256} {k C}
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨363⟩ : UInt256)
      [idx, l, p, ⟨0⟩, sz, idx, base, len, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
      [p, attesterMultiRevokeInnerArrayHeadWord p idx, ⟨381⟩,
        ⟨0⟩, sz, idx, base, len, l, p, len, fp, ret, sel]
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd0⟩ :=
    attesterX_multiRevokeInnerArrayDecoderSetupAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (idx := idx) (l := l) (p := p) (sz := sz) (base := base)
      (len := len) (fp := fp) (ret := ret) (sel := sel)
      (mem := mem) (aw := aw) (k := k) (C := C) hreach
  exact ⟨_, _, evm_run rd0 with [
    raw jump (by attester_decode_at v, ⟨380⟩, 0x56, .JUMP)
      (attesterInnerArrayDecoderJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeInnerArrayOffsetOkAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base head ret sz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hslt :
      UInt256.slt (attesterMultiRevokeInnerArrayOffsetWord I head)
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) base)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
      (base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2374⟩ : UInt256)
      (attesterMultiRevokeInnerArrayOffsetWord I head :: ⟨0⟩ :: ⟨0⟩ ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2353⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2354⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2355⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2356⟩, 0x83, .DUP4) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2357⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨30⟩ (by attester_decode_at v, ⟨2358⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw not (by attester_decode_at v, ⟨2360⟩, 0x19, .NOT) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2361⟩, 0x84, .DUP5) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨2362⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2363⟩, 0x03, .SUB) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2364⟩, 0x01, .ADD) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2365⟩, 0x81, .DUP2) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2366⟩, 0x12, .SLT) (by evm_ov),
    raw push2 ⟨2374⟩ (by attester_decode_at v, ⟨2367⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2370⟩, 0x57, .JUMPI)
      (by
        change UInt256.slt (attesterMultiRevokeInnerArrayOffsetWord I head)
            (UInt256.add
              (UInt256.sub (UInt256.ofNat I.calldata.size) base)
              (UInt256.lnot (⟨30⟩ : UInt256))) ≠ ⟨0⟩
        rw [hslt]
        decide)
      (attesterInnerArrayOffsetOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeInnerArrayOffsetRevertsAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base head ret sz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hslt :
      UInt256.slt (attesterMultiRevokeInnerArrayOffsetWord I head)
        (UInt256.add
          (UInt256.sub (UInt256.ofNat I.calldata.size) base)
          (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2353⟩ : UInt256)
      (base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2353⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2354⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2355⟩, 0x80, .DUP1) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2356⟩, 0x83, .DUP4) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2357⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw push1 ⟨30⟩ (by attester_decode_at v, ⟨2358⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw not (by attester_decode_at v, ⟨2360⟩, 0x19, .NOT) (by evm_ov),
    raw dup5 (by attester_decode_at v, ⟨2361⟩, 0x84, .DUP5) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨2362⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2363⟩, 0x03, .SUB) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2364⟩, 0x01, .ADD) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2365⟩, 0x81, .DUP2) (by evm_ov),
    raw slt (by attester_decode_at v, ⟨2366⟩, 0x12, .SLT) (by evm_ov),
    raw push2 ⟨2374⟩ (by attester_decode_at v, ⟨2367⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2370⟩, 0x57, .JUMPI)
      (by
        change UInt256.slt (attesterMultiRevokeInnerArrayOffsetWord I head)
            (UInt256.add
              (UInt256.sub (UInt256.ofNat I.calldata.size) base)
              (UInt256.lnot (⟨30⟩ : UInt256))) = ⟨0⟩
        rw [hslt])
      (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2371⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2372⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2373⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_multiRevokeInnerArrayLengthMaxOkAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base head ret sz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hgt :
      UInt256.gt (attesterMultiRevokeInnerArrayLengthWord I base head)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2374⟩ : UInt256)
      (attesterMultiRevokeInnerArrayOffsetWord I head :: ⟨0⟩ :: ⟨0⟩ ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2399⟩ : UInt256)
      (attesterMultiRevokeInnerArrayStartWord I base head ::
        attesterMultiRevokeInnerArrayLengthWord I base head :: ⟨0⟩ ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2374⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2375⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2376⟩, 0x01, .ADD) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2377⟩, 0x80, .DUP1) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2378⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2379⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2380⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2381⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2383⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2385⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2387⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2388⟩, 0x03, .SUB) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2389⟩, 0x82, .DUP3) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2390⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2391⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2399⟩ (by attester_decode_at v, ⟨2392⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2395⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt (attesterMultiRevokeInnerArrayLengthWord I base head)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) ≠ ⟨0⟩
        rw [hgt]
        decide)
      (attesterInnerArrayLengthOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeInnerArrayLengthMaxRevertsAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base head ret sz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hgt :
      UInt256.gt (attesterMultiRevokeInnerArrayLengthWord I base head)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩) = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2374⟩ : UInt256)
      (attesterMultiRevokeInnerArrayOffsetWord I head :: ⟨0⟩ :: ⟨0⟩ ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2374⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw dup4 (by attester_decode_at v, ⟨2375⟩, 0x83, .DUP4) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2376⟩, 0x01, .ADD) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2377⟩, 0x80, .DUP1) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨2378⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2379⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2380⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2381⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨2383⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨2385⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2387⟩, 0x1b, .SHL) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2388⟩, 0x03, .SUB) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2389⟩, 0x82, .DUP3) (by evm_ov),
    raw gt (by attester_decode_at v, ⟨2390⟩, 0x11, .GT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2391⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2399⟩ (by attester_decode_at v, ⟨2392⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2395⟩, 0x57, .JUMPI)
      (by
        change UInt256.isZero
            (UInt256.gt (attesterMultiRevokeInnerArrayLengthWord I base head)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨64⟩) ⟨1⟩)) = ⟨0⟩
        rw [hgt]
        decide)
      (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2396⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2397⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2398⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeInnerArrayPayloadSetupAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base head ret sz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2399⟩ : UInt256)
      (attesterMultiRevokeInnerArrayStartWord I base head ::
        attesterMultiRevokeInnerArrayLengthWord I base head :: ⟨0⟩ ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2405⟩ : UInt256)
      (attesterMultiRevokeInnerArrayLengthWord I base head ::
        attesterMultiRevokeInnerArrayPayloadWord I base head ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, by
    simpa [attesterMultiRevokeInnerArrayPayloadWord,
      attester_inner_start_add32_comm] using
      (evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2399⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨2400⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨2402⟩, 0x01, .ADD) (by evm_ov),
    raw swap2 (by attester_decode_at v, ⟨2403⟩, 0x91, .SWAP2) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2404⟩, 0x50, .POP) (by evm_ov)])⟩

theorem attesterX_multiRevokeInnerArrayPayloadGuardOkAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base head ret sz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hsgt :
      UInt256.sgt (attesterMultiRevokeInnerArrayPayloadWord I base head)
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I base head) ⟨5⟩)) = ⟨0⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2405⟩ : UInt256)
      (attesterMultiRevokeInnerArrayLengthWord I base head ::
        attesterMultiRevokeInnerArrayPayloadWord I base head ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2102⟩ : UInt256)
      (attesterMultiRevokeInnerArrayLengthWord I base head ::
        attesterMultiRevokeInnerArrayPayloadWord I base head ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw push1 ⟨5⟩ (by attester_decode_at v, ⟨2405⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2407⟩, 0x81, .DUP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2408⟩, 0x90, .SWAP1) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2409⟩, 0x1b, .SHL) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨2410⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2411⟩, 0x03, .SUB) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2412⟩, 0x82, .DUP3) (by evm_ov),
    raw sgt (by attester_decode_at v, ⟨2413⟩, 0x13, .SGT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2414⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2102⟩ (by attester_decode_at v, ⟨2415⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨2418⟩, 0x57, .JUMPI)
      (by
        rw [hsgt]
        decide)
      (attesterDynamicArrayPayloadOkJumpdest v) (by evm_ov)]⟩

theorem attesterX_multiRevokeInnerArrayPayloadGuardRevertsAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base head ret sz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hsgt :
      UInt256.sgt (attesterMultiRevokeInnerArrayPayloadWord I base head)
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I base head) ⟨5⟩)) = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2405⟩ : UInt256)
      (attesterMultiRevokeInnerArrayLengthWord I base head ::
        attesterMultiRevokeInnerArrayPayloadWord I base head ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    RDrev (patchedRuntime v) g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run hreach with [
    raw push1 ⟨5⟩ (by attester_decode_at v, ⟨2405⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨2407⟩, 0x81, .DUP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2408⟩, 0x90, .SWAP1) (by evm_ov),
    raw shl (by attester_decode_at v, ⟨2409⟩, 0x1b, .SHL) (by evm_ov),
    raw calldatasize (by attester_decode_at v, ⟨2410⟩, 0x36, .CALLDATASIZE) (by evm_ov),
    raw sub (by attester_decode_at v, ⟨2411⟩, 0x03, .SUB) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨2412⟩, 0x82, .DUP3) (by evm_ov),
    raw sgt (by attester_decode_at v, ⟨2413⟩, 0x13, .SGT) (by evm_ov),
    raw iszero (by attester_decode_at v, ⟨2414⟩, 0x15, .ISZERO) (by evm_ov),
    raw push2 ⟨2102⟩ (by attester_decode_at v, ⟨2415⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiNT (by attester_decode_at v, ⟨2418⟩, 0x57, .JUMPI)
      (by
        rw [hsgt]
        decide)
      (by evm_ov),
    raw push0 (by attester_decode_at v, ⟨2419⟩, 0x5f, .PUSH0) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨2420⟩, 0x80, .DUP1) (by evm_ov),
    raw rev 0 (by attester_decode_at v, ⟨2421⟩, 0xfd, .REVERT)
      (fun s _ hstks => memExpRevert0 s hstks) (by evm_ov)]

theorem attesterX_multiRevokeInnerArrayReturnAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base head ret sz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hretJump : (D_J (patchedRuntime v) 0).contains ret = true)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2102⟩ : UInt256)
      (attesterMultiRevokeInnerArrayLengthWord I base head ::
        attesterMultiRevokeInnerArrayPayloadWord I base head ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ret
      (attesterMultiRevokeInnerArrayLengthWord I base head ::
        attesterMultiRevokeInnerArrayPayloadWord I base head ::
        ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨2102⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2103⟩, 0x92, .SWAP3) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2104⟩, 0x50, .POP) (by evm_ov),
    raw swap3 (by attester_decode_at v, ⟨2105⟩, 0x92, .SWAP3) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨2106⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨2107⟩, 0x50, .POP) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨2108⟩, 0x56, .JUMP)
      hretJump (by evm_ov)]⟩

set_option maxHeartbeats 1000000 in
theorem attesterX_multiRevokeInnerArrayPayloadOkToReturnAt
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {base head ret sz : UInt256} {tail : List UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (htail : tail.length ≤ 1000)
    (hsgt :
      UInt256.sgt (attesterMultiRevokeInnerArrayPayloadWord I base head)
        (UInt256.sub (UInt256.ofNat I.calldata.size)
          (UInt256.shiftLeft
            (attesterMultiRevokeInnerArrayLengthWord I base head) ⟨5⟩)) = ⟨0⟩)
    (hretJump : (D_J (patchedRuntime v) 0).contains ret = true)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨2399⟩ : UInt256)
      (attesterMultiRevokeInnerArrayStartWord I base head ::
        attesterMultiRevokeInnerArrayLengthWord I base head :: ⟨0⟩ ::
        base :: head :: ret :: ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) ret
      (attesterMultiRevokeInnerArrayLengthWord I base head ::
        attesterMultiRevokeInnerArrayPayloadWord I base head ::
        ⟨0⟩ :: sz :: tail)
      mem aw ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k0, C0, rd2405⟩ :=
    attesterX_multiRevokeInnerArrayPayloadSetupAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := base) (head := head) (ret := ret) (sz := sz)
      (tail := tail) (mem := mem) (aw := aw) (k := k) (C := C)
      htail hreach
  obtain ⟨k1, C1, rd2102⟩ :=
    attesterX_multiRevokeInnerArrayPayloadGuardOkAt
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) v
      (base := base) (head := head) (ret := ret) (sz := sz)
      (tail := tail) (mem := mem) (aw := aw) (k := k0) (C := C0)
      htail hsgt rd2405
  exact attesterX_multiRevokeInnerArrayReturnAt
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) v
    (base := base) (head := head) (ret := ret) (sz := sz)
    (tail := tail) (mem := mem) (aw := aw) (k := k1) (C := C1)
    htail hretJump rd2102

set_option maxHeartbeats 1500000 in
theorem attesterX_multiRevokePostInnerCopyToOuterLoop
    {cA gh bl σ σ₀ A I} {g : Sat256} (v : AttesterImmutables)
    {innerIdx base innerLen payload idx outerBase schemaLen secondLen secondPayload
      schemaPayload ret selector : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C}
    (hidxSchema : UInt256.lt idx schemaLen = ⟨1⟩)
    (hidxOuter :
      UInt256.lt idx
        (attesterMloadWord
          (attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw)
          (attesterMultiRevokePostCopyDataAw base I schemaPayload idx mem aw)
          outerBase) = ⟨1⟩)
    (hreach : RD (patchedRuntime v) I g
      (initState cA gh bl σ σ₀ g A I) (⟨608⟩ : UInt256)
      [innerIdx, base, innerLen, innerLen, payload, idx, outerBase, schemaLen,
        secondLen, secondPayload, schemaLen, schemaPayload, ret, selector]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k' C',
      RD (patchedRuntime v) I g
        (initState cA gh bl σ σ₀ g A I) (⟨335⟩ : UInt256)
        [attesterMultiRevokePostCopyNextIdx idx, outerBase, schemaLen,
          secondLen, secondPayload, schemaLen, schemaPayload, ret, selector]
        (attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw)
        (attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw)
        ByteArray.empty (cA, σ) k' C' := by
  let free := attesterMultiRevokePostCopyFreeWord mem aw
  let aw1 := attesterMultiRevokePostCopyAwAfterMload aw
  let bump := attesterMultiRevokePostCopyFreeBumpWord mem aw
  let mem1 := attesterMultiRevokePostCopyFreeMem mem aw
  let aw2 := attesterMultiRevokePostCopyFreeAw mem aw
  let schemaOff := attesterMultiRevokePostCopySchemaCalldataOffset schemaPayload idx
  let schema := attesterMultiRevokePostCopySchemaWord I schemaPayload idx
  let mem2 := attesterMultiRevokePostCopySchemaMem I schemaPayload idx mem aw
  let aw3 := attesterMultiRevokePostCopySchemaAw I schemaPayload idx mem aw
  let dataOff := attesterMultiRevokePostCopyDataOffsetWord mem aw
  let mem3 := attesterMultiRevokePostCopyDataMem base I schemaPayload idx mem aw
  let aw4 := attesterMultiRevokePostCopyDataAw base I schemaPayload idx mem aw
  let outerLen := attesterMloadWord mem3 aw4 outerBase
  let aw5 := attesterMultiRevokePostCopyOuterArrayAwAfterMload
    outerBase I schemaPayload idx mem aw
  let slot := attesterMultiRevokePostCopyOuterSlotWord outerBase idx
  let mem4 := attesterMultiRevokePostCopyOuterMem base outerBase I schemaPayload idx mem aw
  let aw6 := attesterMultiRevokePostCopyOuterAw base outerBase I schemaPayload idx mem aw
  have hcostMload64 :
      ∀ s : State,
        s.machineState.activeWords = aw →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: base :: innerLen :: innerLen :: payload ::
            idx :: outerBase :: schemaLen :: secondLen :: secondPayload ::
            schemaLen :: schemaPayload :: ret :: selector :: [] →
        memoryExpansionCost s .MLOAD = Cₘ aw1 - Cₘ aw := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreFree :
      ∀ s : State,
        s.machineState.activeWords = aw1 →
        s.machineState.stack =
          (⟨64⟩ : UInt256) :: bump :: free :: base :: innerLen :: innerLen ::
            payload :: idx :: outerBase :: schemaLen :: secondLen :: secondPayload ::
            schemaLen :: schemaPayload :: ret :: selector :: [] →
        memoryExpansionCost s .MSTORE = Cₘ aw2 - Cₘ aw1 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreSchema :
      ∀ s : State,
        s.machineState.activeWords = aw2 →
        s.machineState.stack =
          free :: schema :: free :: free :: base :: innerLen :: innerLen ::
            payload :: idx :: outerBase :: schemaLen :: secondLen :: secondPayload ::
            schemaLen :: schemaPayload :: ret :: selector :: [] →
        memoryExpansionCost s .MSTORE = Cₘ aw3 - Cₘ aw2 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreData :
      ∀ s : State,
        s.machineState.activeWords = aw3 →
        s.machineState.stack =
          dataOff :: base :: dataOff :: free :: base :: innerLen :: innerLen ::
            payload :: idx :: outerBase :: schemaLen :: secondLen :: secondPayload ::
            schemaLen :: schemaPayload :: ret :: selector :: [] →
        memoryExpansionCost s .MSTORE = Cₘ aw4 - Cₘ aw3 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostMloadOuter :
      ∀ s : State,
        s.machineState.activeWords = aw4 →
        s.machineState.stack =
          outerBase :: idx :: outerBase :: free :: base :: innerLen :: innerLen ::
            payload :: idx :: outerBase :: schemaLen :: secondLen :: secondPayload ::
            schemaLen :: schemaPayload :: ret :: selector :: [] →
        memoryExpansionCost s .MLOAD = Cₘ aw5 - Cₘ aw4 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  have hcostStoreOuter :
      ∀ s : State,
        s.machineState.activeWords = aw5 →
        s.machineState.stack =
          slot :: free :: free :: base :: innerLen :: innerLen :: payload ::
            idx :: outerBase :: schemaLen :: secondLen :: secondPayload ::
            schemaLen :: schemaPayload :: ret :: selector :: [] →
        memoryExpansionCost s .MSTORE = Cₘ aw6 - Cₘ aw5 := by
    intro s haws hstks
    simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
      List.getElem!_cons_zero]
    rfl
  exact ⟨_, _, by
    simpa [free, aw1, bump, mem1, aw2, schemaOff, schema, mem2, aw3,
      dataOff, mem3, aw4, outerLen, aw5, slot, mem4, aw6,
      attesterMultiRevokePostCopyNextIdx] using
      evm_run hreach with [
    raw jumpdest (by attester_decode_at v, ⟨608⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨609⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨610⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mload (Cₘ aw1 - Cₘ aw) free aw1
      (by attester_decode_at v, ⟨612⟩, 0x51, .MLOAD)
      hcostMload64 (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨613⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨614⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨616⟩, 0x01, .ADD) (by evm_ov),
    raw push1 ⟨64⟩ (by attester_decode_at v, ⟨617⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mstore (Cₘ aw2 - Cₘ aw1) mem1 aw2
      (by attester_decode_at v, ⟨619⟩, 0x52, .MSTORE)
      hcostStoreFree (by rfl) (by rfl) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨620⟩, 0x80, .DUP1) (by evm_ov),
    raw dup13 (by attester_decode_at v, ⟨621⟩, 0x8c, .DUP13) (by evm_ov),
    raw dup13 (by attester_decode_at v, ⟨622⟩, 0x8c, .DUP13) (by evm_ov),
    raw dup9 (by attester_decode_at v, ⟨623⟩, 0x88, .DUP9) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨624⟩, 0x81, .DUP2) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨625⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨626⟩, 0x10, .LT) (by evm_ov),
    raw push2 ⟨638⟩ (by attester_decode_at v, ⟨627⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨630⟩, 0x57, .JUMPI)
      (by rw [hidxSchema]; decide)
      (attesterMultiRevokePostCopySchemaOkJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨638⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨639⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨640⟩, 0x50, .POP) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨641⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨643⟩, 0x02, .MUL) (by evm_ov),
    raw add (by attester_decode_at v, ⟨644⟩, 0x01, .ADD) (by evm_ov),
    raw calldataload (by attester_decode_at v, ⟨645⟩, 0x35, .CALLDATALOAD) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨646⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw3 - Cₘ aw2) mem2 aw3
      (by attester_decode_at v, ⟨647⟩, 0x52, .MSTORE)
      hcostStoreSchema (by rfl) (by rfl) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨648⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨650⟩, 0x01, .ADD) (by evm_ov),
    raw dup3 (by attester_decode_at v, ⟨651⟩, 0x82, .DUP3) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨652⟩, 0x81, .DUP2) (by evm_ov),
    raw mstore (Cₘ aw4 - Cₘ aw3) mem3 aw4
      (by attester_decode_at v, ⟨653⟩, 0x52, .MSTORE)
      hcostStoreData (by rfl) (by rfl) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨654⟩, 0x50, .POP) (by evm_ov),
    raw dup7 (by attester_decode_at v, ⟨655⟩, 0x86, .DUP7) (by evm_ov),
    raw dup7 (by attester_decode_at v, ⟨656⟩, 0x86, .DUP7) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨657⟩, 0x81, .DUP2) (by evm_ov),
    raw mload (Cₘ aw5 - Cₘ aw4) outerLen aw5
      (by attester_decode_at v, ⟨658⟩, 0x51, .MLOAD)
      hcostMloadOuter (by rfl) (by rfl) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨659⟩, 0x81, .DUP2) (by evm_ov),
    raw lt (by attester_decode_at v, ⟨660⟩, 0x10, .LT) (by evm_ov),
    raw push2 ⟨672⟩ (by attester_decode_at v, ⟨661⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jumpiT (by attester_decode_at v, ⟨664⟩, 0x57, .JUMPI)
      (by rw [hidxOuter]; decide)
      (attesterMultiRevokePostCopyOuterStoreOkJumpdest v) (by evm_ov),
    raw jumpdest (by attester_decode_at v, ⟨672⟩, 0x5b, .JUMPDEST) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨673⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw mul (by attester_decode_at v, ⟨675⟩, 0x02, .MUL) (by evm_ov),
    raw push1 ⟨32⟩ (by attester_decode_at v, ⟨676⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨678⟩, 0x01, .ADD) (by evm_ov),
    raw add (by attester_decode_at v, ⟨679⟩, 0x01, .ADD) (by evm_ov),
    raw dup2 (by attester_decode_at v, ⟨680⟩, 0x81, .DUP2) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨681⟩, 0x90, .SWAP1) (by evm_ov),
    raw mstore (Cₘ aw6 - Cₘ aw5) mem4 aw6
      (by attester_decode_at v, ⟨682⟩, 0x52, .MSTORE)
      hcostStoreOuter (by rfl) (by rfl) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨683⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨684⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨685⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨686⟩, 0x50, .POP) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨687⟩, 0x50, .POP) (by evm_ov),
    raw dup1 (by attester_decode_at v, ⟨688⟩, 0x80, .DUP1) (by evm_ov),
    raw push1 ⟨1⟩ (by attester_decode_at v, ⟨689⟩, 0x60, (.Push .PUSH1)) (by evm_ov),
    raw add (by attester_decode_at v, ⟨691⟩, 0x01, .ADD) (by evm_ov),
    raw swap1 (by attester_decode_at v, ⟨692⟩, 0x90, .SWAP1) (by evm_ov),
    raw pop (by attester_decode_at v, ⟨693⟩, 0x50, .POP) (by evm_ov),
    raw push2 ⟨335⟩ (by attester_decode_at v, ⟨694⟩, 0x61, (.Push .PUSH2)) (by evm_ov),
    raw jump (by attester_decode_at v, ⟨697⟩, 0x56, .JUMP)
      (attesterMultiRevokeOuterSourceLoopJumpdest v) (by evm_ov)]⟩

end Benchmarks.EAS.Attester
