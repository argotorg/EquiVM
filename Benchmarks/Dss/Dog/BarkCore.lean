import Reasoning.SolcRoutines
import Reasoning.Storage
import Reasoning.ABIViews
import Reasoning.WordArithmetic
import Reasoning.EVMWord
import Reasoning.ABIComposite
import Reasoning.Stepping
import Reasoning.Reach
import Benchmarks.Dss.Dog.Dispatch
import Reasoning.MemCascade
import Reasoning.ExternalCall

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem barkVatUrnsPostCallWrite_size_gt64 (out base : ByteArray) (L : Nat)
    (hbase : base.size = 196) (hLo : L ≤ out.size) :
    64 < (out.write 0 base 128 L).size := by
  rcases Nat.eq_zero_or_pos L with hzero | hpos
  · subst L
    rw [byteArray_write_len_zero, hbase]
    norm_num
  · by_cases hin : 128 + L ≤ base.size
    · rw [write_eq_gen out base 128 L (by omega) hLo hin, ByteArray.size_append,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        ByteArray.size_extract, hbase]
      omega
    · have hdest : 128 ≤ base.size := by
        rw [hbase]
        omega
      have hext : base.size < 128 + L := Nat.lt_of_not_ge hin
      rw [write_eq_gen_extend out base 128 L (by omega) hLo hdest hext,
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, hbase]
      omega

theorem wordAt0Mem_size_256 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 256) :
    (wordAt0Mem word mem).size = 256 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem wordAt32Mem_size_256 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 256) :
    (wordAt32Mem word mem).size = 256 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem wordAt0Mem_size_580 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 580) :
    (wordAt0Mem word mem).size = 580 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem wordAt32Mem_size_580 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 580) :
    (wordAt32Mem word mem).size = 580 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

abbrev barkPostIlksErrorStringMem0 (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem 384 solcErrorStringSelector

theorem barkPartialDue_fit_of_dart_le_art {art dart rate : UInt256}
    (hdartLe : dart.toNat ≤ art.toNat)
    (hfitArt : art.toNat * rate.toNat < UInt256.size) :
    dart.toNat * rate.toNat < UInt256.size := by
  exact lt_of_le_of_lt (Nat.mul_le_mul_right rate.toNat hdartLe) hfitArt

theorem twoWordHashMem_size_256 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 256) :
    (twoWordHashMem key slot mem).size = 256 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size_256 slot (wordAt0Mem_size_256 key hmem)

theorem twoWordHashMem_read0_256 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 256) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_256 key hmem]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read32_256 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 256) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_256 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read64_256 {mem : ByteArray} (key slot ptr : UInt256)
    (hmem : mem.size = 256)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ptr) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ptr := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_256 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_256 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem twoWordHashMem_size_580 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 580) :
    (twoWordHashMem key slot mem).size = 580 := by
  unfold twoWordHashMem
  exact wordAt32Mem_size_580 slot (wordAt0Mem_size_580 key hmem)

theorem twoWordHashMem_read0_580 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 580) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_580 key hmem]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read32_580 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 580) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_580 key hmem]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read64_580 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_580 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_580 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread64

theorem twoWordHashMem_read256_580 {mem : ByteArray} (key slot word : UInt256)
    (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray word) :
    (twoWordHashMem key slot mem).readWithPadding 256 32 =
      UInt256.toByteArray word := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 256 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_580 key hmem]; omega) (by omega)
      (by rw [wordAt0Mem_size_580 key hmem]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 256 (by rw [toByteArray_size]) (by rw [hmem]; omega)
      (by omega) (by rw [hmem]; omega)]
  exact hread256

abbrev barkPostIlksErrorStringMem1 (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkPostIlksErrorStringMem0 mem) 388 ⟨32⟩

theorem barkPostIlksErrorStringMem0_size {mem : ByteArray} (hmem : mem.size = 544) :
    (barkPostIlksErrorStringMem0 mem).size = 544 := by
  unfold barkPostIlksErrorStringMem0
  rw [Reasoning.Theory.writeWord_size mem 384 solcErrorStringSelector
    (by rw [hmem]; exact USize.size_pos)]
  rw [hmem]
  norm_num

theorem twoWordHashMem_read0_64_256 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 256) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_256 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_256 key slot hmem]; omega),
      twoWordHashMem_read0_256 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_256 key slot hmem]; omega),
      twoWordHashMem_read32_256 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      simp]
  rw [hleft, hright]

theorem twoWordHashMem_read0_64_580 {mem : ByteArray} (key slot : UInt256)
    (hmem : mem.size = 580) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_580 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_580 key slot hmem]; omega),
      twoWordHashMem_read0_580 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_580 key slot hmem]; omega),
      twoWordHashMem_read32_580 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      simp]
  rw [hleft, hright]

theorem twoWordHashMem_mload256_580 {mem : ByteArray} (key slot word : UInt256)
    (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray word) :
    (if (⟨256⟩ : UInt256).toNat ≥ (twoWordHashMem key slot mem).size then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((twoWordHashMem key slot mem).readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
      word := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨256⟩ : UInt256)) (v := word)
    (by rw [twoWordHashMem_size_580 key slot hmem]; decide)
    (by
      simpa [show (⟨256⟩ : UInt256).toNat = 256 by decide] using
        twoWordHashMem_read256_580 key slot word hmem hread256)

abbrev barkPostIlksErrorStringMem2 (len : UInt256) (mem : ByteArray) :
    ByteArray :=
  Reasoning.Theory.writeWord (barkPostIlksErrorStringMem1 mem) 420 len

theorem barkPostIlksErrorStringMem1_size {mem : ByteArray} (hmem : mem.size = 544) :
    (barkPostIlksErrorStringMem1 mem).size = 544 := by
  unfold barkPostIlksErrorStringMem1
  rw [Reasoning.Theory.writeWord_size (barkPostIlksErrorStringMem0 mem) 388 ⟨32⟩
    (by rw [barkPostIlksErrorStringMem0_size hmem]; exact USize.size_pos)]
  rw [barkPostIlksErrorStringMem0_size hmem]
  norm_num

theorem twoWordHashMem_solcMappingSlot_256 (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : mem.size = 256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_256 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem twoWordHashMem_solcMappingSlot_580 (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : mem.size = 580) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_580 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

abbrev barkPostIlksErrorStringMem3
    (len word : UInt256) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkPostIlksErrorStringMem2 len mem) 452 word

theorem barkPostIlksErrorStringMem2_size (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544) :
    (barkPostIlksErrorStringMem2 len mem).size = 544 := by
  unfold barkPostIlksErrorStringMem2
  rw [Reasoning.Theory.writeWord_size (barkPostIlksErrorStringMem1 mem) 420 len
    (by rw [barkPostIlksErrorStringMem1_size hmem]; exact USize.size_pos)]
  rw [barkPostIlksErrorStringMem1_size hmem]
  norm_num

theorem barkPostIlksErrorStringMem2_read64 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (barkPostIlksErrorStringMem2 len mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  unfold barkPostIlksErrorStringMem2
  rw [Reasoning.Theory.writeWord_read_preserved
    (barkPostIlksErrorStringMem1 mem) 420 64 len
    (by rw [barkPostIlksErrorStringMem1_size hmem]; exact USize.size_pos)
    (by left; rw [barkPostIlksErrorStringMem1_size hmem]; omega)]
  unfold barkPostIlksErrorStringMem1
  rw [Reasoning.Theory.writeWord_read_preserved
    (barkPostIlksErrorStringMem0 mem) 388 64 (⟨32⟩ : UInt256)
    (by rw [barkPostIlksErrorStringMem0_size hmem]; exact USize.size_pos)
    (by left; rw [barkPostIlksErrorStringMem0_size hmem]; omega)]
  unfold barkPostIlksErrorStringMem0
  rw [Reasoning.Theory.writeWord_read_preserved mem 384 64 solcErrorStringSelector
    (by rw [hmem]; exact USize.size_pos) (by left; rw [hmem]; omega)]
  exact hread64

theorem barkPostIlksErrorStringMem3_size (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544) :
    (barkPostIlksErrorStringMem3 len word mem).size = 544 := by
  unfold barkPostIlksErrorStringMem3
  rw [Reasoning.Theory.writeWord_size (barkPostIlksErrorStringMem2 len mem) 452 word
    (by rw [barkPostIlksErrorStringMem2_size len hmem]; exact USize.size_pos)]
  rw [barkPostIlksErrorStringMem2_size len hmem]
  norm_num

theorem barkPostIlksErrorStringMem3_read64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (barkPostIlksErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  unfold barkPostIlksErrorStringMem3
  rw [Reasoning.Theory.writeWord_read_preserved
    (barkPostIlksErrorStringMem2 len mem) 452 64 word
    (by rw [barkPostIlksErrorStringMem2_size len hmem]; exact USize.size_pos)
    (by left; rw [barkPostIlksErrorStringMem2_size len hmem]; omega)]
  unfold barkPostIlksErrorStringMem2
  rw [Reasoning.Theory.writeWord_read_preserved
    (barkPostIlksErrorStringMem1 mem) 420 64 len
    (by rw [barkPostIlksErrorStringMem1_size hmem]; exact USize.size_pos)
    (by left; rw [barkPostIlksErrorStringMem1_size hmem]; omega)]
  unfold barkPostIlksErrorStringMem1
  rw [Reasoning.Theory.writeWord_read_preserved
    (barkPostIlksErrorStringMem0 mem) 388 64 (⟨32⟩ : UInt256)
    (by rw [barkPostIlksErrorStringMem0_size hmem]; exact USize.size_pos)
    (by left; rw [barkPostIlksErrorStringMem0_size hmem]; omega)]
  unfold barkPostIlksErrorStringMem0
  rw [Reasoning.Theory.writeWord_read_preserved mem 384 64 solcErrorStringSelector
    (by rw [hmem]; exact USize.size_pos) (by left; rw [hmem]; omega)]
  exact hread64

theorem barkPostIlksErrorStringMem3_mload64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkPostIlksErrorStringMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkPostIlksErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkPostIlksErrorStringMem3_size len word hmem]; decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using
        barkPostIlksErrorStringMem3_read64 len word hmem hread64)

end Benchmarks.Dss.Dog

namespace Benchmarks.Dss.Dog.RD

theorem dogBarkPostIlksErrorStringRevertTail {code : ByteArray} {g : Sat256}
    {s0 : EVM.State} {I : ExecutionEnv} {k C : ℕ}
    {pc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code I g s0 pc stk mem (UInt256.ofNat 17) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256))
      (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 by decide] using hread64)
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17) hd3 mem_cost hmload64
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem0 mem) (UInt256.ofNat 17)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem1 mem) (UInt256.ofNat 17)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem2 len mem)
      (UInt256.ofNat 17) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst rawWord (width := width) (op := op)
    hpush hd27 (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 shift hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  rw [hword] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 0 (barkPostIlksErrorStringMem3 len word mem)
      (UInt256.ofNat 17) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17) hdMload
      mem_cost (barkPostIlksErrorStringMem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

end Benchmarks.Dss.Dog.RD

end

namespace Reasoning.Theory


end Reasoning.Theory

namespace Reasoning.Reach


end Reasoning.Reach

namespace Benchmarks.Dss.Dog

/-! ## `bark(bytes32,address,address)` -/

abbrev dogBarkLogTopic : UInt256 :=
  ⟨60223955615635091052364944308915575907717781736950231047312829807587324278156⟩

abbrev barkIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev barkIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev barkIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (barkIlkBytes I)

abbrev barkIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (barkIlkBytes I)

abbrev barkUrnWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev barkKprWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev barkUrn (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (barkUrnWord I).toNat

abbrev barkKpr (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (barkKprWord I).toNat

abbrev barkUrnKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (barkUrnWord I)

abbrev barkKprKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (barkKprWord I)

abbrev barkVatWord (v : DogImmutables) : UInt256 :=
  EVM.Word.ofNat v.vat.toNat

abbrev barkVatUrnsSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨606387804⟩ ⟨224⟩

abbrev barkVatUrnsSelectorMem (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem 128 barkVatUrnsSelectorWord

abbrev barkVatUrnsIlkMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsSelectorMem mem) 132 (barkIlkWord I)

abbrev barkVatUrnsCallMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsIlkMem I mem) 164 (barkUrnKey I)

abbrev barkVatUrnsPostCallMem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  out.write 0 (barkVatUrnsCallMem I mem) 128
    (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat

abbrev barkVatUrnsTupleFreeMem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsPostCallMem I mem out) 64 ⟨256⟩

abbrev barkVatUrnsTupleWord0Mem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsTupleFreeMem I mem out) 128 ⟨0⟩

abbrev barkVatUrnsTupleWord1Mem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsTupleWord0Mem I mem out) 160 ⟨0⟩

abbrev barkVatUrnsTupleWord2Mem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsTupleWord1Mem I mem out) 192 ⟨0⟩

abbrev barkVatUrnsTupleMem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsTupleWord2Mem I mem out) 224 ⟨0⟩

abbrev barkVatUrnsInkWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev barkVatUrnsArtWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev barkLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (barkIlkBytes I))).insert
    "urn" (.address (barkUrn I))).insert "kpr" (.address (barkKpr I))

abbrev barkVatUrnValue (out : ByteArray) : Value :=
  .tuple [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
    .int (Int.ofNat (barkVatUrnsArtWord out).toNat)]

abbrev barkLocalsVatUrn (I : ExecutionEnv) (out : ByteArray) : Store :=
  (barkLocals I).insert "vatUrn" (barkVatUrnValue out)

abbrev barkLocalsInk (I : ExecutionEnv) (out : ByteArray) : Store :=
  (barkLocalsVatUrn I out).insert "ink" (.int (Int.ofNat (barkVatUrnsInkWord out).toNat))

abbrev barkLocalsArt (I : ExecutionEnv) (out : ByteArray) : Store :=
  (barkLocalsInk I out).insert "art" (.int (Int.ofNat (barkVatUrnsArtWord out).toNat))

abbrev barkIlksClipEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (barkIlkKey I), .field "clip"] }

abbrev barkIlksChopEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (barkIlkKey I), .field "chop"] }

abbrev barkIlksHoleEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (barkIlkKey I), .field "hole"] }

abbrev barkIlksDirtEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (barkIlkKey I), .field "dirt"] }

abbrev barkIlksClipSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (barkIlkKey I)

abbrev barkIlksChopSlotFor (I : ExecutionEnv) : UInt256 :=
  barkIlksClipSlotFor I + ⟨1⟩

abbrev barkIlksHoleSlotFor (I : ExecutionEnv) : UInt256 :=
  barkIlksClipSlotFor I + ⟨2⟩

abbrev barkIlksDirtSlotFor (I : ExecutionEnv) : UInt256 :=
  barkIlksClipSlotFor I + ⟨3⟩

abbrev barkLocalsMilkClip (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    Store :=
  (barkLocalsArt I out).insert "milkClip"
    (.address (AccountAddress.ofNat
      (solcAddressSlotWord (barkIlksClipSlotFor I) evm.accountMap evm.executionEnv).toNat))

abbrev barkLocalsMilkChop (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    Store :=
  (barkLocalsMilkClip evm I out).insert "milkChop"
    (.int (Int.ofNat (solcSlotWordAt (barkIlksChopSlotFor I) evm.accountMap
      evm.executionEnv).toNat))

abbrev barkLocalsMilkHole (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    Store :=
  (barkLocalsMilkChop evm I out).insert "milkHole"
    (.int (Int.ofNat (solcSlotWordAt (barkIlksHoleSlotFor I) evm.accountMap
      evm.executionEnv).toNat))

abbrev barkLocalsMilkDirt (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    Store :=
  (barkLocalsMilkHole evm I out).insert "milkDirt"
    (.int (Int.ofNat (solcSlotWordAt (barkIlksDirtSlotFor I) evm.accountMap
      evm.executionEnv).toNat))

abbrev barkIlksSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨1⟩ (barkIlkWord I)

abbrev barkIlksClipWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (solcSlotWord σ I (barkIlksSlot I))

abbrev barkIlksChopWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (barkIlksSlot I + ⟨1⟩)

abbrev barkIlksHoleWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (barkIlksSlot I + ⟨2⟩)

abbrev barkIlksDirtWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (⟨3⟩ + barkIlksSlot I)

abbrev barkIlksHashMem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  twoWordHashMem (barkIlkWord I) ⟨1⟩ (barkVatUrnsTupleMem I mem out)

abbrev barkIlksAllocMem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksHashMem I mem out) 64 ⟨384⟩

abbrev barkIlksClipMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksAllocMem I mem out) 256 (barkIlksClipWord σ I)

abbrev barkIlksChopMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksClipMem σ I mem out) 288 (barkIlksChopWord σ I)

abbrev barkIlksHoleMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksChopMem σ I mem out) 320 (barkIlksHoleWord σ I)

abbrev barkIlksMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksHoleMem σ I mem out) 352 (barkIlksDirtWord σ I)

abbrev barkVatIlksSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨1823590043⟩ ⟨225⟩

abbrev barkVatIlksSelectorMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksMem σ I mem out) 384 barkVatIlksSelectorWord

abbrev barkVatIlksCallMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatIlksSelectorMem σ I mem out) 388 (barkIlkWord I)

abbrev barkVatIlksPostCallMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out outIlks : ByteArray) : ByteArray :=
  outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384
    (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat

abbrev barkVatIlksArtWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev barkVatIlksRateWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev barkVatIlksSpotWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 64 96))

abbrev barkVatIlksLineWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 96 128))

abbrev barkVatIlksDustWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 128 160))

abbrev barkVatIlksReturnValues (out : ByteArray) : List Value :=
  [ .int (Int.ofNat (barkVatIlksArtWord out).toNat),
    .int (Int.ofNat (barkVatIlksRateWord out).toNat),
    .int (Int.ofNat (barkVatIlksSpotWord out).toNat),
    .int (Int.ofNat (barkVatIlksLineWord out).toNat),
    .int (Int.ofNat (barkVatIlksDustWord out).toNat) ]

abbrev barkVatIlkValue (out : ByteArray) : Value :=
  .tuple (barkVatIlksReturnValues out)

abbrev barkLocalsVatIlk
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) : Store :=
  (barkLocalsMilkDirt evm I out).insert "vatIlk" (barkVatIlkValue outIlks)

abbrev barkLocalsRate
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) : Store :=
  (barkLocalsVatIlk evm I out outIlks).insert "rate"
    (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat))

abbrev barkLocalsSpot
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) : Store :=
  (barkLocalsRate evm I out outIlks).insert "spot"
    (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat))

abbrev barkLocalsDust
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) : Store :=
  (barkLocalsSpot evm I out outIlks).insert "dust"
    (.int (Int.ofNat (barkVatIlksDustWord outIlks).toNat))

abbrev barkInkSpotWord (out outIlks : ByteArray) : UInt256 :=
  barkVatUrnsInkWord out * barkVatIlksSpotWord outIlks

abbrev barkArtRateUnsafeWord (out outIlks : ByteArray) : UInt256 :=
  barkVatUrnsArtWord out * barkVatIlksRateWord outIlks

abbrev barkLocalsInkSpot
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) : Store :=
  (barkLocalsDust evm I out outIlks).insert "inkSpot"
    (.int (Int.ofNat (barkInkSpotWord out outIlks).toNat))

abbrev barkLocalsArtRateUnsafe
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) : Store :=
  (barkLocalsInkSpot evm I out outIlks).insert "artRateUnsafe"
    (.int (Int.ofNat (barkArtRateUnsafeWord out outIlks).toNat))

abbrev barkGlobalRoomWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (solcSlotWordAt ⟨4⟩ σ I) (solcSlotWordAt ⟨5⟩ σ I)

abbrev barkIlkRoomWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (barkIlksHoleWord σ I) (barkIlksDirtWord σ I)

abbrev barkRoomWord (σ σMem : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if (barkGlobalRoomWord σ I).toNat ≤ (barkIlkRoomWord σMem I).toNat then
    barkGlobalRoomWord σ I
  else
    barkIlkRoomWord σMem I

abbrev barkSourceGlobalRoomWord (evmIlks : EVM.State) : UInt256 :=
  UInt256.sub (solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv)
    (solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv)

abbrev barkSourceIlkRoomWord (evmUrns : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub
    (solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap evmUrns.executionEnv)
    (solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap evmUrns.executionEnv)

abbrev barkSourceRoomWord (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) : UInt256 :=
  if (barkSourceGlobalRoomWord evmIlks).toNat ≤ (barkSourceIlkRoomWord evmUrns I).toNat then
    barkSourceGlobalRoomWord evmIlks
  else
    barkSourceIlkRoomWord evmUrns I

abbrev dogWadWord : UInt256 :=
  ⟨1000000000000000000⟩

abbrev barkSourceRoomWadWord (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) :
    UInt256 :=
  barkSourceRoomWord evmUrns evmIlks I * dogWadWord

abbrev barkSourceDartByRateWord
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (outIlks : ByteArray) :
    UInt256 :=
  UInt256.div (barkSourceRoomWadWord evmUrns evmIlks I) (barkVatIlksRateWord outIlks)

abbrev barkSourceMilkChopWord (evmUrns : EVM.State) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt (barkIlksChopSlotFor I) evmUrns.accountMap evmUrns.executionEnv

abbrev barkSourceDartCandidateWord
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (outIlks : ByteArray) :
    UInt256 :=
  UInt256.div (barkSourceDartByRateWord evmUrns evmIlks I outIlks)
    (barkSourceMilkChopWord evmUrns I)

abbrev barkSourceDartWord
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    UInt256 :=
  let dartCandidate := barkSourceDartCandidateWord evmUrns evmIlks I outIlks
  if (barkVatUrnsArtWord out).toNat ≤ dartCandidate.toNat then
    barkVatUrnsArtWord out
  else
    dartCandidate

abbrev barkLocalsGlobalRoom
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsArtRateUnsafe evmUrns I out outIlks).insert "globalRoom"
    (.int (Int.ofNat (barkSourceGlobalRoomWord evmIlks).toNat))

abbrev barkLocalsIlkRoom
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsGlobalRoom evmUrns evmIlks I out outIlks).insert "ilkRoom"
    (.int (Int.ofNat (barkSourceIlkRoomWord evmUrns I).toNat))

abbrev barkLocalsRoom
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsIlkRoom evmUrns evmIlks I out outIlks).insert "room"
    (.int (Int.ofNat (barkSourceRoomWord evmUrns evmIlks I).toNat))

abbrev barkLocalsRoomWad
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsRoom evmUrns evmIlks I out outIlks).insert "roomWad"
    (.int (Int.ofNat (barkSourceRoomWadWord evmUrns evmIlks I).toNat))

abbrev barkLocalsDartByRate
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsRoomWad evmUrns evmIlks I out outIlks).insert "dartByRate"
    (.int (Int.ofNat (barkSourceDartByRateWord evmUrns evmIlks I outIlks).toNat))

abbrev barkLocalsDartCandidate
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsDartByRate evmUrns evmIlks I out outIlks).insert "dartCandidate"
    (.int (Int.ofNat (barkSourceDartCandidateWord evmUrns evmIlks I outIlks).toNat))

abbrev barkLocalsDart
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsDartCandidate evmUrns evmIlks I out outIlks).insert "dart"
    (.int (Int.ofNat (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat))

abbrev barkLocalsLeftoverArt
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsDart evmUrns evmIlks I out outIlks).insert "leftoverArt"
    (.int (Int.ofNat
      (UInt256.sub (barkVatUrnsArtWord out)
        (barkSourceDartWord evmUrns evmIlks I out outIlks)).toNat))

abbrev barkLocalsLeftoverDue
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsLeftoverArt evmUrns evmIlks I out outIlks).insert "leftoverDue"
    (.int (Int.ofNat
      ((UInt256.sub (barkVatUrnsArtWord out)
        (barkSourceDartWord evmUrns evmIlks I out outIlks)) *
        barkVatIlksRateWord outIlks).toNat))

abbrev barkLocalsDustyDart
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsLeftoverDue evmUrns evmIlks I out outIlks).insert "dart"
    (.int (Int.ofNat (barkVatUrnsArtWord out).toNat))

abbrev barkLocalsPartialDue
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    Store :=
  (barkLocalsLeftoverDue evmUrns evmIlks I out outIlks).insert "partialDue"
    (.int (Int.ofNat
      ((barkSourceDartWord evmUrns evmIlks I out outIlks) *
        barkVatIlksRateWord outIlks).toNat))

abbrev barkLocalsInkDart (locals : Store) (inkDart : UInt256) : Store :=
  locals.insert "inkDart" (.int (Int.ofNat inkDart.toNat))

abbrev barkLocalsDink (locals : Store) (dink : UInt256) : Store :=
  locals.insert "dink" (.int (Int.ofNat dink.toNat))

abbrev barkLocalsGrabRet (locals : Store) : Store :=
  locals.insert "_grabRet" .unit

abbrev barkDueWord (dart rate : UInt256) : UInt256 :=
  dart * rate

abbrev barkLocalsDue (locals : Store) (due : UInt256) : Store :=
  locals.insert "due" (.int (Int.ofNat due.toNat))

abbrev barkLocalsFessRet (locals : Store) : Store :=
  locals.insert "_fessRet" .unit

abbrev barkTabBaseWord (due milkChop : UInt256) : UInt256 :=
  due * milkChop

abbrev barkLocalsTabBase (locals : Store) (tabBase : UInt256) : Store :=
  locals.insert "tabBase" (.int (Int.ofNat tabBase.toNat))

abbrev barkTabWord (tabBase : UInt256) : UInt256 :=
  UInt256.div tabBase dogWadWord

abbrev barkLocalsTab (locals : Store) (tab : UInt256) : Store :=
  locals.insert "tab" (.int (Int.ofNat tab.toNat))

abbrev barkDirtNewWord (dirt tab : UInt256) : UInt256 :=
  dirt + tab

abbrev barkLocalsDirtNew (locals : Store) (dirtNew : UInt256) : Store :=
  locals.insert "DirtNew" (.int (Int.ofNat dirtNew.toNat))

abbrev barkIlkDirtNewWord (milkDirt tab : UInt256) : UInt256 :=
  milkDirt + tab

abbrev barkLocalsIlkDirtNew (locals : Store) (ilkDirtNew : UInt256) : Store :=
  locals.insert "ilkDirtNew" (.int (Int.ofNat ilkDirtNew.toNat))

abbrev barkLocalsId (locals : Store) (id : UInt256) : Store :=
  locals.insert "id" (.int (Int.ofNat id.toNat))

abbrev barkBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev dogInt256LimitWord : UInt256 :=
  UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩

abbrev barkVowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (solcSlotWordAt ⟨2⟩ σ I)

abbrev barkVatGrabSelectorWord : UInt256 :=
  ⟨0x7bab3f40⟩

abbrev barkVatGrabSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨0x01eeacfd⟩ ⟨230⟩

abbrev barkVatGrabOutPtr : UInt256 :=
  ⟨384⟩

abbrev barkVatGrabInSize : UInt256 :=
  ⟨196⟩

abbrev barkVatGrabOutSize : UInt256 :=
  ⟨0⟩

abbrev barkVatGrabEndPtr : UInt256 :=
  ⟨580⟩

abbrev barkVatGrabSelectorMem (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem 384 barkVatGrabSelectorShifted

abbrev barkVatGrabIlkMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabSelectorMem mem) 388 (barkIlkWord I)

abbrev barkVatGrabUrnMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabIlkMem I mem) 420 (barkUrnKey I)

abbrev barkVatGrabClipMem
    (σMem : AccountMap) (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabUrnMem I mem) 452 (barkIlksClipWord σMem I)

abbrev barkVatGrabVowMem
    (σ σMem : AccountMap) (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabClipMem σMem I mem) 484 (barkVowWord σ I)

abbrev barkVatGrabDinkMem
    (σ σMem : AccountMap) (I : ExecutionEnv) (mem : ByteArray) (dink : UInt256) :
    ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabVowMem σ σMem I mem) 516 (UInt256.sub ⟨0⟩ dink)

abbrev barkVatGrabCallMem
    (σ σMem : AccountMap) (I : ExecutionEnv) (mem : ByteArray)
    (dink dart : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabDinkMem σ σMem I mem dink) 548
    (UInt256.sub ⟨0⟩ dart)

abbrev barkVatGrabPostCallMem
    (σ σMem : AccountMap) (I : ExecutionEnv) (mem out : ByteArray)
    (dink dart : UInt256) : ByteArray :=
  out.write 0 (barkVatGrabCallMem σ σMem I mem dink dart) barkVatGrabOutPtr.toNat
    (min barkVatGrabOutSize (UInt256.ofNat out.size)).toNat

abbrev barkVowFessSelectorWord : UInt256 :=
  ⟨0x697efb78⟩

abbrev barkVowFessSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨0x0d2fdf6f⟩ ⟨227⟩

abbrev barkVowFessOutPtr : UInt256 :=
  ⟨384⟩

abbrev barkVowFessInSize : UInt256 :=
  ⟨36⟩

abbrev barkVowFessOutSize : UInt256 :=
  ⟨0⟩

abbrev barkVowFessEndPtr : UInt256 :=
  ⟨420⟩

abbrev barkVowFessSelectorMem (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem 384 barkVowFessSelectorShifted

abbrev barkVowFessDueMem (mem : ByteArray) (due : UInt256) :
    ByteArray :=
  Reasoning.Theory.writeWord (barkVowFessSelectorMem mem) 388 due

abbrev barkVowFessPostCallMem
    (mem out : ByteArray) (due : UInt256) : ByteArray :=
  out.write 0 (barkVowFessDueMem mem due) barkVowFessOutPtr.toNat
    (min barkVowFessOutSize (UInt256.ofNat out.size)).toNat

abbrev barkKickSelectorWord : UInt256 :=
  ⟨0x898eb267⟩

abbrev barkKickSelectorShifted : UInt256 :=
  UInt256.shiftLeft barkKickSelectorWord ⟨224⟩

abbrev barkKickOutPtr : UInt256 :=
  ⟨384⟩

abbrev barkKickInSize : UInt256 :=
  ⟨132⟩

abbrev barkKickOutSize : UInt256 :=
  ⟨32⟩

abbrev barkKickEndPtr : UInt256 :=
  ⟨516⟩

abbrev barkKickSelectorMem (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem 384 barkKickSelectorShifted

abbrev barkKickTabMem (mem : ByteArray) (tab : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (barkKickSelectorMem mem) 388 tab

abbrev barkKickDinkMem (mem : ByteArray) (tab dink : UInt256) :
    ByteArray :=
  Reasoning.Theory.writeWord (barkKickTabMem mem tab) 420 dink

abbrev barkKickUrnMem (I : ExecutionEnv) (mem : ByteArray)
    (tab dink : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (barkKickDinkMem mem tab dink) 452 (barkUrnKey I)

abbrev barkKickCalldataMem (I : ExecutionEnv) (mem : ByteArray)
    (tab dink : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (barkKickUrnMem I mem tab dink) 484 (barkKprKey I)

abbrev barkKickPostCallMem (I : ExecutionEnv) (mem out : ByteArray)
    (tab dink : UInt256) : ByteArray :=
  out.write 0 (barkKickCalldataMem I mem tab dink) barkKickOutPtr.toNat
    (min barkKickOutSize (UInt256.ofNat out.size)).toNat

abbrev barkRoomWadWord (σ σMem : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if (barkGlobalRoomWord σ I).toNat ≤ (barkIlkRoomWord σMem I).toNat then
    barkGlobalRoomWord σ I * dogWadWord
  else
    barkIlkRoomWord σMem I * dogWadWord

abbrev barkDartByRateWord (σ σMem : AccountMap) (I : ExecutionEnv) (rate : UInt256) :
    UInt256 :=
  UInt256.div (barkRoomWadWord σ σMem I) rate

abbrev barkDartCandidateWord
    (σ σMem : AccountMap) (I : ExecutionEnv) (rate chop : UInt256) : UInt256 :=
  UInt256.div (barkDartByRateWord σ σMem I rate) chop

abbrev barkDartWord
    (σ σMem : AccountMap) (I : ExecutionEnv) (art rate chop : UInt256) : UInt256 :=
  let dartCandidate := barkDartCandidateWord σ σMem I rate chop
  if art.toNat ≤ dartCandidate.toNat then art else dartCandidate

abbrev barkInkDartWord (ink dart : UInt256) : UInt256 :=
  ink * dart

abbrev barkDinkWord (ink dart art : UInt256) : UInt256 :=
  UInt256.div (barkInkDartWord ink dart) art

abbrev barkLeftoverArtWord (art dart : UInt256) : UInt256 :=
  UInt256.sub art dart

abbrev barkLeftoverDueWord (art dart rate : UInt256) : UInt256 :=
  barkLeftoverArtWord art dart * rate

abbrev barkPartialDueWord (dart rate : UInt256) : UInt256 :=
  dart * rate

theorem barkDartWord_toNat_le_art
    (σ σMem : AccountMap) (I : ExecutionEnv) (art rate chop : UInt256) :
    (barkDartWord σ σMem I art rate chop).toNat ≤ art.toNat := by
  change
    (if art.toNat ≤ (barkDartCandidateWord σ σMem I rate chop).toNat then
        art
      else
        barkDartCandidateWord σ σMem I rate chop).toNat ≤ art.toNat
  split_ifs with hle
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (not_le.mp hle)

theorem barkLeftoverArtWord_toNat_le_art {art dart : UInt256}
    (hdartLe : dart.toNat ≤ art.toNat) :
    (barkLeftoverArtWord art dart).toNat ≤ art.toNat := by
  rw [barkLeftoverArtWord, usub_toNat hdartLe]
  omega

theorem barkLeftoverDue_fit_of_art_fit {art dart rate : UInt256}
    (hdartLe : dart.toNat ≤ art.toNat)
    (hfitArt : art.toNat * rate.toNat < UInt256.size) :
    (barkLeftoverArtWord art dart).toNat * rate.toNat < UInt256.size := by
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_right rate.toNat (barkLeftoverArtWord_toNat_le_art hdartLe))
    hfitArt


abbrev dogNotLiveRawWord : UInt256 :=
  ⟨21179658712531102354511591013⟩

abbrev dogNotUnsafeRawWord : UInt256 :=
  ⟨1388030113384438323915188657546853⟩

abbrev dogLiquidationLimitHitRawWord : UInt256 :=
  ⟨429574513270148286153109682416655011243695164593862324283764⟩

abbrev dogNullAuctionRawWord : UInt256 :=
  ⟨45482970755384883464522350792499574711⟩

abbrev dogOverflowRawWord : UInt256 :=
  ⟨21179658712605114076964351863⟩

theorem barkLocals_get_live (I : ExecutionEnv) :
    (barkLocals I).get? "live" = none := by
  rw [barkLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem barkLocals_get_ilk (I : ExecutionEnv) :
    (barkLocals I).get? "ilk" =
      some (.fixedBytes bytes32Width (barkIlkBytes I)) := by
  rw [barkLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem barkLocals_get_urn (I : ExecutionEnv) :
    (barkLocals I).get? "urn" = some (.address (barkUrn I)) := by
  rw [barkLocals, store_get_ne _ _ (by decide), store_get_self]

theorem barkLocals_get_kpr (I : ExecutionEnv) :
    (barkLocals I).get? "kpr" = some (.address (barkKpr I)) := by
  rw [barkLocals, store_get_self]

theorem barkLocals_get_ilks (I : ExecutionEnv) :
    (barkLocals I).get? "ilks" = none := by
  rw [barkLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem barkLocalsVatUrn_get_vatUrn (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsVatUrn I out).get? "vatUrn" = some (barkVatUrnValue out) := by
  rw [barkLocalsVatUrn, store_get_self]

theorem barkLocalsInk_get_vatUrn (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsInk I out).get? "vatUrn" = some (barkVatUrnValue out) := by
  rw [barkLocalsInk, store_get_ne _ _ (by decide), barkLocalsVatUrn_get_vatUrn]

theorem barkLocalsArt_get_vatUrn (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsArt I out).get? "vatUrn" = some (barkVatUrnValue out) := by
  rw [barkLocalsArt, store_get_ne _ _ (by decide), barkLocalsInk_get_vatUrn]

theorem barkLocalsVatUrn_get_ilk (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsVatUrn I out).get? "ilk" =
      some (.fixedBytes bytes32Width (barkIlkBytes I)) := by
  rw [barkLocalsVatUrn, store_get_ne _ _ (by decide), barkLocals_get_ilk]

theorem barkLocalsInk_get_ilk (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsInk I out).get? "ilk" =
      some (.fixedBytes bytes32Width (barkIlkBytes I)) := by
  rw [barkLocalsInk, store_get_ne _ _ (by decide), barkLocalsVatUrn_get_ilk]

theorem barkLocalsArt_get_ilk (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsArt I out).get? "ilk" =
      some (.fixedBytes bytes32Width (barkIlkBytes I)) := by
  rw [barkLocalsArt, store_get_ne _ _ (by decide), barkLocalsInk_get_ilk]

theorem barkLocalsArt_get_ilks (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsArt I out).get? "ilks" = none := by
  rw [barkLocalsArt, store_get_ne _ _ (by decide), barkLocalsInk,
    store_get_ne _ _ (by decide), barkLocalsVatUrn, store_get_ne _ _ (by decide),
    barkLocals_get_ilks]

theorem barkLocalsMilkClip_get_ilk
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsMilkClip evm I out).get? "ilk" =
      some (.fixedBytes bytes32Width (barkIlkBytes I)) := by
  rw [barkLocalsMilkClip, store_get_ne _ _ (by decide), barkLocalsArt_get_ilk]

theorem barkLocalsMilkClip_get_ilks
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsMilkClip evm I out).get? "ilks" = none := by
  rw [barkLocalsMilkClip, store_get_ne _ _ (by decide), barkLocalsArt_get_ilks]

theorem barkLocalsMilkClip_get_milkClip
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsMilkClip evm I out).get? "milkClip" =
      some (.address (AccountAddress.ofNat
        (solcAddressSlotWord (barkIlksClipSlotFor I) evm.accountMap
          evm.executionEnv).toNat)) := by
  rw [barkLocalsMilkClip, store_get_self]

theorem barkLocalsMilkChop_get_ilk
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsMilkChop evm I out).get? "ilk" =
      some (.fixedBytes bytes32Width (barkIlkBytes I)) := by
  rw [barkLocalsMilkChop, store_get_ne _ _ (by decide), barkLocalsMilkClip_get_ilk]

theorem barkLocalsMilkChop_get_ilks
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsMilkChop evm I out).get? "ilks" = none := by
  rw [barkLocalsMilkChop, store_get_ne _ _ (by decide), barkLocalsMilkClip_get_ilks]

theorem barkLocalsMilkHole_get_ilk
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsMilkHole evm I out).get? "ilk" =
      some (.fixedBytes bytes32Width (barkIlkBytes I)) := by
  rw [barkLocalsMilkHole, store_get_ne _ _ (by decide), barkLocalsMilkChop_get_ilk]

theorem barkLocalsMilkHole_get_ilks
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsMilkHole evm I out).get? "ilks" = none := by
  rw [barkLocalsMilkHole, store_get_ne _ _ (by decide), barkLocalsMilkChop_get_ilks]

theorem barkLocalsMilkDirt_get_ilk
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    (barkLocalsMilkDirt evm I out).get? "ilk" =
      some (.fixedBytes bytes32Width (barkIlkBytes I)) := by
  rw [barkLocalsMilkDirt, store_get_ne _ _ (by decide), barkLocalsMilkHole_get_ilk]

theorem barkLocalsVatIlk_get_vatIlk
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsVatIlk evm I out outIlks).get? "vatIlk" =
      some (barkVatIlkValue outIlks) := by
  rw [barkLocalsVatIlk, store_get_self]

theorem barkLocalsVatIlk_get_ilk
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsVatIlk evm I out outIlks).get? "ilk" =
      some (.fixedBytes bytes32Width (barkIlkBytes I)) := by
  rw [barkLocalsVatIlk, store_get_ne _ _ (by decide), barkLocalsMilkDirt_get_ilk]

theorem barkLocalsRate_get_vatIlk
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsRate evm I out outIlks).get? "vatIlk" =
      some (barkVatIlkValue outIlks) := by
  rw [barkLocalsRate, store_get_ne _ _ (by decide), barkLocalsVatIlk_get_vatIlk]

theorem barkLocalsRate_get_rate
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsRate evm I out outIlks).get? "rate" =
      some (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) := by
  rw [barkLocalsRate, store_get_self]

theorem barkLocalsSpot_get_vatIlk
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsSpot evm I out outIlks).get? "vatIlk" =
      some (barkVatIlkValue outIlks) := by
  rw [barkLocalsSpot, store_get_ne _ _ (by decide), barkLocalsRate_get_vatIlk]

theorem barkLocalsSpot_get_rate
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsSpot evm I out outIlks).get? "rate" =
      some (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) := by
  rw [barkLocalsSpot, store_get_ne _ _ (by decide), barkLocalsRate_get_rate]

theorem barkLocalsSpot_get_spot
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsSpot evm I out outIlks).get? "spot" =
      some (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat)) := by
  rw [barkLocalsSpot, store_get_self]

theorem barkLocalsDust_get_vatIlk
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDust evm I out outIlks).get? "vatIlk" =
      some (barkVatIlkValue outIlks) := by
  rw [barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot_get_vatIlk]

theorem barkLocalsDust_get_rate
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDust evm I out outIlks).get? "rate" =
      some (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) := by
  rw [barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot_get_rate]

theorem barkLocalsDust_get_spot
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDust evm I out outIlks).get? "spot" =
      some (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat)) := by
  rw [barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot_get_spot]

theorem barkLocalsDust_get_dust
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDust evm I out outIlks).get? "dust" =
      some (.int (Int.ofNat (barkVatIlksDustWord outIlks).toNat)) := by
  rw [barkLocalsDust, store_get_self]

theorem barkLocalsDust_get_ink
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDust evm I out outIlks).get? "ink" =
      some (.int (Int.ofNat (barkVatUrnsInkWord out).toNat)) := by
  rw [barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot,
    store_get_ne _ _ (by decide), barkLocalsRate, store_get_ne _ _ (by decide),
    barkLocalsVatIlk, store_get_ne _ _ (by decide), barkLocalsMilkDirt,
    store_get_ne _ _ (by decide), barkLocalsMilkHole, store_get_ne _ _ (by decide),
    barkLocalsMilkChop, store_get_ne _ _ (by decide), barkLocalsMilkClip,
    store_get_ne _ _ (by decide), barkLocalsArt, store_get_ne _ _ (by decide),
    barkLocalsInk, store_get_self]

theorem barkLocalsDust_get_art
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDust evm I out outIlks).get? "art" =
      some (.int (Int.ofNat (barkVatUrnsArtWord out).toNat)) := by
  rw [barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot,
    store_get_ne _ _ (by decide), barkLocalsRate, store_get_ne _ _ (by decide),
    barkLocalsVatIlk, store_get_ne _ _ (by decide), barkLocalsMilkDirt,
    store_get_ne _ _ (by decide), barkLocalsMilkHole, store_get_ne _ _ (by decide),
    barkLocalsMilkChop, store_get_ne _ _ (by decide), barkLocalsMilkClip,
    store_get_ne _ _ (by decide), barkLocalsArt, store_get_self]

theorem barkLocalsInkSpot_get_inkSpot
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsInkSpot evm I out outIlks).get? "inkSpot" =
      some (.int (Int.ofNat (barkInkSpotWord out outIlks).toNat)) := by
  rw [barkLocalsInkSpot, store_get_self]

theorem barkLocalsInkSpot_get_art
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsInkSpot evm I out outIlks).get? "art" =
      some (.int (Int.ofNat (barkVatUrnsArtWord out).toNat)) := by
  rw [barkLocalsInkSpot, store_get_ne _ _ (by decide), barkLocalsDust_get_art]

theorem barkLocalsInkSpot_get_ink
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsInkSpot evm I out outIlks).get? "ink" =
      some (.int (Int.ofNat (barkVatUrnsInkWord out).toNat)) := by
  rw [barkLocalsInkSpot, store_get_ne _ _ (by decide), barkLocalsDust_get_ink]

theorem barkLocalsInkSpot_get_rate
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsInkSpot evm I out outIlks).get? "rate" =
      some (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) := by
  rw [barkLocalsInkSpot, store_get_ne _ _ (by decide), barkLocalsDust_get_rate]

theorem barkLocalsInkSpot_get_spot
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsInkSpot evm I out outIlks).get? "spot" =
      some (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat)) := by
  rw [barkLocalsInkSpot, store_get_ne _ _ (by decide), barkLocalsDust_get_spot]

theorem barkLocalsArtRateUnsafe_get_inkSpot
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsArtRateUnsafe evm I out outIlks).get? "inkSpot" =
      some (.int (Int.ofNat (barkInkSpotWord out outIlks).toNat)) := by
  rw [barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot_get_inkSpot]

theorem barkLocalsArtRateUnsafe_get_artRateUnsafe
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsArtRateUnsafe evm I out outIlks).get? "artRateUnsafe" =
      some (.int (Int.ofNat (barkArtRateUnsafeWord out outIlks).toNat)) := by
  rw [barkLocalsArtRateUnsafe, store_get_self]

theorem barkLocalsArtRateUnsafe_get_art
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsArtRateUnsafe evm I out outIlks).get? "art" =
      some (.int (Int.ofNat (barkVatUrnsArtWord out).toNat)) := by
  rw [barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot_get_art]

theorem barkLocalsArtRateUnsafe_get_rate
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsArtRateUnsafe evm I out outIlks).get? "rate" =
      some (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) := by
  rw [barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot_get_rate]

theorem barkLocalsArtRateUnsafe_get_spot
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsArtRateUnsafe evm I out outIlks).get? "spot" =
      some (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat)) := by
  rw [barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot_get_spot]

theorem barkLocalsArtRateUnsafe_get_milkHole
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsArtRateUnsafe evm I out outIlks).get? "milkHole" =
      some (.int (Int.ofNat
        (solcSlotWordAt (barkIlksHoleSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  rw [barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot,
    store_get_ne _ _ (by decide), barkLocalsDust, store_get_ne _ _ (by decide),
    barkLocalsSpot, store_get_ne _ _ (by decide), barkLocalsRate,
    store_get_ne _ _ (by decide), barkLocalsVatIlk, store_get_ne _ _ (by decide),
    barkLocalsMilkDirt, store_get_ne _ _ (by decide), barkLocalsMilkHole, store_get_self]

theorem barkLocalsArtRateUnsafe_get_milkDirt
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsArtRateUnsafe evm I out outIlks).get? "milkDirt" =
      some (.int (Int.ofNat
        (solcSlotWordAt (barkIlksDirtSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  rw [barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot,
    store_get_ne _ _ (by decide), barkLocalsDust, store_get_ne _ _ (by decide),
    barkLocalsSpot, store_get_ne _ _ (by decide), barkLocalsRate,
    store_get_ne _ _ (by decide), barkLocalsVatIlk, store_get_ne _ _ (by decide),
    barkLocalsMilkDirt, store_get_self]

theorem barkLocalsArtRateUnsafe_get_Hole
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsArtRateUnsafe evm I out outIlks).get? "Hole" = none := by
  rw [barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot,
    store_get_ne _ _ (by decide), barkLocalsDust, store_get_ne _ _ (by decide),
    barkLocalsSpot, store_get_ne _ _ (by decide), barkLocalsRate,
    store_get_ne _ _ (by decide), barkLocalsVatIlk, store_get_ne _ _ (by decide),
    barkLocalsMilkDirt, store_get_ne _ _ (by decide), barkLocalsMilkHole,
    store_get_ne _ _ (by decide), barkLocalsMilkChop, store_get_ne _ _ (by decide),
    barkLocalsMilkClip, store_get_ne _ _ (by decide), barkLocalsArt,
    store_get_ne _ _ (by decide), barkLocalsInk, store_get_ne _ _ (by decide),
    barkLocalsVatUrn, store_get_ne _ _ (by decide), barkLocals,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem barkLocalsArtRateUnsafe_get_Dirt
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsArtRateUnsafe evm I out outIlks).get? "Dirt" = none := by
  rw [barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot,
    store_get_ne _ _ (by decide), barkLocalsDust, store_get_ne _ _ (by decide),
    barkLocalsSpot, store_get_ne _ _ (by decide), barkLocalsRate,
    store_get_ne _ _ (by decide), barkLocalsVatIlk, store_get_ne _ _ (by decide),
    barkLocalsMilkDirt, store_get_ne _ _ (by decide), barkLocalsMilkHole,
    store_get_ne _ _ (by decide), barkLocalsMilkChop, store_get_ne _ _ (by decide),
    barkLocalsMilkClip, store_get_ne _ _ (by decide), barkLocalsArt,
    store_get_ne _ _ (by decide), barkLocalsInk, store_get_ne _ _ (by decide),
    barkLocalsVatUrn, store_get_ne _ _ (by decide), barkLocals,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem barkLocalsGlobalRoom_get_globalRoom
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsGlobalRoom evmUrns evmIlks I out outIlks).get? "globalRoom" =
      some (.int (Int.ofNat (barkSourceGlobalRoomWord evmIlks).toNat)) := by
  rw [barkLocalsGlobalRoom, store_get_self]

theorem barkLocalsGlobalRoom_get_Hole
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsGlobalRoom evmUrns evmIlks I out outIlks).get? "Hole" = none := by
  rw [barkLocalsGlobalRoom, store_get_ne _ _ (by decide),
    barkLocalsArtRateUnsafe_get_Hole]

theorem barkLocalsGlobalRoom_get_milkHole
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsGlobalRoom evmUrns evmIlks I out outIlks).get? "milkHole" =
      some (.int (Int.ofNat
        (solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat)) := by
  rw [barkLocalsGlobalRoom, store_get_ne _ _ (by decide),
    barkLocalsArtRateUnsafe_get_milkHole]

theorem barkLocalsGlobalRoom_get_milkDirt
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsGlobalRoom evmUrns evmIlks I out outIlks).get? "milkDirt" =
      some (.int (Int.ofNat
        (solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat)) := by
  rw [barkLocalsGlobalRoom, store_get_ne _ _ (by decide),
    barkLocalsArtRateUnsafe_get_milkDirt]

theorem barkLocalsIlkRoom_get_globalRoom
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsIlkRoom evmUrns evmIlks I out outIlks).get? "globalRoom" =
      some (.int (Int.ofNat (barkSourceGlobalRoomWord evmIlks).toNat)) := by
  rw [barkLocalsIlkRoom, store_get_ne _ _ (by decide),
    barkLocalsGlobalRoom_get_globalRoom]

theorem barkLocalsIlkRoom_get_ilkRoom
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsIlkRoom evmUrns evmIlks I out outIlks).get? "ilkRoom" =
      some (.int (Int.ofNat (barkSourceIlkRoomWord evmUrns I).toNat)) := by
  rw [barkLocalsIlkRoom, store_get_self]

theorem barkLocalsRoom_get_room
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsRoom evmUrns evmIlks I out outIlks).get? "room" =
      some (.int (Int.ofNat (barkSourceRoomWord evmUrns evmIlks I).toNat)) := by
  rw [barkLocalsRoom, store_get_self]

theorem barkLocalsRoom_get_rate
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsRoom evmUrns evmIlks I out outIlks).get? "rate" =
      some (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) := by
  rw [barkLocalsRoom, store_get_ne _ _ (by decide), barkLocalsIlkRoom,
    store_get_ne _ _ (by decide), barkLocalsGlobalRoom, store_get_ne _ _ (by decide),
    barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot,
    store_get_ne _ _ (by decide), barkLocalsDust, store_get_ne _ _ (by decide),
    barkLocalsSpot, store_get_ne _ _ (by decide), barkLocalsRate, store_get_self]

theorem barkLocalsRoom_get_milkChop
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsRoom evmUrns evmIlks I out outIlks).get? "milkChop" =
      some (.int (Int.ofNat
        (solcSlotWordAt (barkIlksChopSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat)) := by
  rw [barkLocalsRoom, store_get_ne _ _ (by decide), barkLocalsIlkRoom,
    store_get_ne _ _ (by decide), barkLocalsGlobalRoom, store_get_ne _ _ (by decide),
    barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot,
    store_get_ne _ _ (by decide), barkLocalsDust, store_get_ne _ _ (by decide),
    barkLocalsSpot, store_get_ne _ _ (by decide), barkLocalsRate,
    store_get_ne _ _ (by decide), barkLocalsVatIlk, store_get_ne _ _ (by decide),
    barkLocalsMilkDirt, store_get_ne _ _ (by decide), barkLocalsMilkHole,
    store_get_ne _ _ (by decide), barkLocalsMilkChop, store_get_self]

theorem barkLocalsRoomWad_get_roomWad
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsRoomWad evmUrns evmIlks I out outIlks).get? "roomWad" =
      some (.int (Int.ofNat (barkSourceRoomWadWord evmUrns evmIlks I).toNat)) := by
  rw [barkLocalsRoomWad, store_get_self]

theorem barkLocalsRoomWad_get_rate
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsRoomWad evmUrns evmIlks I out outIlks).get? "rate" =
      some (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) := by
  rw [barkLocalsRoomWad, store_get_ne _ _ (by decide),
    barkLocalsRoom_get_rate]

theorem barkLocalsDartByRate_get_dartByRate
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDartByRate evmUrns evmIlks I out outIlks).get? "dartByRate" =
      some (.int (Int.ofNat
        (barkSourceDartByRateWord evmUrns evmIlks I outIlks).toNat)) := by
  rw [barkLocalsDartByRate, store_get_self]

theorem barkLocalsDartByRate_get_milkChop
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDartByRate evmUrns evmIlks I out outIlks).get? "milkChop" =
      some (.int (Int.ofNat
        (solcSlotWordAt (barkIlksChopSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat)) := by
  rw [barkLocalsDartByRate, store_get_ne _ _ (by decide), barkLocalsRoomWad,
    store_get_ne _ _ (by decide), barkLocalsRoom_get_milkChop]

theorem barkLocalsDartByRate_get_art
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDartByRate evmUrns evmIlks I out outIlks).get? "art" =
      some (.int (Int.ofNat (barkVatUrnsArtWord out).toNat)) := by
  rw [barkLocalsDartByRate, store_get_ne _ _ (by decide), barkLocalsRoomWad,
    store_get_ne _ _ (by decide), barkLocalsRoom, store_get_ne _ _ (by decide),
    barkLocalsIlkRoom, store_get_ne _ _ (by decide), barkLocalsGlobalRoom,
    store_get_ne _ _ (by decide), barkLocalsArtRateUnsafe_get_art]

theorem barkLocalsDartByRate_get_ink
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDartByRate evmUrns evmIlks I out outIlks).get? "ink" =
      some (.int (Int.ofNat (barkVatUrnsInkWord out).toNat)) := by
  rw [barkLocalsDartByRate, store_get_ne _ _ (by decide), barkLocalsRoomWad,
    store_get_ne _ _ (by decide), barkLocalsRoom, store_get_ne _ _ (by decide),
    barkLocalsIlkRoom, store_get_ne _ _ (by decide), barkLocalsGlobalRoom,
    store_get_ne _ _ (by decide), barkLocalsArtRateUnsafe,
    store_get_ne _ _ (by decide), barkLocalsInkSpot_get_ink]

theorem barkLocalsDartByRate_get_dust
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDartByRate evmUrns evmIlks I out outIlks).get? "dust" =
      some (.int (Int.ofNat (barkVatIlksDustWord outIlks).toNat)) := by
  rw [barkLocalsDartByRate, store_get_ne _ _ (by decide), barkLocalsRoomWad,
    store_get_ne _ _ (by decide), barkLocalsRoom, store_get_ne _ _ (by decide),
    barkLocalsIlkRoom, store_get_ne _ _ (by decide), barkLocalsGlobalRoom,
    store_get_ne _ _ (by decide), barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide),
    barkLocalsInkSpot, store_get_ne _ _ (by decide), barkLocalsDust_get_dust]

theorem barkLocalsDartCandidate_get_dartCandidate
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDartCandidate evmUrns evmIlks I out outIlks).get? "dartCandidate" =
      some (.int (Int.ofNat
        (barkSourceDartCandidateWord evmUrns evmIlks I outIlks).toNat)) := by
  rw [barkLocalsDartCandidate, store_get_self]

theorem barkLocalsDartCandidate_get_art
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDartCandidate evmUrns evmIlks I out outIlks).get? "art" =
      some (.int (Int.ofNat (barkVatUrnsArtWord out).toNat)) := by
  rw [barkLocalsDartCandidate, store_get_ne _ _ (by decide),
    barkLocalsDartByRate_get_art]

theorem barkLocalsDart_get_dart
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "dart" =
      some (.int (Int.ofNat (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat)) := by
  rw [barkLocalsDart, store_get_self]

theorem barkLocalsDart_get_art
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "art" =
      some (.int (Int.ofNat (barkVatUrnsArtWord out).toNat)) := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate_get_art]

theorem barkLocalsDart_get_ink
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "ink" =
      some (.int (Int.ofNat (barkVatUrnsInkWord out).toNat)) := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate_get_ink]

theorem barkLocalsDart_get_rate
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "rate" =
      some (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate, store_get_ne _ _ (by decide),
    barkLocalsRoomWad_get_rate]

theorem barkLocalsDart_get_dust
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "dust" =
      some (.int (Int.ofNat (barkVatIlksDustWord outIlks).toNat)) := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate_get_dust]

theorem barkLocalsDart_get_milkClip
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "milkClip" =
      some (.address (AccountAddress.ofNat
        (solcAddressSlotWord (barkIlksClipSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat)) := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate, store_get_ne _ _ (by decide),
    barkLocalsRoomWad, store_get_ne _ _ (by decide), barkLocalsRoom,
    store_get_ne _ _ (by decide), barkLocalsIlkRoom, store_get_ne _ _ (by decide),
    barkLocalsGlobalRoom, store_get_ne _ _ (by decide), barkLocalsArtRateUnsafe,
    store_get_ne _ _ (by decide), barkLocalsInkSpot, store_get_ne _ _ (by decide),
    barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot,
    store_get_ne _ _ (by decide), barkLocalsRate, store_get_ne _ _ (by decide),
    barkLocalsVatIlk, store_get_ne _ _ (by decide), barkLocalsMilkDirt,
    store_get_ne _ _ (by decide), barkLocalsMilkHole, store_get_ne _ _ (by decide),
    barkLocalsMilkChop, store_get_ne _ _ (by decide),
    barkLocalsMilkClip_get_milkClip]

theorem barkLocalsDart_get_milkChop
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "milkChop" =
      some (.int (Int.ofNat
        (solcSlotWordAt (barkIlksChopSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat)) := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate_get_milkChop]

theorem barkLocalsDart_get_ilk
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "ilk" =
      some (.fixedBytes bytes32Width (barkIlkBytes I)) := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate, store_get_ne _ _ (by decide),
    barkLocalsRoomWad, store_get_ne _ _ (by decide), barkLocalsRoom,
    store_get_ne _ _ (by decide), barkLocalsIlkRoom, store_get_ne _ _ (by decide),
    barkLocalsGlobalRoom, store_get_ne _ _ (by decide), barkLocalsArtRateUnsafe,
    store_get_ne _ _ (by decide), barkLocalsInkSpot, store_get_ne _ _ (by decide),
    barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot,
    store_get_ne _ _ (by decide), barkLocalsRate, store_get_ne _ _ (by decide),
    barkLocalsVatIlk_get_ilk]

theorem barkLocalsDart_get_urn
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "urn" =
      some (.address (barkUrn I)) := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate, store_get_ne _ _ (by decide),
    barkLocalsRoomWad, store_get_ne _ _ (by decide), barkLocalsRoom,
    store_get_ne _ _ (by decide), barkLocalsIlkRoom, store_get_ne _ _ (by decide),
    barkLocalsGlobalRoom, store_get_ne _ _ (by decide), barkLocalsArtRateUnsafe,
    store_get_ne _ _ (by decide), barkLocalsInkSpot, store_get_ne _ _ (by decide),
    barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot,
    store_get_ne _ _ (by decide), barkLocalsRate, store_get_ne _ _ (by decide),
    barkLocalsVatIlk, store_get_ne _ _ (by decide), barkLocalsMilkDirt,
    store_get_ne _ _ (by decide), barkLocalsMilkHole, store_get_ne _ _ (by decide),
    barkLocalsMilkChop, store_get_ne _ _ (by decide), barkLocalsMilkClip,
    store_get_ne _ _ (by decide), barkLocalsArt, store_get_ne _ _ (by decide),
    barkLocalsInk, store_get_ne _ _ (by decide), barkLocalsVatUrn,
    store_get_ne _ _ (by decide), barkLocals_get_urn]

theorem barkLocalsDart_get_kpr
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "kpr" =
      some (.address (barkKpr I)) := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate, store_get_ne _ _ (by decide),
    barkLocalsRoomWad, store_get_ne _ _ (by decide), barkLocalsRoom,
    store_get_ne _ _ (by decide), barkLocalsIlkRoom, store_get_ne _ _ (by decide),
    barkLocalsGlobalRoom, store_get_ne _ _ (by decide), barkLocalsArtRateUnsafe,
    store_get_ne _ _ (by decide), barkLocalsInkSpot, store_get_ne _ _ (by decide),
    barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot,
    store_get_ne _ _ (by decide), barkLocalsRate, store_get_ne _ _ (by decide),
    barkLocalsVatIlk, store_get_ne _ _ (by decide), barkLocalsMilkDirt,
    store_get_ne _ _ (by decide), barkLocalsMilkHole, store_get_ne _ _ (by decide),
    barkLocalsMilkChop, store_get_ne _ _ (by decide), barkLocalsMilkClip,
    store_get_ne _ _ (by decide), barkLocalsArt, store_get_ne _ _ (by decide),
    barkLocalsInk, store_get_ne _ _ (by decide), barkLocalsVatUrn,
    store_get_ne _ _ (by decide), barkLocals_get_kpr]

theorem barkLocalsDart_get_milkDirt
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "milkDirt" =
      some (.int (Int.ofNat
        (solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat)) := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate, store_get_ne _ _ (by decide),
    barkLocalsRoomWad, store_get_ne _ _ (by decide), barkLocalsRoom,
    store_get_ne _ _ (by decide), barkLocalsIlkRoom, store_get_ne _ _ (by decide),
    barkLocalsGlobalRoom, store_get_ne _ _ (by decide),
    barkLocalsArtRateUnsafe_get_milkDirt]

theorem barkLocalsDart_get_Dirt
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "Dirt" = none := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate, store_get_ne _ _ (by decide),
    barkLocalsRoomWad, store_get_ne _ _ (by decide), barkLocalsRoom,
    store_get_ne _ _ (by decide), barkLocalsIlkRoom, store_get_ne _ _ (by decide),
    barkLocalsGlobalRoom, store_get_ne _ _ (by decide), barkLocalsArtRateUnsafe_get_Dirt]

theorem barkLocalsDart_get_ilks
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "ilks" = none := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate, store_get_ne _ _ (by decide),
    barkLocalsRoomWad, store_get_ne _ _ (by decide), barkLocalsRoom,
    store_get_ne _ _ (by decide), barkLocalsIlkRoom, store_get_ne _ _ (by decide),
    barkLocalsGlobalRoom, store_get_ne _ _ (by decide), barkLocalsArtRateUnsafe,
    store_get_ne _ _ (by decide), barkLocalsInkSpot, store_get_ne _ _ (by decide),
    barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot,
    store_get_ne _ _ (by decide), barkLocalsRate, store_get_ne _ _ (by decide),
    barkLocalsVatIlk, store_get_ne _ _ (by decide), barkLocalsMilkDirt,
    store_get_ne _ _ (by decide), barkLocalsMilkHole, store_get_ne _ _ (by decide),
    barkLocalsMilkChop, store_get_ne _ _ (by decide), barkLocalsMilkClip_get_ilks]

theorem barkLocalsDart_get_vow
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDart evmUrns evmIlks I out outIlks).get? "vow" = none := by
  rw [barkLocalsDart, store_get_ne _ _ (by decide), barkLocalsDartCandidate,
    store_get_ne _ _ (by decide), barkLocalsDartByRate, store_get_ne _ _ (by decide),
    barkLocalsRoomWad, store_get_ne _ _ (by decide), barkLocalsRoom,
    store_get_ne _ _ (by decide), barkLocalsIlkRoom, store_get_ne _ _ (by decide),
    barkLocalsGlobalRoom, store_get_ne _ _ (by decide), barkLocalsArtRateUnsafe,
    store_get_ne _ _ (by decide), barkLocalsInkSpot, store_get_ne _ _ (by decide),
    barkLocalsDust, store_get_ne _ _ (by decide), barkLocalsSpot,
    store_get_ne _ _ (by decide), barkLocalsRate, store_get_ne _ _ (by decide),
    barkLocalsVatIlk, store_get_ne _ _ (by decide), barkLocalsMilkDirt,
    store_get_ne _ _ (by decide), barkLocalsMilkHole, store_get_ne _ _ (by decide),
    barkLocalsMilkChop, store_get_ne _ _ (by decide), barkLocalsMilkClip,
    store_get_ne _ _ (by decide), barkLocalsArt, store_get_ne _ _ (by decide),
    barkLocalsInk, store_get_ne _ _ (by decide), barkLocalsVatUrn,
    store_get_ne _ _ (by decide), barkLocals, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem barkLocalsLeftoverArt_get_leftoverArt
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsLeftoverArt evmUrns evmIlks I out outIlks).get? "leftoverArt" =
      some (.int (Int.ofNat
        (UInt256.sub (barkVatUrnsArtWord out)
          (barkSourceDartWord evmUrns evmIlks I out outIlks)).toNat)) := by
  rw [barkLocalsLeftoverArt, store_get_self]

theorem barkLocalsLeftoverDue_get_leftoverDue
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsLeftoverDue evmUrns evmIlks I out outIlks).get? "leftoverDue" =
      some (.int (Int.ofNat
        ((UInt256.sub (barkVatUrnsArtWord out)
          (barkSourceDartWord evmUrns evmIlks I out outIlks)) *
          barkVatIlksRateWord outIlks).toNat)) := by
  rw [barkLocalsLeftoverDue, store_get_self]

theorem barkLocalsLeftoverArt_get_preserved
    {evmUrns evmIlks : EVM.State} {I : ExecutionEnv} {out outIlks : ByteArray}
    {name : Ident} {value : Value} (hname : ("leftoverArt" == name) = false)
    (hget : (barkLocalsDart evmUrns evmIlks I out outIlks).get? name = some value) :
    (barkLocalsLeftoverArt evmUrns evmIlks I out outIlks).get? name = some value := by
  rw [barkLocalsLeftoverArt, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsLeftoverDue_get_preserved
    {evmUrns evmIlks : EVM.State} {I : ExecutionEnv} {out outIlks : ByteArray}
    {name : Ident} {value : Value} (hname : ("leftoverDue" == name) = false)
    (hget : (barkLocalsLeftoverArt evmUrns evmIlks I out outIlks).get? name = some value) :
    (barkLocalsLeftoverDue evmUrns evmIlks I out outIlks).get? name = some value := by
  rw [barkLocalsLeftoverDue, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsDustyDart_get_dart
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsDustyDart evmUrns evmIlks I out outIlks).get? "dart" =
      some (.int (Int.ofNat (barkVatUrnsArtWord out).toNat)) := by
  rw [barkLocalsDustyDart, store_get_self]

theorem barkLocalsDustyDart_get_preserved
    {evmUrns evmIlks : EVM.State} {I : ExecutionEnv} {out outIlks : ByteArray}
    {name : Ident} {value : Value} (hname : ("dart" == name) = false)
    (hget : (barkLocalsLeftoverDue evmUrns evmIlks I out outIlks).get? name = some value) :
    (barkLocalsDustyDart evmUrns evmIlks I out outIlks).get? name = some value := by
  rw [barkLocalsDustyDart, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsPartialDue_get_partialDue
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsPartialDue evmUrns evmIlks I out outIlks).get? "partialDue" =
      some (.int (Int.ofNat
        ((barkSourceDartWord evmUrns evmIlks I out outIlks) *
          barkVatIlksRateWord outIlks).toNat)) := by
  rw [barkLocalsPartialDue, store_get_self]

theorem barkLocalsPartialDue_get_preserved
    {evmUrns evmIlks : EVM.State} {I : ExecutionEnv} {out outIlks : ByteArray}
    {name : Ident} {value : Value} (hname : ("partialDue" == name) = false)
    (hget : (barkLocalsLeftoverDue evmUrns evmIlks I out outIlks).get? name = some value) :
    (barkLocalsPartialDue evmUrns evmIlks I out outIlks).get? name = some value := by
  rw [barkLocalsPartialDue, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsInkDart_get_inkDart (locals : Store) (inkDart : UInt256) :
    (barkLocalsInkDart locals inkDart).get? "inkDart" =
      some (.int (Int.ofNat inkDart.toNat)) := by
  rw [barkLocalsInkDart, store_get_self]

theorem barkLocalsDink_get_dink (locals : Store) (dink : UInt256) :
    (barkLocalsDink locals dink).get? "dink" =
      some (.int (Int.ofNat dink.toNat)) := by
  rw [barkLocalsDink, store_get_self]

theorem barkLocalsGrabRet_get_grabRet (locals : Store) :
    (barkLocalsGrabRet locals).get? "_grabRet" = some .unit := by
  rw [barkLocalsGrabRet, store_get_self]

theorem barkLocalsDue_get_due (locals : Store) (due : UInt256) :
    (barkLocalsDue locals due).get? "due" =
      some (.int (Int.ofNat due.toNat)) := by
  rw [barkLocalsDue, store_get_self]

theorem barkLocalsFessRet_get_fessRet (locals : Store) :
    (barkLocalsFessRet locals).get? "_fessRet" = some .unit := by
  rw [barkLocalsFessRet, store_get_self]

theorem barkLocalsTabBase_get_tabBase (locals : Store) (tabBase : UInt256) :
    (barkLocalsTabBase locals tabBase).get? "tabBase" =
      some (.int (Int.ofNat tabBase.toNat)) := by
  rw [barkLocalsTabBase, store_get_self]

theorem barkLocalsTab_get_tab (locals : Store) (tab : UInt256) :
    (barkLocalsTab locals tab).get? "tab" =
      some (.int (Int.ofNat tab.toNat)) := by
  rw [barkLocalsTab, store_get_self]

theorem barkLocalsDirtNew_get_DirtNew (locals : Store) (dirtNew : UInt256) :
    (barkLocalsDirtNew locals dirtNew).get? "DirtNew" =
      some (.int (Int.ofNat dirtNew.toNat)) := by
  rw [barkLocalsDirtNew, store_get_self]

theorem barkLocalsIlkDirtNew_get_ilkDirtNew (locals : Store) (ilkDirtNew : UInt256) :
    (barkLocalsIlkDirtNew locals ilkDirtNew).get? "ilkDirtNew" =
      some (.int (Int.ofNat ilkDirtNew.toNat)) := by
  rw [barkLocalsIlkDirtNew, store_get_self]

theorem barkLocalsId_get_id (locals : Store) (id : UInt256) :
    (barkLocalsId locals id).get? "id" =
      some (.int (Int.ofNat id.toNat)) := by
  rw [barkLocalsId, store_get_self]

theorem barkLocalsInkDart_get_preserved {locals : Store} {inkDart : UInt256}
    {name : Ident} {value : Value} (hname : ("inkDart" == name) = false)
    (hget : locals.get? name = some value) :
    (barkLocalsInkDart locals inkDart).get? name = some value := by
  rw [barkLocalsInkDart, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsDink_get_preserved {locals : Store} {dink : UInt256}
    {name : Ident} {value : Value} (hname : ("dink" == name) = false)
    (hget : locals.get? name = some value) :
    (barkLocalsDink locals dink).get? name = some value := by
  rw [barkLocalsDink, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsGrabRet_get_preserved {locals : Store} {name : Ident} {value : Value}
    (hname : ("_grabRet" == name) = false) (hget : locals.get? name = some value) :
    (barkLocalsGrabRet locals).get? name = some value := by
  rw [barkLocalsGrabRet, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsDue_get_preserved {locals : Store} {due : UInt256}
    {name : Ident} {value : Value} (hname : ("due" == name) = false)
    (hget : locals.get? name = some value) :
    (barkLocalsDue locals due).get? name = some value := by
  rw [barkLocalsDue, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsFessRet_get_preserved {locals : Store} {name : Ident} {value : Value}
    (hname : ("_fessRet" == name) = false) (hget : locals.get? name = some value) :
    (barkLocalsFessRet locals).get? name = some value := by
  rw [barkLocalsFessRet, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsTabBase_get_preserved {locals : Store} {tabBase : UInt256}
    {name : Ident} {value : Value} (hname : ("tabBase" == name) = false)
    (hget : locals.get? name = some value) :
    (barkLocalsTabBase locals tabBase).get? name = some value := by
  rw [barkLocalsTabBase, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsTab_get_preserved {locals : Store} {tab : UInt256}
    {name : Ident} {value : Value} (hname : ("tab" == name) = false)
    (hget : locals.get? name = some value) :
    (barkLocalsTab locals tab).get? name = some value := by
  rw [barkLocalsTab, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsDirtNew_get_preserved {locals : Store} {dirtNew : UInt256}
    {name : Ident} {value : Value} (hname : ("DirtNew" == name) = false)
    (hget : locals.get? name = some value) :
    (barkLocalsDirtNew locals dirtNew).get? name = some value := by
  rw [barkLocalsDirtNew, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsIlkDirtNew_get_preserved {locals : Store} {ilkDirtNew : UInt256}
    {name : Ident} {value : Value} (hname : ("ilkDirtNew" == name) = false)
    (hget : locals.get? name = some value) :
    (barkLocalsIlkDirtNew locals ilkDirtNew).get? name = some value := by
  rw [barkLocalsIlkDirtNew, store_get_ne _ _ hname]
  exact hget

theorem barkLocalsId_get_preserved {locals : Store} {id : UInt256}
    {name : Ident} {value : Value} (hname : ("id" == name) = false)
    (hget : locals.get? name = some value) :
    (barkLocalsId locals id).get? name = some value := by
  rw [barkLocalsId, store_get_ne _ _ hname]
  exact hget

theorem barkBinaryLocals_get_x (x y : UInt256) :
    (barkBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [barkBinaryLocals, store_get_self]

theorem barkBinaryLocals_get_y (x y : UInt256) :
    (barkBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [barkBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem barkVatWord_canonical (v : DogImmutables) :
    (barkVatWord v).toNat < EVM.addressModulus := by
  change (UInt256.ofNat v.vat.toNat).toNat < EVM.addressModulus
  rw [UInt256.toNat_ofNat_of_lt]
  · exact v.vat.isLt
  · exact lt_of_lt_of_le v.vat.isLt (by decide)

theorem barkVatUrnsSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (barkVatUrnsSelectorMem mem).size = 160 := by
  rw [barkVatUrnsSelectorMem,
    Reasoning.Theory.writeWord_size mem 128 barkVatUrnsSelectorWord
      (by rw [hmem]; native_decide),
    hmem]
  native_decide

theorem barkVatUrnsIlkMem_size {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 96) :
    (barkVatUrnsIlkMem I mem).size = 164 := by
  rw [barkVatUrnsIlkMem,
    Reasoning.Theory.writeWord_size (barkVatUrnsSelectorMem mem) 132 (barkIlkWord I)
      (by rw [barkVatUrnsSelectorMem_size hmem]; native_decide),
    barkVatUrnsSelectorMem_size hmem]
  native_decide

theorem barkVatUrnsCallMem_size {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 96) :
    (barkVatUrnsCallMem I mem).size = 196 := by
  rw [barkVatUrnsCallMem,
    Reasoning.Theory.writeWord_size (barkVatUrnsIlkMem I mem) 164 (barkUrnKey I)
      (by rw [barkVatUrnsIlkMem_size hmem]; native_decide),
    barkVatUrnsIlkMem_size hmem]
  native_decide

theorem barkVatUrnsCallMem_read64 {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (barkVatUrnsCallMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [barkVatUrnsCallMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatUrnsIlkMem I mem) 164 64
      (barkUrnKey I)
      (by rw [barkVatUrnsIlkMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatUrnsIlkMem_size hmem]; decide⟩)]
  rw [barkVatUrnsIlkMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatUrnsSelectorMem mem) 132 64
      (barkIlkWord I)
      (by rw [barkVatUrnsSelectorMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatUrnsSelectorMem_size hmem]; decide⟩)]
  rw [barkVatUrnsSelectorMem,
    Reasoning.Theory.writeWord_read_preserved mem 128 64 barkVatUrnsSelectorWord
      (by rw [hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [hmem]⟩)]
  exact hread64


theorem barkVatUrnsPostCallMem_size_gt64 {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    64 < (barkVatUrnsPostCallMem I mem out).size := by
  unfold barkVatUrnsPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
    umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
  rw [hlen]
  exact barkVatUrnsPostCallWrite_size_gt64 out (barkVatUrnsCallMem I mem) out.size
    (barkVatUrnsCallMem_size hmem) le_rfl

theorem barkVatUrnsPostCallMem_read64 {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    (barkVatUrnsPostCallMem I mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold barkVatUrnsPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
    umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
  rw [hlen]
  change (out.write 0 (barkVatUrnsCallMem I mem) 128 out.size).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact barkVatUrnsCallMem_read64 hmem hread64
  · rw [write_read_below_gen_extend out (barkVatUrnsCallMem I mem)
        128 out.size 64 hzero le_rfl
        (by rw [barkVatUrnsCallMem_size hmem]; omega) (by omega)]
    exact barkVatUrnsCallMem_read64 hmem hread64

theorem barkVatUrnsPostCallMem_mload64 {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatUrnsPostCallMem I mem out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatUrnsPostCallMem I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by
      have hgt := barkVatUrnsPostCallMem_size_gt64 (I := I) hmem hshort hout
      omega)
    (barkVatUrnsPostCallMem_read64 hmem hread64 hshort hout)

theorem barkVatUrnsPostCallMem_size_long {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsPostCallMem I mem out).size = 196 := by
  have hmin :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 := by
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlong hout
  unfold barkVatUrnsPostCallMem
  rw [hmin]
  change (out.write 0 (barkVatUrnsCallMem I mem) 128 64).size = 196
  rw [write_eq_gen out (barkVatUrnsCallMem I mem) 128 64
    (by omega) (by omega) (by rw [barkVatUrnsCallMem_size hmem]; omega)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, barkVatUrnsCallMem_size hmem]
  omega

theorem barkVatUrnsPostCallMem_read64_long {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsPostCallMem I mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hmin :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 := by
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlong hout
  unfold barkVatUrnsPostCallMem
  rw [hmin]
  change (out.write 0 (barkVatUrnsCallMem I mem) 128 64).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write_read_below_gen_extend out (barkVatUrnsCallMem I mem)
    128 64 64 (by omega) (by omega)
    (by rw [barkVatUrnsCallMem_size hmem]; omega) (by omega)]
  exact barkVatUrnsCallMem_read64 hmem hread64

theorem barkVatUrnsPostCallMem_mload64_long {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatUrnsPostCallMem I mem out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatUrnsPostCallMem I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [barkVatUrnsPostCallMem_size_long hmem hlong hout]; decide)
    (barkVatUrnsPostCallMem_read64_long hmem hread64 hlong hout)

theorem barkVatUrnsPostCallMem_read128_long {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsPostCallMem I mem out).readWithPadding 128 32 = out.extract 0 32 := by
  have hmin :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 := by
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlong hout
  unfold barkVatUrnsPostCallMem
  rw [hmin]
  change (out.write 0 (barkVatUrnsCallMem I mem) 128 64).readWithPadding 128 32 =
    out.extract 0 32
  rw [write_eq_gen out (barkVatUrnsCallMem I mem) 128 64
    (by omega) (by omega) (by rw [barkVatUrnsCallMem_size hmem]; omega)]
  have hprefix : ((barkVatUrnsCallMem I mem).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, barkVatUrnsCallMem_size hmem]
    omega
  have hsrc : (out.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  have hheadSize :
      ((barkVatUrnsCallMem I mem).extract 0 128 ++ out.extract 0 64).size = 192 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      128 + 32 ≤
        (((barkVatUrnsCallMem I mem).extract 0 128 ++ out.extract 0 64) ++
          (barkVatUrnsCallMem I mem).extract (128 + 64)
            (barkVatUrnsCallMem I mem).size).size := by
    rw [ByteArray.size_append, hheadSize]
    omega
  rw [readWithPadding_eq_extract _ 128 hreadIn]
  rw [extract_append_left _ _ 128 160 (by rw [hheadSize]; omega)]
  rw [extract_append_right_window _ _ 128 160 (by rw [hprefix]), hprefix]
  rw [show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  norm_num

theorem barkVatUrnsPostCallMem_mload128_long {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (barkVatUrnsPostCallMem I mem out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatUrnsPostCallMem I mem out).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      barkVatUrnsInkWord out := by
  unfold barkVatUrnsInkWord
  rw [if_neg (by
    rw [barkVatUrnsPostCallMem_size_long hmem hlong hout]
    decide)]
  change UInt256.ofNat
      (fromByteArrayBigEndian ((barkVatUrnsPostCallMem I mem out).readWithPadding 128 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  rw [barkVatUrnsPostCallMem_read128_long hmem hlong hout]

theorem barkVatUrnsPostCallMem_read160_long {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsPostCallMem I mem out).readWithPadding 160 32 = out.extract 32 64 := by
  have hmin :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 := by
    exact umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlong hout
  unfold barkVatUrnsPostCallMem
  rw [hmin]
  change (out.write 0 (barkVatUrnsCallMem I mem) 128 64).readWithPadding 160 32 =
    out.extract 32 64
  rw [write_eq_gen out (barkVatUrnsCallMem I mem) 128 64
    (by omega) (by omega) (by rw [barkVatUrnsCallMem_size hmem]; omega)]
  have hprefix : ((barkVatUrnsCallMem I mem).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, barkVatUrnsCallMem_size hmem]
    omega
  have hsrc : (out.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((barkVatUrnsCallMem I mem).extract 0 128 ++ out.extract 0 64).size = 192 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      160 + 32 ≤
        (((barkVatUrnsCallMem I mem).extract 0 128 ++ out.extract 0 64) ++
          (barkVatUrnsCallMem I mem).extract (128 + 64)
            (barkVatUrnsCallMem I mem).size).size := by
    rw [ByteArray.size_append, hmemSize]
    omega
  rw [readWithPadding_eq_extract _ 160 hreadIn]
  rw [extract_append_left _ _ 160 192 (by rw [hmemSize])]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem barkVatUrnsPostCallMem_mload160_long {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (barkVatUrnsPostCallMem I mem out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatUrnsPostCallMem I mem out).readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      barkVatUrnsArtWord out := by
  unfold barkVatUrnsArtWord
  rw [if_neg (by
    rw [barkVatUrnsPostCallMem_size_long hmem hlong hout]
    decide)]
  change UInt256.ofNat
      (fromByteArrayBigEndian ((barkVatUrnsPostCallMem I mem out).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))
  rw [barkVatUrnsPostCallMem_read160_long hmem hlong hout]

theorem barkVatUrnsTupleFreeMem_size {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsTupleFreeMem I mem out).size = 196 := by
  rw [barkVatUrnsTupleFreeMem,
    Reasoning.Theory.writeWord_size (barkVatUrnsPostCallMem I mem out) 64 ⟨256⟩
      (by rw [barkVatUrnsPostCallMem_size_long hmem hlong hout]; native_decide),
    barkVatUrnsPostCallMem_size_long hmem hlong hout]
  native_decide

theorem barkVatUrnsTupleWord0Mem_size {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsTupleWord0Mem I mem out).size = 196 := by
  rw [barkVatUrnsTupleWord0Mem,
    Reasoning.Theory.writeWord_size (barkVatUrnsTupleFreeMem I mem out) 128 ⟨0⟩
      (by rw [barkVatUrnsTupleFreeMem_size hmem hlong hout]; native_decide),
    barkVatUrnsTupleFreeMem_size hmem hlong hout]
  native_decide

theorem barkVatUrnsTupleWord1Mem_size {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsTupleWord1Mem I mem out).size = 196 := by
  rw [barkVatUrnsTupleWord1Mem,
    Reasoning.Theory.writeWord_size (barkVatUrnsTupleWord0Mem I mem out) 160 ⟨0⟩
      (by rw [barkVatUrnsTupleWord0Mem_size hmem hlong hout]; native_decide),
    barkVatUrnsTupleWord0Mem_size hmem hlong hout]
  native_decide

theorem barkVatUrnsTupleWord2Mem_size {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsTupleWord2Mem I mem out).size = 224 := by
  rw [barkVatUrnsTupleWord2Mem,
    Reasoning.Theory.writeWord_size (barkVatUrnsTupleWord1Mem I mem out) 192 ⟨0⟩
      (by rw [barkVatUrnsTupleWord1Mem_size hmem hlong hout]; native_decide),
    barkVatUrnsTupleWord1Mem_size hmem hlong hout]
  native_decide

theorem barkVatUrnsTupleMem_size {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsTupleMem I mem out).size = 256 := by
  rw [barkVatUrnsTupleMem,
    Reasoning.Theory.writeWord_size (barkVatUrnsTupleWord2Mem I mem out) 224 ⟨0⟩
      (by rw [barkVatUrnsTupleWord2Mem_size hmem hlong hout]; native_decide),
    barkVatUrnsTupleWord2Mem_size hmem hlong hout]
  native_decide

theorem barkVatUrnsTupleFreeMem_read64 {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsTupleFreeMem I mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨256⟩ := by
  rw [barkVatUrnsTupleFreeMem,
    Reasoning.Theory.writeWord_read_back (barkVatUrnsPostCallMem I mem out) 64 ⟨256⟩
      (by rw [barkVatUrnsPostCallMem_size_long hmem hlong hout]; native_decide)]

theorem barkVatUrnsTupleMem_read64 {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatUrnsTupleMem I mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨256⟩ := by
  rw [barkVatUrnsTupleMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatUrnsTupleWord2Mem I mem out)
      224 64 ⟨0⟩
      (by rw [barkVatUrnsTupleWord2Mem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatUrnsTupleWord2Mem_size hmem hlong hout]; decide⟩)]
  rw [barkVatUrnsTupleWord2Mem,
    Reasoning.Theory.writeWord_read_preserved (barkVatUrnsTupleWord1Mem I mem out)
      192 64 ⟨0⟩
      (by rw [barkVatUrnsTupleWord1Mem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatUrnsTupleWord1Mem_size hmem hlong hout]; decide⟩)]
  rw [barkVatUrnsTupleWord1Mem,
    Reasoning.Theory.writeWord_read_preserved (barkVatUrnsTupleWord0Mem I mem out)
      160 64 ⟨0⟩
      (by rw [barkVatUrnsTupleWord0Mem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatUrnsTupleWord0Mem_size hmem hlong hout]; decide⟩)]
  rw [barkVatUrnsTupleWord0Mem,
    Reasoning.Theory.writeWord_read_preserved (barkVatUrnsTupleFreeMem I mem out)
      128 64 ⟨0⟩
      (by rw [barkVatUrnsTupleFreeMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatUrnsTupleFreeMem_size hmem hlong hout]; decide⟩)]
  exact barkVatUrnsTupleFreeMem_read64 hmem hlong hout

theorem barkVatUrnsTupleMem_mload64 {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatUrnsTupleMem I mem out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatUrnsTupleMem I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨256⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨256⟩ : UInt256))
    (by rw [barkVatUrnsTupleMem_size hmem hlong hout]; decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
      barkVatUrnsTupleMem_read64 hmem hlong hout)

theorem barkIlkBytes_len32 {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    (barkIlkBytes I).length = 32 := by
  simp [barkIlkBytes, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem barkIlkBytes_eq_toBytesBE {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    barkIlkBytes I = EVM.Word.toBytesBE (barkIlkWord I) := by
  have hlen32 : (barkIlkBytes I).length = 32 :=
    barkIlkBytes_len32 (I := I) hsz100
  have hword : ABI.bytesToWord (barkIlkBytes I) = barkIlkWord I := by
    simpa [barkIlkBytes, barkIlkWord] using
      (decode_word_at_eq_any I.calldata 4 (by omega))
  have hto := toBytesBE_bytesToWord_of_length (bs := barkIlkBytes I) hlen32
  rw [hword] at hto
  exact hto.symm

theorem keyValueToWord_barkIlkKey {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    keyValueToWord (barkIlkKey I) = barkIlkWord I := by
  have hbytes := barkIlkBytes_eq_toBytesBE (I := I) hsz100
  simpa [barkIlkKey, bytes32Width, hbytes] using keyValueToWord_fixedBytes32 (barkIlkWord I)

theorem barkIlksClipSlotFor_eq {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    barkIlksClipSlotFor I = solcMappingSlot ⟨1⟩ (barkIlkWord I) := by
  unfold barkIlksClipSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_barkIlkKey hsz100]

theorem barkIlksChopSlotFor_eq {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    barkIlksChopSlotFor I = solcMappingSlot ⟨1⟩ (barkIlkWord I) + ⟨1⟩ := by
  simp [barkIlksChopSlotFor, barkIlksClipSlotFor_eq hsz100]

theorem barkIlksHoleSlotFor_eq {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    barkIlksHoleSlotFor I = solcMappingSlot ⟨1⟩ (barkIlkWord I) + ⟨2⟩ := by
  simp [barkIlksHoleSlotFor, barkIlksClipSlotFor_eq hsz100]

theorem barkIlksDirtSlotFor_eq {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    barkIlksDirtSlotFor I = solcMappingSlot ⟨1⟩ (barkIlkWord I) + ⟨3⟩ := by
  simp [barkIlksDirtSlotFor, barkIlksClipSlotFor_eq hsz100]

theorem barkIlksClipWord_eq_slotFor {σ : AccountMap} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    barkIlksClipWord σ I = solcAddressSlotWord (barkIlksClipSlotFor I) σ I := by
  simp [barkIlksClipWord, solcAddressSlotWord, solcSlotWordAt, barkIlksSlot,
    barkIlksClipSlotFor_eq hsz100, u256_land_comm]

theorem barkIlksChopWord_eq_slotFor {σ : AccountMap} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    barkIlksChopWord σ I = solcSlotWordAt (barkIlksChopSlotFor I) σ I := by
  simp [barkIlksChopWord, solcSlotWordAt, barkIlksSlot, barkIlksChopSlotFor_eq hsz100]

theorem barkIlksHoleWord_eq_slotFor {σ : AccountMap} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    barkIlksHoleWord σ I = solcSlotWordAt (barkIlksHoleSlotFor I) σ I := by
  simp [barkIlksHoleWord, solcSlotWordAt, barkIlksSlot, barkIlksHoleSlotFor_eq hsz100]

theorem barkIlksDirtWord_eq_slotFor {σ : AccountMap} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    barkIlksDirtWord σ I = solcSlotWordAt (barkIlksDirtSlotFor I) σ I := by
  simp [barkIlksDirtWord, solcSlotWordAt, barkIlksSlot, barkIlksDirtSlotFor_eq hsz100,
    u256_add_comm]

theorem barkUrn_value_masked (I : ExecutionEnv) :
    (.address (barkUrn I) : Value) =
      .address (AccountAddress.ofNat (barkUrnKey I).toNat) := by
  simpa [barkUrn, barkUrnKey, barkUrnWord] using
    (solcAddressValue_masked (calldataWord I.calldata 36))

theorem barkKpr_value_masked (I : ExecutionEnv) :
    (.address (barkKpr I) : Value) =
      .address (AccountAddress.ofNat (barkKprKey I).toNat) := by
  simpa [barkKpr, barkKprKey, barkKprWord] using
    (solcAddressValue_masked (calldataWord I.calldata 68))

theorem barkVatUrnsSelectorWord_extract :
    (UInt256.toByteArray barkVatUrnsSelectorWord).extract 0 4 = vatUrnsSelector := by
  native_decide

theorem barkVatUrnsCallMem_read128_4 {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 96) :
    (barkVatUrnsCallMem I mem).readWithPadding 128 4 = vatUrnsSelector := by
  have hSelectorSize := barkVatUrnsSelectorMem_size (mem := mem) hmem
  have hIlkSize := barkVatUrnsIlkMem_size (I := I) (mem := mem) hmem
  unfold barkVatUrnsCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkUrnKey I)
      (barkVatUrnsIlkMem I mem) 164 128 4
      (by rw [hIlkSize]; omega) (by native_decide) (by omega) (by omega)
      (by rw [hIlkSize]; native_decide)]
  unfold barkVatUrnsIlkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkIlkWord I)
      (barkVatUrnsSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega)
      (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold barkVatUrnsSelectorMem Reasoning.Theory.writeWord
  change (barkVatUrnsSelectorWord.toByteArray.write 0 mem 128 32).readWithPadding
      128 4 = vatUrnsSelector
  rw [toByteArray_write_read_window_of_gap barkVatUrnsSelectorWord mem 128 0 4
      (by omega) (by omega) (by omega)
      (by rw [hmem]; native_decide)]
  exact barkVatUrnsSelectorWord_extract

theorem barkVatUrnsCallMem_read132_32 {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 96) :
    (barkVatUrnsCallMem I mem).readWithPadding 132 32 =
      (barkIlkWord I).toByteArray := by
  have hIlkSize := barkVatUrnsIlkMem_size (I := I) (mem := mem) hmem
  unfold barkVatUrnsCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkUrnKey I)
      (barkVatUrnsIlkMem I mem) 164 132 32
      (by rw [hIlkSize]) (by omega) (by omega) (by omega)
      (by rw [hIlkSize]; native_decide)]
  unfold barkVatUrnsIlkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (barkIlkWord I) (barkVatUrnsSelectorMem mem) 132
      (by rw [barkVatUrnsSelectorMem_size hmem]; native_decide)]

theorem barkVatUrnsCallMem_read164_32 {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 96) :
    (barkVatUrnsCallMem I mem).readWithPadding 164 32 =
      (barkUrnKey I).toByteArray := by
  unfold barkVatUrnsCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (barkUrnKey I) (barkVatUrnsIlkMem I mem) 164
      (by rw [barkVatUrnsIlkMem_size hmem]; native_decide)]

theorem barkVatUrnsCallMem_read128_68 {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 96) :
    (barkVatUrnsCallMem I mem).readWithPadding 128 68 =
      vatUrnsSelector ++ (barkIlkWord I).toByteArray ++ (barkUrnKey I).toByteArray := by
  have hsize : (barkVatUrnsCallMem I mem).size = 196 :=
    barkVatUrnsCallMem_size (I := I) (mem := mem) hmem
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split (barkVatUrnsCallMem I mem) 128 4 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (barkVatUrnsCallMem I mem) 132 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [barkVatUrnsCallMem_read128_4 hmem, barkVatUrnsCallMem_read132_32 hmem,
    barkVatUrnsCallMem_read164_32 hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem barkVatUrnsEncodeWords {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    config.externalABI.encode? "urns"
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] =
      some (vatUrnsSelector ++ (barkIlkWord I).toByteArray ++
        (barkUrnKey I).toByteArray) := by
  have hIlk : ABI.encodeABIValue? bytes32 (.fixedBytes bytes32Width (barkIlkBytes I)) =
      some (EVM.Word.toBytesBE (barkIlkWord I)) := by
    have hbytes := barkIlkBytes_eq_toBytesBE (I := I) hsz100
    have hlen : (EVM.Word.toBytesBE (barkIlkWord I)).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size (barkIlkWord I)
    simp [ABI.encodeABIValue?, hlen, zeroBytes, bytes32, bytes32Width, hbytes]
  have hIlk' :
      ABI.encodeABIValue? (.elem (.bytes bytes32Width))
        (.fixedBytes bytes32Width (barkIlkBytes I)) =
          some (EVM.Word.toBytesBE (barkIlkWord I)) := by
    simpa [bytes32] using hIlk
  have hurn : ABI.encodeABIValue? (.elem .address) (.address (barkUrn I)) =
      some (EVM.Word.toBytesBE (barkUrnKey I)) := by
    rw [barkUrn_value_masked I]
    have hcanon : (barkUrnKey I).toNat < EVM.addressModulus := by
      rw [barkUrnKey, u256_land_comm]
      exact solcAddrMask_result_canonical (barkUrnWord I)
    have haddrToNat :
        (AccountAddress.ofNat (barkUrnKey I).toNat).toNat = (barkUrnKey I).toNat := by
      simp [AccountAddress.ofNat]
      exact Nat.mod_eq_of_lt hcanon
    have hword :
        EVM.word (↑(AccountAddress.ofNat (barkUrnKey I).toNat) : ℕ) = barkUrnKey I := by
      rw [show EVM.word (↑(AccountAddress.ofNat (barkUrnKey I).toNat) : ℕ) =
        UInt256.ofNat (AccountAddress.ofNat (barkUrnKey I).toNat).toNat from rfl,
        haddrToNat, u256_ofNat_toNat]
    simp [ABI.encodeABIValue?, ABI.encodeABIWord?, hword]
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, hIlk', hurn, addr, bytes32]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc, word_toBytesBE_toByteArray_eq_toByteArray]

theorem barkVatUrnsEncode_eq {I : ExecutionEnv} {mem : ByteArray}
    (hsz100 : 100 ≤ I.calldata.size) (hmem : mem.size = 96) :
    config.externalABI.encode? "urns"
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] =
      some ((barkVatUrnsCallMem I mem).readWithPadding 128 68) := by
  rw [barkVatUrnsCallMem_read128_68 hmem]
  exact barkVatUrnsEncodeWords (I := I) hsz100


theorem barkInt256NegArgEncoding (w : UInt256)
    (hw : w.toNat ≤ dogInt256LimitWord.toNat) :
    ABI.encodeABIValue? (.elem (.int int256Int)) (.int (-(Int.ofNat w.toNat))) =
      some (EVM.Word.toBytesBE (UInt256.sub ⟨0⟩ w)) := by
  have hword :
      EVM.wordOfInt (-(Int.ofNat w.toNat)) = UInt256.sub ⟨0⟩ w := by
    simpa using wordOfInt_sub_toUInt256 (⟨0⟩ : UInt256) w
  have hlimit : dogInt256LimitWord.toNat = EVM.twoPow 255 := by
    native_decide
  have hlePow : w.toNat ≤ EVM.twoPow 255 := by
    rw [← hlimit]
    exact hw
  have hcond :
      w.toNat ≤ EVM.twoPow 255 ∧ -↑w.toNat < (↑(EVM.twoPow 255) : Int) := by
    constructor
    · exact hlePow
    · have hpos : 0 < EVM.twoPow 255 := by native_decide
      omega
  simp [int256Int, ABI.encodeABIValue?, ABI.encodeABIWord?]
  rw [if_pos hcond]
  simp only [Option.bind]
  apply congrArg some
  change EVM.Word.toBytesBE (EVM.wordOfInt (-(Int.ofNat w.toNat))) =
    EVM.Word.toBytesBE (UInt256.sub ⟨0⟩ w)
  rw [hword]


theorem barkIlksHashMem_size {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksHashMem I mem out).size = 256 := by
  unfold barkIlksHashMem
  exact twoWordHashMem_size_256 (barkIlkWord I) ⟨1⟩
    (barkVatUrnsTupleMem_size hmem hlong hout)

theorem barkIlksHashMem_read64 {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksHashMem I mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨256⟩ := by
  unfold barkIlksHashMem
  exact twoWordHashMem_read64_256 (barkIlkWord I) ⟨1⟩ ⟨256⟩
    (barkVatUrnsTupleMem_size hmem hlong hout)
    (barkVatUrnsTupleMem_read64 hmem hlong hout)

theorem barkIlksHashMem_mload64 {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkIlksHashMem I mem out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkIlksHashMem I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨256⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨256⟩ : UInt256))
    (by rw [barkIlksHashMem_size hmem hlong hout]; decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
      barkIlksHashMem_read64 hmem hlong hout)

theorem barkIlksHashMem_slot {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((barkIlksHashMem I mem out).readWithPadding 0 64))) =
      barkIlksSlot I := by
  unfold barkIlksHashMem barkIlksSlot
  exact twoWordHashMem_solcMappingSlot_256 ⟨1⟩ (barkIlkWord I)
    (barkVatUrnsTupleMem_size hmem hlong hout)

theorem barkIlksAllocMem_size {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksAllocMem I mem out).size = 256 := by
  rw [barkIlksAllocMem,
    Reasoning.Theory.writeWord_size (barkIlksHashMem I mem out) 64 ⟨384⟩
      (by rw [barkIlksHashMem_size hmem hlong hout]; native_decide),
    barkIlksHashMem_size hmem hlong hout]
  native_decide

theorem barkIlksClipMem_size {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksClipMem σ I mem out).size = 288 := by
  rw [barkIlksClipMem,
    Reasoning.Theory.writeWord_size (barkIlksAllocMem I mem out) 256
      (barkIlksClipWord σ I)
      (by rw [barkIlksAllocMem_size hmem hlong hout]; native_decide),
    barkIlksAllocMem_size hmem hlong hout]
  native_decide

theorem barkIlksChopMem_size {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksChopMem σ I mem out).size = 320 := by
  rw [barkIlksChopMem,
    Reasoning.Theory.writeWord_size (barkIlksClipMem σ I mem out) 288
      (barkIlksChopWord σ I)
      (by rw [barkIlksClipMem_size hmem hlong hout]; native_decide),
    barkIlksClipMem_size hmem hlong hout]
  native_decide

theorem barkIlksHoleMem_size {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksHoleMem σ I mem out).size = 352 := by
  rw [barkIlksHoleMem,
    Reasoning.Theory.writeWord_size (barkIlksChopMem σ I mem out) 320
      (barkIlksHoleWord σ I)
      (by rw [barkIlksChopMem_size hmem hlong hout]; native_decide),
    barkIlksChopMem_size hmem hlong hout]
  native_decide

theorem barkIlksMem_size {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksMem σ I mem out).size = 384 := by
  rw [barkIlksMem,
    Reasoning.Theory.writeWord_size (barkIlksHoleMem σ I mem out) 352
      (barkIlksDirtWord σ I)
      (by rw [barkIlksHoleMem_size hmem hlong hout]; native_decide),
    barkIlksHoleMem_size hmem hlong hout]
  native_decide

theorem barkIlksAllocMem_read64 {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksAllocMem I mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  rw [barkIlksAllocMem,
    Reasoning.Theory.writeWord_read_back (barkIlksHashMem I mem out) 64 ⟨384⟩
      (by rw [barkIlksHashMem_size hmem hlong hout]; native_decide)]

theorem barkIlksMem_read64 {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksMem σ I mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  rw [barkIlksMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksHoleMem σ I mem out) 352 64
      (barkIlksDirtWord σ I)
      (by rw [barkIlksHoleMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksHoleMem_size hmem hlong hout]; decide⟩)]
  rw [barkIlksHoleMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksChopMem σ I mem out) 320 64
      (barkIlksHoleWord σ I)
      (by rw [barkIlksChopMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksChopMem_size hmem hlong hout]; decide⟩)]
  rw [barkIlksChopMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksClipMem σ I mem out) 288 64
      (barkIlksChopWord σ I)
      (by rw [barkIlksClipMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksClipMem_size hmem hlong hout]; decide⟩)]
  rw [barkIlksClipMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksAllocMem I mem out) 256 64
      (barkIlksClipWord σ I)
      (by rw [barkIlksAllocMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksAllocMem_size hmem hlong hout]; decide⟩)]
  exact barkIlksAllocMem_read64 hmem hlong hout

theorem barkIlksMem_mload64 {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkIlksMem σ I mem out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkIlksMem σ I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkIlksMem_size hmem hlong hout]; decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
      barkIlksMem_read64 hmem hlong hout)

theorem barkIlksMem_read256 {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksMem σ I mem out).readWithPadding 256 32 =
      UInt256.toByteArray (barkIlksClipWord σ I) := by
  rw [barkIlksMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksHoleMem σ I mem out) 352 256
      (barkIlksDirtWord σ I)
      (by rw [barkIlksHoleMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksHoleMem_size hmem hlong hout]; decide⟩)]
  rw [barkIlksHoleMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksChopMem σ I mem out) 320 256
      (barkIlksHoleWord σ I)
      (by rw [barkIlksChopMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksChopMem_size hmem hlong hout]; decide⟩)]
  rw [barkIlksChopMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksClipMem σ I mem out) 288 256
      (barkIlksChopWord σ I)
      (by rw [barkIlksClipMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksClipMem_size hmem hlong hout]⟩)]
  rw [barkIlksClipMem,
    Reasoning.Theory.writeWord_read_back (barkIlksAllocMem I mem out) 256
      (barkIlksClipWord σ I)
      (by rw [barkIlksAllocMem_size hmem hlong hout]; native_decide)]

theorem barkIlksMem_read288 {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksMem σ I mem out).readWithPadding 288 32 =
      UInt256.toByteArray (barkIlksChopWord σ I) := by
  rw [barkIlksMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksHoleMem σ I mem out) 352 288
      (barkIlksDirtWord σ I)
      (by rw [barkIlksHoleMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksHoleMem_size hmem hlong hout]; decide⟩)]
  rw [barkIlksHoleMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksChopMem σ I mem out) 320 288
      (barkIlksHoleWord σ I)
      (by rw [barkIlksChopMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksChopMem_size hmem hlong hout]⟩)]
  rw [barkIlksChopMem,
    Reasoning.Theory.writeWord_read_back (barkIlksClipMem σ I mem out) 288
      (barkIlksChopWord σ I)
      (by rw [barkIlksClipMem_size hmem hlong hout]; native_decide)]

theorem barkIlksMem_read320 {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksMem σ I mem out).readWithPadding 320 32 =
      UInt256.toByteArray (barkIlksHoleWord σ I) := by
  rw [barkIlksMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksHoleMem σ I mem out) 352 320
      (barkIlksDirtWord σ I)
      (by rw [barkIlksHoleMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksHoleMem_size hmem hlong hout]⟩)]
  rw [barkIlksHoleMem,
    Reasoning.Theory.writeWord_read_back (barkIlksChopMem σ I mem out) 320
      (barkIlksHoleWord σ I)
      (by rw [barkIlksChopMem_size hmem hlong hout]; native_decide)]

theorem barkIlksMem_read352 {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkIlksMem σ I mem out).readWithPadding 352 32 =
      UInt256.toByteArray (barkIlksDirtWord σ I) := by
  rw [barkIlksMem,
    Reasoning.Theory.writeWord_read_back (barkIlksHoleMem σ I mem out) 352
      (barkIlksDirtWord σ I)
      (by rw [barkIlksHoleMem_size hmem hlong hout]; native_decide)]

theorem barkVatIlksSelectorMem_size {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksSelectorMem σ I mem out).size = 416 := by
  rw [barkVatIlksSelectorMem,
    Reasoning.Theory.writeWord_size (barkIlksMem σ I mem out) 384 barkVatIlksSelectorWord
      (by rw [barkIlksMem_size hmem hlong hout]; native_decide),
    barkIlksMem_size hmem hlong hout]
  native_decide

theorem barkVatIlksCallMem_size {σ : AccountMap} {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksCallMem σ I mem out).size = 420 := by
  rw [barkVatIlksCallMem,
    Reasoning.Theory.writeWord_size (barkVatIlksSelectorMem σ I mem out) 388
      (barkIlkWord I)
      (by rw [barkVatIlksSelectorMem_size hmem hlong hout]; native_decide),
    barkVatIlksSelectorMem_size hmem hlong hout]
  native_decide

theorem barkVatIlksSelectorMem_read64 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksSelectorMem σ I mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  rw [barkVatIlksSelectorMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksMem σ I mem out) 384 64
      barkVatIlksSelectorWord
      (by rw [barkIlksMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksMem_size hmem hlong hout]; decide⟩)]
  exact barkIlksMem_read64 hmem hlong hout

theorem barkVatIlksSelectorMem_read256 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksSelectorMem σ I mem out).readWithPadding 256 32 =
      UInt256.toByteArray (barkIlksClipWord σ I) := by
  rw [barkVatIlksSelectorMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksMem σ I mem out) 384 256
      barkVatIlksSelectorWord
      (by rw [barkIlksMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksMem_size hmem hlong hout]; decide⟩)]
  exact barkIlksMem_read256 hmem hlong hout

theorem barkVatIlksSelectorMem_read288 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksSelectorMem σ I mem out).readWithPadding 288 32 =
      UInt256.toByteArray (barkIlksChopWord σ I) := by
  rw [barkVatIlksSelectorMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksMem σ I mem out) 384 288
      barkVatIlksSelectorWord
      (by rw [barkIlksMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksMem_size hmem hlong hout]; decide⟩)]
  exact barkIlksMem_read288 hmem hlong hout

theorem barkVatIlksSelectorMem_read320 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksSelectorMem σ I mem out).readWithPadding 320 32 =
      UInt256.toByteArray (barkIlksHoleWord σ I) := by
  rw [barkVatIlksSelectorMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksMem σ I mem out) 384 320
      barkVatIlksSelectorWord
      (by rw [barkIlksMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksMem_size hmem hlong hout]; decide⟩)]
  exact barkIlksMem_read320 hmem hlong hout

theorem barkVatIlksSelectorMem_read352 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksSelectorMem σ I mem out).readWithPadding 352 32 =
      UInt256.toByteArray (barkIlksDirtWord σ I) := by
  rw [barkVatIlksSelectorMem,
    Reasoning.Theory.writeWord_read_preserved (barkIlksMem σ I mem out) 384 352
      barkVatIlksSelectorWord
      (by rw [barkIlksMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkIlksMem_size hmem hlong hout]⟩)]
  exact barkIlksMem_read352 hmem hlong hout

theorem barkVatIlksCallMem_read64 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksCallMem σ I mem out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  rw [barkVatIlksCallMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatIlksSelectorMem σ I mem out)
      388 64 (barkIlkWord I)
      (by rw [barkVatIlksSelectorMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatIlksSelectorMem_size hmem hlong hout]; decide⟩)]
  exact barkVatIlksSelectorMem_read64 hmem hlong hout

theorem barkVatIlksCallMem_read256 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksCallMem σ I mem out).readWithPadding 256 32 =
      UInt256.toByteArray (barkIlksClipWord σ I) := by
  rw [barkVatIlksCallMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatIlksSelectorMem σ I mem out)
      388 256 (barkIlkWord I)
      (by rw [barkVatIlksSelectorMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatIlksSelectorMem_size hmem hlong hout]; decide⟩)]
  exact barkVatIlksSelectorMem_read256 hmem hlong hout

theorem barkVatIlksCallMem_read288 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksCallMem σ I mem out).readWithPadding 288 32 =
      UInt256.toByteArray (barkIlksChopWord σ I) := by
  rw [barkVatIlksCallMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatIlksSelectorMem σ I mem out)
      388 288 (barkIlkWord I)
      (by rw [barkVatIlksSelectorMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatIlksSelectorMem_size hmem hlong hout]; decide⟩)]
  exact barkVatIlksSelectorMem_read288 hmem hlong hout

theorem barkVatIlksCallMem_read320 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksCallMem σ I mem out).readWithPadding 320 32 =
      UInt256.toByteArray (barkIlksHoleWord σ I) := by
  rw [barkVatIlksCallMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatIlksSelectorMem σ I mem out)
      388 320 (barkIlkWord I)
      (by rw [barkVatIlksSelectorMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatIlksSelectorMem_size hmem hlong hout]; decide⟩)]
  exact barkVatIlksSelectorMem_read320 hmem hlong hout

theorem barkVatIlksCallMem_read352 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksCallMem σ I mem out).readWithPadding 352 32 =
      UInt256.toByteArray (barkIlksDirtWord σ I) := by
  rw [barkVatIlksCallMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatIlksSelectorMem σ I mem out)
      388 352 (barkIlkWord I)
      (by rw [barkVatIlksSelectorMem_size hmem hlong hout]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatIlksSelectorMem_size hmem hlong hout]; decide⟩)]
  exact barkVatIlksSelectorMem_read352 hmem hlong hout

theorem barkVatIlksCallMem_mload64 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatIlksCallMem σ I mem out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksCallMem σ I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
      barkVatIlksCallMem_read64 hmem hlong hout)

theorem barkVatIlksPostCallMem_size_gt64 {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hshort : outIlks.size < 160) (houtIlks : outIlks.size < UInt256.size) :
    64 < (barkVatIlksPostCallMem σ I mem out outIlks).size := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = outIlks.size := by
    exact umin_ofNat_right_toNat_of_lt (c := 160) (n := outIlks.size)
      (by decide) hshort houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  by_cases hzero : outIlks.size = 0
  · rw [hzero, byteArray_write_len_zero, barkVatIlksCallMem_size hmem hlong hout]
    omega
  · change 64 < (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384
      outIlks.size).size
    by_cases hfit : 384 + outIlks.size ≤ (barkVatIlksCallMem σ I mem out).size
    · rw [write_eq_gen outIlks (barkVatIlksCallMem σ I mem out) 384 outIlks.size
        hzero le_rfl hfit,
        ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract,
        barkVatIlksCallMem_size hmem hlong hout]
      omega
    · rw [write_eq_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384 outIlks.size
        hzero le_rfl (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega)
        (by omega),
        ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        barkVatIlksCallMem_size hmem hlong hout]
      omega

theorem barkVatIlksPostCallMem_read64 {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hshort : outIlks.size < 160) (houtIlks : outIlks.size < UInt256.size) :
    (barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = outIlks.size := by
    exact umin_ofNat_right_toNat_of_lt (c := 160) (n := outIlks.size)
      (by decide) hshort houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  by_cases hzero : outIlks.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact barkVatIlksCallMem_read64 hmem hlong hout
  · change (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384
      outIlks.size).readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩
    rw [write_read_below_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384
      outIlks.size 64 hzero le_rfl
      (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega) (by omega)]
    exact barkVatIlksCallMem_read64 hmem hlong hout

theorem barkVatIlksPostCallMem_mload64 {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hshort : outIlks.size < 160) (houtIlks : outIlks.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by
      have hgt := barkVatIlksPostCallMem_size_gt64 (σ := σ) (I := I) hmem hlong
        hout hshort houtIlks
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hgt)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
      barkVatIlksPostCallMem_read64 hmem hlong hout hshort houtIlks)

theorem barkVatIlksPostCallMem_size_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (barkVatIlksPostCallMem σ I mem out outIlks).size = 544 := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := outIlks.size)
      (by decide) hlongIlks houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  change (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384 160).size = 544
  rw [write_eq_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384 160
    (by omega) (by omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega),
    ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    barkVatIlksCallMem_size hmem hlong hout]
  omega

theorem barkVatIlksPostCallMem_read64_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := outIlks.size)
      (by decide) hlongIlks houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  change (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384 160).readWithPadding
      64 32 = UInt256.toByteArray ⟨384⟩
  rw [write_read_below_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384 160
    64 (by omega) (by omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega) (by omega)]
  exact barkVatIlksCallMem_read64 hmem hlong hout

theorem barkVatIlksPostCallMem_mload64_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]; decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
      barkVatIlksPostCallMem_read64_long hmem hlong hout hlongIlks houtIlks)

theorem barkVatIlksPostCallMem_read256_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 256 32 =
      UInt256.toByteArray (barkIlksClipWord σ I) := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := outIlks.size)
      (by decide) hlongIlks houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  change (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384 160).readWithPadding
      256 32 = UInt256.toByteArray (barkIlksClipWord σ I)
  rw [write_read_below_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384 160
    256 (by omega) (by omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega) (by omega)]
  exact barkVatIlksCallMem_read256 hmem hlong hout

theorem barkVatIlksPostCallMem_mload256_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (if (⟨256⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨256⟩ : UInt256).toNat 32))) =
      barkIlksClipWord σ I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨256⟩ : UInt256))
    (v := barkIlksClipWord σ I)
    (by
      rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]
      native_decide)
    (by simpa [show (⟨256⟩ : UInt256).toNat = 256 by native_decide] using
      barkVatIlksPostCallMem_read256_long hmem hlong hout hlongIlks houtIlks)

theorem barkVatIlksPostCallMem_read288_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 288 32 =
      UInt256.toByteArray (barkIlksChopWord σ I) := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := outIlks.size)
      (by decide) hlongIlks houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  change (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384 160).readWithPadding
      288 32 = UInt256.toByteArray (barkIlksChopWord σ I)
  rw [write_read_below_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384 160
    288 (by omega) (by omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega) (by omega)]
  exact barkVatIlksCallMem_read288 hmem hlong hout

theorem barkVatIlksPostCallMem_mload288_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (if (⟨288⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨288⟩ : UInt256).toNat 32))) =
      barkIlksChopWord σ I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨288⟩ : UInt256))
    (v := barkIlksChopWord σ I)
    (by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]; decide)
    (by simpa [show (⟨288⟩ : UInt256).toNat = 288 by native_decide] using
      barkVatIlksPostCallMem_read288_long hmem hlong hout hlongIlks houtIlks)

theorem barkVatIlksPostCallMem_read320_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 320 32 =
      UInt256.toByteArray (barkIlksHoleWord σ I) := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := outIlks.size)
      (by decide) hlongIlks houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  change (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384 160).readWithPadding
      320 32 = UInt256.toByteArray (barkIlksHoleWord σ I)
  rw [write_read_below_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384 160
    320 (by omega) (by omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega) (by omega)]
  exact barkVatIlksCallMem_read320 hmem hlong hout

theorem barkVatIlksPostCallMem_mload320_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (if (⟨320⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨320⟩ : UInt256).toNat 32))) =
      barkIlksHoleWord σ I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨320⟩ : UInt256))
    (v := barkIlksHoleWord σ I)
    (by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]; decide)
    (by simpa [show (⟨320⟩ : UInt256).toNat = 320 by native_decide] using
      barkVatIlksPostCallMem_read320_long hmem hlong hout hlongIlks houtIlks)

theorem barkVatIlksPostCallMem_read352_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 352 32 =
      UInt256.toByteArray (barkIlksDirtWord σ I) := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := outIlks.size)
      (by decide) hlongIlks houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  change (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384 160).readWithPadding
      352 32 = UInt256.toByteArray (barkIlksDirtWord σ I)
  rw [write_read_below_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384 160
    352 (by omega) (by omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega) (by omega)]
  exact barkVatIlksCallMem_read352 hmem hlong hout

theorem barkVatIlksPostCallMem_mload352_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (if (⟨352⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨352⟩ : UInt256).toNat 32))) =
      barkIlksDirtWord σ I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨352⟩ : UInt256))
    (v := barkIlksDirtWord σ I)
    (by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]; decide)
    (by simpa [show (⟨352⟩ : UInt256).toNat = 352 by native_decide] using
      barkVatIlksPostCallMem_read352_long hmem hlong hout hlongIlks houtIlks)

theorem barkVatIlksPostCallMem_read416_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 416 32 =
      outIlks.extract 32 64 := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := outIlks.size)
      (by decide) hlongIlks houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  change (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384 160).readWithPadding
      416 32 = outIlks.extract 32 64
  rw [write_eq_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384 160
    (by omega) (by omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega)]
  have hprefix : ((barkVatIlksCallMem σ I mem out).extract 0 384).size = 384 := by
    rw [ByteArray.size_extract, barkVatIlksCallMem_size hmem hlong hout]
    omega
  have hsrc : (outIlks.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  have htotal :
      ((barkVatIlksCallMem σ I mem out).extract 0 384 ++
        outIlks.extract 0 160).size = 544 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      416 + 32 ≤
        ((barkVatIlksCallMem σ I mem out).extract 0 384 ++
          outIlks.extract 0 160).size := by
    rw [htotal]
    omega
  rw [readWithPadding_eq_extract _ 416 hreadIn]
  rw [extract_append_right_window _ _ 416 448 (by rw [hprefix]; omega), hprefix]
  rw [show 416 - 384 = 32 by omega, show 448 - 384 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem barkVatIlksPostCallMem_mload416_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (if (⟨416⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨416⟩ : UInt256).toNat 32))) =
      barkVatIlksRateWord outIlks := by
  unfold barkVatIlksRateWord
  rw [if_neg (by
    rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]
    decide)]
  change UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 416 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (outIlks.extract 32 64))
  rw [barkVatIlksPostCallMem_read416_long hmem hlong hout hlongIlks houtIlks]

theorem barkVatIlksPostCallMem_read448_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 448 32 =
      outIlks.extract 64 96 := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := outIlks.size)
      (by decide) hlongIlks houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  change (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384 160).readWithPadding
      448 32 = outIlks.extract 64 96
  rw [write_eq_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384 160
    (by omega) (by omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega)]
  have hprefix : ((barkVatIlksCallMem σ I mem out).extract 0 384).size = 384 := by
    rw [ByteArray.size_extract, barkVatIlksCallMem_size hmem hlong hout]
    omega
  have hsrc : (outIlks.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  have htotal :
      ((barkVatIlksCallMem σ I mem out).extract 0 384 ++
        outIlks.extract 0 160).size = 544 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      448 + 32 ≤
        ((barkVatIlksCallMem σ I mem out).extract 0 384 ++
          outIlks.extract 0 160).size := by
    rw [htotal]
    omega
  rw [readWithPadding_eq_extract _ 448 hreadIn]
  rw [extract_append_right_window _ _ 448 480 (by rw [hprefix]; omega), hprefix]
  rw [show 448 - 384 = 64 by omega, show 480 - 384 = 96 by omega]
  rw [extract_extract_BA]
  norm_num

theorem barkVatIlksPostCallMem_mload448_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (if (⟨448⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨448⟩ : UInt256).toNat 32))) =
      barkVatIlksSpotWord outIlks := by
  unfold barkVatIlksSpotWord
  have hnot :
      ¬ ((⟨448⟩ : UInt256).toNat ≥
        (barkVatIlksPostCallMem σ I mem out outIlks).size) := by
    rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]
    decide
  rw [if_neg hnot]
  change UInt256.ofNat
    (fromByteArrayBigEndian
      ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 448 32)) =
      UInt256.ofNat (fromByteArrayBigEndian (outIlks.extract 64 96))
  rw [barkVatIlksPostCallMem_read448_long hmem hlong hout hlongIlks houtIlks]

theorem barkVatIlksPostCallMem_read512_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 512 32 =
      outIlks.extract 128 160 := by
  have hmin :
      (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat = 160 := by
    exact umin_ofNat_right_toNat_of_ge (c := 160) (n := outIlks.size)
      (by decide) hlongIlks houtIlks
  unfold barkVatIlksPostCallMem
  rw [hmin]
  change (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384 160).readWithPadding
      512 32 = outIlks.extract 128 160
  rw [write_eq_gen_extend outIlks (barkVatIlksCallMem σ I mem out) 384 160
    (by omega) (by omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega)
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; omega)]
  have hprefix : ((barkVatIlksCallMem σ I mem out).extract 0 384).size = 384 := by
    rw [ByteArray.size_extract, barkVatIlksCallMem_size hmem hlong hout]
    omega
  have hsrc : (outIlks.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  have htotal :
      ((barkVatIlksCallMem σ I mem out).extract 0 384 ++
        outIlks.extract 0 160).size = 544 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      512 + 32 ≤
        ((barkVatIlksCallMem σ I mem out).extract 0 384 ++
          outIlks.extract 0 160).size := by
    rw [htotal]
  rw [readWithPadding_eq_extract _ 512 hreadIn]
  rw [extract_append_right_window _ _ 512 544 (by rw [hprefix]; omega), hprefix]
  rw [show 512 - 384 = 128 by omega, show 544 - 384 = 160 by omega]
  rw [extract_extract_BA]
  norm_num

theorem barkVatIlksPostCallMem_mload512_long {σ : AccountMap} {I : ExecutionEnv}
    {mem out outIlks : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size) :
    (if (⟨512⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨512⟩ : UInt256).toNat 32))) =
      barkVatIlksDustWord outIlks := by
  unfold barkVatIlksDustWord
  have hnot :
      ¬ ((⟨512⟩ : UInt256).toNat ≥
        (barkVatIlksPostCallMem σ I mem out outIlks).size) := by
    rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]
    decide
  rw [if_neg hnot]
  change UInt256.ofNat
    (fromByteArrayBigEndian
      ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 512 32)) =
      UInt256.ofNat (fromByteArrayBigEndian (outIlks.extract 128 160))
  rw [barkVatIlksPostCallMem_read512_long hmem hlong hout hlongIlks houtIlks]

theorem barkVatGrabSelectorMem_size {mem : ByteArray} (hmem : mem.size = 544) :
    (barkVatGrabSelectorMem mem).size = 544 := by
  rw [barkVatGrabSelectorMem,
    Reasoning.Theory.writeWord_size mem 384 barkVatGrabSelectorShifted
      (by rw [hmem]; native_decide),
    hmem]
  native_decide

theorem barkVatGrabIlkMem_size {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 544) :
    (barkVatGrabIlkMem I mem).size = 544 := by
  rw [barkVatGrabIlkMem,
    Reasoning.Theory.writeWord_size (barkVatGrabSelectorMem mem) 388 (barkIlkWord I)
      (by rw [barkVatGrabSelectorMem_size hmem]; native_decide),
    barkVatGrabSelectorMem_size hmem]
  native_decide

theorem barkVatGrabUrnMem_size {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 544) :
    (barkVatGrabUrnMem I mem).size = 544 := by
  rw [barkVatGrabUrnMem,
    Reasoning.Theory.writeWord_size (barkVatGrabIlkMem I mem) 420 (barkUrnKey I)
      (by rw [barkVatGrabIlkMem_size hmem]; native_decide),
    barkVatGrabIlkMem_size hmem]
  native_decide

theorem barkVatGrabClipMem_size {σMem : AccountMap} {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 544) :
    (barkVatGrabClipMem σMem I mem).size = 544 := by
  rw [barkVatGrabClipMem,
    Reasoning.Theory.writeWord_size (barkVatGrabUrnMem I mem) 452
      (barkIlksClipWord σMem I)
      (by rw [barkVatGrabUrnMem_size hmem]; native_decide),
    barkVatGrabUrnMem_size hmem]
  native_decide

theorem barkVatGrabVowMem_size {σ σMem : AccountMap} {I : ExecutionEnv} {mem : ByteArray}
    (hmem : mem.size = 544) :
    (barkVatGrabVowMem σ σMem I mem).size = 544 := by
  rw [barkVatGrabVowMem,
    Reasoning.Theory.writeWord_size (barkVatGrabClipMem σMem I mem) 484 (barkVowWord σ I)
      (by rw [barkVatGrabClipMem_size hmem]; native_decide),
    barkVatGrabClipMem_size hmem]
  native_decide

theorem barkVatGrabDinkMem_size {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabDinkMem σ σMem I mem dink).size = 548 := by
  rw [barkVatGrabDinkMem,
    Reasoning.Theory.writeWord_size (barkVatGrabVowMem σ σMem I mem) 516
      (UInt256.sub ⟨0⟩ dink)
      (by rw [barkVatGrabVowMem_size hmem]; native_decide),
    barkVatGrabVowMem_size hmem]
  native_decide

theorem barkVatGrabCallMem_size {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabCallMem σ σMem I mem dink dart).size = 580 := by
  rw [barkVatGrabCallMem,
    Reasoning.Theory.writeWord_size (barkVatGrabDinkMem σ σMem I mem dink) 548
      (UInt256.sub ⟨0⟩ dart)
      (by rw [barkVatGrabDinkMem_size hmem]; native_decide),
    barkVatGrabDinkMem_size hmem]
  native_decide

theorem barkVatGrabCallMem_read64 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  rw [barkVatGrabCallMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabDinkMem σ σMem I mem dink)
      548 64 (UInt256.sub ⟨0⟩ dart)
      (by rw [barkVatGrabDinkMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabDinkMem_size hmem]; decide⟩)]
  rw [barkVatGrabDinkMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabVowMem σ σMem I mem) 516 64
      (UInt256.sub ⟨0⟩ dink)
      (by rw [barkVatGrabVowMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabVowMem_size hmem]; decide⟩)]
  rw [barkVatGrabVowMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabClipMem σMem I mem) 484 64
      (barkVowWord σ I)
      (by rw [barkVatGrabClipMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabClipMem_size hmem]; decide⟩)]
  rw [barkVatGrabClipMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabUrnMem I mem) 452 64
      (barkIlksClipWord σMem I)
      (by rw [barkVatGrabUrnMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabUrnMem_size hmem]; decide⟩)]
  rw [barkVatGrabUrnMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabIlkMem I mem) 420 64
      (barkUrnKey I)
      (by rw [barkVatGrabIlkMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabIlkMem_size hmem]; decide⟩)]
  rw [barkVatGrabIlkMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabSelectorMem mem) 388 64
      (barkIlkWord I)
      (by rw [barkVatGrabSelectorMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabSelectorMem_size hmem]; decide⟩)]
  rw [barkVatGrabSelectorMem,
    Reasoning.Theory.writeWord_read_preserved mem 384 64 barkVatGrabSelectorShifted
      (by rw [hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  exact hread64

theorem barkVatGrabCallMem_mload64 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatGrabCallMem σ σMem I mem dink dart).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkVatGrabCallMem_size hmem]; decide)
    (by
      have hread := barkVatGrabCallMem_read64 (σ := σ) (σMem := σMem) (I := I)
        (mem := mem) (dink := dink) (dart := dart) hmem hread64
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread)

theorem barkVatGrabCallMem_read256 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart word : UInt256}
    (hmem : mem.size = 544)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray word) :
    (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 256 32 =
      UInt256.toByteArray word := by
  rw [barkVatGrabCallMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabDinkMem σ σMem I mem dink)
      548 256 (UInt256.sub ⟨0⟩ dart)
      (by rw [barkVatGrabDinkMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabDinkMem_size hmem]; decide⟩)]
  rw [barkVatGrabDinkMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabVowMem σ σMem I mem) 516 256
      (UInt256.sub ⟨0⟩ dink)
      (by rw [barkVatGrabVowMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabVowMem_size hmem]; decide⟩)]
  rw [barkVatGrabVowMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabClipMem σMem I mem) 484 256
      (barkVowWord σ I)
      (by rw [barkVatGrabClipMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabClipMem_size hmem]; decide⟩)]
  rw [barkVatGrabClipMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabUrnMem I mem) 452 256
      (barkIlksClipWord σMem I)
      (by rw [barkVatGrabUrnMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabUrnMem_size hmem]; decide⟩)]
  rw [barkVatGrabUrnMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabIlkMem I mem) 420 256
      (barkUrnKey I)
      (by rw [barkVatGrabIlkMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabIlkMem_size hmem]; decide⟩)]
  rw [barkVatGrabIlkMem,
    Reasoning.Theory.writeWord_read_preserved (barkVatGrabSelectorMem mem) 388 256
      (barkIlkWord I)
      (by rw [barkVatGrabSelectorMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVatGrabSelectorMem_size hmem]; decide⟩)]
  rw [barkVatGrabSelectorMem,
    Reasoning.Theory.writeWord_read_preserved mem 384 256 barkVatGrabSelectorShifted
      (by rw [hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  exact hread256

theorem barkVatGrabCallMem_mload288 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart milkChop : UInt256}
    (hmem : mem.size = 544)
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (mem.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        milkChop) :
    (if (⟨288⟩ : UInt256).toNat ≥ (barkVatGrabCallMem σ σMem I mem dink dart).size then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding
          (⟨288⟩ : UInt256).toNat 32))) =
      milkChop := by
  have hread :
      (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 288 32 =
        mem.readWithPadding 288 32 := by
    rw [barkVatGrabCallMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabDinkMem σ σMem I mem dink)
        548 288 (UInt256.sub ⟨0⟩ dart)
        (by rw [barkVatGrabDinkMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabDinkMem_size hmem]; decide⟩)]
    rw [barkVatGrabDinkMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabVowMem σ σMem I mem) 516 288
        (UInt256.sub ⟨0⟩ dink)
        (by rw [barkVatGrabVowMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabVowMem_size hmem]; decide⟩)]
    rw [barkVatGrabVowMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabClipMem σMem I mem) 484 288
        (barkVowWord σ I)
        (by rw [barkVatGrabClipMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabClipMem_size hmem]; decide⟩)]
    rw [barkVatGrabClipMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabUrnMem I mem) 452 288
        (barkIlksClipWord σMem I)
        (by rw [barkVatGrabUrnMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabUrnMem_size hmem]; decide⟩)]
    rw [barkVatGrabUrnMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabIlkMem I mem) 420 288
        (barkUrnKey I)
        (by rw [barkVatGrabIlkMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabIlkMem_size hmem]; decide⟩)]
    rw [barkVatGrabIlkMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabSelectorMem mem) 388 288
        (barkIlkWord I)
        (by rw [barkVatGrabSelectorMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabSelectorMem_size hmem]; decide⟩)]
    rw [barkVatGrabSelectorMem,
      Reasoning.Theory.writeWord_read_preserved mem 384 288 barkVatGrabSelectorShifted
        (by rw [hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  simpa [barkVatGrabCallMem_size hmem, hmem,
    show (⟨288⟩ : UInt256).toNat = 288 by native_decide, hread] using hmload288

theorem barkVatGrabPostCallMem_eq {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray} {dink dart : UInt256} :
    barkVatGrabPostCallMem σ σMem I mem out dink dart =
      barkVatGrabCallMem σ σMem I mem dink dart := by
  unfold barkVatGrabPostCallMem barkVatGrabOutSize
  change out.write 0 (barkVatGrabCallMem σ σMem I mem dink dart) 384 0 =
    barkVatGrabCallMem σ σMem I mem dink dart
  rw [byteArray_write_len_zero]

theorem barkVatGrabPostCallMem_size {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray} {dink dart : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabPostCallMem σ σMem I mem out dink dart).size = 580 := by
  rw [barkVatGrabPostCallMem_eq, barkVatGrabCallMem_size hmem]

theorem barkVatGrabPostCallMem_read64 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray} {dink dart : UInt256}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (barkVatGrabPostCallMem σ σMem I mem out dink dart).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  rw [barkVatGrabPostCallMem_eq]
  exact barkVatGrabCallMem_read64 hmem hread64

theorem barkVatGrabPostCallMem_read256 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray} {dink dart word : UInt256}
    (hmem : mem.size = 544)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray word) :
    (barkVatGrabPostCallMem σ σMem I mem out dink dart).readWithPadding 256 32 =
      UInt256.toByteArray word := by
  rw [barkVatGrabPostCallMem_eq]
  exact barkVatGrabCallMem_read256 hmem hread256

theorem barkVatGrabPostCallMem_mload288 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray} {dink dart milkChop : UInt256}
    (hmem : mem.size = 544)
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (mem.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        milkChop) :
    (if (⟨288⟩ : UInt256).toNat ≥
          (barkVatGrabPostCallMem σ σMem I mem out dink dart).size then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVatGrabPostCallMem σ σMem I mem out dink dart).readWithPadding
          (⟨288⟩ : UInt256).toNat 32))) =
      milkChop := by
  simpa [barkVatGrabPostCallMem_eq] using
    (barkVatGrabCallMem_mload288 (σ := σ) (σMem := σMem) (I := I)
      (mem := mem) (dink := dink) (dart := dart) hmem hmload288)

theorem barkVatGrabCallMem_mload352 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart word : UInt256}
    (hmem : mem.size = 544)
    (hmload352 :
      (if (⟨352⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (mem.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
        word) :
    (if (⟨352⟩ : UInt256).toNat ≥ (barkVatGrabCallMem σ σMem I mem dink dart).size then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding
          (⟨352⟩ : UInt256).toNat 32))) =
      word := by
  have hread :
      (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 352 32 =
        mem.readWithPadding 352 32 := by
    rw [barkVatGrabCallMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabDinkMem σ σMem I mem dink)
        548 352 (UInt256.sub ⟨0⟩ dart)
        (by rw [barkVatGrabDinkMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabDinkMem_size hmem]; decide⟩)]
    rw [barkVatGrabDinkMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabVowMem σ σMem I mem) 516 352
        (UInt256.sub ⟨0⟩ dink)
        (by rw [barkVatGrabVowMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabVowMem_size hmem]; decide⟩)]
    rw [barkVatGrabVowMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabClipMem σMem I mem) 484 352
        (barkVowWord σ I)
        (by rw [barkVatGrabClipMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabClipMem_size hmem]; decide⟩)]
    rw [barkVatGrabClipMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabUrnMem I mem) 452 352
        (barkIlksClipWord σMem I)
        (by rw [barkVatGrabUrnMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabUrnMem_size hmem]; decide⟩)]
    rw [barkVatGrabUrnMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabIlkMem I mem) 420 352
        (barkUrnKey I)
        (by rw [barkVatGrabIlkMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabIlkMem_size hmem]; decide⟩)]
    rw [barkVatGrabIlkMem,
      Reasoning.Theory.writeWord_read_preserved (barkVatGrabSelectorMem mem) 388 352
        (barkIlkWord I)
        (by rw [barkVatGrabSelectorMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVatGrabSelectorMem_size hmem]; decide⟩)]
    rw [barkVatGrabSelectorMem,
      Reasoning.Theory.writeWord_read_preserved mem 384 352 barkVatGrabSelectorShifted
        (by rw [hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  simpa [barkVatGrabCallMem_size hmem, hmem,
    show (⟨352⟩ : UInt256).toNat = 352 by native_decide, hread] using hmload352

theorem barkVatGrabPostCallMem_mload352 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray} {dink dart word : UInt256}
    (hmem : mem.size = 544)
    (hmload352 :
      (if (⟨352⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (mem.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
        word) :
    (if (⟨352⟩ : UInt256).toNat ≥
          (barkVatGrabPostCallMem σ σMem I mem out dink dart).size then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVatGrabPostCallMem σ σMem I mem out dink dart).readWithPadding
          (⟨352⟩ : UInt256).toNat 32))) =
      word := by
  simpa [barkVatGrabPostCallMem_eq] using
    (barkVatGrabCallMem_mload352 (σ := σ) (σMem := σMem) (I := I)
      (mem := mem) (dink := dink) (dart := dart) hmem hmload352)

theorem barkVatGrabSelectorShifted_extract :
    (UInt256.toByteArray barkVatGrabSelectorShifted).extract 0 4 = vatGrabSelector := by
  native_decide

theorem barkVatGrabCallMem_read384_4 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 384 4 =
      vatGrabSelector := by
  unfold barkVatGrabCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dart)
      (barkVatGrabDinkMem σ σMem I mem dink) 548 384 4
      (by rw [barkVatGrabDinkMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabDinkMem_size hmem]; native_decide)]
  unfold barkVatGrabDinkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dink)
      (barkVatGrabVowMem σ σMem I mem) 516 384 4
      (by rw [barkVatGrabVowMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabVowMem_size hmem]; native_decide)]
  unfold barkVatGrabVowMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkVowWord σ I)
      (barkVatGrabClipMem σMem I mem) 484 384 4
      (by rw [barkVatGrabClipMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabClipMem_size hmem]; native_decide)]
  unfold barkVatGrabClipMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkIlksClipWord σMem I)
      (barkVatGrabUrnMem I mem) 452 384 4
      (by rw [barkVatGrabUrnMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabUrnMem_size hmem]; native_decide)]
  unfold barkVatGrabUrnMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkUrnKey I)
      (barkVatGrabIlkMem I mem) 420 384 4
      (by rw [barkVatGrabIlkMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabIlkMem_size hmem]; native_decide)]
  unfold barkVatGrabIlkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkIlkWord I)
      (barkVatGrabSelectorMem mem) 388 384 4
      (by rw [barkVatGrabSelectorMem_size hmem]; omega) (by native_decide)
      (by omega) (by omega) (by rw [barkVatGrabSelectorMem_size hmem]; native_decide)]
  unfold barkVatGrabSelectorMem Reasoning.Theory.writeWord
  change (barkVatGrabSelectorShifted.toByteArray.write 0 mem 384 32).readWithPadding
      384 4 = vatGrabSelector
  rw [toByteArray_write_read_window_of_gap barkVatGrabSelectorShifted mem 384 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  exact barkVatGrabSelectorShifted_extract

theorem barkVatGrabCallMem_read388_32 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 388 32 =
      (barkIlkWord I).toByteArray := by
  unfold barkVatGrabCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dart)
      (barkVatGrabDinkMem σ σMem I mem dink) 548 388 32
      (by rw [barkVatGrabDinkMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabDinkMem_size hmem]; native_decide)]
  unfold barkVatGrabDinkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dink)
      (barkVatGrabVowMem σ σMem I mem) 516 388 32
      (by rw [barkVatGrabVowMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabVowMem_size hmem]; native_decide)]
  unfold barkVatGrabVowMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkVowWord σ I)
      (barkVatGrabClipMem σMem I mem) 484 388 32
      (by rw [barkVatGrabClipMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabClipMem_size hmem]; native_decide)]
  unfold barkVatGrabClipMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkIlksClipWord σMem I)
      (barkVatGrabUrnMem I mem) 452 388 32
      (by rw [barkVatGrabUrnMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabUrnMem_size hmem]; native_decide)]
  unfold barkVatGrabUrnMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkUrnKey I)
      (barkVatGrabIlkMem I mem) 420 388 32
      (by rw [barkVatGrabIlkMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabIlkMem_size hmem]; native_decide)]
  unfold barkVatGrabIlkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (barkIlkWord I) (barkVatGrabSelectorMem mem)
      388 (by rw [barkVatGrabSelectorMem_size hmem]; native_decide)]

theorem barkVatGrabCallMem_read420_32 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 420 32 =
      (barkUrnKey I).toByteArray := by
  unfold barkVatGrabCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dart)
      (barkVatGrabDinkMem σ σMem I mem dink) 548 420 32
      (by rw [barkVatGrabDinkMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabDinkMem_size hmem]; native_decide)]
  unfold barkVatGrabDinkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dink)
      (barkVatGrabVowMem σ σMem I mem) 516 420 32
      (by rw [barkVatGrabVowMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabVowMem_size hmem]; native_decide)]
  unfold barkVatGrabVowMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkVowWord σ I)
      (barkVatGrabClipMem σMem I mem) 484 420 32
      (by rw [barkVatGrabClipMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabClipMem_size hmem]; native_decide)]
  unfold barkVatGrabClipMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkIlksClipWord σMem I)
      (barkVatGrabUrnMem I mem) 452 420 32
      (by rw [barkVatGrabUrnMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabUrnMem_size hmem]; native_decide)]
  unfold barkVatGrabUrnMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (barkUrnKey I) (barkVatGrabIlkMem I mem)
      420 (by rw [barkVatGrabIlkMem_size hmem]; native_decide)]

theorem barkVatGrabCallMem_read452_32 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 452 32 =
      (barkIlksClipWord σMem I).toByteArray := by
  unfold barkVatGrabCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dart)
      (barkVatGrabDinkMem σ σMem I mem dink) 548 452 32
      (by rw [barkVatGrabDinkMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabDinkMem_size hmem]; native_decide)]
  unfold barkVatGrabDinkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dink)
      (barkVatGrabVowMem σ σMem I mem) 516 452 32
      (by rw [barkVatGrabVowMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabVowMem_size hmem]; native_decide)]
  unfold barkVatGrabVowMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkVowWord σ I)
      (barkVatGrabClipMem σMem I mem) 484 452 32
      (by rw [barkVatGrabClipMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabClipMem_size hmem]; native_decide)]
  unfold barkVatGrabClipMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (barkIlksClipWord σMem I)
      (barkVatGrabUrnMem I mem) 452
      (by rw [barkVatGrabUrnMem_size hmem]; native_decide)]

theorem barkVatGrabCallMem_read484_32 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 484 32 =
      (barkVowWord σ I).toByteArray := by
  unfold barkVatGrabCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dart)
      (barkVatGrabDinkMem σ σMem I mem dink) 548 484 32
      (by rw [barkVatGrabDinkMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabDinkMem_size hmem]; native_decide)]
  unfold barkVatGrabDinkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dink)
      (barkVatGrabVowMem σ σMem I mem) 516 484 32
      (by rw [barkVatGrabVowMem_size hmem]; omega) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabVowMem_size hmem]; native_decide)]
  unfold barkVatGrabVowMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (barkVowWord σ I)
      (barkVatGrabClipMem σMem I mem) 484
      (by rw [barkVatGrabClipMem_size hmem]; native_decide)]

theorem barkVatGrabCallMem_read516_32 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 516 32 =
      (UInt256.sub ⟨0⟩ dink).toByteArray := by
  unfold barkVatGrabCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (UInt256.sub ⟨0⟩ dart)
      (barkVatGrabDinkMem σ σMem I mem dink) 548 516 32
      (by rw [barkVatGrabDinkMem_size hmem]) (by omega) (by omega)
      (by omega) (by rw [barkVatGrabDinkMem_size hmem]; native_decide)]
  unfold barkVatGrabDinkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (UInt256.sub ⟨0⟩ dink)
      (barkVatGrabVowMem σ σMem I mem) 516
      (by rw [barkVatGrabVowMem_size hmem]; native_decide)]

theorem barkVatGrabCallMem_read548_32 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 548 32 =
      (UInt256.sub ⟨0⟩ dart).toByteArray := by
  unfold barkVatGrabCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (UInt256.sub ⟨0⟩ dart)
      (barkVatGrabDinkMem σ σMem I mem dink) 548
      (by rw [barkVatGrabDinkMem_size hmem]; native_decide)]

theorem barkVatGrabCallMem_read384_196 {σ σMem : AccountMap} {I : ExecutionEnv}
    {mem : ByteArray} {dink dart : UInt256} (hmem : mem.size = 544) :
    (barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 384 196 =
      vatGrabSelector ++ (barkIlkWord I).toByteArray ++ (barkUrnKey I).toByteArray ++
        (barkIlksClipWord σMem I).toByteArray ++ (barkVowWord σ I).toByteArray ++
        (UInt256.sub ⟨0⟩ dink).toByteArray ++ (UInt256.sub ⟨0⟩ dart).toByteArray := by
  have hsize : (barkVatGrabCallMem σ σMem I mem dink dart).size = 580 :=
    barkVatGrabCallMem_size hmem
  rw [show 196 = 4 + 192 from rfl,
    byteArray_readWithPadding_split (barkVatGrabCallMem σ σMem I mem dink dart)
      384 4 192 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 192 = 32 + 160 from rfl,
    byteArray_readWithPadding_split (barkVatGrabCallMem σ σMem I mem dink dart)
      388 32 160 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 160 = 32 + 128 from rfl,
    byteArray_readWithPadding_split (barkVatGrabCallMem σ σMem I mem dink dart)
      420 32 128 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split (barkVatGrabCallMem σ σMem I mem dink dart)
      452 32 96 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (barkVatGrabCallMem σ σMem I mem dink dart)
      484 32 64 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (barkVatGrabCallMem σ σMem I mem dink dart)
      516 32 32 (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [barkVatGrabCallMem_read384_4 hmem, barkVatGrabCallMem_read388_32 hmem,
    barkVatGrabCallMem_read420_32 hmem, barkVatGrabCallMem_read452_32 hmem,
    barkVatGrabCallMem_read484_32 hmem, barkVatGrabCallMem_read516_32 hmem,
    barkVatGrabCallMem_read548_32 hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem barkVatGrabEncodeWords {σ σMem : AccountMap}
    {I : ExecutionEnv} {dink dart : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hdinkBound : dink.toNat ≤ dogInt256LimitWord.toNat)
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat) :
    config.externalABI.encode? "grab"
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I),
          .address (AccountAddress.ofNat (barkIlksClipWord σMem I).toNat),
          .address (AccountAddress.ofNat (barkVowWord σ I).toNat),
          .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))] =
      some (vatGrabSelector ++ (barkIlkWord I).toByteArray ++
        (barkUrnKey I).toByteArray ++ (barkIlksClipWord σMem I).toByteArray ++
        (barkVowWord σ I).toByteArray ++ (UInt256.sub ⟨0⟩ dink).toByteArray ++
        (UInt256.sub ⟨0⟩ dart).toByteArray) := by
  have hIlk : ABI.encodeABIValue? bytes32 (.fixedBytes bytes32Width (barkIlkBytes I)) =
      some (EVM.Word.toBytesBE (barkIlkWord I)) := by
    have hbytes := barkIlkBytes_eq_toBytesBE (I := I) hsz100
    have hlen : (EVM.Word.toBytesBE (barkIlkWord I)).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size (barkIlkWord I)
    simp [ABI.encodeABIValue?, hlen, zeroBytes, bytes32, bytes32Width, hbytes]
  have hIlk' :
      ABI.encodeABIValue? (.elem (.bytes bytes32Width))
        (.fixedBytes bytes32Width (barkIlkBytes I)) =
          some (EVM.Word.toBytesBE (barkIlkWord I)) := by
    simpa [bytes32] using hIlk
  have hurnCanon : (barkUrnKey I).toNat < EVM.addressModulus := by
    simpa [barkUrnKey, u256_land_comm] using
      solcAddrMask_result_canonical (barkUrnWord I)
  have hurn : ABI.encodeABIValue? (.elem .address) (.address (barkUrn I)) =
      some (EVM.Word.toBytesBE (barkUrnKey I)) := by
    rw [barkUrn_value_masked I]
    simpa [← accountAddress_ofUInt256_eq_ofNat_toNat] using
      encodeABIValue_address_ofUInt256_of_canonical (barkUrnKey I) hurnCanon
  have hclipCanon : (barkIlksClipWord σMem I).toNat < EVM.addressModulus := by
    simpa [barkIlksClipWord, u256_land_comm] using
      solcAddrMask_result_canonical (solcSlotWord σMem I (barkIlksSlot I))
  have hclip : ABI.encodeABIValue? (.elem .address)
      (.address (AccountAddress.ofNat (barkIlksClipWord σMem I).toNat)) =
        some (EVM.Word.toBytesBE (barkIlksClipWord σMem I)) := by
    simpa [← accountAddress_ofUInt256_eq_ofNat_toNat] using
      encodeABIValue_address_ofUInt256_of_canonical (barkIlksClipWord σMem I) hclipCanon
  have hvowCanon : (barkVowWord σ I).toNat < EVM.addressModulus := by
    simpa [barkVowWord, u256_land_comm] using
      solcAddrMask_result_canonical (solcSlotWordAt ⟨2⟩ σ I)
  have hvow : ABI.encodeABIValue? (.elem .address)
      (.address (AccountAddress.ofNat (barkVowWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (barkVowWord σ I)) := by
    simpa [← accountAddress_ofUInt256_eq_ofNat_toNat] using
      encodeABIValue_address_ofUInt256_of_canonical (barkVowWord σ I) hvowCanon
  have hdink :
      ABI.encodeABIValue? (.elem (.int int256Int)) (.int (-(↑dink.toNat : Int))) =
        some (EVM.Word.toBytesBE (UInt256.sub ⟨0⟩ dink)) := by
    simpa using barkInt256NegArgEncoding dink hdinkBound
  have hdart :
      ABI.encodeABIValue? (.elem (.int int256Int)) (.int (-(↑dart.toNat : Int))) =
        some (EVM.Word.toBytesBE (UInt256.sub ⟨0⟩ dart)) := by
    simpa using barkInt256NegArgEncoding dart hdartBound
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, hIlk', hurn, hclip, hvow, addr, bytes32, int256]
  rw [hdink, hdart]
  simp
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc, word_toBytesBE_toByteArray_eq_toByteArray]

theorem barkVatGrabEncode_eq {σ σMem : AccountMap}
    {I : ExecutionEnv} {mem : ByteArray} {dink dart : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hmem : mem.size = 544)
    (hdinkBound : dink.toNat ≤ dogInt256LimitWord.toNat)
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat) :
    config.externalABI.encode? "grab"
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I),
          .address (AccountAddress.ofNat (barkIlksClipWord σMem I).toNat),
          .address (AccountAddress.ofNat (barkVowWord σ I).toNat),
          .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))] =
      some ((barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding 384 196) := by
  rw [barkVatGrabCallMem_read384_196 hmem]
  exact barkVatGrabEncodeWords (σ := σ) (σMem := σMem) (I := I)
    (dink := dink) (dart := dart) hsz100 hdinkBound hdartBound

theorem barkVowFessSelectorMem_size {mem : ByteArray} (hmem : mem.size = 580) :
    (barkVowFessSelectorMem mem).size = 580 := by
  rw [barkVowFessSelectorMem,
    Reasoning.Theory.writeWord_size mem 384 barkVowFessSelectorShifted
      (by rw [hmem]; native_decide),
    hmem]
  native_decide

theorem barkVowFessDueMem_size {mem : ByteArray} {due : UInt256}
    (hmem : mem.size = 580) :
    (barkVowFessDueMem mem due).size = 580 := by
  rw [barkVowFessDueMem,
    Reasoning.Theory.writeWord_size (barkVowFessSelectorMem mem) 388 due
      (by rw [barkVowFessSelectorMem_size hmem]; native_decide),
    barkVowFessSelectorMem_size hmem]
  native_decide

theorem barkVowFessDueMem_read64 {mem : ByteArray} {due : UInt256}
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (barkVowFessDueMem mem due).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  rw [barkVowFessDueMem,
    Reasoning.Theory.writeWord_read_preserved (barkVowFessSelectorMem mem) 388 64 due
      (by rw [barkVowFessSelectorMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVowFessSelectorMem_size hmem]; decide⟩)]
  rw [barkVowFessSelectorMem,
    Reasoning.Theory.writeWord_read_preserved mem 384 64 barkVowFessSelectorShifted
      (by rw [hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  exact hread64

theorem barkVowFessDueMem_mload64 {mem : ByteArray} {due : UInt256}
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVowFessDueMem mem due).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVowFessDueMem mem due).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkVowFessDueMem_size hmem]; decide)
    (by
      have hread := barkVowFessDueMem_read64 (mem := mem) (due := due) hmem hread64
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread)

theorem barkVowFessDueMem_read256 {mem : ByteArray} {due word : UInt256}
    (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray word) :
    (barkVowFessDueMem mem due).readWithPadding 256 32 =
      UInt256.toByteArray word := by
  rw [barkVowFessDueMem,
    Reasoning.Theory.writeWord_read_preserved (barkVowFessSelectorMem mem) 388 256 due
      (by rw [barkVowFessSelectorMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkVowFessSelectorMem_size hmem]; decide⟩)]
  rw [barkVowFessSelectorMem,
    Reasoning.Theory.writeWord_read_preserved mem 384 256 barkVowFessSelectorShifted
      (by rw [hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  exact hread256

theorem barkVowFessDueMem_mload288 {mem : ByteArray} {due milkChop : UInt256}
    (hmem : mem.size = 580)
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (mem.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        milkChop) :
    (if (⟨288⟩ : UInt256).toNat ≥ (barkVowFessDueMem mem due).size then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVowFessDueMem mem due).readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
      milkChop := by
  have hread :
      (barkVowFessDueMem mem due).readWithPadding 288 32 =
        mem.readWithPadding 288 32 := by
    rw [barkVowFessDueMem,
      Reasoning.Theory.writeWord_read_preserved (barkVowFessSelectorMem mem) 388 288 due
        (by rw [barkVowFessSelectorMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVowFessSelectorMem_size hmem]; decide⟩)]
    rw [barkVowFessSelectorMem,
      Reasoning.Theory.writeWord_read_preserved mem 384 288 barkVowFessSelectorShifted
        (by rw [hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  simpa [barkVowFessDueMem_size hmem, hmem,
    show (⟨288⟩ : UInt256).toNat = 288 by native_decide, hread] using hmload288

theorem barkVowFessPostCallMem_eq {mem out : ByteArray} {due : UInt256} :
    barkVowFessPostCallMem mem out due = barkVowFessDueMem mem due := by
  unfold barkVowFessPostCallMem barkVowFessOutSize
  change out.write 0 (barkVowFessDueMem mem due) barkVowFessOutPtr.toNat 0 =
    barkVowFessDueMem mem due
  rw [byteArray_write_len_zero]

theorem barkVowFessPostCallMem_size {mem out : ByteArray} {due : UInt256}
    (hmem : mem.size = 580) :
    (barkVowFessPostCallMem mem out due).size = 580 := by
  rw [barkVowFessPostCallMem_eq, barkVowFessDueMem_size hmem]

theorem barkVowFessPostCallMem_read64 {mem out : ByteArray} {due : UInt256}
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (barkVowFessPostCallMem mem out due).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  rw [barkVowFessPostCallMem_eq]
  exact barkVowFessDueMem_read64 hmem hread64

theorem barkVowFessPostCallMem_read256 {mem out : ByteArray} {due word : UInt256}
    (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray word) :
    (barkVowFessPostCallMem mem out due).readWithPadding 256 32 =
      UInt256.toByteArray word := by
  rw [barkVowFessPostCallMem_eq]
  exact barkVowFessDueMem_read256 hmem hread256

theorem barkVowFessPostCallMem_mload288 {mem out : ByteArray} {due milkChop : UInt256}
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ (barkVowFessDueMem mem due).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((barkVowFessDueMem mem due).readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        milkChop) :
    (if (⟨288⟩ : UInt256).toNat ≥ (barkVowFessPostCallMem mem out due).size then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVowFessPostCallMem mem out due).readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
      milkChop := by
  simpa [barkVowFessPostCallMem_eq] using hmload288

theorem barkVowFessDueMem_mload352 {mem : ByteArray} {due word : UInt256}
    (hmem : mem.size = 580)
    (hmload352 :
      (if (⟨352⟩ : UInt256).toNat ≥ mem.size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (mem.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
        word) :
    (if (⟨352⟩ : UInt256).toNat ≥ (barkVowFessDueMem mem due).size then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVowFessDueMem mem due).readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
      word := by
  have hread :
      (barkVowFessDueMem mem due).readWithPadding 352 32 =
        mem.readWithPadding 352 32 := by
    rw [barkVowFessDueMem,
      Reasoning.Theory.writeWord_read_preserved (barkVowFessSelectorMem mem) 388 352 due
        (by rw [barkVowFessSelectorMem_size hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [barkVowFessSelectorMem_size hmem]; decide⟩)]
    rw [barkVowFessSelectorMem,
      Reasoning.Theory.writeWord_read_preserved mem 384 352 barkVowFessSelectorShifted
        (by rw [hmem]; native_decide)
        (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  simpa [barkVowFessDueMem_size hmem, hmem,
    show (⟨352⟩ : UInt256).toNat = 352 by native_decide, hread] using hmload352

theorem barkVowFessPostCallMem_mload352 {mem out : ByteArray} {due word : UInt256}
    (hmload352 :
      (if (⟨352⟩ : UInt256).toNat ≥ (barkVowFessDueMem mem due).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((barkVowFessDueMem mem due).readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
        word) :
    (if (⟨352⟩ : UInt256).toNat ≥ (barkVowFessPostCallMem mem out due).size then ⟨0⟩
     else UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVowFessPostCallMem mem out due).readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
      word := by
  simpa [barkVowFessPostCallMem_eq] using hmload352

theorem barkVowFessSelectorShifted_extract :
    (UInt256.toByteArray barkVowFessSelectorShifted).extract 0 4 = vowFessSelector := by
  native_decide

theorem barkVowFessDueMem_read384_4 {mem : ByteArray} {due : UInt256}
    (hmem : mem.size = 580) :
    (barkVowFessDueMem mem due).readWithPadding 384 4 =
      vowFessSelector := by
  unfold barkVowFessDueMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap due
      (barkVowFessSelectorMem mem) 388 384 4
      (by rw [barkVowFessSelectorMem_size hmem]; omega) (by native_decide)
      (by omega) (by omega) (by rw [barkVowFessSelectorMem_size hmem]; native_decide)]
  unfold barkVowFessSelectorMem Reasoning.Theory.writeWord
  change (barkVowFessSelectorShifted.toByteArray.write 0 mem 384 32).readWithPadding
      384 4 = vowFessSelector
  rw [toByteArray_write_read_window_of_gap barkVowFessSelectorShifted mem 384 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  exact barkVowFessSelectorShifted_extract

theorem barkVowFessDueMem_read388_32 {mem : ByteArray} {due : UInt256}
    (hmem : mem.size = 580) :
    (barkVowFessDueMem mem due).readWithPadding 388 32 =
      due.toByteArray := by
  unfold barkVowFessDueMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap due (barkVowFessSelectorMem mem) 388
      (by rw [barkVowFessSelectorMem_size hmem]; native_decide)]

theorem barkVowFessDueMem_read384_36 {mem : ByteArray} {due : UInt256}
    (hmem : mem.size = 580) :
    (barkVowFessDueMem mem due).readWithPadding 384 36 =
      vowFessSelector ++ due.toByteArray := by
  have hsize : (barkVowFessDueMem mem due).size = 580 :=
    barkVowFessDueMem_size hmem
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split (barkVowFessDueMem mem due)
      384 4 32 (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by rw [hsize]; native_decide)]
  rw [barkVowFessDueMem_read384_4 hmem, barkVowFessDueMem_read388_32 hmem]

theorem barkVowFessEncodeWords {due : UInt256} :
    config.externalABI.encode? "fess" [.int (Int.ofNat due.toNat)] =
      some (vowFessSelector ++ due.toByteArray) := by
  have hdue :
      ABI.encodeABIValue? (.elem (.int uint256Int)) (.int (↑due.toNat : Int)) =
        some (EVM.Word.toBytesBE due) := by
    have hword : EVM.word due.toNat = due := by
      show UInt256.ofNat due.toNat = due
      exact u256_ofNat_toNat due
    have hltNat : due.toNat < EVM.twoPow 256 := by
      change due.val.val < EVM.twoPow 256
      exact due.val.isLt
    simp [uint256Int, ABI.encodeABIValue?, ABI.encodeABIWord?, hword, hltNat]
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, uint256]
  rw [hdue]
  simp [word_toBytesBE_toByteArray_eq_toByteArray]

theorem barkVowFessEncode_eq {mem : ByteArray} {due : UInt256}
    (hmem : mem.size = 580) :
    config.externalABI.encode? "fess" [.int (Int.ofNat due.toNat)] =
      some ((barkVowFessDueMem mem due).readWithPadding 384 36) := by
  rw [barkVowFessDueMem_read384_36 hmem]
  exact barkVowFessEncodeWords (due := due)

theorem barkKickSelectorMem_size {mem : ByteArray} (hmem : mem.size = 580) :
    (barkKickSelectorMem mem).size = 580 := by
  rw [barkKickSelectorMem,
    Reasoning.Theory.writeWord_size mem 384 barkKickSelectorShifted
      (by rw [hmem]; native_decide),
    hmem]
  native_decide

theorem barkKickTabMem_size {mem : ByteArray} {tab : UInt256}
    (hmem : mem.size = 580) :
    (barkKickTabMem mem tab).size = 580 := by
  rw [barkKickTabMem,
    Reasoning.Theory.writeWord_size (barkKickSelectorMem mem) 388 tab
      (by rw [barkKickSelectorMem_size hmem]; native_decide),
    barkKickSelectorMem_size hmem]
  native_decide

theorem barkKickDinkMem_size {mem : ByteArray} {tab dink : UInt256}
    (hmem : mem.size = 580) :
    (barkKickDinkMem mem tab dink).size = 580 := by
  rw [barkKickDinkMem,
    Reasoning.Theory.writeWord_size (barkKickTabMem mem tab) 420 dink
      (by rw [barkKickTabMem_size hmem]; native_decide),
    barkKickTabMem_size hmem]
  native_decide

theorem barkKickUrnMem_size {I : ExecutionEnv} {mem : ByteArray}
    {tab dink : UInt256} (hmem : mem.size = 580) :
    (barkKickUrnMem I mem tab dink).size = 580 := by
  rw [barkKickUrnMem,
    Reasoning.Theory.writeWord_size (barkKickDinkMem mem tab dink) 452 (barkUrnKey I)
      (by rw [barkKickDinkMem_size hmem]; native_decide),
    barkKickDinkMem_size hmem]
  native_decide

theorem barkKickCalldataMem_size {I : ExecutionEnv} {mem : ByteArray}
    {tab dink : UInt256} (hmem : mem.size = 580) :
    (barkKickCalldataMem I mem tab dink).size = 580 := by
  rw [barkKickCalldataMem,
    Reasoning.Theory.writeWord_size (barkKickUrnMem I mem tab dink) 484 (barkKprKey I)
      (by rw [barkKickUrnMem_size hmem]; native_decide),
    barkKickUrnMem_size hmem]
  native_decide

theorem barkKickCalldataMem_read64 {I : ExecutionEnv} {mem : ByteArray}
    {tab dink : UInt256} (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (barkKickCalldataMem I mem tab dink).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  rw [barkKickCalldataMem,
    Reasoning.Theory.writeWord_read_preserved (barkKickUrnMem I mem tab dink) 484 64
      (barkKprKey I)
      (by rw [barkKickUrnMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkKickUrnMem_size hmem]; decide⟩)]
  rw [barkKickUrnMem,
    Reasoning.Theory.writeWord_read_preserved (barkKickDinkMem mem tab dink) 452 64
      (barkUrnKey I)
      (by rw [barkKickDinkMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkKickDinkMem_size hmem]; decide⟩)]
  rw [barkKickDinkMem,
    Reasoning.Theory.writeWord_read_preserved (barkKickTabMem mem tab) 420 64 dink
      (by rw [barkKickTabMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkKickTabMem_size hmem]; decide⟩)]
  rw [barkKickTabMem,
    Reasoning.Theory.writeWord_read_preserved (barkKickSelectorMem mem) 388 64 tab
      (by rw [barkKickSelectorMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkKickSelectorMem_size hmem]; decide⟩)]
  rw [barkKickSelectorMem,
    Reasoning.Theory.writeWord_read_preserved mem 384 64 barkKickSelectorShifted
      (by rw [hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  exact hread64

theorem barkKickCalldataMem_mload64 {I : ExecutionEnv} {mem : ByteArray}
    {tab dink : UInt256} (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkKickCalldataMem I mem tab dink).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkKickCalldataMem I mem tab dink).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkKickCalldataMem_size hmem]; decide)
    (by
      have hread := barkKickCalldataMem_read64 (I := I) (mem := mem)
        (tab := tab) (dink := dink) hmem hread64
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread)

theorem barkKickCalldataMem_read256 {I : ExecutionEnv} {mem : ByteArray}
    {tab dink clip : UInt256} (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray clip) :
    (barkKickCalldataMem I mem tab dink).readWithPadding 256 32 =
      UInt256.toByteArray clip := by
  rw [barkKickCalldataMem,
    Reasoning.Theory.writeWord_read_preserved (barkKickUrnMem I mem tab dink) 484 256
      (barkKprKey I)
      (by rw [barkKickUrnMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkKickUrnMem_size hmem]; decide⟩)]
  rw [barkKickUrnMem,
    Reasoning.Theory.writeWord_read_preserved (barkKickDinkMem mem tab dink) 452 256
      (barkUrnKey I)
      (by rw [barkKickDinkMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkKickDinkMem_size hmem]; decide⟩)]
  rw [barkKickDinkMem,
    Reasoning.Theory.writeWord_read_preserved (barkKickTabMem mem tab) 420 256 dink
      (by rw [barkKickTabMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkKickTabMem_size hmem]; decide⟩)]
  rw [barkKickTabMem,
    Reasoning.Theory.writeWord_read_preserved (barkKickSelectorMem mem) 388 256 tab
      (by rw [barkKickSelectorMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkKickSelectorMem_size hmem]; decide⟩)]
  rw [barkKickSelectorMem,
    Reasoning.Theory.writeWord_read_preserved mem 384 256 barkKickSelectorShifted
      (by rw [hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  exact hread256

theorem barkKickSelectorShifted_extract :
    (UInt256.toByteArray barkKickSelectorShifted).extract 0 4 =
      clipperKickSelector := by
  native_decide

theorem barkKickCalldataMem_read384_4 {I : ExecutionEnv} {mem : ByteArray}
    {tab dink : UInt256} (hmem : mem.size = 580) :
    (barkKickCalldataMem I mem tab dink).readWithPadding 384 4 =
      clipperKickSelector := by
  have hUrnSize := barkKickUrnMem_size (I := I) (mem := mem) (tab := tab)
    (dink := dink) hmem
  have hDinkSize := barkKickDinkMem_size (mem := mem) (tab := tab) (dink := dink) hmem
  have hTabSize := barkKickTabMem_size (mem := mem) (tab := tab) hmem
  have hSelectorSize := barkKickSelectorMem_size (mem := mem) hmem
  unfold barkKickCalldataMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkKprKey I)
      (barkKickUrnMem I mem tab dink) 484 384 4
      (by rw [hUrnSize]; omega) (by native_decide) (by omega) (by omega)
      (by rw [hUrnSize]; native_decide)]
  unfold barkKickUrnMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkUrnKey I)
      (barkKickDinkMem mem tab dink) 452 384 4
      (by rw [hDinkSize]; omega) (by native_decide) (by omega) (by omega)
      (by rw [hDinkSize]; native_decide)]
  unfold barkKickDinkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap dink (barkKickTabMem mem tab) 420 384 4
      (by rw [hTabSize]; omega) (by native_decide) (by omega) (by omega)
      (by rw [hTabSize]; native_decide)]
  unfold barkKickTabMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap tab (barkKickSelectorMem mem) 388 384 4
      (by rw [hSelectorSize]; omega) (by native_decide) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold barkKickSelectorMem Reasoning.Theory.writeWord
  change (barkKickSelectorShifted.toByteArray.write 0 mem 384 32).readWithPadding
      384 4 = clipperKickSelector
  rw [toByteArray_write_read_window_of_gap barkKickSelectorShifted mem 384 0 4
      (by omega) (by omega) (by omega) (by rw [hmem]; native_decide)]
  exact barkKickSelectorShifted_extract

theorem barkKickCalldataMem_read388_32 {I : ExecutionEnv} {mem : ByteArray}
    {tab dink : UInt256} (hmem : mem.size = 580) :
    (barkKickCalldataMem I mem tab dink).readWithPadding 388 32 =
      tab.toByteArray := by
  have hUrnSize := barkKickUrnMem_size (I := I) (mem := mem) (tab := tab)
    (dink := dink) hmem
  have hDinkSize := barkKickDinkMem_size (mem := mem) (tab := tab) (dink := dink) hmem
  have hTabSize := barkKickTabMem_size (mem := mem) (tab := tab) hmem
  unfold barkKickCalldataMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkKprKey I)
      (barkKickUrnMem I mem tab dink) 484 388 32
      (by rw [hUrnSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUrnSize]; native_decide)]
  unfold barkKickUrnMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkUrnKey I)
      (barkKickDinkMem mem tab dink) 452 388 32
      (by rw [hDinkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hDinkSize]; native_decide)]
  unfold barkKickDinkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap dink (barkKickTabMem mem tab) 420 388 32
      (by rw [hTabSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hTabSize]; native_decide)]
  unfold barkKickTabMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap tab (barkKickSelectorMem mem) 388
      (by rw [barkKickSelectorMem_size hmem]; native_decide)]

theorem barkKickCalldataMem_read420_32 {I : ExecutionEnv} {mem : ByteArray}
    {tab dink : UInt256} (hmem : mem.size = 580) :
    (barkKickCalldataMem I mem tab dink).readWithPadding 420 32 =
      dink.toByteArray := by
  have hUrnSize := barkKickUrnMem_size (I := I) (mem := mem) (tab := tab)
    (dink := dink) hmem
  have hDinkSize := barkKickDinkMem_size (mem := mem) (tab := tab) (dink := dink) hmem
  unfold barkKickCalldataMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkKprKey I)
      (barkKickUrnMem I mem tab dink) 484 420 32
      (by rw [hUrnSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUrnSize]; native_decide)]
  unfold barkKickUrnMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkUrnKey I)
      (barkKickDinkMem mem tab dink) 452 420 32
      (by rw [hDinkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hDinkSize]; native_decide)]
  unfold barkKickDinkMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap dink (barkKickTabMem mem tab) 420
      (by rw [barkKickTabMem_size hmem]; native_decide)]

theorem barkKickCalldataMem_read452_32 {I : ExecutionEnv} {mem : ByteArray}
    {tab dink : UInt256} (hmem : mem.size = 580) :
    (barkKickCalldataMem I mem tab dink).readWithPadding 452 32 =
      (barkUrnKey I).toByteArray := by
  have hUrnSize := barkKickUrnMem_size (I := I) (mem := mem) (tab := tab)
    (dink := dink) hmem
  unfold barkKickCalldataMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkKprKey I)
      (barkKickUrnMem I mem tab dink) 484 452 32
      (by rw [hUrnSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUrnSize]; native_decide)]
  unfold barkKickUrnMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (barkUrnKey I) (barkKickDinkMem mem tab dink)
      452 (by rw [barkKickDinkMem_size hmem]; native_decide)]

theorem barkKickCalldataMem_read484_32 {I : ExecutionEnv} {mem : ByteArray}
    {tab dink : UInt256} (hmem : mem.size = 580) :
    (barkKickCalldataMem I mem tab dink).readWithPadding 484 32 =
      (barkKprKey I).toByteArray := by
  unfold barkKickCalldataMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (barkKprKey I)
      (barkKickUrnMem I mem tab dink) 484
      (by rw [barkKickUrnMem_size hmem]; native_decide)]

theorem barkKickCalldataMem_read384_132 {I : ExecutionEnv} {mem : ByteArray}
    {tab dink : UInt256} (hmem : mem.size = 580) :
    (barkKickCalldataMem I mem tab dink).readWithPadding 384 132 =
      clipperKickSelector ++ tab.toByteArray ++ dink.toByteArray ++
        (barkUrnKey I).toByteArray ++ (barkKprKey I).toByteArray := by
  have hsize : (barkKickCalldataMem I mem tab dink).size = 580 :=
    barkKickCalldataMem_size (I := I) (mem := mem) (tab := tab) (dink := dink) hmem
  rw [show 132 = 4 + 128 from rfl,
    byteArray_readWithPadding_split (barkKickCalldataMem I mem tab dink)
      384 4 128 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; native_decide)]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split (barkKickCalldataMem I mem tab dink)
      388 32 96 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; native_decide)]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (barkKickCalldataMem I mem tab dink)
      420 32 64 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; native_decide)]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (barkKickCalldataMem I mem tab dink)
      452 32 32 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; native_decide)]
  rw [barkKickCalldataMem_read384_4 hmem, barkKickCalldataMem_read388_32 hmem,
    barkKickCalldataMem_read420_32 hmem, barkKickCalldataMem_read452_32 hmem,
    barkKickCalldataMem_read484_32 hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem barkKickEncodeWords {I : ExecutionEnv}
    {tab dink : UInt256} :
    config.externalABI.encode? "kick"
      [.int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat),
       .address (barkUrn I), .address (barkKpr I)] =
    some (clipperKickSelector ++ tab.toByteArray ++ dink.toByteArray ++
      (barkUrnKey I).toByteArray ++ (barkKprKey I).toByteArray) := by
  have htab :
      ABI.encodeABIValue? (.elem (.int uint256Int)) (.int (↑tab.toNat : Int)) =
        some (EVM.Word.toBytesBE tab) := by
    have hword : EVM.word tab.toNat = tab := by
      show UInt256.ofNat tab.toNat = tab
      exact u256_ofNat_toNat tab
    have hltNat : tab.toNat < EVM.twoPow 256 := by
      change tab.val.val < EVM.twoPow 256
      exact tab.val.isLt
    simp [uint256Int, ABI.encodeABIValue?, ABI.encodeABIWord?, hword, hltNat]
  have hdink :
      ABI.encodeABIValue? (.elem (.int uint256Int)) (.int (↑dink.toNat : Int)) =
        some (EVM.Word.toBytesBE dink) := by
    have hword : EVM.word dink.toNat = dink := by
      show UInt256.ofNat dink.toNat = dink
      exact u256_ofNat_toNat dink
    have hltNat : dink.toNat < EVM.twoPow 256 := by
      change dink.val.val < EVM.twoPow 256
      exact dink.val.isLt
    simp [uint256Int, ABI.encodeABIValue?, ABI.encodeABIWord?, hword, hltNat]
  have hurnCanon : (barkUrnKey I).toNat < EVM.addressModulus := by
    simpa [barkUrnKey, u256_land_comm] using
      solcAddrMask_result_canonical (barkUrnWord I)
  have hurn : ABI.encodeABIValue? (.elem .address) (.address (barkUrn I)) =
      some (EVM.Word.toBytesBE (barkUrnKey I)) := by
    rw [barkUrn_value_masked I]
    simpa [← accountAddress_ofUInt256_eq_ofNat_toNat] using
      encodeABIValue_address_ofUInt256_of_canonical (barkUrnKey I) hurnCanon
  have hkprCanon : (barkKprKey I).toNat < EVM.addressModulus := by
    simpa [barkKprKey, u256_land_comm] using
      solcAddrMask_result_canonical (barkKprWord I)
  have hkpr : ABI.encodeABIValue? (.elem .address) (.address (barkKpr I)) =
      some (EVM.Word.toBytesBE (barkKprKey I)) := by
    rw [barkKpr_value_masked I]
    simpa [← accountAddress_ofUInt256_eq_ofNat_toNat] using
      encodeABIValue_address_ofUInt256_of_canonical (barkKprKey I) hkprCanon
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, htab, hdink, hurn, hkpr, addr, uint256]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc, word_toBytesBE_toByteArray_eq_toByteArray]

theorem barkKickEncode_eq {I : ExecutionEnv}
    {mem : ByteArray} {tab dink : UInt256} (hmem : mem.size = 580) :
    config.externalABI.encode? "kick"
      [.int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat),
       .address (barkUrn I), .address (barkKpr I)] =
    some ((barkKickCalldataMem I mem tab dink).readWithPadding 384 132) := by
  rw [barkKickCalldataMem_read384_132 hmem]
  exact barkKickEncodeWords (I := I) (tab := tab) (dink := dink)

theorem barkKickPostCallWrite_size {I : ExecutionEnv} {tab dink : UInt256}
    {mem : ByteArray} (out : ByteArray) (L : ℕ)
    (hmem : mem.size = 580) (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 (barkKickCalldataMem I mem tab dink) 384 L).size = 580 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact barkKickCalldataMem_size (I := I) (mem := mem) (tab := tab)
      (dink := dink) hmem
  · rw [write_eq_gen out (barkKickCalldataMem I mem tab dink) 384 L
      (by omega) hLo
      (by rw [barkKickCalldataMem_size (I := I) (mem := mem) (tab := tab)
        (dink := dink) hmem]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      barkKickCalldataMem_size (I := I) (mem := mem) (tab := tab)
        (dink := dink) hmem]
    omega

theorem barkKickPostCallWrite_read64 {I : ExecutionEnv} {tab dink : UInt256}
    {mem : ByteArray} (out : ByteArray) (L : ℕ)
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 (barkKickCalldataMem I mem tab dink) 384 L).readWithPadding
      64 32 = UInt256.toByteArray ⟨384⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact barkKickCalldataMem_read64 (I := I) (mem := mem) (tab := tab)
      (dink := dink) hmem hread64
  · rw [write_read_below_gen out (barkKickCalldataMem I mem tab dink) 384 L 64
      (by omega) hLo
      (by rw [barkKickCalldataMem_size (I := I) (mem := mem) (tab := tab)
        (dink := dink) hmem]; omega) (by omega),
      barkKickCalldataMem_read64 (I := I) (mem := mem) (tab := tab)
        (dink := dink) hmem hread64]

theorem barkKickPostCallWrite_read256 {I : ExecutionEnv} {tab dink clip : UInt256}
    {mem : ByteArray} (out : ByteArray) (L : ℕ)
    (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray clip)
    (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 (barkKickCalldataMem I mem tab dink) 384 L).readWithPadding
      256 32 = UInt256.toByteArray clip := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact barkKickCalldataMem_read256 (I := I) (mem := mem) (tab := tab)
      (dink := dink) hmem hread256
  · rw [write_read_below_gen out (barkKickCalldataMem I mem tab dink) 384 L 256
      (by omega) hLo
      (by rw [barkKickCalldataMem_size (I := I) (mem := mem) (tab := tab)
        (dink := dink) hmem]; omega) (by omega),
      barkKickCalldataMem_read256 (I := I) (mem := mem) (tab := tab)
        (dink := dink) hmem hread256]

theorem barkKickPostCallWrite_read384_32 {I : ExecutionEnv} {tab dink : UInt256}
    {mem : ByteArray} (out : ByteArray)
    (hmem : mem.size = 580) (ho32 : 32 ≤ out.size) :
    (out.write 0 (barkKickCalldataMem I mem tab dink) 384 32).readWithPadding
      384 32 = out.extract 0 32 :=
  write32_read_back out (barkKickCalldataMem I mem tab dink) 384 ho32
    (by rw [barkKickCalldataMem_size (I := I) (mem := mem) (tab := tab)
      (dink := dink) hmem]; omega)

theorem barkKickPostCallWrite_mload64 {I : ExecutionEnv} {tab dink : UInt256}
    {mem : ByteArray} {out : ByteArray} {L : ℕ}
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (out.write 0 (barkKickCalldataMem I mem tab dink) 384 L).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((out.write 0 (barkKickCalldataMem I mem tab dink) 384 L).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkKickPostCallWrite_size (I := I) (tab := tab) (dink := dink)
      (out := out) (L := L) hmem hL hLo]; decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
        barkKickPostCallWrite_read64 (I := I) (tab := tab) (dink := dink)
          (out := out) (L := L) hmem hread64 hL hLo)

theorem barkKickPostCallWrite_mload256 {I : ExecutionEnv} {tab dink clip : UInt256}
    {mem : ByteArray} {out : ByteArray} {L : ℕ}
    (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray clip)
    (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (if (⟨256⟩ : UInt256).toNat ≥
          (out.write 0 (barkKickCalldataMem I mem tab dink) 384 L).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((out.write 0 (barkKickCalldataMem I mem tab dink) 384 L).readWithPadding
          (⟨256⟩ : UInt256).toNat 32))) =
      clip := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨256⟩ : UInt256)) (v := clip)
    (by rw [barkKickPostCallWrite_size (I := I) (tab := tab) (dink := dink)
      (out := out) (L := L) hmem hL hLo]; decide)
    (by
      simpa [show (⟨256⟩ : UInt256).toNat = 256 by native_decide] using
        barkKickPostCallWrite_read256 (I := I) (tab := tab) (dink := dink)
          (out := out) (L := L) hmem hread256 hL hLo)

theorem barkKickPostCallMem_size_long {I : ExecutionEnv} {tab dink : UInt256}
    {mem out : ByteArray}
    (hmem : mem.size = 580) (hlong : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkKickPostCallMem I mem out tab dink).size = 580 := by
  have hmin :
      (min barkKickOutSize (UInt256.ofNat out.size)).toNat = 32 := by
    exact umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hlong hout
  unfold barkKickPostCallMem
  rw [hmin]
  exact barkKickPostCallWrite_size (I := I) (tab := tab) (dink := dink)
    (out := out) (L := 32) hmem (by decide) hlong

theorem barkKickPostCallMem_read64_long {I : ExecutionEnv} {tab dink : UInt256}
    {mem out : ByteArray}
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hlong : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkKickPostCallMem I mem out tab dink).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  have hmin :
      (min barkKickOutSize (UInt256.ofNat out.size)).toNat = 32 := by
    exact umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hlong hout
  unfold barkKickPostCallMem
  rw [hmin]
  exact barkKickPostCallWrite_read64 (I := I) (tab := tab) (dink := dink)
    (out := out) (L := 32) hmem hread64 (by decide) hlong

theorem barkKickPostCallMem_mload64_long {I : ExecutionEnv} {tab dink : UInt256}
    {mem out : ByteArray}
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hlong : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkKickPostCallMem I mem out tab dink).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkKickPostCallMem I mem out tab dink).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkKickPostCallMem_size_long hmem hlong hout]; decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
        barkKickPostCallMem_read64_long (I := I) (tab := tab) (dink := dink)
          hmem hread64 hlong hout)

theorem barkKickPostCallMem_read256_long {I : ExecutionEnv} {tab dink clip : UInt256}
    {mem out : ByteArray}
    (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray clip)
    (hlong : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkKickPostCallMem I mem out tab dink).readWithPadding 256 32 =
      UInt256.toByteArray clip := by
  have hmin :
      (min barkKickOutSize (UInt256.ofNat out.size)).toNat = 32 := by
    exact umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hlong hout
  unfold barkKickPostCallMem
  rw [hmin]
  exact barkKickPostCallWrite_read256 (I := I) (tab := tab) (dink := dink)
    (out := out) (L := 32) hmem hread256 (by decide) hlong

theorem barkKickPostCallMem_mload256_long {I : ExecutionEnv} {tab dink clip : UInt256}
    {mem out : ByteArray}
    (hmem : mem.size = 580)
    (hread256 : mem.readWithPadding 256 32 = UInt256.toByteArray clip)
    (hlong : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨256⟩ : UInt256).toNat ≥ (barkKickPostCallMem I mem out tab dink).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkKickPostCallMem I mem out tab dink).readWithPadding
          (⟨256⟩ : UInt256).toNat 32))) =
      clip := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨256⟩ : UInt256)) (v := clip)
    (by rw [barkKickPostCallMem_size_long hmem hlong hout]; decide)
    (by
      simpa [show (⟨256⟩ : UInt256).toNat = 256 by native_decide] using
        barkKickPostCallMem_read256_long (I := I) (tab := tab) (dink := dink)
          hmem hread256 hlong hout)

theorem barkKickPostCallMem_read384_long {I : ExecutionEnv} {tab dink : UInt256}
    {mem out : ByteArray}
    (hmem : mem.size = 580) (hlong : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkKickPostCallMem I mem out tab dink).readWithPadding 384 32 =
      out.extract 0 32 := by
  have hmin :
      (min barkKickOutSize (UInt256.ofNat out.size)).toNat = 32 := by
    exact umin_ofNat_right_toNat_of_ge (c := 32) (n := out.size)
      (by decide) hlong hout
  unfold barkKickPostCallMem
  rw [hmin]
  exact barkKickPostCallWrite_read384_32 (I := I) (tab := tab) (dink := dink)
    (out := out) hmem hlong

theorem barkKickPostCallMem_mload384_long {I : ExecutionEnv} {tab dink : UInt256}
    {mem out : ByteArray}
    (hmem : mem.size = 580) (hlong : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨384⟩ : UInt256).toNat ≥ (barkKickPostCallMem I mem out tab dink).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkKickPostCallMem I mem out tab dink).readWithPadding
          (⟨384⟩ : UInt256).toNat 32))) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) := by
  rw [if_neg (by
    rw [barkKickPostCallMem_size_long hmem hlong hout]
    decide)]
  change UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkKickPostCallMem I mem out tab dink).readWithPadding 384 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  rw [barkKickPostCallMem_read384_long hmem hlong hout]

abbrev barkBarkLogDinkMem (mem : ByteArray) (dink : UInt256) :
    ByteArray :=
  Reasoning.Theory.writeWord mem 384 dink

abbrev barkBarkLogDartMem (mem : ByteArray) (dink dart : UInt256) :
    ByteArray :=
  Reasoning.Theory.writeWord (barkBarkLogDinkMem mem dink) 416 dart

abbrev barkBarkLogDueMem (mem : ByteArray) (dink dart due : UInt256) :
    ByteArray :=
  Reasoning.Theory.writeWord (barkBarkLogDartMem mem dink dart) 448 due

abbrev barkBarkLogMem (mem : ByteArray) (dink dart due clip : UInt256) :
    ByteArray :=
  Reasoning.Theory.writeWord (barkBarkLogDueMem mem dink dart due) 480 clip

abbrev barkReturnIdMem (mem : ByteArray) (id : UInt256) : ByteArray :=
  (UInt256.toByteArray id).write 0 mem 384 32

theorem barkBarkLogDinkMem_size {mem : ByteArray} {dink : UInt256}
    (hmem : mem.size = 580) :
    (barkBarkLogDinkMem mem dink).size = 580 := by
  rw [barkBarkLogDinkMem,
    Reasoning.Theory.writeWord_size mem 384 dink (by rw [hmem]; native_decide),
    hmem]
  native_decide

theorem barkBarkLogDartMem_size {mem : ByteArray} {dink dart : UInt256}
    (hmem : mem.size = 580) :
    (barkBarkLogDartMem mem dink dart).size = 580 := by
  rw [barkBarkLogDartMem,
    Reasoning.Theory.writeWord_size (barkBarkLogDinkMem mem dink) 416 dart
      (by rw [barkBarkLogDinkMem_size hmem]; native_decide),
    barkBarkLogDinkMem_size hmem]
  native_decide

theorem barkBarkLogDueMem_size {mem : ByteArray} {dink dart due : UInt256}
    (hmem : mem.size = 580) :
    (barkBarkLogDueMem mem dink dart due).size = 580 := by
  rw [barkBarkLogDueMem,
    Reasoning.Theory.writeWord_size (barkBarkLogDartMem mem dink dart) 448 due
      (by rw [barkBarkLogDartMem_size hmem]; native_decide),
    barkBarkLogDartMem_size hmem]
  native_decide

theorem barkBarkLogMem_size {mem : ByteArray} {dink dart due clip : UInt256}
    (hmem : mem.size = 580) :
    (barkBarkLogMem mem dink dart due clip).size = 580 := by
  rw [barkBarkLogMem,
    Reasoning.Theory.writeWord_size (barkBarkLogDueMem mem dink dart due) 480 clip
      (by rw [barkBarkLogDueMem_size hmem]; native_decide),
    barkBarkLogDueMem_size hmem]
  native_decide

theorem barkBarkLogMem_read64 {mem : ByteArray} {dink dart due clip : UInt256}
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (barkBarkLogMem mem dink dart due clip).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  rw [barkBarkLogMem,
    Reasoning.Theory.writeWord_read_preserved (barkBarkLogDueMem mem dink dart due)
      480 64 clip
      (by rw [barkBarkLogDueMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkBarkLogDueMem_size hmem]; decide⟩)]
  rw [barkBarkLogDueMem,
    Reasoning.Theory.writeWord_read_preserved (barkBarkLogDartMem mem dink dart)
      448 64 due
      (by rw [barkBarkLogDartMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkBarkLogDartMem_size hmem]; decide⟩)]
  rw [barkBarkLogDartMem,
    Reasoning.Theory.writeWord_read_preserved (barkBarkLogDinkMem mem dink)
      416 64 dart
      (by rw [barkBarkLogDinkMem_size hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [barkBarkLogDinkMem_size hmem]; decide⟩)]
  rw [barkBarkLogDinkMem,
    Reasoning.Theory.writeWord_read_preserved mem 384 64 dink
      (by rw [hmem]; native_decide)
      (Or.inl ⟨by decide, by rw [hmem]; decide⟩)]
  exact hread64

theorem barkBarkLogMem_mload64 {mem : ByteArray} {dink dart due clip : UInt256}
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkBarkLogMem mem dink dart due clip).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkBarkLogMem mem dink dart due clip).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkBarkLogMem_size hmem]; decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
        barkBarkLogMem_read64 hmem hread64)

theorem barkReturnIdMem_size {mem : ByteArray} {id : UInt256}
    (hmem : mem.size = 580) :
    (barkReturnIdMem mem id).size = 580 := by
  unfold barkReturnIdMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem barkReturnIdMem_read64 {mem : ByteArray} {id : UInt256}
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (barkReturnIdMem mem id).readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩ := by
  unfold barkReturnIdMem
  rw [write_read_below_gen (UInt256.toByteArray id) mem 384 32 64
    (by decide) (by rw [toByteArray_size]) (by rw [hmem]; omega) (by omega)]
  exact hread64

theorem barkReturnIdMem_mload64 {mem : ByteArray} {id : UInt256}
    (hmem : mem.size = 580)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkReturnIdMem mem id).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkReturnIdMem mem id).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkReturnIdMem_size hmem]; decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
        barkReturnIdMem_read64 hmem hread64)

theorem barkReturnIdMem_read384 {mem : ByteArray} {id : UInt256}
    (hmem : mem.size = 580) :
    (barkReturnIdMem mem id).readWithPadding 384 32 = UInt256.toByteArray id := by
  unfold barkReturnIdMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  rw [toByteArray_extract_all]


abbrev barkPostIlksCodecopyErrorMem
    (code : ByteArray) (mem : ByteArray) : ByteArray :=
  code.write 4691 (barkPostIlksErrorStringMem2 (⟨42⟩ : UInt256) mem) 452 42

theorem barkPostIlksCodecopyErrorMem_size {code mem : ByteArray}
    (hmem : mem.size = 544) (hsrc : 4691 + 42 ≤ code.size) :
    (barkPostIlksCodecopyErrorMem code mem).size = 544 := by
  unfold barkPostIlksCodecopyErrorMem
  rw [write_eq_gen_from code (barkPostIlksErrorStringMem2 (⟨42⟩ : UInt256) mem)
    4691 452 42 (by decide) hsrc
    (by rw [barkPostIlksErrorStringMem2_size (⟨42⟩ : UInt256) hmem]; native_decide)]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract]
  rw [barkPostIlksErrorStringMem2_size (⟨42⟩ : UInt256) hmem]
  omega

theorem barkPostIlksCodecopyErrorMem_read64 {code mem : ByteArray}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hsrc : 4691 + 42 ≤ code.size) :
    (barkPostIlksCodecopyErrorMem code mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨384⟩ := by
  unfold barkPostIlksCodecopyErrorMem
  rw [write_eq_gen_from code (barkPostIlksErrorStringMem2 (⟨42⟩ : UInt256) mem)
    4691 452 42 (by decide) hsrc
    (by rw [barkPostIlksErrorStringMem2_size (⟨42⟩ : UInt256) hmem]; native_decide)]
  rw [readWithPadding_eq_extract _ 64 (by
    rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract]
    rw [barkPostIlksErrorStringMem2_size (⟨42⟩ : UInt256) hmem]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
    rw [barkPostIlksErrorStringMem2_size (⟨42⟩ : UInt256) hmem]
    omega)]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_extract]
    rw [barkPostIlksErrorStringMem2_size (⟨42⟩ : UInt256) hmem]
    omega)]
  rw [extract_prefix _ 452 64 96 (by omega)]
  rw [← readWithPadding_eq_extract _ 64
    (by rw [barkPostIlksErrorStringMem2_size (⟨42⟩ : UInt256) hmem]; omega)]
  exact barkPostIlksErrorStringMem2_read64 (⟨42⟩ : UInt256) hmem hread64

theorem barkPostIlksCodecopyErrorMem_mload64 {code mem : ByteArray}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hsrc : 4691 + 42 ≤ code.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkPostIlksCodecopyErrorMem code mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkPostIlksCodecopyErrorMem code mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (v := (⟨384⟩ : UInt256))
    (by rw [barkPostIlksCodecopyErrorMem_size hmem hsrc]; decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
        barkPostIlksCodecopyErrorMem_read64 hmem hread64 hsrc)

theorem barkVatIlksSelectorWord_extract :
    (UInt256.toByteArray barkVatIlksSelectorWord).extract 0 4 = vatIlksSelector := by
  native_decide

theorem barkVatIlksCallMem_read384_4 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksCallMem σ I mem out).readWithPadding 384 4 = vatIlksSelector := by
  have hSelectorSize := barkVatIlksSelectorMem_size (σ := σ) (I := I) hmem hlong hout
  unfold barkVatIlksCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap (barkIlkWord I)
      (barkVatIlksSelectorMem σ I mem out) 388 384 4
      (by rw [hSelectorSize]; omega) (by native_decide) (by omega) (by omega)
      (by rw [hSelectorSize]; native_decide)]
  unfold barkVatIlksSelectorMem Reasoning.Theory.writeWord
  change (barkVatIlksSelectorWord.toByteArray.write 0
    (barkIlksMem σ I mem out) 384 32).readWithPadding 384 4 = vatIlksSelector
  rw [toByteArray_write_read_window_of_gap barkVatIlksSelectorWord
      (barkIlksMem σ I mem out) 384 0 4
      (by omega) (by omega) (by omega)
      (by rw [barkIlksMem_size hmem hlong hout]; native_decide)]
  exact barkVatIlksSelectorWord_extract

theorem barkVatIlksCallMem_read388_32 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksCallMem σ I mem out).readWithPadding 388 32 =
      (barkIlkWord I).toByteArray := by
  unfold barkVatIlksCallMem Reasoning.Theory.writeWord
  rw [toByteArray_write_read_back_of_gap (barkIlkWord I)
      (barkVatIlksSelectorMem σ I mem out) 388
      (by rw [barkVatIlksSelectorMem_size hmem hlong hout]; native_decide)]

theorem barkVatIlksCallMem_read384_36 {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (barkVatIlksCallMem σ I mem out).readWithPadding 384 36 =
      vatIlksSelector ++ (barkIlkWord I).toByteArray := by
  have hsize : (barkVatIlksCallMem σ I mem out).size = 420 :=
    barkVatIlksCallMem_size hmem hlong hout
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split (barkVatIlksCallMem σ I mem out) 384 4 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [barkVatIlksCallMem_read384_4 hmem hlong hout,
    barkVatIlksCallMem_read388_32 hmem hlong hout]

theorem barkVatIlksEncodeWords {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    config.externalABI.encode? "ilks" [.fixedBytes bytes32Width (barkIlkBytes I)] =
      some (vatIlksSelector ++ (barkIlkWord I).toByteArray) := by
  have hIlk : ABI.encodeABIValue? bytes32 (.fixedBytes bytes32Width (barkIlkBytes I)) =
      some (EVM.Word.toBytesBE (barkIlkWord I)) := by
    have hbytes := barkIlkBytes_eq_toBytesBE (I := I) hsz100
    have hlen : (EVM.Word.toBytesBE (barkIlkWord I)).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size (barkIlkWord I)
    simp [ABI.encodeABIValue?, hlen, zeroBytes, bytes32, bytes32Width, hbytes]
  have hIlk' :
      ABI.encodeABIValue? (.elem (.bytes bytes32Width))
        (.fixedBytes bytes32Width (barkIlkBytes I)) =
          some (EVM.Word.toBytesBE (barkIlkWord I)) := by
    simpa [bytes32] using hIlk
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, hIlk', bytes32]
  apply ByteArray.ext
  simp [ByteArray.data_append, word_toBytesBE_toByteArray_eq_toByteArray]

theorem barkVatIlksEncode_eq {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hsz100 : 100 ≤ I.calldata.size)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    config.externalABI.encode? "ilks" [.fixedBytes bytes32Width (barkIlkBytes I)] =
      some ((barkVatIlksCallMem σ I mem out).readWithPadding 384 36) := by
  rw [barkVatIlksCallMem_read384_36 hmem hlong hout]
  exact barkVatIlksEncodeWords (I := I) hsz100

theorem dogLiveGuardEval_false {v : DogImmutables}
    {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : solcSlotWordAt ⟨3⟩ σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v }
      (initState σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have her :
      evalStorageRef config { contract := contract, locals := locals, immutables := immStore v }
        (initState σ σ₀ g A I) liveRef =
          .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
    simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  let w := Stele.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner ⟨3⟩
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hlive (by simpa [w, solcSlotWordAt] using hw)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar (hbackend := rfl)
    (t := .int uint256Int) (loc := wordLoc ⟨3⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      simp [config, storageLayout, solidityStorageBackend, storageLayoutRaw])]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals native_decide

theorem dogLiveGuardEval_true {v : DogImmutables}
    {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v }
      (initState σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have her :
      evalStorageRef config { contract := contract, locals := locals, immutables := immStore v }
        (initState σ σ₀ g A I) liveRef =
          .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
    simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  let w := Stele.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner ⟨3⟩
  have hload : w = ⟨1⟩ := by
    simpa [w, solcSlotWordAt] using hlive
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar (hbackend := rfl)
    (t := .int uint256Int) (loc := wordLoc ⟨3⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      simp [config, storageLayout, solidityStorageBackend, storageLayoutRaw])]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  have hload' :
      Stele.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner ⟨3⟩ = ⟨1⟩ := by
    simpa [w] using hload
  simp only [initState] at hload' ⊢
  rw [hload']
  simp [evalExpr?, evalBinaryOp?]
  all_goals native_decide

theorem dogAddrLitEval_locals {v : DogImmutables}
    {σ σ₀ A I} {g : Sat256} {locals : Store} (a : EVM.Address) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v }
      (initState σ σ₀ g A I) (Reasoning.Theory.addressLiteral a) =
      .ok (Value.address (AccountAddress.ofNat a.toNat)) := by
  dsimp [Reasoning.Theory.addressLiteral]
  have hint :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v }
        (initState σ σ₀ g A I) (.intLit (↑↑a)) =
        .ok (.int (↑↑a)) := by
    simp [evalExpr?, pure]
  unfold evalExpr?
  rw [hint]
  change (if (↑↑a : Int) < 0 then EvalResult.error EvalError.typeError
      else EvalResult.ok
        (Value.address (AccountAddress.ofNat (Int.toNat (↑↑a : Int))))) =
    EvalResult.ok (Value.address (AccountAddress.ofNat ↑a))
  rw [if_neg (by omega)]
  simp

theorem evalExpr_barkVat {v : DogImmutables}
    {σ σ₀ A I} {g : Sat256} {locals : Store} :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v }
      (initState σ σ₀ g A I) vatExpr =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
  exact dogVatEval

theorem evalExpr_barkVatCodeGuard_true {v : DogImmutables}
    {evm : EVM.State} {locals : Store}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm vatExpr =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)))
    (hcode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat]
  simpa using hcode

theorem evalExpr_barkVatCodeGuard_false {v : DogImmutables}
    {evm : EVM.State} {locals : Store}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm vatExpr =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)))
    (hcode :
      (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat]
  simpa using hcode

theorem evalExpr_barkAddressCodeGuard_true {v : DogImmutables}
    {evm : EVM.State} {locals : Store} {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat]
  simpa using hcode

theorem evalExpr_barkAddressCodeGuard_false {v : DogImmutables}
    {evm : EVM.State} {locals : Store} {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm receiver =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat
        ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat]
  simpa using hcode

theorem evalExprs_barkVatUrnsArgs {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I)))
    (hurn : locals.get? "urn" = some (.address (barkUrn I))) :
    evalExprs? config { contract := contract, locals := locals, immutables := immStore v } evm
      [.var "ilk", .var "urn"] =
        .ok [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] := by
  simp only [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]
  rw [hilk, hurn]
  rfl

theorem evalExprs_barkVatIlksArgs {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I))) :
    evalExprs? config { contract := contract, locals := locals, immutables := immStore v } evm
      [.var "ilk"] = .ok [.fixedBytes bytes32Width (barkIlkBytes I)] := by
  simp only [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]
  rw [hilk]
  rfl

theorem evalExpr_barkVatUrnInk {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {out : ByteArray}
    (hvatUrn : locals.get? "vatUrn" = some (barkVatUrnValue out)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.tupleGet (.var "vatUrn") 0) =
        .ok (.int (Int.ofNat (barkVatUrnsInkWord out).toNat)) := by
  have hvatUrn' : locals["vatUrn"]? = some (barkVatUrnValue out) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hvatUrn
  simp [evalExpr?, tupleGetValue?, EvalResult.bind, bind, EvalResult.ofOption, hvatUrn',
    barkVatUrnValue]

theorem evalExpr_barkVatUrnArt {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {out : ByteArray}
    (hvatUrn : locals.get? "vatUrn" = some (barkVatUrnValue out)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.tupleGet (.var "vatUrn") 1) =
        .ok (.int (Int.ofNat (barkVatUrnsArtWord out).toNat)) := by
  have hvatUrn' : locals["vatUrn"]? = some (barkVatUrnValue out) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hvatUrn
  simp [evalExpr?, tupleGetValue?, EvalResult.bind, bind, EvalResult.ofOption, hvatUrn',
    barkVatUrnValue]

theorem evalExpr_barkVatIlkRate {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {out : ByteArray}
    (hvatIlk : locals.get? "vatIlk" = some (barkVatIlkValue out)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.tupleGet (.var "vatIlk") 1) =
        .ok (.int (Int.ofNat (barkVatIlksRateWord out).toNat)) := by
  have hvatIlk' : locals["vatIlk"]? = some (barkVatIlkValue out) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hvatIlk
  simp [evalExpr?, tupleGetValue?, EvalResult.bind, bind, EvalResult.ofOption, hvatIlk',
    barkVatIlkValue, barkVatIlksReturnValues]

theorem evalExpr_barkVatIlkSpot {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {out : ByteArray}
    (hvatIlk : locals.get? "vatIlk" = some (barkVatIlkValue out)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.tupleGet (.var "vatIlk") 2) =
        .ok (.int (Int.ofNat (barkVatIlksSpotWord out).toNat)) := by
  have hvatIlk' : locals["vatIlk"]? = some (barkVatIlkValue out) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hvatIlk
  simp [evalExpr?, tupleGetValue?, EvalResult.bind, bind, EvalResult.ofOption, hvatIlk',
    barkVatIlkValue, barkVatIlksReturnValues]

theorem evalExpr_barkVatIlkDust {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {out : ByteArray}
    (hvatIlk : locals.get? "vatIlk" = some (barkVatIlkValue out)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.tupleGet (.var "vatIlk") 4) =
        .ok (.int (Int.ofNat (barkVatIlksDustWord out).toNat)) := by
  have hvatIlk' : locals["vatIlk"]? = some (barkVatIlkValue out) := by
    rw [← Std.HashMap.get?_eq_getElem?]
    exact hvatIlk
  simp [evalExpr?, tupleGetValue?, EvalResult.bind, bind, EvalResult.ofOption, hvatIlk',
    barkVatIlkValue, barkVatIlksReturnValues]

theorem evalExpr_bark_varUInt256 {v : DogImmutables} {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem evalExpr_bark_neg_asInt256_var {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat)))
    (hbound : value.toNat ≤ dogInt256LimitWord.toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (asInt256 (.unary .neg (asInt256 (.var name)))) =
        .ok (.int (-(Int.ofNat value.toNat))) := by
  have hbound' : value.toNat ≤ EVM.twoPow 255 := by
    simpa using hbound
  have hnormalize :
      normalizeInt int256Int (-normalizeInt int256Int (Int.ofNat value.toNat)) =
        -Int.ofNat value.toNat := by
    simpa [int256Int] using normalizeInt_sint256_neg_word_of_le value hbound'
  have hvar := evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
    (name := name) (value := value) h
  have hcast := evalExpr_cast_int (intType := int256Int) hvar
  have hneg := evalExpr_cast_neg_int (intType := int256Int) hcast
  calc
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (asInt256 (.unary .neg (asInt256 (.var name)))) =
        .ok (.int
          (normalizeInt int256Int (-normalizeInt int256Int (Int.ofNat value.toNat)))) := by
      simpa only [asInt256, int256St] using hneg
    _ = .ok (.int (-Int.ofNat value.toNat)) :=
      congrArg (fun i => EvalResult.ok (Value.int i)) hnormalize

theorem evalExpr_bark_mul256_ok {v : DogImmutables} {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = a * b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (mul256 x y) =
      .ok (.int (Int.ofNat prod.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : prod.toNat = a.toNat * b.toNat := by
    rw [hprod, umul_toNat a b hfit]
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_bark_mul256_revert {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (mul256 x y) =
      .revert := by
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem evalExpr_bark_sub256_ok {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b) (hle : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (sub256 x y) =
      .ok (.int (Int.ofNat diff.toNat)) := by
  have hdiffNat : diff.toNat = a.toNat - b.toNat := by
    rw [hdiff, usub_toNat hle]
  have hsubInt : (a.toNat : Int) - (b.toNat : Int) = ((a.toNat - b.toNat : Nat) : Int) :=
    (Int.ofNat_sub hle).symm
  have hltNat : a.toNat - b.toNat < UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    omega
  have hlt : ¬ ((a.toNat - b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hltNat))
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int]
  rw [if_neg]
  · rw [hsubInt, ← hdiffNat]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_le.mpr hbad) hle
    · rw [hsubInt] at hbad
      exact hlt hbad

theorem evalExpr_bark_add256_ok {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b) (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (add256 x y) =
      .ok (.int (Int.ofNat sum.toNat)) := by
  have hsumNat : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hlt : ¬ ((a.toNat + b.toNat : Nat) : Int) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int]
  rw [if_neg]
  · have hsumInt : (↑a.toNat + ↑b.toNat : Int) = ↑sum.toNat := by
      exact_mod_cast hsumNat.symm
    rw [hsumInt]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_bark_add256_revert {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (add256 x y) =
      .revert := by
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem evalExpr_bark_div_uint256_ok {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {x y : Expr} {a b q : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b ≠ ⟨0⟩)
    (hq : q = UInt256.div a b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.binary .div x y) =
      .ok (.int (Int.ofNat q.toNat)) := by
  have hbNat : ¬ b.toNat = 0 := by
    intro hzero
    exact hb (uint256_toNat_eq_zero hzero)
  have hqNat : q.toNat = a.toNat / b.toNat := by
    rw [hq, udiv_toNat]
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, hbNat, hqNat]

theorem evalExpr_bark_div_uint256_revert {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.binary .div x y) =
      .revert := by
  have hbNat : b.toNat = 0 := by
    simp [hb]
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, hbNat]

theorem evalExpr_bark_eq_int_true {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .eq lhs rhs) = .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem evalExpr_bark_eq_int_false {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .eq lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_lt_int_true {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.int b))
    (h : a < b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .lt lhs rhs) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_lt_int_false {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.int b))
    (h : ¬ a < b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .lt lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_gt_int_true {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.int b))
    (h : a > b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .gt lhs rhs) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_gt_int_false {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.int b))
    (h : ¬ a > b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .gt lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_le_int_true {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.int b))
    (h : a ≤ b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .le lhs rhs) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_le_int_false {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.int b))
    (h : ¬ a ≤ b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .le lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_ge_int_true {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.int b))
    (h : a ≥ b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .ge lhs rhs) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_ge_int_false {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.int b))
    (h : ¬ a ≥ b) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .ge lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_or_true_left {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .or lhs rhs) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem evalExpr_bark_or_false_right {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .or lhs rhs) = .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem evalExpr_bark_and_false_left {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.bool false)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .and lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem evalExpr_bark_and_true_right {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm lhs =
      .ok (.bool true))
    (hrhs : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .and lhs rhs) = .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem execBarkMinFunctionReturn {v : DogImmutables} (evm : EVM.State)
    (x y : UInt256) :
    ExecFuncBody config { contract := contract, locals := barkBinaryLocals x y, immutables := immStore v } evm
      minFunction.body
      (.returned { contract := contract, locals := barkBinaryLocals x y, immutables := immStore v } evm
        (some [.int (Int.ofNat ((if x.toNat ≤ y.toNat then x else y).toNat))])) := by
  let locals := barkBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
        (name := "x") (value := x) (barkBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
        (name := "y") (value := y) (barkBinaryLocals_get_y x y)
  by_cases hle : x.toNat ≤ y.toNat
  · have hcond :
        evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
          (.binary .le (.var "x") (.var "y")) = .ok (.bool true) := by
      simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]
      exact_mod_cast hle
    have hret :
        evalExprs? config { contract := contract, locals := locals, immutables := immStore v } evm
          [.var "x"] = .ok [.int (Int.ofNat x.toNat)] := by
      simp [evalExprs?, hx, EvalResult.bind, bind, pure]
    have hthen :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
          [.return [.var "x"]]
          (.returned { contract := contract, locals := locals, immutables := immStore v } evm
            (some [.int (Int.ofNat x.toNat)])) :=
      ExecBlock.consReturn (ExecStmt.return hret)
    have hblock :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
          minFunction.body
          (.returned { contract := contract, locals := locals, immutables := immStore v } evm
            (some [.int (Int.ofNat x.toNat)])) := by
      simpa [minFunction] using ExecBlock.consReturn (ExecStmt.iteTrue hcond hthen)
    simpa [ExecFuncBody, locals, hle] using ExecFuncBody.execBlockRet hblock
  · have hcond :
        evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
          (.binary .le (.var "x") (.var "y")) = .ok (.bool false) := by
      simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]
      exact_mod_cast (Nat.lt_of_not_ge hle)
    have hret :
        evalExprs? config { contract := contract, locals := locals, immutables := immStore v } evm
          [.var "y"] = .ok [.int (Int.ofNat y.toNat)] := by
      simp [evalExprs?, hy, EvalResult.bind, bind, pure]
    have helse :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
          [.return [.var "y"]]
          (.returned { contract := contract, locals := locals, immutables := immStore v } evm
            (some [.int (Int.ofNat y.toNat)])) :=
      ExecBlock.consReturn (ExecStmt.return hret)
    have hblock :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
          minFunction.body
          (.returned { contract := contract, locals := locals, immutables := immStore v } evm
            (some [.int (Int.ofNat y.toNat)])) := by
      simpa [minFunction] using ExecBlock.consReturn (ExecStmt.iteFalse hcond helse)
    simpa [ExecFuncBody, locals, hle] using ExecFuncBody.execBlockRet hblock


theorem evalExpr_barkVat_state {v : DogImmutables} {evm : EVM.State} {locals : Store} :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm vatExpr =
      .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
  exact dogVatEval

theorem evalExpr_barkStorageMilkClip {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I))) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.storage (ilksF (.var "ilk") "clip")) =
        .ok (.address (AccountAddress.ofNat
          (solcAddressSlotWord (barkIlksClipSlotFor I) evm.accountMap
            evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value (hbackend := rfl)
    (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v }) (evm := evm)
    (slot := ilksF (.var "ilk") "clip") (er := barkIlksClipEvaledRef I)
    (t := .address) (loc := addrLoc (barkIlksClipSlotFor I))
    (value := .address (AccountAddress.ofNat
      (solcAddressSlotWord (barkIlksClipSlotFor I) evm.accountMap
        evm.executionEnv).toNat))
    hilks
    (by
      have hkeyLen : (barkIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using barkIlkBytes_len32 (I := I) hsz100
      simp [barkIlksClipEvaledRef, barkIlkKey, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        ← Std.HashMap.get?_eq_getElem?, hilk, EvalResult.ofOption, EvalResult.bind, pure,
        bind, hkeyLen])
    (by simp [barkIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      IlkStructTy, addrSt])
    (by rfl)
    (by simpa [solcAddressSlotWord, solcSlotWordAt] using
      storageLocLoad_address_offset0 evm (barkIlksClipSlotFor I))

theorem evalExpr_barkStorageMilkChop {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I))) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.storage (ilksF (.var "ilk") "chop")) =
        .ok (.int (Int.ofNat
          (solcSlotWordAt (barkIlksChopSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value (hbackend := rfl)
    (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v }) (evm := evm)
    (slot := ilksF (.var "ilk") "chop") (er := barkIlksChopEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (barkIlksChopSlotFor I))
    (value := .int (Int.ofNat
      (solcSlotWordAt (barkIlksChopSlotFor I) evm.accountMap evm.executionEnv).toNat))
    hilks
    (by
      have hkeyLen : (barkIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using barkIlkBytes_len32 (I := I) hsz100
      simp [barkIlksChopEvaledRef, barkIlkKey, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        ← Std.HashMap.get?_eq_getElem?, hilk, EvalResult.ofOption, EvalResult.bind, pure,
        bind, hkeyLen])
    (by simp [barkIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      IlkStructTy, uint256St])
    (by rfl)
    (by simpa [solcSlotWordAt] using storageLocLoad_uint256 evm (barkIlksChopSlotFor I))

theorem evalExpr_barkStorageMilkHole {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I))) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.storage (ilksF (.var "ilk") "hole")) =
        .ok (.int (Int.ofNat
          (solcSlotWordAt (barkIlksHoleSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value (hbackend := rfl)
    (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v }) (evm := evm)
    (slot := ilksF (.var "ilk") "hole") (er := barkIlksHoleEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (barkIlksHoleSlotFor I))
    (value := .int (Int.ofNat
      (solcSlotWordAt (barkIlksHoleSlotFor I) evm.accountMap evm.executionEnv).toNat))
    hilks
    (by
      have hkeyLen : (barkIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using barkIlkBytes_len32 (I := I) hsz100
      simp [barkIlksHoleEvaledRef, barkIlkKey, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        ← Std.HashMap.get?_eq_getElem?, hilk, EvalResult.ofOption, EvalResult.bind, pure,
        bind, hkeyLen])
    (by simp [barkIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      IlkStructTy, uint256St])
    (by rfl)
    (by simpa [solcSlotWordAt] using storageLocLoad_uint256 evm (barkIlksHoleSlotFor I))

theorem evalExpr_barkStorageMilkDirt {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I))) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.storage (ilksF (.var "ilk") "dirt")) =
        .ok (.int (Int.ofNat
          (solcSlotWordAt (barkIlksDirtSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value (hbackend := rfl)
    (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v }) (evm := evm)
    (slot := ilksF (.var "ilk") "dirt") (er := barkIlksDirtEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (barkIlksDirtSlotFor I))
    (value := .int (Int.ofNat
      (solcSlotWordAt (barkIlksDirtSlotFor I) evm.accountMap evm.executionEnv).toNat))
    hilks
    (by
      have hkeyLen : (barkIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using barkIlkBytes_len32 (I := I) hsz100
      simp [barkIlksDirtEvaledRef, barkIlkKey, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        ← Std.HashMap.get?_eq_getElem?, hilk, EvalResult.ofOption, EvalResult.bind, pure,
        bind, hkeyLen])
    (by simp [barkIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
      IlkStructTy, uint256St])
    (by rfl)
    (by simpa [solcSlotWordAt] using storageLocLoad_uint256 evm (barkIlksDirtSlotFor I))

theorem evalExpr_barkStorageHole {v : DogImmutables} {evm : EVM.State}
    {locals : Store}
    (hHole : locals.get? "Hole" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.storage HoleRef) =
        .ok (.int (Int.ofNat (solcSlotWordAt ⟨4⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value (hbackend := rfl)
    (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v }) (evm := evm)
    (slot := HoleRef) (er := ({ base := "Hole", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨4⟩)
    (value := .int (Int.ofNat (solcSlotWordAt ⟨4⟩ evm.accountMap evm.executionEnv).toNat))
    hHole
    (by simp [evalStorageRef, evalStorageRefSteps, HoleRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [solcSlotWordAt] using storageLocLoad_uint256 evm ⟨4⟩)

theorem evalExpr_barkStorageDirt {v : DogImmutables} {evm : EVM.State}
    {locals : Store}
    (hDirt : locals.get? "Dirt" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.storage DirtRef) =
        .ok (.int (Int.ofNat (solcSlotWordAt ⟨5⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value (hbackend := rfl)
    (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v }) (evm := evm)
    (slot := DirtRef) (er := ({ base := "Dirt", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨5⟩)
    (value := .int (Int.ofNat (solcSlotWordAt ⟨5⟩ evm.accountMap evm.executionEnv).toNat))
    hDirt
    (by simp [evalStorageRef, evalStorageRefSteps, DirtRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [solcSlotWordAt] using storageLocLoad_uint256 evm ⟨5⟩)

theorem evalExpr_barkStorageVow {v : DogImmutables} {evm : EVM.State}
    {locals : Store}
    (hvow : locals.get? "vow" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm vowAddr =
      .ok (.address (AccountAddress.ofNat (barkVowWord evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value (hbackend := rfl)
    (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v }) (evm := evm)
    (slot := vowRef) (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨2⟩)
    (value := .address (AccountAddress.ofNat
      (barkVowWord evm.accountMap evm.executionEnv).toNat))
    hvow
    (by simp [evalStorageRef, evalStorageRefSteps, vowRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by simpa [barkVowWord, solcAddressSlotWord, u256_land_comm] using
      storageLocLoad_address_offset0 evm ⟨2⟩)

theorem evalExprs_barkVatGrabArgs {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {I : ExecutionEnv} {milkClip dink dart : UInt256}
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I)))
    (hurn : locals.get? "urn" = some (.address (barkUrn I)))
    (hmilkClip :
      locals.get? "milkClip" =
        some (.address (AccountAddress.ofNat milkClip.toNat)))
    (hvow : locals.get? "vow" = none)
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hdinkBound : dink.toNat ≤ dogInt256LimitWord.toNat)
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat) :
    evalExprs? config { contract := contract, locals := locals, immutables := immStore v } evm
      [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
        asInt256 (.unary .neg (asInt256 (.var "dink"))),
        asInt256 (.unary .neg (asInt256 (.var "dart"))) ] =
      .ok
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I),
          .address (AccountAddress.ofNat milkClip.toNat),
          .address (AccountAddress.ofNat
            (barkVowWord evm.accountMap evm.executionEnv).toNat),
          .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))] := by
  have hilkExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "ilk") =
        .ok (.fixedBytes bytes32Width (barkIlkBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") =
      .ok (.fixedBytes bytes32Width (barkIlkBytes I))
    rw [hilk]
    rfl
  have hurnExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "urn") =
        .ok (.address (barkUrn I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "urn") =
      .ok (.address (barkUrn I))
    rw [hurn]
    rfl
  have hmilkClipExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "milkClip") =
          .ok (.address (AccountAddress.ofNat milkClip.toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "milkClip") =
      .ok (.address (AccountAddress.ofNat milkClip.toNat))
    rw [hmilkClip]
    rfl
  have hvowExpr :=
    evalExpr_barkStorageVow (v := v) (evm := evm) (locals := locals) hvow
  have hdinkExpr :=
    evalExpr_bark_neg_asInt256_var (v := v) (evm := evm) (locals := locals)
      (name := "dink") (value := dink) hdink hdinkBound
  have hdartExpr :=
    evalExpr_bark_neg_asInt256_var (v := v) (evm := evm) (locals := locals)
      (name := "dart") (value := dart) hdart hdartBound
  simp [evalExprs?, hilkExpr, hurnExpr, hmilkClipExpr, hvowExpr, hdinkExpr, hdartExpr,
    EvalResult.bind, bind, pure]

theorem dogBarkVatGrabNoCodeBlock {v : DogImmutables} {evm : EVM.State}
    {locals : Store}
    (hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedExternalCallStmts vatExpr "grab" (.intLit 0)
        [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
          asInt256 (.unary .neg (asInt256 (.var "dink"))),
          asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet")
      .reverted := by
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm) (locals := locals)
      (receiver := vatExpr) (name := "grab") (sendVal := 0)
      (args :=
        [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
          asInt256 (.unary .neg (asInt256 (.var "dink"))),
          asInt256 (.unary .neg (asInt256 (.var "dart"))) ])
      (retVar := "_grabRet") (perm := true) hguard)

theorem dogBarkVatGrabCallFailureBlock {v : DogImmutables} {evm evm' : EVM.State}
    {locals : Store} {I : ExecutionEnv} {outGrab : ByteArray}
    {milkClip dink dart : UInt256}
    (hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool true))
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I)))
    (hurn : locals.get? "urn" = some (.address (barkUrn I)))
    (hmilkClip :
      locals.get? "milkClip" =
        some (.address (AccountAddress.ofNat milkClip.toNat)))
    (hvow : locals.get? "vow" = none)
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hdinkBound : dink.toNat ≤ dogInt256LimitWord.toNat)
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "grab" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I),
          .address (AccountAddress.ofNat milkClip.toNat),
          .address (AccountAddress.ofNat
            (barkVowWord evm.accountMap evm.executionEnv).toNat),
          .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))]
        (false, evm', outGrab) true) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedExternalCallStmts vatExpr "grab" (.intLit 0)
        [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
          asInt256 (.unary .neg (asInt256 (.var "dink"))),
          asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet")
      .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm vatExpr =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evm) (locals := locals)
  have hargs :=
    evalExprs_barkVatGrabArgs (v := v) (evm := evm) (locals := locals) (I := I)
      (milkClip := milkClip) (dink := dink) (dart := dart)
      hilk hurn hmilkClip hvow hdink hdart hdinkBound hdartBound
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallFailure (hperm := Or.inl rfl)
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := locals) (receiver := vatExpr) (retVar := "_grabRet")
      (name := "grab") (target := AccountAddress.ofNat v.vat.toNat) (sendVal := 0)
      (args :=
        [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
          asInt256 (.unary .neg (asInt256 (.var "dink"))),
          asInt256 (.unary .neg (asInt256 (.var "dart"))) ])
      (argVals :=
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I),
          .address (AccountAddress.ofNat milkClip.toNat),
          .address (AccountAddress.ofNat
            (barkVowWord evm.accountMap evm.executionEnv).toNat),
          .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))])
      (out := outGrab) (perm := true) hguard hreceiver hargs hcall)

theorem dogBarkVatGrabCallSuccessBlock {v : DogImmutables} {evm evm' : EVM.State}
    {locals : Store} {I : ExecutionEnv} {outGrab : ByteArray}
    {milkClip dink dart : UInt256}
    (hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool true))
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I)))
    (hurn : locals.get? "urn" = some (.address (barkUrn I)))
    (hmilkClip :
      locals.get? "milkClip" =
        some (.address (AccountAddress.ofNat milkClip.toNat)))
    (hvow : locals.get? "vow" = none)
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hdinkBound : dink.toNat ≤ dogInt256LimitWord.toNat)
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "grab" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I),
          .address (AccountAddress.ofNat milkClip.toNat),
          .address (AccountAddress.ofNat
            (barkVowWord evm.accountMap evm.executionEnv).toNat),
          .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))]
        (true, evm', outGrab) true) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedExternalCallStmts vatExpr "grab" (.intLit 0)
        [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
          asInt256 (.unary .neg (asInt256 (.var "dink"))),
          asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet")
      (.ok { contract := contract, locals := barkLocalsGrabRet locals, immutables := immStore v } evm') := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm vatExpr =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evm) (locals := locals)
  have hargs :=
    evalExprs_barkVatGrabArgs (v := v) (evm := evm) (locals := locals) (I := I)
      (milkClip := milkClip) (dink := dink) (dart := dart)
      hilk hurn hmilkClip hvow hdink hdart hdinkBound hdartBound
  have hdec : config.externalABI.decode? "grab" outGrab = some ([] : List Value) := by
    simp [config, externalABI, decodeVoid?]
  simpa [checkedExternalCallStmts, barkLocalsGrabRet] using
    (checkedExternalCallSuccess (hperm := Or.inl rfl)
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := locals) (receiver := vatExpr) (retVar := "_grabRet")
      (name := "grab") (target := AccountAddress.ofNat v.vat.toNat) (sendVal := 0)
      (args :=
        [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
          asInt256 (.unary .neg (asInt256 (.var "dink"))),
          asInt256 (.unary .neg (asInt256 (.var "dart"))) ])
      (argVals :=
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I),
          .address (AccountAddress.ofNat milkClip.toNat),
          .address (AccountAddress.ofNat
            (barkVowWord evm.accountMap evm.executionEnv).toNat),
          .int (-(Int.ofNat dink.toNat)), .int (-(Int.ofNat dart.toNat))])
      (out := outGrab) (perm := true) (value := []) hguard hreceiver hargs hcall hdec)

theorem dogBarkDueCheckedMulOkSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {dart rate : UInt256}
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hrate : locals.get? "rate" = some (.int (Int.ofNat rate.toNat)))
    (hfit : dart.toNat * rate.toNat < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto "due" (.var "dart") (.var "rate"))
      (.ok { contract := contract, locals := barkLocalsDue locals (barkDueWord dart rate), immutables := immStore v }
        evm) := by
  have hdartExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "dart") =
        .ok (.int (Int.ofNat dart.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dart") (value := dart) hdart
  have hrateExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "rate") =
        .ok (.int (Int.ofNat rate.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "rate") (value := rate) hrate
  let due := barkDueWord dart rate
  let locals1 := barkLocalsDue locals due
  have hmul :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (mul256 (.var "dart") (.var "rate")) = .ok (.int (Int.ofNat due.toNat)) := by
    exact evalExpr_bark_mul256_ok hdartExpr hrateExpr (by simp [due, barkDueWord]) hfit
  have hlet :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
        (.letDecl "due" (some uint256) (mul256 (.var "dart") (.var "rate")))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evm) := by
    simpa [locals1, due, barkLocalsDue] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v })
        (evm := evm) (name := "due") (ty := some uint256)
        (expr := mul256 (.var "dart") (.var "rate"))
        (value := .int (Int.ofNat due.toNat)) hmul)
  have hdueAfter :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.var "due") =
        .ok (.int (Int.ofNat due.toNat)) := by
    simpa [locals1, due] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "due") (value := due) (barkLocalsDue_get_due locals due)
  have hdartAfter :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.var "dart") =
        .ok (.int (Int.ofNat dart.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
      (name := "dart") (value := dart) (barkLocalsDue_get_preserved (by decide) hdart)
  have hrateAfter :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.var "rate") =
        .ok (.int (Int.ofNat rate.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
      (name := "rate") (value := rate) (barkLocalsDue_get_preserved (by decide) hrate)
  have hzero :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.binary .or
          (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "due") (.var "rate")) (.var "dart"))) =
        .ok (.bool true) := by
    by_cases hrateZero : rate = ⟨0⟩
    · have hleft :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.var "rate") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_bark_eq_int_true hrateAfter hzero
        simp [hrateZero]
      exact evalExpr_bark_or_true_left hleft
    · have hleft :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.var "rate") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_bark_eq_int_false hrateAfter hzero
        intro hnat
        exact hrateZero (uint256_toNat_eq_zero (Int.ofNat.inj hnat))
      have hdivWord : UInt256.div due rate = dart := by
        apply u256_inj
        rw [udiv_toNat]
        have hprod : due.toNat = dart.toNat * rate.toNat := by
          dsimp [due, barkDueWord]
          exact umul_toNat dart rate hfit
        rw [hprod]
        rw [Nat.mul_comm dart.toNat rate.toNat]
        exact Nat.mul_div_right dart.toNat
          (Nat.pos_of_ne_zero (fun hzeroNat => hrateZero (uint256_toNat_eq_zero hzeroNat)))
      have hdiv :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .div (.var "due") (.var "rate")) =
              .ok (.int (Int.ofNat dart.toNat)) := by
        have hraw := evalExpr_bark_div_uint256_ok
          (v := v) (evm := evm) (locals := locals1)
          (x := .var "due") (y := .var "rate")
          (a := due) (b := rate) (q := UInt256.div due rate)
          hdueAfter hrateAfter hrateZero rfl
        simpa [hdivWord] using hraw
      have hright :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.binary .div (.var "due") (.var "rate")) (.var "dart")) =
              .ok (.bool true) :=
        evalExpr_bark_eq_int_true hdiv hdartAfter rfl
      exact evalExpr_bark_or_false_right hleft hright
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal hlet
    (ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkDueCheckedMulOverflowSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {dart rate : UInt256}
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hrate : locals.get? "rate" = some (.int (Int.ofNat rate.toNat)))
    (hover : UInt256.size ≤ dart.toNat * rate.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto "due" (.var "dart") (.var "rate")) .reverted := by
  have hdartExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "dart") =
        .ok (.int (Int.ofNat dart.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dart") (value := dart) hdart
  have hrateExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "rate") =
        .ok (.int (Int.ofNat rate.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "rate") (value := rate) hrate
  have hmul :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (mul256 (.var "dart") (.var "rate")) = .revert :=
    evalExpr_bark_mul256_revert hdartExpr hrateExpr hover
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmul)

theorem evalExprs_barkVowFessArgs {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {due : UInt256}
    (hdue : locals.get? "due" = some (.int (Int.ofNat due.toNat))) :
    evalExprs? config { contract := contract, locals := locals, immutables := immStore v } evm [.var "due"] =
      .ok [.int (Int.ofNat due.toNat)] := by
  have hdueExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "due") =
        .ok (.int (Int.ofNat due.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "due") (value := due) hdue
  simp [evalExprs?, hdueExpr, EvalResult.bind, bind, pure]

theorem dogBarkVowFessNoCodeBlock {v : DogImmutables} {evm : EVM.State}
    {locals : Store}
    (hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.extCodeSize vowAddr) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet")
      .reverted := by
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm) (locals := locals)
      (receiver := vowAddr) (name := "fess") (sendVal := 0)
      (args := [.var "due"]) (retVar := "_fessRet") (perm := true) hguard)

theorem dogBarkVowFessCallFailureBlock {v : DogImmutables} {evm evm' : EVM.State}
    {locals : Store} {outFess : ByteArray} {due : UInt256}
    (hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.extCodeSize vowAddr) (.intLit 0)) = .ok (.bool true))
    (hvow : locals.get? "vow" = none)
    (hdue : locals.get? "due" = some (.int (Int.ofNat due.toNat)))
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat
          (barkVowWord evm.accountMap evm.executionEnv).toNat)) "fess" 0
        [.int (Int.ofNat due.toNat)] (false, evm', outFess) true) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet")
      .reverted := by
  have hreceiver :=
    evalExpr_barkStorageVow (v := v) (evm := evm) (locals := locals) hvow
  have hargs :=
    evalExprs_barkVowFessArgs (v := v) (evm := evm) (locals := locals) hdue
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallFailure (hperm := Or.inl rfl)
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := locals) (receiver := vowAddr) (retVar := "_fessRet")
      (name := "fess")
      (target := AccountAddress.ofNat
        (barkVowWord evm.accountMap evm.executionEnv).toNat)
      (sendVal := 0) (args := [.var "due"])
      (argVals := [.int (Int.ofNat due.toNat)]) (out := outFess) (perm := true)
      hguard hreceiver hargs hcall)

theorem dogBarkVowFessCallSuccessBlock {v : DogImmutables} {evm evm' : EVM.State}
    {locals : Store} {outFess : ByteArray} {due : UInt256}
    (hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.extCodeSize vowAddr) (.intLit 0)) = .ok (.bool true))
    (hvow : locals.get? "vow" = none)
    (hdue : locals.get? "due" = some (.int (Int.ofNat due.toNat)))
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat
          (barkVowWord evm.accountMap evm.executionEnv).toNat)) "fess" 0
        [.int (Int.ofNat due.toNat)] (true, evm', outFess) true) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet")
      (.ok { contract := contract, locals := barkLocalsFessRet locals, immutables := immStore v } evm') := by
  have hreceiver :=
    evalExpr_barkStorageVow (v := v) (evm := evm) (locals := locals) hvow
  have hargs :=
    evalExprs_barkVowFessArgs (v := v) (evm := evm) (locals := locals) hdue
  have hdec : config.externalABI.decode? "fess" outFess = some ([] : List Value) := by
    simp [config, externalABI, decodeVoid?]
  simpa [checkedExternalCallStmts, barkLocalsFessRet] using
    (checkedExternalCallSuccess (hperm := Or.inl rfl)
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := locals) (receiver := vowAddr) (retVar := "_fessRet")
      (name := "fess")
      (target := AccountAddress.ofNat
        (barkVowWord evm.accountMap evm.executionEnv).toNat)
      (sendVal := 0) (args := [.var "due"])
      (argVals := [.int (Int.ofNat due.toNat)]) (out := outFess) (perm := true)
      (value := []) hguard hreceiver hargs hcall hdec)

theorem assign_barkDirtStorage {v : DogImmutables} (evm : EVM.State)
    {locals : Store} (dirtNew : UInt256) (hbase : locals.get? "Dirt" = none) :
    let evm' := Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ dirtNew
    assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm
      .storage DirtRef (.int (Int.ofNat dirtNew.toNat)) =
        .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm') := by
  intro evm'
  have hstore :
      storageLocStore evm (wordLoc ⟨5⟩) (.int (Int.ofNat dirtNew.toNat)) =
        some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨5⟩ dirtNew
  exact assignStorageRef_storage_scalar (hbackend := rfl)
    (er := ({ base := "Dirt", steps := [] } : EvaledStorageRef))
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩) (hleaf := by first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩)
    (hbase := hbase)
    (her := by simp [DirtRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hstore := hstore)

theorem assign_barkIlkDirtStorage {v : DogImmutables} (evm : EVM.State)
    {I : ExecutionEnv} {locals : Store} (hsz100 : 100 ≤ I.calldata.size)
    (ilkDirtNew : UInt256)
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (barkIlkValue I)) :
    let evm' := Stele.EVM.storageStore evm evm.executionEnv.codeOwner
      (barkIlksDirtSlotFor I) ilkDirtNew
    assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm
      .storage (ilksF (.var "ilk") "dirt") (.int (Int.ofNat ilkDirtNew.toNat)) =
        .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm') := by
  intro evm'
  have hkeyLen : (barkIlkBytes I).length = bytes32Width.val + 1 := by
    simpa [bytes32Width] using barkIlkBytes_len32 (I := I) hsz100
  have hvar :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "ilk") =
        .ok (barkIlkValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") =
      .ok (barkIlkValue I)
    rw [hilk]
    rfl
  have hstore :
      storageLocStore evm (wordLoc (barkIlksDirtSlotFor I))
          (.int (Int.ofNat ilkDirtNew.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm (barkIlksDirtSlotFor I) ilkDirtNew
  exact assignStorageRef_storage_scalar (hbackend := rfl)
    (er := barkIlksDirtEvaledRef I)
    (ty := .elem (.int uint256Int)) (loc := wordLoc (barkIlksDirtSlotFor I)) (hleaf := by first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩)
    (hbase := hbase)
    (her := by
      simp [barkIlksDirtEvaledRef, barkIlkKey, barkIlkValue, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, ilksF, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen, hvar])
    (hty := by simp [barkIlkKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, IlkStructTy, uint256St])
    (hloc := by rfl)
    (hstore := hstore)

theorem barkVat_eq_vatKey (v : DogImmutables) :
    AccountAddress.ofNat v.vat.toNat = AccountAddress.ofUInt256 (barkVatWord v) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  have hword : (barkVatWord v).toNat = v.vat.toNat := by
    change (UInt256.ofNat v.vat.toNat).toNat = v.vat.toNat
    rw [UInt256.toNat_ofNat_of_lt]
    exact lt_of_lt_of_le v.vat.isLt (show AccountAddress.size ≤ UInt256.size from by decide)
  rw [hword]

theorem barkVatCode_zero_of_codeSize_zero {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  rw [barkVat_eq_vatKey v]
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.get? (AccountAddress.ofUInt256 (barkVatWord v)) with
  | none =>
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, initState, State.lookupAccount, hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, initState, State.lookupAccount, hacc] using hword

theorem barkVatCode_pos_of_codeSize_ne {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat := by
  rw [barkVat_eq_vatKey v]
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.get? (AccountAddress.ofUInt256 (barkVatWord v)) with
  | none =>
      exfalso
      exact hne (by simp [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, initState, State.lookupAccount, hacc] using Nat.pos_of_ne_zero htoNatNe

theorem barkVatCode_zero_of_state_codeSize_zero {v : DogImmutables} {evm : EVM.State}
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (barkVatWord v) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  rw [barkVat_eq_vatKey v]
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : evm.accountMap.get? (AccountAddress.ofUInt256 (barkVatWord v)) with
  | none =>
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount, hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount, hacc] using hword

theorem barkVatCode_pos_of_state_codeSize_ne {v : DogImmutables} {evm : EVM.State}
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap (barkVatWord v) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
        (fun acc => acc.code.size))).toNat := by
  rw [barkVat_eq_vatKey v]
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : evm.accountMap.get? (AccountAddress.ofUInt256 (barkVatWord v)) with
  | none =>
      exfalso
      exact hne (by simp [-Std.ExtTreeMap.get?_eq_getElem?, hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, State.lookupAccount, hacc] using Nat.pos_of_ne_zero htoNatNe


theorem dogBarkVatUrnsNoCodeSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodeZero :
      (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, locals] using
      dogLiveGuardEval_true (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I) (barkLocals_get_live I) hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 vatExpr =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
    simpa [evm0, locals] using
      (evalExpr_barkVat (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I))
  have hcodeGuard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_barkVatCodeGuard_false (v := v) (locals := locals) hvat
      (by simpa [evm0] using hcodeZero)
  have hcallvalue :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 3) .reverted := by
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hcallvalue) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) <|
          ExecBlock.consRevert (ExecStmt.requireFalse hcodeGuard) :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
          [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) ]
          .reverted)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hfull :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
          (barkTransition.body.take 3 ++ barkTransition.body.drop 3)
          .reverted :=
      execBlock_append_term (s2 := barkTransition.body.drop 3) hprefix
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatUrnsCallFailureSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256} {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (false, evmCall, out) false) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, locals] using
      dogLiveGuardEval_true (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I) (barkLocals_get_live I) hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 vatExpr =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
    simpa [evm0, locals] using
      (evalExpr_barkVat (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I))
  have hcodeGuard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_barkVatCodeGuard_true (v := v) (locals := locals) hvat
      (by simpa [evm0] using hcodePos)
  have hargs :
      evalExprs? config { contract := contract, locals := locals, immutables := immStore v } evm0
        [.var "ilk", .var "urn"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] :=
    evalExprs_barkVatUrnsArgs (v := v) (evm := evm0) (I := I)
      (locals := locals)
      (by simpa [locals] using barkLocals_get_ilk I)
      (by simpa [locals] using barkLocals_get_urn I)
  have hcall' :
      typedCallViaEVM config evm0 (EVM.address (AccountAddress.ofNat v.vat.toNat))
        "urns" 0 [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (false, evmCall, out) false := by
    simpa [evm0] using hcall
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.externalCall vatExpr "urns" (.intLit 0) [.var "ilk", .var "urn"]
          "vatUrn" (perm := false))
        .reverted :=
    ExecStmt.externalCallFailure (hperm := Or.inl rfl) hvat (by simp [evalExpr?, pure]) hargs hcall'
  have hcallvalue :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 4) .reverted := by
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hcallvalue) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) <|
          ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
            ExecBlock.consRevert hcallStmt :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
          [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .gt (.extCodeSize vatExpr) (.intLit 0)),
            .externalCall vatExpr "urns" (.intLit 0) [.var "ilk", .var "urn"]
              "vatUrn" (perm := false) ]
          .reverted)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hfull :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
          (barkTransition.body.take 4 ++ barkTransition.body.drop 4)
          .reverted :=
      execBlock_append_term (s2 := barkTransition.body.drop 4) hprefix
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatUrnsDecodeRevertSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256} {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmCall, out) false)
    (hdec : config.externalABI.decode? "urns" out = none) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, locals] using
      dogLiveGuardEval_true (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I) (barkLocals_get_live I) hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 vatExpr =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
    simpa [evm0, locals] using
      (evalExpr_barkVat (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I))
  have hcodeGuard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_barkVatCodeGuard_true (v := v) (locals := locals) hvat
      (by simpa [evm0] using hcodePos)
  have hargs :
      evalExprs? config { contract := contract, locals := locals, immutables := immStore v } evm0
        [.var "ilk", .var "urn"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] :=
    evalExprs_barkVatUrnsArgs (v := v) (evm := evm0) (I := I)
      (locals := locals)
      (by simpa [locals] using barkLocals_get_ilk I)
      (by simpa [locals] using barkLocals_get_urn I)
  have hcall' :
      typedCallViaEVM config evm0 (EVM.address (AccountAddress.ofNat v.vat.toNat))
        "urns" 0 [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmCall, out) false := by
    simpa [evm0] using hcall
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.externalCall vatExpr "urns" (.intLit 0) [.var "ilk", .var "urn"]
          "vatUrn" (perm := false))
        .reverted :=
    ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) hvat (by simp [evalExpr?, pure]) hargs
      hcall' hdec
  have hcallvalue :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 4) .reverted := by
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hcallvalue) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) <|
          ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
            ExecBlock.consRevert hcallStmt :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
          [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .gt (.extCodeSize vatExpr) (.intLit 0)),
            .externalCall vatExpr "urns" (.intLit 0) [.var "ilk", .var "urn"]
              "vatUrn" (perm := false) ]
          .reverted)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hfull :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
          (barkTransition.body.take 4 ++ barkTransition.body.drop 4)
          .reverted :=
      execBlock_append_term (s2 := barkTransition.body.drop 4) hprefix
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatUrnsSuccessIlksPrefix {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256} {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmCall, out) false)
    (hdec : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
      (barkTransition.body.take 10)
      (.ok { contract := contract, locals := barkLocalsMilkDirt evmCall I out, immutables := immStore v }
        evmCall) := by
  intro locals evm0
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, locals] using
      dogLiveGuardEval_true (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I) (barkLocals_get_live I) hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 vatExpr =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
    simpa [evm0, locals] using
      (evalExpr_barkVat (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I))
  have hcodeGuard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_barkVatCodeGuard_true (v := v) (locals := locals) hvat
      (by simpa [evm0] using hcodePos)
  have hargs :
      evalExprs? config { contract := contract, locals := locals, immutables := immStore v } evm0
        [.var "ilk", .var "urn"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] :=
    evalExprs_barkVatUrnsArgs (v := v) (evm := evm0) (I := I)
      (locals := locals)
      (by simpa [locals] using barkLocals_get_ilk I)
      (by simpa [locals] using barkLocals_get_urn I)
  have hcall' :
      typedCallViaEVM config evm0 (EVM.address (AccountAddress.ofNat v.vat.toNat))
        "urns" 0 [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmCall, out) false := by
    simpa [evm0] using hcall
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.externalCall vatExpr "urns" (.intLit 0) [.var "ilk", .var "urn"]
          "vatUrn" (perm := false))
        (.ok { contract := contract, locals := barkLocalsVatUrn I out, immutables := immStore v } evmCall) := by
    have heth :
        evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
          (.intLit 0) = .ok (.int 0) := by
      simp [evalExpr?, pure]
    simpa [locals, barkLocalsVatUrn, barkVatUrnValue, collapseReturns] using
      (ExecStmt.externalCallSuccess (hperm := Or.inl rfl) (retVar := "vatUrn") hvat heth hargs hcall' hdec)
  have hinkExpr :
      evalExpr? config { contract := contract, locals := barkLocalsVatUrn I out, immutables := immStore v }
        evmCall (.tupleGet (.var "vatUrn") 0) =
          .ok (.int (Int.ofNat (barkVatUrnsInkWord out).toNat)) :=
    evalExpr_barkVatUrnInk (v := v) (evm := evmCall)
      (locals := barkLocalsVatUrn I out) (out := out)
      (barkLocalsVatUrn_get_vatUrn I out)
  have hinkStmt :
      ExecStmt config { contract := contract, locals := barkLocalsVatUrn I out, immutables := immStore v }
        evmCall (.letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0))
        (.ok { contract := contract, locals := barkLocalsInk I out, immutables := immStore v } evmCall) := by
    simpa [barkLocalsInk] using (ExecStmt.letDecl (cfg := config) hinkExpr)
  have hartExpr :
      evalExpr? config { contract := contract, locals := barkLocalsInk I out, immutables := immStore v }
        evmCall (.tupleGet (.var "vatUrn") 1) =
          .ok (.int (Int.ofNat (barkVatUrnsArtWord out).toNat)) :=
    evalExpr_barkVatUrnArt (v := v) (evm := evmCall)
      (locals := barkLocalsInk I out) (out := out)
      (barkLocalsInk_get_vatUrn I out)
  have hartStmt :
      ExecStmt config { contract := contract, locals := barkLocalsInk I out, immutables := immStore v }
        evmCall (.letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1))
        (.ok { contract := contract, locals := barkLocalsArt I out, immutables := immStore v } evmCall) := by
    simpa [barkLocalsArt] using (ExecStmt.letDecl (cfg := config) hartExpr)
  have hclipExpr :
      evalExpr? config { contract := contract, locals := barkLocalsArt I out, immutables := immStore v }
        evmCall (.storage (ilksF (.var "ilk") "clip")) =
          .ok (.address (AccountAddress.ofNat
            (solcAddressSlotWord (barkIlksClipSlotFor I) evmCall.accountMap
              evmCall.executionEnv).toNat)) :=
    evalExpr_barkStorageMilkClip (v := v) (evm := evmCall)
      (locals := barkLocalsArt I out) (I := I) hsz100
      (barkLocalsArt_get_ilks I out) (barkLocalsArt_get_ilk I out)
  have hclipStmt :
      ExecStmt config { contract := contract, locals := barkLocalsArt I out, immutables := immStore v }
        evmCall (.letDecl "milkClip" (some addr) (.storage (ilksF (.var "ilk") "clip")))
        (.ok { contract := contract, locals := barkLocalsMilkClip evmCall I out, immutables := immStore v }
          evmCall) := by
    simpa [barkLocalsMilkClip] using (ExecStmt.letDecl (cfg := config) hclipExpr)
  have hchopExpr :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkClip evmCall I out, immutables := immStore v } evmCall
        (.storage (ilksF (.var "ilk") "chop")) =
          .ok (.int (Int.ofNat
            (solcSlotWordAt (barkIlksChopSlotFor I) evmCall.accountMap
              evmCall.executionEnv).toNat)) :=
    evalExpr_barkStorageMilkChop (v := v) (evm := evmCall)
      (locals := barkLocalsMilkClip evmCall I out) (I := I) hsz100
      (barkLocalsMilkClip_get_ilks evmCall I out)
      (barkLocalsMilkClip_get_ilk evmCall I out)
  have hchopStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsMilkClip evmCall I out, immutables := immStore v } evmCall
        (.letDecl "milkChop" (some uint256) (.storage (ilksF (.var "ilk") "chop")))
        (.ok { contract := contract, locals := barkLocalsMilkChop evmCall I out, immutables := immStore v }
          evmCall) := by
    simpa [barkLocalsMilkChop] using (ExecStmt.letDecl (cfg := config) hchopExpr)
  have hholeExpr :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkChop evmCall I out, immutables := immStore v } evmCall
        (.storage (ilksF (.var "ilk") "hole")) =
          .ok (.int (Int.ofNat
            (solcSlotWordAt (barkIlksHoleSlotFor I) evmCall.accountMap
              evmCall.executionEnv).toNat)) :=
    evalExpr_barkStorageMilkHole (v := v) (evm := evmCall)
      (locals := barkLocalsMilkChop evmCall I out) (I := I) hsz100
      (barkLocalsMilkChop_get_ilks evmCall I out)
      (barkLocalsMilkChop_get_ilk evmCall I out)
  have hholeStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsMilkChop evmCall I out, immutables := immStore v } evmCall
        (.letDecl "milkHole" (some uint256) (.storage (ilksF (.var "ilk") "hole")))
        (.ok { contract := contract, locals := barkLocalsMilkHole evmCall I out, immutables := immStore v }
          evmCall) := by
    simpa [barkLocalsMilkHole] using (ExecStmt.letDecl (cfg := config) hholeExpr)
  have hdirtExpr :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkHole evmCall I out, immutables := immStore v } evmCall
        (.storage (ilksF (.var "ilk") "dirt")) =
          .ok (.int (Int.ofNat
            (solcSlotWordAt (barkIlksDirtSlotFor I) evmCall.accountMap
              evmCall.executionEnv).toNat)) :=
    evalExpr_barkStorageMilkDirt (v := v) (evm := evmCall)
      (locals := barkLocalsMilkHole evmCall I out) (I := I) hsz100
      (barkLocalsMilkHole_get_ilks evmCall I out)
      (barkLocalsMilkHole_get_ilk evmCall I out)
  have hdirtStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsMilkHole evmCall I out, immutables := immStore v } evmCall
        (.letDecl "milkDirt" (some uint256) (.storage (ilksF (.var "ilk") "dirt")))
        (.ok { contract := contract, locals := barkLocalsMilkDirt evmCall I out, immutables := immStore v }
          evmCall) := by
    simpa [barkLocalsMilkDirt] using (ExecStmt.letDecl (cfg := config) hdirtExpr)
  have hcallvalue :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using
    (ExecBlock.consNormal (ExecStmt.requireTrue hcallvalue) <|
      ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
          ExecBlock.consNormal hcallStmt <|
            ExecBlock.consNormal hinkStmt <|
              ExecBlock.consNormal hartStmt <|
                ExecBlock.consNormal hclipStmt <|
                  ExecBlock.consNormal hchopStmt <|
                    ExecBlock.consNormal hholeStmt <|
                      ExecBlock.consNormal hdirtStmt ExecBlock.nil :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .gt (.extCodeSize vatExpr) (.intLit 0)),
          .externalCall vatExpr "urns" (.intLit 0) [.var "ilk", .var "urn"]
            "vatUrn" (perm := false),
          .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
          .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
          .letDecl "milkClip" (some addr) (.storage (ilksF (.var "ilk") "clip")),
          .letDecl "milkChop" (some uint256) (.storage (ilksF (.var "ilk") "chop")),
          .letDecl "milkHole" (some uint256) (.storage (ilksF (.var "ilk") "hole")),
          .letDecl "milkDirt" (some uint256) (.storage (ilksF (.var "ilk") "dirt")) ]
        (.ok { contract := contract, locals := barkLocalsMilkDirt evmCall I out, immutables := immStore v }
          evmCall))

theorem dogBarkVatIlksNoCodeSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256} {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodeZero :
      (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 10)
        (.ok { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
          evmUrns) := by
    simpa [locals, evm0] using
      dogBarkVatUrnsSuccessIlksPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCall := evmUrns) (out := out) hwv hlive hcodePos hcallUrns hdecUrns hsz100
  have hvat :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns vatExpr =
          .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evmUrns)
      (locals := barkLocalsMilkDirt evmUrns I out)
  have hcodeGuard :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_barkVatCodeGuard_false (v := v)
      (locals := barkLocalsMilkDirt evmUrns I out) hvat hcodeZero
  have hsecond :
      ExecBlock config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v } evmUrns
        [ .require (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) ] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse hcodeGuard)
  have hprefixRevert :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 11) .reverted := by
    have hcombined := execBlock_append hprefix hsecond
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using hcombined
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hfull :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
          (barkTransition.body.take 11 ++ barkTransition.body.drop 11)
          .reverted :=
      execBlock_append_term (s2 := barkTransition.body.drop 11) hprefixRevert
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksCallFailureSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM config evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (false, evmIlks, outIlks) false)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 10)
        (.ok { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
          evmUrns) := by
    simpa [locals, evm0] using
      dogBarkVatUrnsSuccessIlksPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCall := evmUrns) (out := out) hwv hlive hcodePos hcallUrns hdecUrns hsz100
  have hvat :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns vatExpr =
          .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evmUrns)
      (locals := barkLocalsMilkDirt evmUrns I out)
  have hcodeGuard :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_barkVatCodeGuard_true (v := v)
      (locals := barkLocalsMilkDirt evmUrns I out) hvat hcodePosIlks
  have hargs :
      evalExprs? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns [.var "ilk"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I)] :=
    evalExprs_barkVatIlksArgs (v := v) (evm := evmUrns) (I := I)
      (locals := barkLocalsMilkDirt evmUrns I out)
      (barkLocalsMilkDirt_get_ilk evmUrns I out)
  have heth :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hcallStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v } evmUrns
        (.externalCall vatExpr "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
          (perm := false))
        .reverted :=
    ExecStmt.externalCallFailure (hperm := Or.inl rfl) hvat heth hargs hcallIlks
  have hsecond :
      ExecBlock config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v } evmUrns
        [ .require (.binary .gt (.extCodeSize vatExpr) (.intLit 0)),
          .externalCall vatExpr "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
            (perm := false) ] .reverted :=
    ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
      ExecBlock.consRevert hcallStmt
  have hprefixRevert :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 12) .reverted := by
    have hcombined := execBlock_append hprefix hsecond
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using hcombined
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hfull :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
          (barkTransition.body.take 12 ++ barkTransition.body.drop 12)
          .reverted :=
      execBlock_append_term (s2 := barkTransition.body.drop 12) hprefixRevert
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksDecodeRevertSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM config evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : config.externalABI.decode? "ilks" outIlks = none)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 10)
        (.ok { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
          evmUrns) := by
    simpa [locals, evm0] using
      dogBarkVatUrnsSuccessIlksPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCall := evmUrns) (out := out) hwv hlive hcodePos hcallUrns hdecUrns hsz100
  have hvat :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns vatExpr =
          .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evmUrns)
      (locals := barkLocalsMilkDirt evmUrns I out)
  have hcodeGuard :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_barkVatCodeGuard_true (v := v)
      (locals := barkLocalsMilkDirt evmUrns I out) hvat hcodePosIlks
  have hargs :
      evalExprs? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns [.var "ilk"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I)] :=
    evalExprs_barkVatIlksArgs (v := v) (evm := evmUrns) (I := I)
      (locals := barkLocalsMilkDirt evmUrns I out)
      (barkLocalsMilkDirt_get_ilk evmUrns I out)
  have heth :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hcallStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v } evmUrns
        (.externalCall vatExpr "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
          (perm := false))
        .reverted :=
    ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) hvat heth hargs hcallIlks hdecIlks
  have hsecond :
      ExecBlock config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v } evmUrns
        [ .require (.binary .gt (.extCodeSize vatExpr) (.intLit 0)),
          .externalCall vatExpr "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
            (perm := false) ] .reverted :=
    ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
      ExecBlock.consRevert hcallStmt
  have hprefixRevert :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 12) .reverted := by
    have hcombined := execBlock_append hprefix hsecond
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using hcombined
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hfull :
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
          (barkTransition.body.take 12 ++ barkTransition.body.drop 12)
          .reverted :=
      execBlock_append_term (s2 := barkTransition.body.drop 12) hprefixRevert
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksSuccessDustPrefix {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM config evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : config.externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
      (barkTransition.body.take 15)
      (.ok { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks) := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 10)
        (.ok { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
          evmUrns) := by
    simpa [locals, evm0] using
      dogBarkVatUrnsSuccessIlksPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCall := evmUrns) (out := out) hwv hlive hcodePos hcallUrns hdecUrns hsz100
  have hvat :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns vatExpr =
          .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evmUrns)
      (locals := barkLocalsMilkDirt evmUrns I out)
  have hcodeGuard :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_barkVatCodeGuard_true (v := v)
      (locals := barkLocalsMilkDirt evmUrns I out) hvat hcodePosIlks
  have hargs :
      evalExprs? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns [.var "ilk"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I)] :=
    evalExprs_barkVatIlksArgs (v := v) (evm := evmUrns) (I := I)
      (locals := barkLocalsMilkDirt evmUrns I out)
      (barkLocalsMilkDirt_get_ilk evmUrns I out)
  have heth :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hcallStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v } evmUrns
        (.externalCall vatExpr "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
          (perm := false))
        (.ok { contract := contract, locals := barkLocalsVatIlk evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [barkLocalsVatIlk, barkVatIlkValue, collapseReturns] using
      (ExecStmt.externalCallSuccess (hperm := Or.inl rfl) (retVar := "vatIlk") hvat heth hargs hcallIlks hdecIlks)
  have hrateExpr :
      evalExpr? config
        { contract := contract, locals := barkLocalsVatIlk evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.tupleGet (.var "vatIlk") 1) =
          .ok (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) :=
    evalExpr_barkVatIlkRate (v := v) (evm := evmIlks)
      (locals := barkLocalsVatIlk evmUrns I out outIlks) (out := outIlks)
      (barkLocalsVatIlk_get_vatIlk evmUrns I out outIlks)
  have hrateStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsVatIlk evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := barkLocalsRate evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [barkLocalsRate] using (ExecStmt.letDecl (cfg := config) hrateExpr)
  have hspotExpr :
      evalExpr? config
        { contract := contract, locals := barkLocalsRate evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.tupleGet (.var "vatIlk") 2) =
          .ok (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat)) :=
    evalExpr_barkVatIlkSpot (v := v) (evm := evmIlks)
      (locals := barkLocalsRate evmUrns I out outIlks) (out := outIlks)
      (barkLocalsRate_get_vatIlk evmUrns I out outIlks)
  have hspotStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsRate evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2))
        (.ok { contract := contract, locals := barkLocalsSpot evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [barkLocalsSpot] using (ExecStmt.letDecl (cfg := config) hspotExpr)
  have hdustExpr :
      evalExpr? config
        { contract := contract, locals := barkLocalsSpot evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.tupleGet (.var "vatIlk") 4) =
          .ok (.int (Int.ofNat (barkVatIlksDustWord outIlks).toNat)) :=
    evalExpr_barkVatIlkDust (v := v) (evm := evmIlks)
      (locals := barkLocalsSpot evmUrns I out outIlks) (out := outIlks)
      (barkLocalsSpot_get_vatIlk evmUrns I out outIlks)
  have hdustStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsSpot evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4))
        (.ok { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [barkLocalsDust] using (ExecStmt.letDecl (cfg := config) hdustExpr)
  have hsecond :
      ExecBlock config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v } evmUrns
        [ .require (.binary .gt (.extCodeSize vatExpr) (.intLit 0)),
          .externalCall vatExpr "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
            (perm := false),
          .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2),
          .letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4) ]
        (.ok { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
      ExecBlock.consNormal hcallStmt <|
        ExecBlock.consNormal hrateStmt <|
          ExecBlock.consNormal hspotStmt <|
            ExecBlock.consNormal hdustStmt ExecBlock.nil
  have hcombined := execBlock_append hprefix hsecond
  simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using hcombined

theorem dogBarkVatIlksInkSpotOverflowSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM config evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : config.externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hfitOverflow :
      UInt256.size ≤ (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 10)
        (.ok { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
          evmUrns) := by
    simpa [locals, evm0] using
      dogBarkVatUrnsSuccessIlksPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCall := evmUrns) (out := out) hwv hlive hcodePos hcallUrns hdecUrns hsz100
  have hvat :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns vatExpr =
          .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evmUrns)
      (locals := barkLocalsMilkDirt evmUrns I out)
  have hcodeGuard :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns (.binary .gt (.extCodeSize vatExpr) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_barkVatCodeGuard_true (v := v)
      (locals := barkLocalsMilkDirt evmUrns I out) hvat hcodePosIlks
  have hargs :
      evalExprs? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns [.var "ilk"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I)] :=
    evalExprs_barkVatIlksArgs (v := v) (evm := evmUrns) (I := I)
      (locals := barkLocalsMilkDirt evmUrns I out)
      (barkLocalsMilkDirt_get_ilk evmUrns I out)
  have heth :
      evalExpr? config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v }
        evmUrns (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hcallStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v } evmUrns
        (.externalCall vatExpr "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
          (perm := false))
        (.ok { contract := contract, locals := barkLocalsVatIlk evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [barkLocalsVatIlk, barkVatIlkValue, collapseReturns] using
      (ExecStmt.externalCallSuccess (hperm := Or.inl rfl) (retVar := "vatIlk") hvat heth hargs hcallIlks hdecIlks)
  have hrateExpr :
      evalExpr? config
        { contract := contract, locals := barkLocalsVatIlk evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.tupleGet (.var "vatIlk") 1) =
          .ok (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) :=
    evalExpr_barkVatIlkRate (v := v) (evm := evmIlks)
      (locals := barkLocalsVatIlk evmUrns I out outIlks) (out := outIlks)
      (barkLocalsVatIlk_get_vatIlk evmUrns I out outIlks)
  have hrateStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsVatIlk evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract, locals := barkLocalsRate evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [barkLocalsRate] using (ExecStmt.letDecl (cfg := config) hrateExpr)
  have hspotExpr :
      evalExpr? config
        { contract := contract, locals := barkLocalsRate evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.tupleGet (.var "vatIlk") 2) =
          .ok (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat)) :=
    evalExpr_barkVatIlkSpot (v := v) (evm := evmIlks)
      (locals := barkLocalsRate evmUrns I out outIlks) (out := outIlks)
      (barkLocalsRate_get_vatIlk evmUrns I out outIlks)
  have hspotStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsRate evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2))
        (.ok { contract := contract, locals := barkLocalsSpot evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [barkLocalsSpot] using (ExecStmt.letDecl (cfg := config) hspotExpr)
  have hdustExpr :
      evalExpr? config
        { contract := contract, locals := barkLocalsSpot evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.tupleGet (.var "vatIlk") 4) =
          .ok (.int (Int.ofNat (barkVatIlksDustWord outIlks).toNat)) :=
    evalExpr_barkVatIlkDust (v := v) (evm := evmIlks)
      (locals := barkLocalsSpot evmUrns I out outIlks) (out := outIlks)
      (barkLocalsSpot_get_vatIlk evmUrns I out outIlks)
  have hdustStmt :
      ExecStmt config
        { contract := contract, locals := barkLocalsSpot evmUrns I out outIlks, immutables := immStore v }
        evmIlks (.letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4))
        (.ok { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [barkLocalsDust] using (ExecStmt.letDecl (cfg := config) hdustExpr)
  let localsDust := barkLocalsDust evmUrns I out outIlks
  have hink :
      evalExpr? config { contract := contract, locals := localsDust, immutables := immStore v } evmIlks
        (.var "ink") =
          .ok (.int (Int.ofNat (barkVatUrnsInkWord out).toNat)) := by
    simpa [localsDust] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDust)
        (name := "ink") (value := barkVatUrnsInkWord out)
        (barkLocalsDust_get_ink evmUrns I out outIlks)
  have hspot :
      evalExpr? config { contract := contract, locals := localsDust, immutables := immStore v } evmIlks
        (.var "spot") =
          .ok (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat)) := by
    simpa [localsDust] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDust)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsDust_get_spot evmUrns I out outIlks)
  have hmul :
      evalExpr? config { contract := contract, locals := localsDust, immutables := immStore v } evmIlks
        (mul256 (.var "ink") (.var "spot")) = .revert :=
    evalExpr_bark_mul256_revert hink hspot hfitOverflow
  have hsecond :
      ExecBlock config
        { contract := contract, locals := barkLocalsMilkDirt evmUrns I out, immutables := immStore v } evmUrns
        ([ .require (.binary .gt (.extCodeSize vatExpr) (.intLit 0)),
          .externalCall vatExpr "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
            (perm := false),
          .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2),
          .letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4) ] ++
          checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [ .require
              (.binary .and
                (.binary .gt (.var "spot") (.intLit 0))
                (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))),
            .require
              (.binary .and
                (.binary .gt (.storage HoleRef) (.storage DirtRef))
                (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [ .internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room" ] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
          [ .letDecl "dartByRate" (some uint256)
              (.binary .div (.var "roomWad") (.var "rate")),
            .letDecl "dartCandidate" (some uint256)
              (.binary .div (.var "dartByRate") (.var "milkChop")),
            .internalCall "min" [.var "art", .var "dartCandidate"] "dart",
            .ite
              (.binary .gt (.var "art") (.var "dart"))
              (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
                checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
                [ .ite
                    (.binary .lt (.var "leftoverDue") (.var "dust"))
                    [ .assign .localVar (varRef "dart") (.var "art") ]
                    (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                      [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
              [] ] ++
          checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
          [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
            .require (.binary .gt (.var "dink") (.intLit 0)),
            .require
              (.binary .and
                (.binary .le (.var "dart") (.intLit int256Limit))
                (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
          checkedExternalCallStmts vatExpr "grab" (.intLit 0)
            [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
              asInt256 (.unary .neg (asInt256 (.var "dink"))),
              asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet" ++
          checkedMulUintInto "due" (.var "dart") (.var "rate") ++
          checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet" ++
          checkedMulUintInto "tabBase" (.var "due") (.var "milkChop") ++
          [ .letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
          checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab") ++
          [ .assign .storage DirtRef (.var "DirtNew") ] ++
          checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab") ++
          [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] ++
          checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
            [.var "tab", .var "dink", .var "urn", .var "kpr"] "id" ++
          [ .return [.var "id"] ])
        .reverted :=
    by
      simp only [checkedMulUintInto, List.cons_append, List.nil_append]
      exact
        ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
          ExecBlock.consNormal hcallStmt <|
            ExecBlock.consNormal hrateStmt <|
              ExecBlock.consNormal hspotStmt <|
                ExecBlock.consNormal hdustStmt <|
                  ExecBlock.consRevert (ExecStmt.letDeclRevert hmul)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hcombined := execBlock_append hprefix hsecond
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts,
      checkedMulUintInto] using hcombined
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkInkSpotCheckedMulOk {v : DogImmutables}
    (evm localsEvm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hfit :
      (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat <
        UInt256.size) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDust localsEvm I out outIlks, immutables := immStore v } evm
      (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
      (.ok { contract := contract, locals := barkLocalsInkSpot localsEvm I out outIlks, immutables := immStore v }
        evm) := by
  let locals0 := barkLocalsDust localsEvm I out outIlks
  let locals1 := barkLocalsInkSpot localsEvm I out outIlks
  let ink := barkVatUrnsInkWord out
  let spot := barkVatIlksSpotWord outIlks
  let inkSpot := barkInkSpotWord out outIlks
  have hink0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm (.var "ink") =
        .ok (.int (Int.ofNat ink.toNat)) := by
    simpa [locals0, ink] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "ink") (value := barkVatUrnsInkWord out)
        (barkLocalsDust_get_ink localsEvm I out outIlks)
  have hspot0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm (.var "spot") =
        .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals0, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsDust_get_spot localsEvm I out outIlks)
  have hmul :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm
        (mul256 (.var "ink") (.var "spot")) =
          .ok (.int (Int.ofNat inkSpot.toNat)) := by
    exact evalExpr_bark_mul256_ok hink0 hspot0 (by simp [inkSpot, ink, spot, barkInkSpotWord])
      (by simpa [ink, spot] using hfit)
  have hlet :
      ExecStmt config { contract := contract, locals := locals0, immutables := immStore v } evm
        (.letDecl "inkSpot" (some uint256) (mul256 (.var "ink") (.var "spot")))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evm) := by
    simpa [locals0, locals1, inkSpot, barkLocalsInkSpot] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals0, immutables := immStore v })
        (evm := evm) (name := "inkSpot") (ty := some uint256)
        (expr := mul256 (.var "ink") (.var "spot"))
        (value := .int (Int.ofNat inkSpot.toNat)) hmul)
  have hspot1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.var "spot") =
        .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals1, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsInkSpot_get_spot localsEvm I out outIlks)
  have hink1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.var "ink") =
        .ok (.int (Int.ofNat ink.toNat)) := by
    simpa [locals1, ink] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "ink") (value := barkVatUrnsInkWord out)
        (barkLocalsInkSpot_get_ink localsEvm I out outIlks)
  have hinkSpot1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.var "inkSpot") =
          .ok (.int (Int.ofNat inkSpot.toNat)) := by
    simpa [locals1, inkSpot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "inkSpot") (value := barkInkSpotWord out outIlks)
        (barkLocalsInkSpot_get_inkSpot localsEvm I out outIlks)
  have hzero :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.binary .or
          (.binary .eq (.var "spot") (.intLit 0))
          (.binary .eq (.binary .div (.var "inkSpot") (.var "spot")) (.var "ink"))) =
        .ok (.bool true) := by
    by_cases hspotZero : spot = ⟨0⟩
    · have heqZero :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.var "spot") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_bark_eq_int_true hspot1 hzero
        simp [hspotZero]
      exact evalExpr_bark_or_true_left heqZero
    · have hspotNatNe : spot.toNat ≠ 0 := by
        intro hnat
        exact hspotZero (uint256_toNat_eq_zero hnat)
      have heqZero :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.var "spot") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_bark_eq_int_false hspot1 hzero
        intro hbad
        have hnat : spot.toNat = 0 := by
          norm_num at hbad
          exact hbad
        exact hspotNatNe hnat
      have hdivWord : UInt256.div inkSpot spot = ink := by
        apply u256_inj
        rw [udiv_toNat]
        have hprod : inkSpot.toNat = ink.toNat * spot.toNat := by
          change (barkInkSpotWord out outIlks).toNat =
            (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat
          rw [barkInkSpotWord]
          exact umul_toNat (barkVatUrnsInkWord out) (barkVatIlksSpotWord outIlks) hfit
        rw [hprod]
        simpa [Nat.mul_comm] using Nat.mul_div_right ink.toNat
          (Nat.pos_of_ne_zero hspotNatNe)
      have hdiv :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .div (.var "inkSpot") (.var "spot")) =
              .ok (.int (Int.ofNat ink.toNat)) := by
        have h := evalExpr_bark_div_uint256_ok (v := v) (evm := evm) (locals := locals1)
          (x := .var "inkSpot") (y := .var "spot")
          (a := inkSpot) (b := spot) (q := UInt256.div inkSpot spot)
          hinkSpot1 hspot1 hspotZero rfl
        simpa [hdivWord] using h
      have hright :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.binary .div (.var "inkSpot") (.var "spot")) (.var "ink")) =
              .ok (.bool true) :=
        evalExpr_bark_eq_int_true hdiv hink1 rfl
      exact evalExpr_bark_or_false_right heqZero hright
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal hlet (ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkArtRateUnsafeCheckedMulOverflow {v : DogImmutables}
    (evm localsEvm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hover :
      UInt256.size ≤ (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat) :
    ExecBlock config
      { contract := contract, locals := barkLocalsInkSpot localsEvm I out outIlks, immutables := immStore v } evm
      (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) .reverted := by
  let locals0 := barkLocalsInkSpot localsEvm I out outIlks
  let art := barkVatUrnsArtWord out
  let rate := barkVatIlksRateWord outIlks
  have hart :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm (.var "art") =
        .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "art") (value := barkVatUrnsArtWord out)
        (barkLocalsInkSpot_get_art localsEvm I out outIlks)
  have hrate :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm (.var "rate") =
        .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [locals0, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "rate") (value := barkVatIlksRateWord outIlks)
        (barkLocalsInkSpot_get_rate localsEvm I out outIlks)
  have hmul :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm
        (mul256 (.var "art") (.var "rate")) = .revert :=
    evalExpr_bark_mul256_revert hart hrate (by simpa [art, rate] using hover)
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmul)

theorem dogBarkArtRateUnsafeCheckedMulOk {v : DogImmutables}
    (evm localsEvm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hfit :
      (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat <
        UInt256.size) :
    ExecBlock config
      { contract := contract, locals := barkLocalsInkSpot localsEvm I out outIlks, immutables := immStore v } evm
      (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
      (.ok { contract := contract, locals := barkLocalsArtRateUnsafe localsEvm I out outIlks, immutables := immStore v }
        evm) := by
  let locals0 := barkLocalsInkSpot localsEvm I out outIlks
  let locals1 := barkLocalsArtRateUnsafe localsEvm I out outIlks
  let art := barkVatUrnsArtWord out
  let rate := barkVatIlksRateWord outIlks
  let artRate := barkArtRateUnsafeWord out outIlks
  have hart0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm (.var "art") =
        .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "art") (value := barkVatUrnsArtWord out)
        (barkLocalsInkSpot_get_art localsEvm I out outIlks)
  have hrate0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm (.var "rate") =
        .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [locals0, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "rate") (value := barkVatIlksRateWord outIlks)
        (barkLocalsInkSpot_get_rate localsEvm I out outIlks)
  have hmul :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm
        (mul256 (.var "art") (.var "rate")) =
          .ok (.int (Int.ofNat artRate.toNat)) := by
    exact evalExpr_bark_mul256_ok hart0 hrate0
      (by simp [artRate, art, rate, barkArtRateUnsafeWord])
      (by simpa [art, rate] using hfit)
  have hlet :
      ExecStmt config { contract := contract, locals := locals0, immutables := immStore v } evm
        (.letDecl "artRateUnsafe" (some uint256) (mul256 (.var "art") (.var "rate")))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evm) := by
    simpa [locals0, locals1, artRate, barkLocalsArtRateUnsafe] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals0, immutables := immStore v })
        (evm := evm) (name := "artRateUnsafe") (ty := some uint256)
        (expr := mul256 (.var "art") (.var "rate"))
        (value := .int (Int.ofNat artRate.toNat)) hmul)
  have hrate1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.var "rate") =
        .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [locals1, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "rate") (value := barkVatIlksRateWord outIlks)
        (barkLocalsArtRateUnsafe_get_rate localsEvm I out outIlks)
  have hart1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.var "art") =
        .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals1, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "art") (value := barkVatUrnsArtWord out)
        (barkLocalsArtRateUnsafe_get_art localsEvm I out outIlks)
  have hartRate1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.var "artRateUnsafe") =
          .ok (.int (Int.ofNat artRate.toNat)) := by
    simpa [locals1, artRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "artRateUnsafe") (value := barkArtRateUnsafeWord out outIlks)
        (barkLocalsArtRateUnsafe_get_artRateUnsafe localsEvm I out outIlks)
  have hzero :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.binary .or
          (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "artRateUnsafe") (.var "rate")) (.var "art"))) =
        .ok (.bool true) := by
    by_cases hrateZero : rate = ⟨0⟩
    · have heqZero :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.var "rate") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_bark_eq_int_true hrate1 hzero
        simp [hrateZero]
      exact evalExpr_bark_or_true_left heqZero
    · have hrateNatNe : rate.toNat ≠ 0 := by
        intro hnat
        exact hrateZero (uint256_toNat_eq_zero hnat)
      have heqZero :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.var "rate") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_bark_eq_int_false hrate1 hzero
        intro hbad
        have hnat : rate.toNat = 0 := by
          norm_num at hbad
          exact hbad
        exact hrateNatNe hnat
      have hdivWord : UInt256.div artRate rate = art := by
        apply u256_inj
        rw [udiv_toNat]
        have hprod : artRate.toNat = art.toNat * rate.toNat := by
          change (barkArtRateUnsafeWord out outIlks).toNat =
            (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat
          rw [barkArtRateUnsafeWord]
          exact umul_toNat (barkVatUrnsArtWord out) (barkVatIlksRateWord outIlks) hfit
        rw [hprod]
        simpa [Nat.mul_comm] using Nat.mul_div_right art.toNat
          (Nat.pos_of_ne_zero hrateNatNe)
      have hdiv :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .div (.var "artRateUnsafe") (.var "rate")) =
              .ok (.int (Int.ofNat art.toNat)) := by
        have h := evalExpr_bark_div_uint256_ok (v := v) (evm := evm) (locals := locals1)
          (x := .var "artRateUnsafe") (y := .var "rate")
          (a := artRate) (b := rate) (q := UInt256.div artRate rate)
          hartRate1 hrate1 hrateZero rfl
        simpa [hdivWord] using h
      have hright :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.binary .div (.var "artRateUnsafe") (.var "rate")) (.var "art")) =
              .ok (.bool true) :=
        evalExpr_bark_eq_int_true hdiv hart1 rfl
      exact evalExpr_bark_or_false_right heqZero hright
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal hlet (ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkVatIlksArtRateOverflowSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM config evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : config.externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hfitInk :
      (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat <
        UInt256.size)
    (hoverArt :
      UInt256.size ≤ (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15)
        (.ok { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [locals, evm0] using
      dogBarkVatIlksSuccessDustPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmUrns := evmUrns) (evmIlks := evmIlks) (out := out)
        (outIlks := outIlks) hwv hlive hcodePos hcallUrns hdecUrns hcodePosIlks
        hcallIlks hdecIlks hsz100
  have hInkBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
        (.ok { contract := contract, locals := barkLocalsInkSpot evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    dogBarkInkSpotCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitInk
  have hArtRevert :
      ExecBlock config
        { contract := contract, locals := barkLocalsInkSpot evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) .reverted :=
    dogBarkArtRateUnsafeCheckedMulOverflow (v := v) evmIlks evmUrns I out outIlks
      hoverArt
  let rest : List Stmt :=
    [ .require
        (.binary .and
          (.binary .gt (.var "spot") (.intLit 0))
          (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))),
      .require
        (.binary .and
          (.binary .gt (.storage HoleRef) (.storage DirtRef))
          (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
    checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
    checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
    [ .internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room" ] ++
    checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
    [ .letDecl "dartByRate" (some uint256)
        (.binary .div (.var "roomWad") (.var "rate")),
      .letDecl "dartCandidate" (some uint256)
        (.binary .div (.var "dartByRate") (.var "milkChop")),
      .internalCall "min" [.var "art", .var "dartCandidate"] "dart",
      .ite
        (.binary .gt (.var "art") (.var "dart"))
        (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
          checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
          [ .ite
              (.binary .lt (.var "leftoverDue") (.var "dust"))
              [ .assign .localVar (varRef "dart") (.var "art") ]
              (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
        [] ] ++
    checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
    [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
      .require (.binary .gt (.var "dink") (.intLit 0)),
      .require
        (.binary .and
          (.binary .le (.var "dart") (.intLit int256Limit))
          (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
    checkedExternalCallStmts vatExpr "grab" (.intLit 0)
      [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
        asInt256 (.unary .neg (asInt256 (.var "dink"))),
        asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet" ++
    checkedMulUintInto "due" (.var "dart") (.var "rate") ++
    checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet" ++
    checkedMulUintInto "tabBase" (.var "due") (.var "milkChop") ++
    [ .letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
    checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab") ++
    [ .assign .storage DirtRef (.var "DirtNew") ] ++
    checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab") ++
    [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] ++
    checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
      [.var "tab", .var "dink", .var "urn", .var "kpr"] "id" ++
    [ .return [.var "id"] ]
  have htailPrefix :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        .reverted :=
    execBlock_append hInkBlock hArtRevert
  have htail :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        ((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++ rest)
        .reverted :=
    execBlock_append_term htailPrefix (by intro f e h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hcombined := execBlock_append hprefix htail
    simpa [rest, barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts,
      checkedMulUintInto, List.append_assoc] using hcombined
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksNotUnsafeSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM config evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : config.externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hfitInk :
      (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat <
        UInt256.size)
    (hfitArt :
      (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat <
        UInt256.size)
    (hnotSafe :
      ¬ (0 < (barkVatIlksSpotWord outIlks).toNat ∧
        (barkInkSpotWord out outIlks).toNat <
          (barkArtRateUnsafeWord out outIlks).toNat))
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15)
        (.ok { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [locals, evm0] using
      dogBarkVatIlksSuccessDustPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmUrns := evmUrns) (evmIlks := evmIlks) (out := out)
        (outIlks := outIlks) hwv hlive hcodePos hcallUrns hdecUrns hcodePosIlks
        hcallIlks hdecIlks hsz100
  have hInkBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
        (.ok { contract := contract, locals := barkLocalsInkSpot evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    dogBarkInkSpotCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitInk
  have hArtBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsInkSpot evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    dogBarkArtRateUnsafeCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitArt
  let unsafeGuard : Expr :=
    .binary .and
      (.binary .gt (.var "spot") (.intLit 0))
      (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))
  let locals2 := barkLocalsArtRateUnsafe evmUrns I out outIlks
  let spot := barkVatIlksSpotWord outIlks
  let inkSpot := barkInkSpotWord out outIlks
  let artRate := barkArtRateUnsafeWord out outIlks
  have hspot :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "spot") = .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals2, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsArtRateUnsafe_get_spot evmUrns I out outIlks)
  have hzero :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hinkSpot :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "inkSpot") = .ok (.int (Int.ofNat inkSpot.toNat)) := by
    simpa [locals2, inkSpot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "inkSpot") (value := barkInkSpotWord out outIlks)
        (barkLocalsArtRateUnsafe_get_inkSpot evmUrns I out outIlks)
  have hartRate :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "artRateUnsafe") = .ok (.int (Int.ofNat artRate.toNat)) := by
    simpa [locals2, artRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "artRateUnsafe") (value := barkArtRateUnsafeWord out outIlks)
        (barkLocalsArtRateUnsafe_get_artRateUnsafe evmUrns I out outIlks)
  have hreq :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        unsafeGuard = .ok (.bool false) := by
    by_cases hspotPos : 0 < spot.toNat
    · have hgt :
          evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
            (.binary .gt (.var "spot") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_bark_gt_int_true hspot hzero
        show (0 : Int) < Int.ofNat spot.toNat
        exact Int.ofNat_lt.mpr hspotPos
      have hnotLt : ¬ inkSpot.toNat < artRate.toNat := by
        intro hlt
        exact hnotSafe ⟨by simpa [spot] using hspotPos, by simpa [inkSpot, artRate] using hlt⟩
      have hltFalse :
          evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
            (.binary .lt (.var "inkSpot") (.var "artRateUnsafe")) = .ok (.bool false) := by
        apply evalExpr_bark_lt_int_false hinkSpot hartRate
        intro hlt
        exact hnotLt (Int.ofNat_lt.mp hlt)
      simpa [unsafeGuard] using evalExpr_bark_and_true_right hgt hltFalse
    · have hgt :
          evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
            (.binary .gt (.var "spot") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_bark_gt_int_false hspot hzero
        intro hgt
        exact hspotPos (Int.ofNat_lt.mp hgt)
      simpa [unsafeGuard] using evalExpr_bark_and_false_left hgt
  have hchecked :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    execBlock_append hInkBlock hArtBlock
  have hreqBlock :
      ExecBlock config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        [.require unsafeGuard] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse hreq)
  let rest : List Stmt :=
    [ .require
        (.binary .and
          (.binary .gt (.storage HoleRef) (.storage DirtRef))
          (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
    checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
    checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
    [ .internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room" ] ++
    checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
    [ .letDecl "dartByRate" (some uint256)
        (.binary .div (.var "roomWad") (.var "rate")),
      .letDecl "dartCandidate" (some uint256)
        (.binary .div (.var "dartByRate") (.var "milkChop")),
      .internalCall "min" [.var "art", .var "dartCandidate"] "dart",
      .ite
        (.binary .gt (.var "art") (.var "dart"))
        (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
          checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
          [ .ite
              (.binary .lt (.var "leftoverDue") (.var "dust"))
              [ .assign .localVar (varRef "dart") (.var "art") ]
              (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
        [] ] ++
    checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
    [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
      .require (.binary .gt (.var "dink") (.intLit 0)),
      .require
        (.binary .and
          (.binary .le (.var "dart") (.intLit int256Limit))
          (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
    checkedExternalCallStmts vatExpr "grab" (.intLit 0)
      [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
        asInt256 (.unary .neg (asInt256 (.var "dink"))),
        asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet" ++
    checkedMulUintInto "due" (.var "dart") (.var "rate") ++
    checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet" ++
    checkedMulUintInto "tabBase" (.var "due") (.var "milkChop") ++
    [ .letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
    checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab") ++
    [ .assign .storage DirtRef (.var "DirtNew") ] ++
    checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab") ++
    [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] ++
    checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
      [.var "tab", .var "dink", .var "urn", .var "kpr"] "id" ++
    [ .return [.var "id"] ]
  have hcheckedReq :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        ((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard])
        .reverted :=
    execBlock_append hchecked (by simpa [locals2] using hreqBlock)
  have htail :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard]) ++ rest)
        .reverted :=
    execBlock_append_term (s2 := rest) hcheckedReq (by intro f e h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hcombined := execBlock_append hprefix htail
    simpa [unsafeGuard, rest, barkTransition, barkBodyRest, nonpayable,
      checkedExternalCallStmts, checkedMulUintInto, List.append_assoc] using hcombined
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksLiquidationLimitHitSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM config evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : config.externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hfitInk :
      (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat <
        UInt256.size)
    (hfitArt :
      (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat <
        UInt256.size)
    (hspotPos : 0 < (barkVatIlksSpotWord outIlks).toNat)
    (hsafeLt :
      (barkInkSpotWord out outIlks).toNat <
        (barkArtRateUnsafeWord out outIlks).toNat)
    (hlimitFalse :
      ¬ ((solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv).toNat <
          (solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv).toNat ∧
        (solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat <
          (solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat))
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15)
        (.ok { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [locals, evm0] using
      dogBarkVatIlksSuccessDustPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmUrns := evmUrns) (evmIlks := evmIlks) (out := out)
        (outIlks := outIlks) hwv hlive hcodePos hcallUrns hdecUrns hcodePosIlks
        hcallIlks hdecIlks hsz100
  have hInkBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
        (.ok { contract := contract, locals := barkLocalsInkSpot evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    dogBarkInkSpotCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitInk
  have hArtBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsInkSpot evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    dogBarkArtRateUnsafeCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitArt
  let unsafeGuard : Expr :=
    .binary .and
      (.binary .gt (.var "spot") (.intLit 0))
      (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))
  let limitGuard : Expr :=
    .binary .and
      (.binary .gt (.storage HoleRef) (.storage DirtRef))
      (.binary .gt (.var "milkHole") (.var "milkDirt"))
  let locals2 := barkLocalsArtRateUnsafe evmUrns I out outIlks
  let spot := barkVatIlksSpotWord outIlks
  let inkSpot := barkInkSpotWord out outIlks
  let artRate := barkArtRateUnsafeWord out outIlks
  let hole := solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv
  let dirt := solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv
  let milkHole :=
    solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  let milkDirt :=
    solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  have hspot :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "spot") = .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals2, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsArtRateUnsafe_get_spot evmUrns I out outIlks)
  have hzero :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hinkSpot :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "inkSpot") = .ok (.int (Int.ofNat inkSpot.toNat)) := by
    simpa [locals2, inkSpot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "inkSpot") (value := barkInkSpotWord out outIlks)
        (barkLocalsArtRateUnsafe_get_inkSpot evmUrns I out outIlks)
  have hartRate :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "artRateUnsafe") = .ok (.int (Int.ofNat artRate.toNat)) := by
    simpa [locals2, artRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "artRateUnsafe") (value := barkArtRateUnsafeWord out outIlks)
        (barkLocalsArtRateUnsafe_get_artRateUnsafe evmUrns I out outIlks)
  have hunsafeReq :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        unsafeGuard = .ok (.bool true) := by
    have hgt :
        evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
          (.binary .gt (.var "spot") (.intLit 0)) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hspot hzero
      show (0 : Int) < Int.ofNat spot.toNat
      exact Int.ofNat_lt.mpr (by simpa [spot] using hspotPos)
    have hlt :
        evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
          (.binary .lt (.var "inkSpot") (.var "artRateUnsafe")) = .ok (.bool true) := by
      apply evalExpr_bark_lt_int_true hinkSpot hartRate
      exact Int.ofNat_lt.mpr (by simpa [inkSpot, artRate] using hsafeLt)
    simpa [unsafeGuard] using evalExpr_bark_and_true_right hgt hlt
  have hHoleExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.storage HoleRef) = .ok (.int (Int.ofNat hole.toNat)) := by
    simpa [locals2, hole] using
      evalExpr_barkStorageHole (v := v) (evm := evmIlks) (locals := locals2)
        (barkLocalsArtRateUnsafe_get_Hole evmUrns I out outIlks)
  have hDirtExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt.toNat)) := by
    simpa [locals2, dirt] using
      evalExpr_barkStorageDirt (v := v) (evm := evmIlks) (locals := locals2)
        (barkLocalsArtRateUnsafe_get_Dirt evmUrns I out outIlks)
  have hmilkHoleExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "milkHole") = .ok (.int (Int.ofNat milkHole.toNat)) := by
    simpa [locals2, milkHole] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "milkHole")
        (value := solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv)
        (barkLocalsArtRateUnsafe_get_milkHole evmUrns I out outIlks)
  have hmilkDirtExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "milkDirt") = .ok (.int (Int.ofNat milkDirt.toNat)) := by
    simpa [locals2, milkDirt] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "milkDirt")
        (value := solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv)
        (barkLocalsArtRateUnsafe_get_milkDirt evmUrns I out outIlks)
  have hlimitReq :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        limitGuard = .ok (.bool false) := by
    by_cases hglobal : dirt.toNat < hole.toNat
    · have hgtGlobal :
          evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
            (.binary .gt (.storage HoleRef) (.storage DirtRef)) = .ok (.bool true) := by
        apply evalExpr_bark_gt_int_true hHoleExpr hDirtExpr
        exact Int.ofNat_lt.mpr hglobal
      have hmilkNot : ¬ milkDirt.toNat < milkHole.toNat := by
        intro hmilk
        exact hlimitFalse ⟨by simpa [dirt, hole] using hglobal,
          by simpa [milkDirt, milkHole] using hmilk⟩
      have hgtMilk :
          evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
            (.binary .gt (.var "milkHole") (.var "milkDirt")) = .ok (.bool false) := by
        apply evalExpr_bark_gt_int_false hmilkHoleExpr hmilkDirtExpr
        intro hbad
        exact hmilkNot (Int.ofNat_lt.mp hbad)
      simpa [limitGuard] using evalExpr_bark_and_true_right hgtGlobal hgtMilk
    · have hgtGlobal :
          evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
            (.binary .gt (.storage HoleRef) (.storage DirtRef)) = .ok (.bool false) := by
        apply evalExpr_bark_gt_int_false hHoleExpr hDirtExpr
        intro hbad
        exact hglobal (Int.ofNat_lt.mp hbad)
      simpa [limitGuard] using evalExpr_bark_and_false_left hgtGlobal
  have hchecked :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    execBlock_append hInkBlock hArtBlock
  have hunsafeBlock :
      ExecBlock config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        [.require unsafeGuard]
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hunsafeReq) ExecBlock.nil
  have hlimitBlock :
      ExecBlock config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        [.require limitGuard] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse hlimitReq)
  have hcheckedUnsafe :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        ((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard])
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    execBlock_append hchecked (by simpa [locals2] using hunsafeBlock)
  have hcheckedUnsafeLimit :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard]) ++ [.require limitGuard])
        .reverted :=
    execBlock_append hcheckedUnsafe (by simpa [locals2] using hlimitBlock)
  let afterLimit : List Stmt :=
    checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
    checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
    [ .internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room" ] ++
    checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
    [ .letDecl "dartByRate" (some uint256)
        (.binary .div (.var "roomWad") (.var "rate")),
      .letDecl "dartCandidate" (some uint256)
        (.binary .div (.var "dartByRate") (.var "milkChop")),
      .internalCall "min" [.var "art", .var "dartCandidate"] "dart",
      .ite
        (.binary .gt (.var "art") (.var "dart"))
        (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
          checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
          [ .ite
              (.binary .lt (.var "leftoverDue") (.var "dust"))
              [ .assign .localVar (varRef "dart") (.var "art") ]
              (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
        [] ] ++
    checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
    [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
      .require (.binary .gt (.var "dink") (.intLit 0)),
      .require
        (.binary .and
          (.binary .le (.var "dart") (.intLit int256Limit))
          (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
    checkedExternalCallStmts vatExpr "grab" (.intLit 0)
      [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
        asInt256 (.unary .neg (asInt256 (.var "dink"))),
        asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet" ++
    checkedMulUintInto "due" (.var "dart") (.var "rate") ++
    checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet" ++
    checkedMulUintInto "tabBase" (.var "due") (.var "milkChop") ++
    [ .letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
    checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab") ++
    [ .assign .storage DirtRef (.var "DirtNew") ] ++
    checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab") ++
    [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] ++
    checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
      [.var "tab", .var "dink", .var "urn", .var "kpr"] "id" ++
    [ .return [.var "id"] ]
  have htail :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        ((((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard]) ++ [.require limitGuard]) ++ afterLimit)
        .reverted :=
    execBlock_append_term (s2 := afterLimit) hcheckedUnsafeLimit (by intro f e h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hcombined := execBlock_append hprefix htail
    simpa [unsafeGuard, limitGuard, afterLimit, barkTransition, barkBodyRest, nonpayable,
      checkedExternalCallStmts, checkedMulUintInto, List.append_assoc] using hcombined
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkGlobalRoomCheckedSubOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hglobal :
      (solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv).toNat <
        (solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv).toNat) :
    ExecBlock config
      { contract := contract, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks, immutables := immStore v }
      evmIlks (checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef))
      (.ok { contract := contract, locals := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsArtRateUnsafe evmUrns I out outIlks
  let locals1 := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks
  let hole := solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv
  let dirt := solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv
  let globalRoom := barkSourceGlobalRoomWord evmIlks
  have hdirtLe : dirt.toNat ≤ hole.toNat := by
    simpa [hole, dirt] using le_of_lt hglobal
  have hHole0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.storage HoleRef) = .ok (.int (Int.ofNat hole.toNat)) := by
    simpa [locals0, hole] using
      evalExpr_barkStorageHole (v := v) (evm := evmIlks) (locals := locals0)
        (barkLocalsArtRateUnsafe_get_Hole evmUrns I out outIlks)
  have hDirt0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt.toNat)) := by
    simpa [locals0, dirt] using
      evalExpr_barkStorageDirt (v := v) (evm := evmIlks) (locals := locals0)
        (barkLocalsArtRateUnsafe_get_Dirt evmUrns I out outIlks)
  have hsub :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (sub256 (.storage HoleRef) (.storage DirtRef)) =
          .ok (.int (Int.ofNat globalRoom.toNat)) := by
    exact evalExpr_bark_sub256_ok hHole0 hDirt0
      (by simp [globalRoom, barkSourceGlobalRoomWord, hole, dirt]) hdirtLe
  have hlet :
      ExecStmt config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.letDecl "globalRoom" (some uint256) (sub256 (.storage HoleRef) (.storage DirtRef)))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evmIlks) := by
    simpa [locals0, locals1, globalRoom, barkLocalsGlobalRoom] using
      (ExecStmt.letDecl (cfg := config)
        (stele := { contract := contract, locals := locals0, immutables := immStore v }) (evm := evmIlks)
        (name := "globalRoom") (ty := some uint256)
        (expr := sub256 (.storage HoleRef) (.storage DirtRef))
        (value := .int (Int.ofNat globalRoom.toNat)) hsub)
  have hglobalExpr :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.var "globalRoom") = .ok (.int (Int.ofNat globalRoom.toNat)) := by
    simpa [locals1, globalRoom] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals1)
        (name := "globalRoom") (value := globalRoom)
        (barkLocalsGlobalRoom_get_globalRoom evmUrns evmIlks I out outIlks)
  have hHole1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.storage HoleRef) = .ok (.int (Int.ofNat hole.toNat)) := by
    simpa [locals1, hole] using
      evalExpr_barkStorageHole (v := v) (evm := evmIlks) (locals := locals1)
        (barkLocalsGlobalRoom_get_Hole evmUrns evmIlks I out outIlks)
  have hglobalLe : globalRoom.toNat ≤ hole.toNat := by
    have hdef : globalRoom = UInt256.sub hole dirt := by
      simp [globalRoom, barkSourceGlobalRoomWord, hole, dirt]
    rw [hdef, usub_toNat hdirtLe]
    omega
  have hreq :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.binary .le (.var "globalRoom") (.storage HoleRef)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hglobalExpr, hHole1, evalBinaryOp?]
    exact_mod_cast hglobalLe
  simpa [checkedSubUintInto, locals0, locals1] using
    (ExecBlock.consNormal hlet <|
      ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkIlkRoomCheckedSubOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hmilk :
      (solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat <
        (solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat) :
    ExecBlock config
      { contract := contract, locals := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks (checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt"))
      (.ok { contract := contract, locals := barkLocalsIlkRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks
  let locals1 := barkLocalsIlkRoom evmUrns evmIlks I out outIlks
  let milkHole :=
    solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  let milkDirt :=
    solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  let ilkRoom := barkSourceIlkRoomWord evmUrns I
  have hmilkLe : milkDirt.toNat ≤ milkHole.toNat := by
    simpa [milkDirt, milkHole] using le_of_lt hmilk
  have hHole0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "milkHole") = .ok (.int (Int.ofNat milkHole.toNat)) := by
    simpa [locals0, milkHole] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "milkHole") (value := milkHole)
        (barkLocalsGlobalRoom_get_milkHole evmUrns evmIlks I out outIlks)
  have hDirt0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "milkDirt") = .ok (.int (Int.ofNat milkDirt.toNat)) := by
    simpa [locals0, milkDirt] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "milkDirt") (value := milkDirt)
        (barkLocalsGlobalRoom_get_milkDirt evmUrns evmIlks I out outIlks)
  have hsub :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (sub256 (.var "milkHole") (.var "milkDirt")) =
          .ok (.int (Int.ofNat ilkRoom.toNat)) := by
    exact evalExpr_bark_sub256_ok hHole0 hDirt0
      (by simp [ilkRoom, barkSourceIlkRoomWord, milkHole, milkDirt]) hmilkLe
  have hlet :
      ExecStmt config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.letDecl "ilkRoom" (some uint256) (sub256 (.var "milkHole") (.var "milkDirt")))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evmIlks) := by
    simpa [locals0, locals1, ilkRoom, barkLocalsIlkRoom] using
      (ExecStmt.letDecl (cfg := config)
        (stele := { contract := contract, locals := locals0, immutables := immStore v }) (evm := evmIlks)
        (name := "ilkRoom") (ty := some uint256)
        (expr := sub256 (.var "milkHole") (.var "milkDirt"))
        (value := .int (Int.ofNat ilkRoom.toNat)) hsub)
  have hilkExpr :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.var "ilkRoom") = .ok (.int (Int.ofNat ilkRoom.toNat)) := by
    simpa [locals1, ilkRoom] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals1)
        (name := "ilkRoom") (value := ilkRoom)
        (barkLocalsIlkRoom_get_ilkRoom evmUrns evmIlks I out outIlks)
  have hHole1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.var "milkHole") = .ok (.int (Int.ofNat milkHole.toNat)) := by
    apply evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals1)
      (name := "milkHole") (value := milkHole)
    change (barkLocalsIlkRoom evmUrns evmIlks I out outIlks).get? "milkHole" =
      some (.int (Int.ofNat milkHole.toNat))
    rw [barkLocalsIlkRoom, store_get_ne _ _ (by decide)]
    exact barkLocalsGlobalRoom_get_milkHole evmUrns evmIlks I out outIlks
  have hilkLe : ilkRoom.toNat ≤ milkHole.toNat := by
    have hdef : ilkRoom = UInt256.sub milkHole milkDirt := by
      simp [ilkRoom, barkSourceIlkRoomWord, milkHole, milkDirt]
    rw [hdef, usub_toNat hmilkLe]
    omega
  have hreq :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.binary .le (.var "ilkRoom") (.var "milkHole")) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hilkExpr, hHole1, evalBinaryOp?]
    exact_mod_cast hilkLe
  simpa [checkedSubUintInto, locals0, locals1] using
    (ExecBlock.consNormal hlet <|
      ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkRoomMinCallOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    ExecStmt config
      { contract := contract, locals := barkLocalsIlkRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks (.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room")
      (.ok { contract := contract, locals := barkLocalsRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsIlkRoom evmUrns evmIlks I out outIlks
  let globalRoom := barkSourceGlobalRoomWord evmIlks
  let ilkRoom := barkSourceIlkRoomWord evmUrns I
  have hglobal :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "globalRoom") = .ok (.int (Int.ofNat globalRoom.toNat)) := by
    simpa [locals0, globalRoom] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "globalRoom") (value := globalRoom)
        (barkLocalsIlkRoom_get_globalRoom evmUrns evmIlks I out outIlks)
  have hilk :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "ilkRoom") = .ok (.int (Int.ofNat ilkRoom.toNat)) := by
    simpa [locals0, ilkRoom] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "ilkRoom") (value := ilkRoom)
        (barkLocalsIlkRoom_get_ilkRoom evmUrns evmIlks I out outIlks)
  have hargs :
      evalExprs? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        [.var "globalRoom", .var "ilkRoom"] =
          .ok [.int (Int.ofNat globalRoom.toNat), .int (Int.ofNat ilkRoom.toNat)] := by
    simp [evalExprs?, hglobal, hilk, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? minFunction.params
          [.int (Int.ofNat globalRoom.toNat), .int (Int.ofNat ilkRoom.toNat)] =
        some (barkBinaryLocals globalRoom ilkRoom) := by
    simp [minFunction, uint256, bindParams?, barkBinaryLocals]
  have hbody :
      ExecFuncBody config
        { contract := contract, locals := barkBinaryLocals globalRoom ilkRoom, immutables := immStore v } evmIlks
        minFunction.body
        (.returned { contract := contract, locals := barkBinaryLocals globalRoom ilkRoom, immutables := immStore v }
          evmIlks (some [.int (Int.ofNat (barkSourceRoomWord evmUrns evmIlks I).toNat)])) := by
    simpa [barkSourceRoomWord, globalRoom, ilkRoom] using
      execBarkMinFunctionReturn (v := v) evmIlks globalRoom ilkRoom
  simpa [locals0, barkLocalsRoom, barkSourceRoomWord, globalRoom, ilkRoom,
    resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := locals0, immutables := immStore v })
      (evm := evmIlks) (calleeEvm := evmIlks) (name := "min") (retVar := "room")
      (args := [.var "globalRoom", .var "ilkRoom"])
      (argVals := [.int (Int.ofNat globalRoom.toNat), .int (Int.ofNat ilkRoom.toNat)])
      (callee := minFunction) (locals := barkBinaryLocals globalRoom ilkRoom)
      (calleeStele := { contract := contract, locals := barkBinaryLocals globalRoom ilkRoom, immutables := immStore v })
      (value := some [.int (Int.ofNat (barkSourceRoomWord evmUrns evmIlks I).toNat)])
      hargs (by rfl) hbind hbody)

theorem dogBarkVatIlksDustToRoomOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hfitInk :
      (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat <
        UInt256.size)
    (hfitArt :
      (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat <
        UInt256.size)
    (hspotPos : 0 < (barkVatIlksSpotWord outIlks).toNat)
    (hsafeLt :
      (barkInkSpotWord out outIlks).toNat <
        (barkArtRateUnsafeWord out outIlks).toNat)
    (hlimit :
      (solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv).toNat <
          (solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv).toNat ∧
        (solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat <
          (solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
      evmIlks
      (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
        checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
        [ .require
            (.binary .and
              (.binary .gt (.var "spot") (.intLit 0))
              (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
        [ .require
            (.binary .and
              (.binary .gt (.storage HoleRef) (.storage DirtRef))
              (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
        checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
        checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
        [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"])
      (.ok { contract := contract, locals := barkLocalsRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  have hInkBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
        (.ok { contract := contract, locals := barkLocalsInkSpot evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    dogBarkInkSpotCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitInk
  have hArtBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsInkSpot evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    dogBarkArtRateUnsafeCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitArt
  let unsafeGuard : Expr :=
    .binary .and
      (.binary .gt (.var "spot") (.intLit 0))
      (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))
  let limitGuard : Expr :=
    .binary .and
      (.binary .gt (.storage HoleRef) (.storage DirtRef))
      (.binary .gt (.var "milkHole") (.var "milkDirt"))
  let locals2 := barkLocalsArtRateUnsafe evmUrns I out outIlks
  let spot := barkVatIlksSpotWord outIlks
  let inkSpot := barkInkSpotWord out outIlks
  let artRate := barkArtRateUnsafeWord out outIlks
  let hole := solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv
  let dirt := solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv
  let milkHole :=
    solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  let milkDirt :=
    solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  have hspot :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "spot") = .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals2, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsArtRateUnsafe_get_spot evmUrns I out outIlks)
  have hzero :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hinkSpot :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "inkSpot") = .ok (.int (Int.ofNat inkSpot.toNat)) := by
    simpa [locals2, inkSpot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "inkSpot") (value := barkInkSpotWord out outIlks)
        (barkLocalsArtRateUnsafe_get_inkSpot evmUrns I out outIlks)
  have hartRate :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "artRateUnsafe") = .ok (.int (Int.ofNat artRate.toNat)) := by
    simpa [locals2, artRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "artRateUnsafe") (value := barkArtRateUnsafeWord out outIlks)
        (barkLocalsArtRateUnsafe_get_artRateUnsafe evmUrns I out outIlks)
  have hunsafeReq :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        unsafeGuard = .ok (.bool true) := by
    have hgt :
        evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
          (.binary .gt (.var "spot") (.intLit 0)) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hspot hzero
      exact Int.ofNat_lt.mpr (by simpa [spot] using hspotPos)
    have hlt :
        evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
          (.binary .lt (.var "inkSpot") (.var "artRateUnsafe")) = .ok (.bool true) := by
      apply evalExpr_bark_lt_int_true hinkSpot hartRate
      exact Int.ofNat_lt.mpr (by simpa [inkSpot, artRate] using hsafeLt)
    simpa [unsafeGuard] using evalExpr_bark_and_true_right hgt hlt
  have hHoleExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.storage HoleRef) = .ok (.int (Int.ofNat hole.toNat)) := by
    simpa [locals2, hole] using
      evalExpr_barkStorageHole (v := v) (evm := evmIlks) (locals := locals2)
        (barkLocalsArtRateUnsafe_get_Hole evmUrns I out outIlks)
  have hDirtExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt.toNat)) := by
    simpa [locals2, dirt] using
      evalExpr_barkStorageDirt (v := v) (evm := evmIlks) (locals := locals2)
        (barkLocalsArtRateUnsafe_get_Dirt evmUrns I out outIlks)
  have hmilkHoleExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "milkHole") = .ok (.int (Int.ofNat milkHole.toNat)) := by
    simpa [locals2, milkHole] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "milkHole") (value := milkHole)
        (barkLocalsArtRateUnsafe_get_milkHole evmUrns I out outIlks)
  have hmilkDirtExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "milkDirt") = .ok (.int (Int.ofNat milkDirt.toNat)) := by
    simpa [locals2, milkDirt] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "milkDirt") (value := milkDirt)
        (barkLocalsArtRateUnsafe_get_milkDirt evmUrns I out outIlks)
  have hlimitReq :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        limitGuard = .ok (.bool true) := by
    have hgtGlobal :
        evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
          (.binary .gt (.storage HoleRef) (.storage DirtRef)) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hHoleExpr hDirtExpr
      exact Int.ofNat_lt.mpr (by simpa [dirt, hole] using hlimit.1)
    have hgtMilk :
        evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
          (.binary .gt (.var "milkHole") (.var "milkDirt")) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hmilkHoleExpr hmilkDirtExpr
      exact Int.ofNat_lt.mpr (by simpa [milkDirt, milkHole] using hlimit.2)
    simpa [limitGuard] using evalExpr_bark_and_true_right hgtGlobal hgtMilk
  have hchecked :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    by simpa [locals2] using execBlock_append hInkBlock hArtBlock
  have hunsafeBlock :
      ExecBlock config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        [.require unsafeGuard]
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hunsafeReq) ExecBlock.nil
  have hlimitBlock :
      ExecBlock config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        [.require limitGuard]
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hlimitReq) ExecBlock.nil
  have hcheckedUnsafe :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        ((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard])
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    execBlock_append hchecked (by simpa [locals2] using hunsafeBlock)
  have hcheckedUnsafeLimit :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard]) ++ [.require limitGuard])
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    execBlock_append hcheckedUnsafe (by simpa [locals2] using hlimitBlock)
  have hglobalBlock :=
    dogBarkGlobalRoomCheckedSubOk (v := v) evmUrns evmIlks I out outIlks hlimit.1
  have htoGlobal :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef))
        (.ok { contract := contract, locals := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append hcheckedUnsafeLimit hglobalBlock
  have hilkBlock :=
    dogBarkIlkRoomCheckedSubOk (v := v) evmUrns evmIlks I out outIlks hlimit.2
  have htoIlk :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt"))
        (.ok { contract := contract, locals := barkLocalsIlkRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append htoGlobal hilkBlock
  have hminStmt :=
    dogBarkRoomMinCallOk (v := v) evmUrns evmIlks I out outIlks
  have hminBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsIlkRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks
        [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"]
        (.ok { contract := contract, locals := barkLocalsRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) :=
    ExecBlock.consNormal hminStmt ExecBlock.nil
  have htoRoom :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"])
        (.ok { contract := contract, locals := barkLocalsRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append htoIlk hminBlock
  simpa [unsafeGuard, limitGuard, List.append_assoc] using htoRoom

theorem dogBarkRoomWadCheckedMulOverflow {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hover :
      UInt256.size ≤ (barkSourceRoomWord evmUrns evmIlks I).toNat * dogWadWord.toNat) :
    ExecBlock config
      { contract := contract, locals := barkLocalsRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks (checkedMulUintInto "roomWad" (.var "room") (.intLit WAD)) .reverted := by
  let locals0 := barkLocalsRoom evmUrns evmIlks I out outIlks
  let room := barkSourceRoomWord evmUrns evmIlks I
  have hroom :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "room") = .ok (.int (Int.ofNat room.toNat)) := by
    simpa [locals0, room] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "room") (value := room)
        (barkLocalsRoom_get_room evmUrns evmIlks I out outIlks)
  have hWad :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.intLit WAD) = .ok (.int (Int.ofNat dogWadWord.toNat)) := by
    have hWadNat : dogWadWord.toNat = 1000000000000000000 := by
      native_decide
    simp [evalExpr?, pure, WAD, hWadNat]
  have hmul :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (mul256 (.var "room") (.intLit WAD)) = .revert :=
    evalExpr_bark_mul256_revert hroom hWad (by simpa [room] using hover)
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmul)

theorem dogBarkRoomWadCheckedMulOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hfit :
      (barkSourceRoomWord evmUrns evmIlks I).toNat * dogWadWord.toNat < UInt256.size) :
    ExecBlock config
      { contract := contract, locals := barkLocalsRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks (checkedMulUintInto "roomWad" (.var "room") (.intLit WAD))
      (.ok { contract := contract, locals := barkLocalsRoomWad evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsRoom evmUrns evmIlks I out outIlks
  let locals1 := barkLocalsRoomWad evmUrns evmIlks I out outIlks
  let room := barkSourceRoomWord evmUrns evmIlks I
  let roomWad := barkSourceRoomWadWord evmUrns evmIlks I
  have hroom0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "room") = .ok (.int (Int.ofNat room.toNat)) := by
    simpa [locals0, room] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "room") (value := room)
        (barkLocalsRoom_get_room evmUrns evmIlks I out outIlks)
  have hWad0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.intLit WAD) = .ok (.int (Int.ofNat dogWadWord.toNat)) := by
    have hWadNat : dogWadWord.toNat = 1000000000000000000 := by
      native_decide
    simp [evalExpr?, pure, WAD, hWadNat]
  have hmul :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (mul256 (.var "room") (.intLit WAD)) =
          .ok (.int (Int.ofNat roomWad.toNat)) := by
    exact evalExpr_bark_mul256_ok hroom0 hWad0
      (by simp [roomWad, room, barkSourceRoomWadWord]) (by simpa [room] using hfit)
  have hlet :
      ExecStmt config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.letDecl "roomWad" (some uint256) (mul256 (.var "room") (.intLit WAD)))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evmIlks) := by
    simpa [locals0, locals1, roomWad, barkLocalsRoomWad] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals0, immutables := immStore v })
        (evm := evmIlks) (name := "roomWad") (ty := some uint256)
        (expr := mul256 (.var "room") (.intLit WAD))
        (value := .int (Int.ofNat roomWad.toNat)) hmul)
  have hroom1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.var "room") = .ok (.int (Int.ofNat room.toNat)) := by
    have hgetRoom :
        locals1.get? "room" = some (.int (Int.ofNat room.toNat)) := by
      change (barkLocalsRoomWad evmUrns evmIlks I out outIlks).get? "room" =
        some (.int (Int.ofNat (barkSourceRoomWord evmUrns evmIlks I).toNat))
      rw [barkLocalsRoomWad, store_get_ne _ _ (by decide), barkLocalsRoom_get_room]
    simpa [locals1, room] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals1)
        (name := "room") (value := room) hgetRoom
  have hWad1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.intLit WAD) = .ok (.int (Int.ofNat dogWadWord.toNat)) := by
    have hWadNat : dogWadWord.toNat = 1000000000000000000 := by
      native_decide
    simp [evalExpr?, pure, WAD, hWadNat]
  have hroomWad1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.var "roomWad") = .ok (.int (Int.ofNat roomWad.toNat)) := by
    simpa [locals1, roomWad] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals1)
        (name := "roomWad") (value := roomWad)
        (barkLocalsRoomWad_get_roomWad evmUrns evmIlks I out outIlks)
  have hzero :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.binary .or
          (.binary .eq (.intLit WAD) (.intLit 0))
          (.binary .eq (.binary .div (.var "roomWad") (.intLit WAD)) (.var "room"))) =
        .ok (.bool true) := by
    have hleft :
        evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
          (.binary .eq (.intLit WAD) (.intLit 0)) = .ok (.bool false) := by
      apply evalExpr_bark_eq_int_false hWad1 hzero
      native_decide
    have hdivWord : UInt256.div roomWad dogWadWord = room := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : roomWad.toNat = room.toNat * dogWadWord.toNat := by
        change (barkSourceRoomWadWord evmUrns evmIlks I).toNat =
          (barkSourceRoomWord evmUrns evmIlks I).toNat * dogWadWord.toNat
        rw [barkSourceRoomWadWord]
        exact umul_toNat room dogWadWord (by simpa [room] using hfit)
      rw [hprod]
      have hWadPos : 0 < dogWadWord.toNat := by
        native_decide
      rw [Nat.mul_comm]
      exact Nat.mul_div_right room.toNat hWadPos
    have hdiv :
        evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
          (.binary .div (.var "roomWad") (.intLit WAD)) =
            .ok (.int (Int.ofNat room.toNat)) := by
      have h := evalExpr_bark_div_uint256_ok (v := v) (evm := evmIlks)
        (locals := locals1) (x := .var "roomWad") (y := .intLit WAD)
        (a := roomWad) (b := dogWadWord) (q := UInt256.div roomWad dogWadWord)
        hroomWad1 hWad1 (by native_decide) rfl
      simpa [hdivWord] using h
    have hright :
        evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
          (.binary .eq (.binary .div (.var "roomWad") (.intLit WAD)) (.var "room")) =
            .ok (.bool true) :=
      evalExpr_bark_eq_int_true hdiv hroom1 rfl
    exact evalExpr_bark_or_false_right hleft hright
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal hlet
    (ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkDartByRateLetOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hrateNe : barkVatIlksRateWord outIlks ≠ ⟨0⟩) :
    ExecBlock config
      { contract := contract, locals := barkLocalsRoomWad evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks
      [ .letDecl "dartByRate" (some uint256) (.binary .div (.var "roomWad") (.var "rate")) ]
      (.ok
        { contract := contract, locals := barkLocalsDartByRate evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsRoomWad evmUrns evmIlks I out outIlks
  let locals1 := barkLocalsDartByRate evmUrns evmIlks I out outIlks
  let roomWad := barkSourceRoomWadWord evmUrns evmIlks I
  let rate := barkVatIlksRateWord outIlks
  let dartByRate := barkSourceDartByRateWord evmUrns evmIlks I outIlks
  have hroomWad :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "roomWad") = .ok (.int (Int.ofNat roomWad.toNat)) := by
    simpa [locals0, roomWad] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "roomWad") (value := roomWad)
        (barkLocalsRoomWad_get_roomWad evmUrns evmIlks I out outIlks)
  have hrate :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "rate") = .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [locals0, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "rate") (value := rate)
        (barkLocalsRoomWad_get_rate evmUrns evmIlks I out outIlks)
  have hdiv :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.binary .div (.var "roomWad") (.var "rate")) =
          .ok (.int (Int.ofNat dartByRate.toNat)) := by
    exact evalExpr_bark_div_uint256_ok hroomWad hrate (by simpa [rate] using hrateNe)
      (by simp [dartByRate, roomWad, rate, barkSourceDartByRateWord])
  have hlet :
      ExecStmt config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.letDecl "dartByRate" (some uint256) (.binary .div (.var "roomWad") (.var "rate")))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evmIlks) := by
    simpa [locals0, locals1, dartByRate, barkLocalsDartByRate] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals0, immutables := immStore v })
        (evm := evmIlks) (name := "dartByRate") (ty := some uint256)
        (expr := .binary .div (.var "roomWad") (.var "rate"))
        (value := .int (Int.ofNat dartByRate.toNat)) hdiv)
  exact ExecBlock.consNormal hlet ExecBlock.nil

theorem dogBarkDartCandidateLetOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hchopNe : barkSourceMilkChopWord evmUrns I ≠ ⟨0⟩) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDartByRate evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks
      [ .letDecl "dartCandidate" (some uint256)
          (.binary .div (.var "dartByRate") (.var "milkChop")) ]
      (.ok
        { contract := contract,
          locals := barkLocalsDartCandidate evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsDartByRate evmUrns evmIlks I out outIlks
  let locals1 := barkLocalsDartCandidate evmUrns evmIlks I out outIlks
  let dartByRate := barkSourceDartByRateWord evmUrns evmIlks I outIlks
  let chop := barkSourceMilkChopWord evmUrns I
  let dartCandidate := barkSourceDartCandidateWord evmUrns evmIlks I outIlks
  have hdartByRate :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "dartByRate") = .ok (.int (Int.ofNat dartByRate.toNat)) := by
    simpa [locals0, dartByRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "dartByRate") (value := dartByRate)
        (barkLocalsDartByRate_get_dartByRate evmUrns evmIlks I out outIlks)
  have hchop :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "milkChop") = .ok (.int (Int.ofNat chop.toNat)) := by
    simpa [locals0, chop, barkSourceMilkChopWord] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "milkChop") (value := chop)
        (barkLocalsDartByRate_get_milkChop evmUrns evmIlks I out outIlks)
  have hdiv :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.binary .div (.var "dartByRate") (.var "milkChop")) =
          .ok (.int (Int.ofNat dartCandidate.toNat)) := by
    exact evalExpr_bark_div_uint256_ok hdartByRate hchop
      (by simpa [chop] using hchopNe)
      (by simp [dartCandidate, dartByRate, chop, barkSourceDartCandidateWord])
  have hlet :
      ExecStmt config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.letDecl "dartCandidate" (some uint256)
          (.binary .div (.var "dartByRate") (.var "milkChop")))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evmIlks) := by
    simpa [locals0, locals1, dartCandidate, barkLocalsDartCandidate] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals0, immutables := immStore v })
        (evm := evmIlks) (name := "dartCandidate") (ty := some uint256)
        (expr := .binary .div (.var "dartByRate") (.var "milkChop"))
        (value := .int (Int.ofNat dartCandidate.toNat)) hdiv)
  exact ExecBlock.consNormal hlet ExecBlock.nil

theorem dogBarkDartMinCallOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    ExecStmt config
      { contract := contract,
        locals := barkLocalsDartCandidate evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks (.internalCall "min" [.var "art", .var "dartCandidate"] "dart")
      (.ok { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsDartCandidate evmUrns evmIlks I out outIlks
  let art := barkVatUrnsArtWord out
  let dartCandidate := barkSourceDartCandidateWord evmUrns evmIlks I outIlks
  have hart :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "art") = .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "art") (value := art)
        (barkLocalsDartCandidate_get_art evmUrns evmIlks I out outIlks)
  have hdartCandidate :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "dartCandidate") = .ok (.int (Int.ofNat dartCandidate.toNat)) := by
    simpa [locals0, dartCandidate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "dartCandidate") (value := dartCandidate)
        (barkLocalsDartCandidate_get_dartCandidate evmUrns evmIlks I out outIlks)
  have hargs :
      evalExprs? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        [.var "art", .var "dartCandidate"] =
          .ok [.int (Int.ofNat art.toNat), .int (Int.ofNat dartCandidate.toNat)] := by
    simp [evalExprs?, hart, hdartCandidate, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? minFunction.params
          [.int (Int.ofNat art.toNat), .int (Int.ofNat dartCandidate.toNat)] =
        some (barkBinaryLocals art dartCandidate) := by
    simp [minFunction, uint256, bindParams?, barkBinaryLocals]
  have hbody :
      ExecFuncBody config
        { contract := contract, locals := barkBinaryLocals art dartCandidate, immutables := immStore v } evmIlks
        minFunction.body
        (.returned { contract := contract, locals := barkBinaryLocals art dartCandidate, immutables := immStore v }
          evmIlks
          (some [.int (Int.ofNat
            (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat)])) := by
    simpa [barkSourceDartWord, art, dartCandidate] using
      execBarkMinFunctionReturn (v := v) evmIlks art dartCandidate
  simpa [locals0, barkLocalsDart, barkSourceDartWord, art, dartCandidate,
    resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config)
      (caller := { contract := contract, locals := locals0, immutables := immStore v })
      (evm := evmIlks) (calleeEvm := evmIlks) (name := "min") (retVar := "dart")
      (args := [.var "art", .var "dartCandidate"])
      (argVals := [.int (Int.ofNat art.toNat), .int (Int.ofNat dartCandidate.toNat)])
      (callee := minFunction) (locals := barkBinaryLocals art dartCandidate)
      (calleeStele := { contract := contract, locals := barkBinaryLocals art dartCandidate, immutables := immStore v })
      (value := some [.int (Int.ofNat
        (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat)])
      hargs (by rfl) hbind hbody)

theorem dogBarkVatIlksDustToDartOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hfitInk :
      (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat <
        UInt256.size)
    (hfitArt :
      (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat <
        UInt256.size)
    (hspotPos : 0 < (barkVatIlksSpotWord outIlks).toNat)
    (hsafeLt :
      (barkInkSpotWord out outIlks).toNat <
        (barkArtRateUnsafeWord out outIlks).toNat)
    (hlimit :
      (solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv).toNat <
          (solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv).toNat ∧
        (solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat <
          (solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat)
    (hfitRoom :
      (barkSourceRoomWord evmUrns evmIlks I).toNat * dogWadWord.toNat < UInt256.size)
    (hrateNe : barkVatIlksRateWord outIlks ≠ ⟨0⟩)
    (hchopNe : barkSourceMilkChopWord evmUrns I ≠ ⟨0⟩) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
      evmIlks
      (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
        checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
        [ .require
            (.binary .and
              (.binary .gt (.var "spot") (.intLit 0))
              (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
        [ .require
            (.binary .and
              (.binary .gt (.storage HoleRef) (.storage DirtRef))
              (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
        checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
        checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
        [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
        checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
        [ .letDecl "dartByRate" (some uint256)
            (.binary .div (.var "roomWad") (.var "rate")) ] ++
        [ .letDecl "dartCandidate" (some uint256)
            (.binary .div (.var "dartByRate") (.var "milkChop")) ] ++
        [.internalCall "min" [.var "art", .var "dartCandidate"] "dart"])
      (.ok { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  have htoRoom :=
    dogBarkVatIlksDustToRoomOk (v := v) evmUrns evmIlks I out outIlks
      hfitInk hfitArt hspotPos hsafeLt hlimit
  have hroomWad :=
    dogBarkRoomWadCheckedMulOk (v := v) evmUrns evmIlks I out outIlks hfitRoom
  have htoRoomWad :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [ .require
              (.binary .and
                (.binary .gt (.var "spot") (.intLit 0))
                (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
          [ .require
              (.binary .and
                (.binary .gt (.storage HoleRef) (.storage DirtRef))
                (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD))
        (.ok
          { contract := contract,
            locals := barkLocalsRoomWad evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append htoRoom hroomWad
  have hdartByRate :=
    dogBarkDartByRateLetOk (v := v) evmUrns evmIlks I out outIlks hrateNe
  have htoDartByRate :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [ .require
              (.binary .and
                (.binary .gt (.var "spot") (.intLit 0))
                (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
          [ .require
              (.binary .and
                (.binary .gt (.storage HoleRef) (.storage DirtRef))
                (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
          [ .letDecl "dartByRate" (some uint256)
              (.binary .div (.var "roomWad") (.var "rate")) ])
        (.ok
          { contract := contract,
            locals := barkLocalsDartByRate evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append htoRoomWad hdartByRate
  have hdartCandidate :=
    dogBarkDartCandidateLetOk (v := v) evmUrns evmIlks I out outIlks hchopNe
  have htoDartCandidate :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [ .require
              (.binary .and
                (.binary .gt (.var "spot") (.intLit 0))
                (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
          [ .require
              (.binary .and
                (.binary .gt (.storage HoleRef) (.storage DirtRef))
                (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
          [ .letDecl "dartByRate" (some uint256)
              (.binary .div (.var "roomWad") (.var "rate")) ] ++
          [ .letDecl "dartCandidate" (some uint256)
              (.binary .div (.var "dartByRate") (.var "milkChop")) ])
        (.ok
          { contract := contract,
            locals := barkLocalsDartCandidate evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append htoDartByRate hdartCandidate
  have hdartMin :
      ExecBlock config
        { contract := contract,
          locals := barkLocalsDartCandidate evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks
        [.internalCall "min" [.var "art", .var "dartCandidate"] "dart"]
        (.ok
          { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) :=
    ExecBlock.consNormal (dogBarkDartMinCallOk (v := v) evmUrns evmIlks I out outIlks)
      ExecBlock.nil
  simpa [List.append_assoc] using execBlock_append htoDartCandidate hdartMin

theorem dogBarkNoLeftoverIteOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hnoLeftover :
      (barkVatUrnsArtWord out).toNat ≤
        (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks
      [ .ite
          (.binary .gt (.var "art") (.var "dart"))
          (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
            checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
            [ .ite
                (.binary .lt (.var "leftoverDue") (.var "dust"))
                [ .assign .localVar (varRef "dart") (.var "art") ]
                (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                  [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
          [] ]
      (.ok { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsDart evmUrns evmIlks I out outIlks
  let art := barkVatUrnsArtWord out
  let dart := barkSourceDartWord evmUrns evmIlks I out outIlks
  have hart :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "art") = .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "art") (value := art)
        (barkLocalsDart_get_art evmUrns evmIlks I out outIlks)
  have hdart :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    simpa [locals0, dart] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "dart") (value := dart)
        (barkLocalsDart_get_dart evmUrns evmIlks I out outIlks)
  have hcond :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.binary .gt (.var "art") (.var "dart")) = .ok (.bool false) := by
    apply evalExpr_bark_gt_int_false hart hdart
    exact not_lt.mpr (Int.ofNat_le.mpr (by simpa [art, dart] using hnoLeftover))
  exact ExecBlock.consNormal (ExecStmt.iteFalse hcond ExecBlock.nil) ExecBlock.nil

theorem dogBarkInkDartCheckedMulOk {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {ink dart : UInt256}
    (hink : locals.get? "ink" = some (.int (Int.ofNat ink.toNat)))
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hfit : ink.toNat * dart.toNat < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto "inkDart" (.var "ink") (.var "dart"))
      (.ok
        { contract := contract, locals := barkLocalsInkDart locals (barkInkDartWord ink dart), immutables := immStore v }
        evm) := by
  let inkDart := barkInkDartWord ink dart
  let locals1 := barkLocalsInkDart locals inkDart
  have hink0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "ink") =
        .ok (.int (Int.ofNat ink.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "ink") (value := ink) hink
  have hdart0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "dart") =
        .ok (.int (Int.ofNat dart.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dart") (value := dart) hdart
  have hmul :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (mul256 (.var "ink") (.var "dart")) =
          .ok (.int (Int.ofNat inkDart.toNat)) := by
    exact evalExpr_bark_mul256_ok hink0 hdart0
      (by simp [inkDart, barkInkDartWord]) hfit
  have hlet :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
        (.letDecl "inkDart" (some uint256) (mul256 (.var "ink") (.var "dart")))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evm) := by
    simpa [locals1, inkDart, barkLocalsInkDart] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v })
        (evm := evm) (name := "inkDart") (ty := some uint256)
        (expr := mul256 (.var "ink") (.var "dart"))
        (value := .int (Int.ofNat inkDart.toNat)) hmul)
  have hink1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.var "ink") =
        .ok (.int (Int.ofNat ink.toNat)) := by
    simpa [locals1] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "ink") (value := ink)
        (barkLocalsInkDart_get_preserved (by decide) hink)
  have hdart1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm (.var "dart") =
        .ok (.int (Int.ofNat dart.toNat)) := by
    simpa [locals1] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "dart") (value := dart)
        (barkLocalsInkDart_get_preserved (by decide) hdart)
  have hinkDart1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.var "inkDart") = .ok (.int (Int.ofNat inkDart.toNat)) := by
    simpa [locals1, inkDart] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "inkDart") (value := inkDart)
        (barkLocalsInkDart_get_inkDart locals inkDart)
  have hzero :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.binary .or
          (.binary .eq (.var "dart") (.intLit 0))
          (.binary .eq (.binary .div (.var "inkDart") (.var "dart")) (.var "ink"))) =
        .ok (.bool true) := by
    by_cases hdartZero : dart = ⟨0⟩
    · have hleft :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.var "dart") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_bark_eq_int_true hdart1 hzero
        simp [hdartZero]
      exact evalExpr_bark_or_true_left hleft
    · have hleft :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.var "dart") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_bark_eq_int_false hdart1 hzero
        intro hnat
        apply hdartZero
        exact uint256_toNat_eq_zero (Int.ofNat.inj hnat)
      have hdivWord : UInt256.div inkDart dart = ink := by
        apply u256_inj
        rw [udiv_toNat]
        have hprod : inkDart.toNat = ink.toNat * dart.toNat := by
          dsimp [inkDart, barkInkDartWord]
          exact umul_toNat ink dart hfit
        rw [hprod]
        rw [Nat.mul_comm ink.toNat dart.toNat]
        exact Nat.mul_div_right ink.toNat
          (Nat.pos_of_ne_zero (fun hzeroNat => hdartZero (uint256_toNat_eq_zero hzeroNat)))
      have hdiv :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .div (.var "inkDart") (.var "dart")) =
              .ok (.int (Int.ofNat ink.toNat)) := by
        have hraw := evalExpr_bark_div_uint256_ok
          (v := v) (evm := evm) (locals := locals1)
          (x := .var "inkDart") (y := .var "dart")
          (a := inkDart) (b := dart) (q := UInt256.div inkDart dart)
          hinkDart1 hdart1 hdartZero rfl
        simpa [hdivWord] using hraw
      have hright :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.binary .div (.var "inkDart") (.var "dart")) (.var "ink")) =
              .ok (.bool true) :=
        evalExpr_bark_eq_int_true hdiv hink1 rfl
      exact evalExpr_bark_or_false_right hleft hright
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal hlet
    (ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkInkDartCheckedMulOverflow {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {ink dart : UInt256}
    (hink : locals.get? "ink" = some (.int (Int.ofNat ink.toNat)))
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hover : UInt256.size ≤ ink.toNat * dart.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto "inkDart" (.var "ink") (.var "dart")) .reverted := by
  have hink0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "ink") =
        .ok (.int (Int.ofNat ink.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "ink") (value := ink) hink
  have hdart0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "dart") =
        .ok (.int (Int.ofNat dart.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dart") (value := dart) hdart
  have hmul :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (mul256 (.var "ink") (.var "dart")) = .revert :=
    evalExpr_bark_mul256_revert hink0 hdart0 hover
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmul)

theorem dogBarkCheckedSubOk {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {name : Ident} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hxAfter :
      evalExpr? config
        { contract := contract,
          locals := locals.insert name (.int (Int.ofNat (UInt256.sub a b).toNat)), immutables := immStore v } evm x =
        .ok (.int (Int.ofNat a.toNat)))
    (hle : b.toNat ≤ a.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedSubUintInto name x y)
      (.ok
        { contract := contract,
          locals := locals.insert name (.int (Int.ofNat (UInt256.sub a b).toNat)), immutables := immStore v } evm) := by
  let diff := UInt256.sub a b
  let locals1 := locals.insert name (.int (Int.ofNat diff.toNat))
  have hsub :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (sub256 x y) =
        .ok (.int (Int.ofNat diff.toNat)) := by
    exact evalExpr_bark_sub256_ok hx hy (by simp [diff]) hle
  have hlet :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
        (.letDecl name (some uint256) (sub256 x y))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evm) := by
    simpa [locals1, diff] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v })
        (evm := evm) (name := name) (ty := some uint256) (expr := sub256 x y)
        (value := .int (Int.ofNat diff.toNat)) hsub)
  have hname :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.var name) = .ok (.int (Int.ofNat diff.toNat)) := by
    simpa [locals1, diff] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := name) (value := diff) (by simp [locals1])
  have hdiffLe : diff.toNat ≤ a.toNat := by
    simp [diff, usub_toNat hle]
  have hreq :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.binary .le (.var name) x) = .ok (.bool true) := by
    apply evalExpr_bark_le_int_true hname
    simpa [locals1, diff] using hxAfter
    exact Int.ofNat_le.mpr hdiffLe
  simpa [checkedSubUintInto, locals1, diff] using
    (ExecBlock.consNormal hlet <|
      ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkCheckedAddOk {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {name : Ident} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hxAfter :
      evalExpr? config
        { contract := contract,
          locals := locals.insert name (.int (Int.ofNat (a + b).toNat)), immutables := immStore v } evm x =
        .ok (.int (Int.ofNat a.toNat)))
    (hfit : a.toNat + b.toNat < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedAddUintInto name x y)
      (.ok
        { contract := contract, locals := locals.insert name (.int (Int.ofNat (a + b).toNat)), immutables := immStore v }
        evm) := by
  let sum := a + b
  let locals1 := locals.insert name (.int (Int.ofNat sum.toNat))
  have hadd :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (add256 x y) =
        .ok (.int (Int.ofNat sum.toNat)) := by
    exact evalExpr_bark_add256_ok hx hy (by simp [sum]) hfit
  have hlet :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
        (.letDecl name (some uint256) (add256 x y))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evm) := by
    simpa [locals1, sum] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v })
        (evm := evm) (name := name) (ty := some uint256) (expr := add256 x y)
        (value := .int (Int.ofNat sum.toNat)) hadd)
  have hname :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.var name) = .ok (.int (Int.ofNat sum.toNat)) := by
    simpa [locals1, sum] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := name) (value := sum) (by simp [locals1])
  have haLe : a.toNat ≤ sum.toNat := by
    simp [sum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hreq :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.binary .ge (.var name) x) = .ok (.bool true) := by
    apply evalExpr_bark_ge_int_true hname
    simpa [locals1, sum] using hxAfter
    exact Int.ofNat_le.mpr haLe
  simpa [checkedAddUintInto, locals1, sum] using
    (ExecBlock.consNormal hlet <|
      ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkCheckedMulOk {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {name : Ident} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hxAfter :
      evalExpr? config
        { contract := contract,
          locals := locals.insert name (.int (Int.ofNat (a * b).toNat)), immutables := immStore v } evm x =
        .ok (.int (Int.ofNat a.toNat)))
    (hyAfter :
      evalExpr? config
        { contract := contract,
          locals := locals.insert name (.int (Int.ofNat (a * b).toNat)), immutables := immStore v } evm y =
        .ok (.int (Int.ofNat b.toNat)))
    (hfit : a.toNat * b.toNat < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto name x y)
      (.ok
        { contract := contract,
          locals := locals.insert name (.int (Int.ofNat (a * b).toNat)), immutables := immStore v } evm) := by
  let prod := a * b
  let locals1 := locals.insert name (.int (Int.ofNat prod.toNat))
  have hmul :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (mul256 x y) =
        .ok (.int (Int.ofNat prod.toNat)) := by
    exact evalExpr_bark_mul256_ok hx hy (by simp [prod]) hfit
  have hlet :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
        (.letDecl name (some uint256) (mul256 x y))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evm) := by
    simpa [locals1, prod] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v })
        (evm := evm) (name := name) (ty := some uint256) (expr := mul256 x y)
        (value := .int (Int.ofNat prod.toNat)) hmul)
  have hname :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.var name) = .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [locals1, prod] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := name) (value := prod) (by simp [locals1])
  have hzero :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
        (.binary .or
          (.binary .eq y (.intLit 0))
          (.binary .eq (.binary .div (.var name) y) x)) =
        .ok (.bool true) := by
    by_cases hbZero : b = ⟨0⟩
    · have hleft :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq y (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_bark_eq_int_true hyAfter hzero
        simp [hbZero]
      exact evalExpr_bark_or_true_left hleft
    · have hleft :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq y (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_bark_eq_int_false hyAfter hzero
        intro hnat
        apply hbZero
        exact uint256_toNat_eq_zero (Int.ofNat.inj hnat)
      have hdivWord : UInt256.div prod b = a := by
        apply u256_inj
        rw [udiv_toNat]
        have hprod : prod.toNat = a.toNat * b.toNat := by
          dsimp [prod]
          exact umul_toNat a b hfit
        rw [hprod]
        rw [Nat.mul_comm a.toNat b.toNat]
        exact Nat.mul_div_right a.toNat
          (Nat.pos_of_ne_zero (fun hzeroNat => hbZero (uint256_toNat_eq_zero hzeroNat)))
      have hdiv :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .div (.var name) y) =
              .ok (.int (Int.ofNat a.toNat)) := by
        have hraw := evalExpr_bark_div_uint256_ok
          (v := v) (evm := evm) (locals := locals1)
          (x := .var name) (y := y)
          (a := prod) (b := b) (q := UInt256.div prod b)
          hname hyAfter hbZero rfl
        simpa [hdivWord] using hraw
      have hright :
          evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evm
            (.binary .eq (.binary .div (.var name) y) x) =
              .ok (.bool true) :=
        evalExpr_bark_eq_int_true hdiv hxAfter rfl
      exact evalExpr_bark_or_false_right hleft hright
  simpa [checkedMulUintInto, locals1, prod] using
    (ExecBlock.consNormal hlet <|
      ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkCheckedMulOverflow {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {name : Ident} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto name x y) .reverted := by
  have hmul :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (mul256 x y) =
        .revert :=
    evalExpr_bark_mul256_revert hx hy hover
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmul)

theorem dogBarkCheckedAddOverflow {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {name : Ident} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedAddUintInto name x y) .reverted := by
  have hadd :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (add256 x y) =
        .revert :=
    evalExpr_bark_add256_revert hx hy hover
  simp only [checkedAddUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hadd)

theorem dogBarkTabBaseCheckedMulOkSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {due milkChop : UInt256}
    (hdue : locals.get? "due" = some (.int (Int.ofNat due.toNat)))
    (hmilkChop : locals.get? "milkChop" = some (.int (Int.ofNat milkChop.toNat)))
    (hfit : due.toNat * milkChop.toNat < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto "tabBase" (.var "due") (.var "milkChop"))
      (.ok
        { contract := contract,
          locals := barkLocalsTabBase locals (barkTabBaseWord due milkChop), immutables := immStore v } evm) := by
  have hdue0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "due") =
        .ok (.int (Int.ofNat due.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "due") (value := due) hdue
  have hmilk0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "milkChop") = .ok (.int (Int.ofNat milkChop.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "milkChop") (value := milkChop) hmilkChop
  have hdue1 :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "tabBase" (.int (Int.ofNat (due * milkChop).toNat)), immutables := immStore v }
        evm (.var "due") = .ok (.int (Int.ofNat due.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm)
      (locals := locals.insert "tabBase" (.int (Int.ofNat (due * milkChop).toNat)))
      (name := "due") (value := due)
      (by rw [store_get_ne _ _ (by decide)]; exact hdue)
  have hmilk1 :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "tabBase" (.int (Int.ofNat (due * milkChop).toNat)), immutables := immStore v }
        evm (.var "milkChop") = .ok (.int (Int.ofNat milkChop.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm)
      (locals := locals.insert "tabBase" (.int (Int.ofNat (due * milkChop).toNat)))
      (name := "milkChop") (value := milkChop)
      (by rw [store_get_ne _ _ (by decide)]; exact hmilkChop)
  simpa [barkLocalsTabBase, barkTabBaseWord] using
    dogBarkCheckedMulOk (v := v) evm (name := "tabBase")
      (x := .var "due") (y := .var "milkChop") (a := due) (b := milkChop)
      hdue0 hmilk0 hdue1 hmilk1 hfit

theorem dogBarkTabBaseCheckedMulOverflowSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {due milkChop : UInt256}
    (hdue : locals.get? "due" = some (.int (Int.ofNat due.toNat)))
    (hmilkChop : locals.get? "milkChop" = some (.int (Int.ofNat milkChop.toNat)))
    (hover : UInt256.size ≤ due.toNat * milkChop.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto "tabBase" (.var "due") (.var "milkChop")) .reverted := by
  have hdue0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "due") =
        .ok (.int (Int.ofNat due.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "due") (value := due) hdue
  have hmilk0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "milkChop") = .ok (.int (Int.ofNat milkChop.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "milkChop") (value := milkChop) hmilkChop
  exact dogBarkCheckedMulOverflow (v := v) evm
    (name := "tabBase") (x := .var "due") (y := .var "milkChop")
    hdue0 hmilk0 hover

theorem dogBarkTabLetOk {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {tabBase : UInt256}
    (htabBase : locals.get? "tabBase" = some (.int (Int.ofNat tabBase.toNat))) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      [ .letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)) ]
      (.ok { contract := contract, locals := barkLocalsTab locals (barkTabWord tabBase), immutables := immStore v }
        evm) := by
  let tab := barkTabWord tabBase
  have htabBaseExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "tabBase") = .ok (.int (Int.ofNat tabBase.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "tabBase") (value := tabBase) htabBase
  have hWad :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.intLit WAD) = .ok (.int (Int.ofNat dogWadWord.toNat)) := by
    have hWadNat : dogWadWord.toNat = 1000000000000000000 := by
      native_decide
    simp [evalExpr?, pure, WAD, hWadNat]
  have hdiv :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .div (.var "tabBase") (.intLit WAD)) =
          .ok (.int (Int.ofNat tab.toNat)) := by
    exact evalExpr_bark_div_uint256_ok htabBaseExpr hWad
      (by native_decide : dogWadWord ≠ ⟨0⟩)
      (by simp [tab, barkTabWord])
  have hlet :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
        (.letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)))
        (.ok { contract := contract, locals := barkLocalsTab locals tab, immutables := immStore v } evm) := by
    simpa [tab, barkLocalsTab] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals, immutables := immStore v })
        (evm := evm) (name := "tab") (ty := some uint256)
        (expr := .binary .div (.var "tabBase") (.intLit WAD))
        (value := .int (Int.ofNat tab.toNat)) hdiv)
  exact ExecBlock.consNormal hlet ExecBlock.nil

theorem dogBarkDirtAddOkSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {tab : UInt256}
    (hDirt : locals.get? "Dirt" = none)
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hfit :
      (solcSlotWordAt ⟨5⟩ evm.accountMap evm.executionEnv).toNat + tab.toNat <
        UInt256.size) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab"))
      (.ok
        { contract := contract,
          locals :=
            barkLocalsDirtNew locals
              (barkDirtNewWord (solcSlotWordAt ⟨5⟩ evm.accountMap evm.executionEnv) tab), immutables := immStore v }
        evm) := by
  let dirt := solcSlotWordAt ⟨5⟩ evm.accountMap evm.executionEnv
  have hdirt0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt.toNat)) := by
    simpa [dirt] using evalExpr_barkStorageDirt (v := v) (evm := evm)
      (locals := locals) hDirt
  have htab0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "tab") =
        .ok (.int (Int.ofNat tab.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "tab") (value := tab) htab
  have hDirtAfter :
      (locals.insert "DirtNew" (.int (Int.ofNat (dirt + tab).toNat))).get? "Dirt" =
        none := by
    rw [store_get_ne _ _ (by decide)]
    exact hDirt
  have hdirt1 :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "DirtNew" (.int (Int.ofNat (dirt + tab).toNat)), immutables := immStore v } evm
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt.toNat)) := by
    exact evalExpr_barkStorageDirt (v := v) (evm := evm)
      (locals := locals.insert "DirtNew" (.int (Int.ofNat (dirt + tab).toNat)))
      hDirtAfter
  simpa [barkLocalsDirtNew, barkDirtNewWord, dirt] using
    dogBarkCheckedAddOk (v := v) evm (name := "DirtNew")
      (x := .storage DirtRef) (y := .var "tab") (a := dirt) (b := tab)
      hdirt0 htab0 hdirt1 (by simpa [dirt] using hfit)

theorem dogBarkDirtAddOverflowSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {tab : UInt256}
    (hDirt : locals.get? "Dirt" = none)
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hover :
      UInt256.size ≤
        (solcSlotWordAt ⟨5⟩ evm.accountMap evm.executionEnv).toNat + tab.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab")) .reverted := by
  let dirt := solcSlotWordAt ⟨5⟩ evm.accountMap evm.executionEnv
  have hdirt0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt.toNat)) := by
    simpa [dirt] using evalExpr_barkStorageDirt (v := v) (evm := evm)
      (locals := locals) hDirt
  have htab0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "tab") =
        .ok (.int (Int.ofNat tab.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "tab") (value := tab) htab
  exact dogBarkCheckedAddOverflow (v := v) evm
    (name := "DirtNew") (x := .storage DirtRef) (y := .var "tab")
    hdirt0 htab0 (by simpa [dirt] using hover)

theorem dogBarkDirtAssignOkSourceSplit {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {dirtNew : UInt256}
    (hDirt : locals.get? "Dirt" = none)
    (hDirtNew : locals.get? "DirtNew" = some (.int (Int.ofNat dirtNew.toNat))) :
    (evm.executionEnv.perm = true → ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      [ .assign .storage DirtRef (.var "DirtNew") ]
      (.ok { contract := contract, locals := locals, immutables := immStore v }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ dirtNew))) ∧
      (evm.executionEnv.perm = false →
        ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
          [.assign .storage DirtRef (.var "DirtNew")] .staticViolation) := by
  let evm' := Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ dirtNew
  have hval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "DirtNew") = .ok (.int (Int.ofNat dirtNew.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "DirtNew") (value := dirtNew) hDirtNew
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm
        .storage DirtRef (.int (Int.ofNat dirtNew.toNat)) =
        .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm') := by
    simpa [evm'] using assign_barkDirtStorage (v := v) evm dirtNew hDirt
  constructor
  · intro hperm
    exact ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm) hval hassign) ExecBlock.nil
  · intro hperm
    exact ExecBlock.consStatic (ExecStmt.assignStatic hval hassign hperm)

theorem dogBarkIlkDirtAddOkSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {milkDirt tab : UInt256}
    (hmilkDirt : locals.get? "milkDirt" = some (.int (Int.ofNat milkDirt.toNat)))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hfit : milkDirt.toNat + tab.toNat < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab"))
      (.ok
        { contract := contract,
          locals := barkLocalsIlkDirtNew locals (barkIlkDirtNewWord milkDirt tab), immutables := immStore v } evm) := by
  have hmilk0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "milkDirt") = .ok (.int (Int.ofNat milkDirt.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "milkDirt") (value := milkDirt) hmilkDirt
  have htab0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "tab") =
        .ok (.int (Int.ofNat tab.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "tab") (value := tab) htab
  have hmilk1 :
      evalExpr? config
        { contract := contract,
          locals := locals.insert "ilkDirtNew" (.int (Int.ofNat (milkDirt + tab).toNat)), immutables := immStore v }
        evm (.var "milkDirt") = .ok (.int (Int.ofNat milkDirt.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm)
      (locals := locals.insert "ilkDirtNew" (.int (Int.ofNat (milkDirt + tab).toNat)))
      (name := "milkDirt") (value := milkDirt)
      (by rw [store_get_ne _ _ (by decide)]; exact hmilkDirt)
  simpa [barkLocalsIlkDirtNew, barkIlkDirtNewWord] using
    dogBarkCheckedAddOk (v := v) evm (name := "ilkDirtNew")
      (x := .var "milkDirt") (y := .var "tab") (a := milkDirt) (b := tab)
      hmilk0 htab0 hmilk1 hfit

theorem dogBarkIlkDirtAddOverflowSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {milkDirt tab : UInt256}
    (hmilkDirt : locals.get? "milkDirt" = some (.int (Int.ofNat milkDirt.toNat)))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hover : UInt256.size ≤ milkDirt.toNat + tab.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab")) .reverted := by
  have hmilk0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "milkDirt") = .ok (.int (Int.ofNat milkDirt.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "milkDirt") (value := milkDirt) hmilkDirt
  have htab0 :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "tab") =
        .ok (.int (Int.ofNat tab.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "tab") (value := tab) htab
  exact dogBarkCheckedAddOverflow (v := v) evm
    (name := "ilkDirtNew") (x := .var "milkDirt") (y := .var "tab")
    hmilk0 htab0 hover

theorem dogBarkIlkDirtAssignOkSource {v : DogImmutables} (evm : EVM.State)
    {I : ExecutionEnv} {locals : Store} {ilkDirtNew : UInt256}
    (hsz100 : 100 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (barkIlkValue I))
    (hIlkDirtNew :
      locals.get? "ilkDirtNew" = some (.int (Int.ofNat ilkDirtNew.toNat)))
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ]
      (.ok { contract := contract, locals := locals, immutables := immStore v }
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner
          (barkIlksDirtSlotFor I) ilkDirtNew)) := by
  let evm' := Stele.EVM.storageStore evm evm.executionEnv.codeOwner
    (barkIlksDirtSlotFor I) ilkDirtNew
  have hval :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "ilkDirtNew") = .ok (.int (Int.ofNat ilkDirtNew.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "ilkDirtNew") (value := ilkDirtNew) hIlkDirtNew
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm
        .storage (ilksF (.var "ilk") "dirt") (.int (Int.ofNat ilkDirtNew.toNat)) =
        .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm') := by
    simpa [evm'] using
      assign_barkIlkDirtStorage (v := v) evm (I := I) hsz100 ilkDirtNew hilks hilk
  exact ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inr hperm) hval hassign) ExecBlock.nil

theorem evalExprs_barkKickArgs {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {tab dink : UInt256} {urn kpr : AccountAddress}
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hurn : locals.get? "urn" = some (.address urn))
    (hkpr : locals.get? "kpr" = some (.address kpr)) :
    evalExprs? config { contract := contract, locals := locals, immutables := immStore v } evm
      [.var "tab", .var "dink", .var "urn", .var "kpr"] =
      .ok [.int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat),
        .address urn, .address kpr] := by
  have htabExpr :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "tab") (value := tab) htab
  have hdinkExpr :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dink") (value := dink) hdink
  have hurnExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "urn") = .ok (.address urn) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "urn") =
      .ok (.address urn)
    rw [hurn]
    rfl
  have hkprExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "kpr") = .ok (.address kpr) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "kpr") =
      .ok (.address kpr)
    rw [hkpr]
    rfl
  simp [evalExprs?, htabExpr, hdinkExpr, hurnExpr, hkprExpr, EvalResult.bind, bind, pure]

theorem dogBarkKickNoCodeBlock {v : DogImmutables} {evm : EVM.State}
    {locals : Store}
    (hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.extCodeSize (.var "milkClip")) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
        [.var "tab", .var "dink", .var "urn", .var "kpr"] "id")
      .reverted := by
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm) (locals := locals)
      (receiver := .var "milkClip") (name := "kick") (sendVal := 0)
      (args := [.var "tab", .var "dink", .var "urn", .var "kpr"])
      (retVar := "id") (perm := true) hguard)

theorem dogBarkKickCallFailureBlock {v : DogImmutables} {evm evm' : EVM.State}
    {locals : Store} {outKick : ByteArray} {milkClip tab dink : UInt256}
    {urn kpr : AccountAddress}
    (hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.extCodeSize (.var "milkClip")) (.intLit 0)) = .ok (.bool true))
    (hmilkClip :
      locals.get? "milkClip" =
        some (.address (AccountAddress.ofNat milkClip.toNat)))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hurn : locals.get? "urn" = some (.address urn))
    (hkpr : locals.get? "kpr" = some (.address kpr))
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat milkClip.toNat)) "kick" 0
        [.int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat), .address urn,
          .address kpr]
        (false, evm', outKick) true) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
        [.var "tab", .var "dink", .var "urn", .var "kpr"] "id")
      .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "milkClip") = .ok (.address (AccountAddress.ofNat milkClip.toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "milkClip") =
      .ok (.address (AccountAddress.ofNat milkClip.toNat))
    rw [hmilkClip]
    rfl
  have hargs :=
    evalExprs_barkKickArgs (v := v) (evm := evm) (locals := locals)
      (tab := tab) (dink := dink) (urn := urn) (kpr := kpr)
      htab hdink hurn hkpr
  simpa [checkedExternalCallStmts] using
    (checkedExternalCallFailure (hperm := Or.inl rfl)
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := locals) (receiver := .var "milkClip") (retVar := "id")
      (name := "kick") (target := AccountAddress.ofNat milkClip.toNat)
      (sendVal := 0)
      (args := [.var "tab", .var "dink", .var "urn", .var "kpr"])
      (argVals := [.int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat),
        .address urn, .address kpr])
      (out := outKick) (perm := true) hguard hreceiver hargs hcall)

theorem dogBarkKickDecodeRevertBlock {v : DogImmutables} {evm evm' : EVM.State}
    {locals : Store} {outKick : ByteArray} {milkClip tab dink : UInt256}
    {urn kpr : AccountAddress}
    (hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.extCodeSize (.var "milkClip")) (.intLit 0)) = .ok (.bool true))
    (hmilkClip :
      locals.get? "milkClip" =
        some (.address (AccountAddress.ofNat milkClip.toNat)))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hurn : locals.get? "urn" = some (.address urn))
    (hkpr : locals.get? "kpr" = some (.address kpr))
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat milkClip.toNat)) "kick" 0
        [.int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat), .address urn,
          .address kpr]
        (true, evm', outKick) true)
    (hdec : config.externalABI.decode? "kick" outKick = none) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
        [.var "tab", .var "dink", .var "urn", .var "kpr"] "id")
      .reverted := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "milkClip") = .ok (.address (AccountAddress.ofNat milkClip.toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "milkClip") =
      .ok (.address (AccountAddress.ofNat milkClip.toNat))
    rw [hmilkClip]
    rfl
  have hargs :=
    evalExprs_barkKickArgs (v := v) (evm := evm) (locals := locals)
      (tab := tab) (dink := dink) (urn := urn) (kpr := kpr)
      htab hdink hurn hkpr
  have hstmt :
      ExecStmt config { contract := contract, locals := locals, immutables := immStore v } evm
        (.externalCall (.var "milkClip") "kick" (.intLit 0)
          [.var "tab", .var "dink", .var "urn", .var "kpr"] "id")
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert (hperm := Or.inl rfl) hreceiver (by simp [evalExpr?, pure])
      hargs hcall hdec
  simp only [checkedExternalCallStmts, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal (ExecStmt.requireTrue hguard)
    (ExecBlock.consRevert hstmt)

theorem dogBarkKickCallSuccessBlock {v : DogImmutables} {evm evm' : EVM.State}
    {locals : Store} {outKick : ByteArray} {milkClip tab dink id : UInt256}
    {urn kpr : AccountAddress}
    (hguard :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.extCodeSize (.var "milkClip")) (.intLit 0)) = .ok (.bool true))
    (hmilkClip :
      locals.get? "milkClip" =
        some (.address (AccountAddress.ofNat milkClip.toNat)))
    (htab : locals.get? "tab" = some (.int (Int.ofNat tab.toNat)))
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hurn : locals.get? "urn" = some (.address urn))
    (hkpr : locals.get? "kpr" = some (.address kpr))
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (AccountAddress.ofNat milkClip.toNat)) "kick" 0
        [.int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat), .address urn,
          .address kpr]
        (true, evm', outKick) true)
    (hdec :
      config.externalABI.decode? "kick" outKick =
        some [.int (Int.ofNat id.toNat)]) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
        [.var "tab", .var "dink", .var "urn", .var "kpr"] "id")
      (.ok { contract := contract, locals := barkLocalsId locals id, immutables := immStore v } evm') := by
  have hreceiver :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "milkClip") = .ok (.address (AccountAddress.ofNat milkClip.toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "milkClip") =
      .ok (.address (AccountAddress.ofNat milkClip.toNat))
    rw [hmilkClip]
    rfl
  have hargs :=
    evalExprs_barkKickArgs (v := v) (evm := evm) (locals := locals)
      (tab := tab) (dink := dink) (urn := urn) (kpr := kpr)
      htab hdink hurn hkpr
  simpa [checkedExternalCallStmts, barkLocalsId, collapseReturns] using
    (checkedExternalCallSuccess (hperm := Or.inl rfl)
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := locals) (receiver := .var "milkClip") (retVar := "id")
      (name := "kick") (target := AccountAddress.ofNat milkClip.toNat)
      (sendVal := 0)
      (args := [.var "tab", .var "dink", .var "urn", .var "kpr"])
      (argVals := [.int (Int.ofNat tab.toNat), .int (Int.ofNat dink.toNat),
        .address urn, .address kpr])
      (out := outKick) (perm := true) (value := [.int (Int.ofNat id.toNat)])
      hguard hreceiver hargs hcall hdec)

theorem dogBarkReturnIdBlock {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {id : UInt256}
    (hid : locals.get? "id" = some (.int (Int.ofNat id.toNat))) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      [ .return [.var "id"] ]
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm
        (some [.int (Int.ofNat id.toNat)])) := by
  have hidExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "id") = .ok (.int (Int.ofNat id.toNat)) :=
    evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "id") (value := id) hid
  exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hidExpr))

theorem dogAssignLocalVarBaseOk {v : DogImmutables} {evm : EVM.State} {locals : Store}
    {name : Ident} {old value : Value}
    (hget : locals.get? name = some old) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm .localVar
        { base := name } value =
      .ok ({ contract := contract, locals := locals.insert name value, immutables := immStore v }, evm) := by
  simp only [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure]
  change (match locals.get? name with
    | some _ =>
        EvalResult.ok (({ contract := contract, locals := locals.insert name value, immutables := immStore v } : Frame),
          evm)
    | none => EvalResult.error EvalError.unboundVariable) =
      EvalResult.ok (({ contract := contract, locals := locals.insert name value, immutables := immStore v } : Frame),
        evm)
  rw [hget]

theorem dogBarkLeftoverDuePrefixOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hleftover :
      (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat <
        (barkVatUrnsArtWord out).toNat)
    (hfitLeftoverDue :
      (barkLeftoverArtWord (barkVatUrnsArtWord out)
        (barkSourceDartWord evmUrns evmIlks I out outIlks)).toNat *
        (barkVatIlksRateWord outIlks).toNat < UInt256.size) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks
      (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
        checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate"))
      (.ok
        { contract := contract,
          locals := barkLocalsLeftoverDue evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsDart evmUrns evmIlks I out outIlks
  let locals1 := barkLocalsLeftoverArt evmUrns evmIlks I out outIlks
  let art := barkVatUrnsArtWord out
  let dart := barkSourceDartWord evmUrns evmIlks I out outIlks
  let rate := barkVatIlksRateWord outIlks
  let leftoverArt := barkLeftoverArtWord art dart
  have hart0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "art") = .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "art") (value := art)
        (barkLocalsDart_get_art evmUrns evmIlks I out outIlks)
  have hdart0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    simpa [locals0, dart] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "dart") (value := dart)
        (barkLocalsDart_get_dart evmUrns evmIlks I out outIlks)
  have hart1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.var "art") = .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals1, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals1)
        (name := "art") (value := art)
        (barkLocalsLeftoverArt_get_preserved (by decide)
          (barkLocalsDart_get_art evmUrns evmIlks I out outIlks))
  have hsub :
      ExecBlock config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart"))
        (.ok { contract := contract, locals := locals1, immutables := immStore v } evmIlks) := by
    simpa [locals0, locals1, art, dart, leftoverArt, barkLeftoverArtWord] using
      dogBarkCheckedSubOk (v := v) evmIlks (name := "leftoverArt")
        (x := .var "art") (y := .var "dart") (a := art) (b := dart)
        hart0 hdart0 hart1 (le_of_lt hleftover)
  have hleftoverArt1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.var "leftoverArt") = .ok (.int (Int.ofNat leftoverArt.toNat)) := by
    simpa [locals1, leftoverArt, art, dart, barkLeftoverArtWord] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals1)
        (name := "leftoverArt") (value := leftoverArt)
        (barkLocalsLeftoverArt_get_leftoverArt evmUrns evmIlks I out outIlks)
  have hrate1 :
      evalExpr? config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (.var "rate") = .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [locals1, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals1)
        (name := "rate") (value := rate)
        (barkLocalsLeftoverArt_get_preserved (by decide)
          (barkLocalsDart_get_rate evmUrns evmIlks I out outIlks))
  have hleftoverArt2 :
      evalExpr? config
        { contract := contract,
          locals := locals1.insert "leftoverDue"
            (.int (Int.ofNat (leftoverArt * rate).toNat)), immutables := immStore v } evmIlks
        (.var "leftoverArt") = .ok (.int (Int.ofNat leftoverArt.toNat)) := by
    simpa [locals1, leftoverArt, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks)
        (locals := locals1.insert "leftoverDue"
          (.int (Int.ofNat (leftoverArt * rate).toNat)))
        (name := "leftoverArt") (value := leftoverArt)
        (by
          rw [store_get_ne _ _ (by decide)]
          simpa [locals1, leftoverArt, art, dart, barkLeftoverArtWord] using
            barkLocalsLeftoverArt_get_leftoverArt evmUrns evmIlks I out outIlks)
  have hrate2 :
      evalExpr? config
        { contract := contract,
          locals := locals1.insert "leftoverDue"
            (.int (Int.ofNat (leftoverArt * rate).toNat)), immutables := immStore v } evmIlks
        (.var "rate") = .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [locals1, rate, leftoverArt] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks)
        (locals := locals1.insert "leftoverDue"
          (.int (Int.ofNat (leftoverArt * rate).toNat)))
        (name := "rate") (value := rate)
        (by
          rw [store_get_ne _ _ (by decide)]
          exact barkLocalsLeftoverArt_get_preserved (evmUrns := evmUrns)
            (evmIlks := evmIlks) (I := I) (out := out) (outIlks := outIlks)
            (name := "rate") (value := .int (Int.ofNat rate.toNat)) (by decide)
            (by simpa [rate] using
              barkLocalsDart_get_rate evmUrns evmIlks I out outIlks))
  have hmul :
      ExecBlock config { contract := contract, locals := locals1, immutables := immStore v } evmIlks
        (checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate"))
        (.ok
          { contract := contract,
            locals := barkLocalsLeftoverDue evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [locals1, art, dart, rate, leftoverArt, barkLeftoverArtWord,
      barkLocalsLeftoverDue] using
      dogBarkCheckedMulOk (v := v) evmIlks (name := "leftoverDue")
        (x := .var "leftoverArt") (y := .var "rate")
        (a := leftoverArt) (b := rate)
        hleftoverArt1 hrate1 hleftoverArt2 hrate2
        (by simpa [art, dart, rate, leftoverArt] using hfitLeftoverDue)
  simpa [locals0] using execBlock_append hsub hmul

theorem dogBarkDustyLeftoverIteOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hleftover :
      (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat <
        (barkVatUrnsArtWord out).toNat)
    (hfitLeftoverDue :
      (barkLeftoverArtWord (barkVatUrnsArtWord out)
        (barkSourceDartWord evmUrns evmIlks I out outIlks)).toNat *
        (barkVatIlksRateWord outIlks).toNat < UInt256.size)
    (hdusty :
      (barkLeftoverDueWord (barkVatUrnsArtWord out)
        (barkSourceDartWord evmUrns evmIlks I out outIlks)
        (barkVatIlksRateWord outIlks)).toNat <
        (barkVatIlksDustWord outIlks).toNat) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks
      [ .ite
          (.binary .gt (.var "art") (.var "dart"))
          (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
            checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
            [ .ite
                (.binary .lt (.var "leftoverDue") (.var "dust"))
                [ .assign .localVar (varRef "dart") (.var "art") ]
                (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                  [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
          [] ]
      (.ok
        { contract := contract,
          locals := barkLocalsDustyDart evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsDart evmUrns evmIlks I out outIlks
  let localsDue := barkLocalsLeftoverDue evmUrns evmIlks I out outIlks
  let art := barkVatUrnsArtWord out
  let dart := barkSourceDartWord evmUrns evmIlks I out outIlks
  let rate := barkVatIlksRateWord outIlks
  let dust := barkVatIlksDustWord outIlks
  let leftoverDue := barkLeftoverDueWord art dart rate
  have hart0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "art") = .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "art") (value := art)
        (barkLocalsDart_get_art evmUrns evmIlks I out outIlks)
  have hdart0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    simpa [locals0, dart] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "dart") (value := dart)
        (barkLocalsDart_get_dart evmUrns evmIlks I out outIlks)
  have houter :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.binary .gt (.var "art") (.var "dart")) = .ok (.bool true) := by
    apply evalExpr_bark_gt_int_true hart0 hdart0
    exact Int.ofNat_lt.mpr (by simpa [art, dart] using hleftover)
  have hprefix :=
    dogBarkLeftoverDuePrefixOk (v := v) evmUrns evmIlks I out outIlks
      hleftover hfitLeftoverDue
  have hleftoverDueExpr :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "leftoverDue") = .ok (.int (Int.ofNat leftoverDue.toNat)) := by
    simpa [localsDue, leftoverDue, art, dart, rate, barkLeftoverDueWord,
      barkLeftoverArtWord] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "leftoverDue") (value := leftoverDue)
        (barkLocalsLeftoverDue_get_leftoverDue evmUrns evmIlks I out outIlks)
  have hdustExpr :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "dust") = .ok (.int (Int.ofNat dust.toNat)) := by
    simpa [localsDue, dust] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "dust") (value := dust)
        (barkLocalsLeftoverDue_get_preserved (by decide)
          (barkLocalsLeftoverArt_get_preserved (by decide)
            (barkLocalsDart_get_dust evmUrns evmIlks I out outIlks)))
  have hinnerCond :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.binary .lt (.var "leftoverDue") (.var "dust")) = .ok (.bool true) := by
    apply evalExpr_bark_lt_int_true hleftoverDueExpr hdustExpr
    exact Int.ofNat_lt.mpr (by simpa [leftoverDue, art, dart, rate] using hdusty)
  have hartDue :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "art") = .ok (.int (Int.ofNat art.toNat)) := by
    simpa [localsDue, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "art") (value := art)
        (barkLocalsLeftoverDue_get_preserved (by decide)
          (barkLocalsLeftoverArt_get_preserved (by decide)
            (barkLocalsDart_get_art evmUrns evmIlks I out outIlks)))
  have hdartDueGet :
      (barkLocalsLeftoverDue evmUrns evmIlks I out outIlks).get? "dart" =
        some (.int (Int.ofNat dart.toNat)) := by
    simpa [dart] using
      barkLocalsLeftoverDue_get_preserved (evmUrns := evmUrns) (evmIlks := evmIlks)
        (I := I) (out := out) (outIlks := outIlks)
        (name := "dart") (value := .int (Int.ofNat dart.toNat)) (by decide)
        (barkLocalsLeftoverArt_get_preserved (evmUrns := evmUrns) (evmIlks := evmIlks)
          (I := I) (out := out) (outIlks := outIlks)
          (name := "dart") (value := .int (Int.ofNat dart.toNat)) (by decide)
          (by simpa [dart] using
            barkLocalsDart_get_dart evmUrns evmIlks I out outIlks))
  have hassign :
      assignStorageRef? config
        { contract := contract, locals := localsDue, immutables := immStore v } evmIlks .localVar
        (varRef "dart") (.int (Int.ofNat art.toNat)) =
      EvalResult.ok
        (({ contract := contract,
            locals := barkLocalsDustyDart evmUrns evmIlks I out outIlks, immutables := immStore v } : Frame),
          evmIlks) := by
    simpa [localsDue, art, barkLocalsDustyDart, varRef] using
      dogAssignLocalVarBaseOk (v := v) (evm := evmIlks)
        (locals := barkLocalsLeftoverDue evmUrns evmIlks I out outIlks)
        (name := "dart") (old := .int (Int.ofNat dart.toNat))
        (value := .int (Int.ofNat art.toNat)) hdartDueGet
  have hinner :
      ExecBlock config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        [ .ite
            (.binary .lt (.var "leftoverDue") (.var "dust"))
            [ .assign .localVar (varRef "dart") (.var "art") ]
            (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
              [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ]
        (.ok
          { contract := contract,
            locals := barkLocalsDustyDart evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    exact ExecBlock.consNormal
      (ExecStmt.iteTrue hinnerCond
        (ExecBlock.consNormal (ExecStmt.assign (hperm := Or.inl rfl) hartDue hassign) ExecBlock.nil))
      ExecBlock.nil
  have hthen :
      ExecBlock config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
          checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
          [ .ite
              (.binary .lt (.var "leftoverDue") (.var "dust"))
              [ .assign .localVar (varRef "dart") (.var "art") ]
              (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
        (.ok
          { contract := contract,
            locals := barkLocalsDustyDart evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append hprefix hinner
  exact ExecBlock.consNormal (ExecStmt.iteTrue houter hthen) ExecBlock.nil

theorem dogBarkPartialLeftoverIteOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hleftover :
      (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat <
        (barkVatUrnsArtWord out).toNat)
    (hfitLeftoverDue :
      (barkLeftoverArtWord (barkVatUrnsArtWord out)
        (barkSourceDartWord evmUrns evmIlks I out outIlks)).toNat *
        (barkVatIlksRateWord outIlks).toNat < UInt256.size)
    (hnotDusty :
      (barkVatIlksDustWord outIlks).toNat ≤
        (barkLeftoverDueWord (barkVatUrnsArtWord out)
          (barkSourceDartWord evmUrns evmIlks I out outIlks)
          (barkVatIlksRateWord outIlks)).toNat)
    (hfitPartialDue :
      (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat *
        (barkVatIlksRateWord outIlks).toNat < UInt256.size)
    (hpartialDueOk :
      (barkVatIlksDustWord outIlks).toNat ≤
        (barkPartialDueWord (barkSourceDartWord evmUrns evmIlks I out outIlks)
          (barkVatIlksRateWord outIlks)).toNat) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks
      [ .ite
          (.binary .gt (.var "art") (.var "dart"))
          (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
            checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
            [ .ite
                (.binary .lt (.var "leftoverDue") (.var "dust"))
                [ .assign .localVar (varRef "dart") (.var "art") ]
                (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                  [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
          [] ]
      (.ok
        { contract := contract,
          locals := barkLocalsPartialDue evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks) := by
  let locals0 := barkLocalsDart evmUrns evmIlks I out outIlks
  let localsDue := barkLocalsLeftoverDue evmUrns evmIlks I out outIlks
  let localsPartial := barkLocalsPartialDue evmUrns evmIlks I out outIlks
  let art := barkVatUrnsArtWord out
  let dart := barkSourceDartWord evmUrns evmIlks I out outIlks
  let rate := barkVatIlksRateWord outIlks
  let dust := barkVatIlksDustWord outIlks
  let leftoverDue := barkLeftoverDueWord art dart rate
  let partialDue := barkPartialDueWord dart rate
  have hart0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "art") = .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "art") (value := art)
        (barkLocalsDart_get_art evmUrns evmIlks I out outIlks)
  have hdart0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    simpa [locals0, dart] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "dart") (value := dart)
        (barkLocalsDart_get_dart evmUrns evmIlks I out outIlks)
  have houter :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.binary .gt (.var "art") (.var "dart")) = .ok (.bool true) := by
    apply evalExpr_bark_gt_int_true hart0 hdart0
    exact Int.ofNat_lt.mpr (by simpa [art, dart] using hleftover)
  have hprefix :=
    dogBarkLeftoverDuePrefixOk (v := v) evmUrns evmIlks I out outIlks
      hleftover hfitLeftoverDue
  have hleftoverDueExpr :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "leftoverDue") = .ok (.int (Int.ofNat leftoverDue.toNat)) := by
    simpa [localsDue, leftoverDue, art, dart, rate, barkLeftoverDueWord,
      barkLeftoverArtWord] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "leftoverDue") (value := leftoverDue)
        (barkLocalsLeftoverDue_get_leftoverDue evmUrns evmIlks I out outIlks)
  have hdustDue :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "dust") = .ok (.int (Int.ofNat dust.toNat)) := by
    simpa [localsDue, dust] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "dust") (value := dust)
        (barkLocalsLeftoverDue_get_preserved (by decide)
          (barkLocalsLeftoverArt_get_preserved (by decide)
            (barkLocalsDart_get_dust evmUrns evmIlks I out outIlks)))
  have hinnerCond :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.binary .lt (.var "leftoverDue") (.var "dust")) = .ok (.bool false) := by
    apply evalExpr_bark_lt_int_false hleftoverDueExpr hdustDue
    exact not_lt.mpr (Int.ofNat_le.mpr (by simpa [leftoverDue, art, dart, rate] using hnotDusty))
  have hdartDue :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    simpa [localsDue, dart] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "dart") (value := dart)
        (barkLocalsLeftoverDue_get_preserved (by decide)
          (barkLocalsLeftoverArt_get_preserved (by decide)
            (barkLocalsDart_get_dart evmUrns evmIlks I out outIlks)))
  have hrateDue :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "rate") = .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [localsDue, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "rate") (value := rate)
        (barkLocalsLeftoverDue_get_preserved (by decide)
          (barkLocalsLeftoverArt_get_preserved (by decide)
            (barkLocalsDart_get_rate evmUrns evmIlks I out outIlks)))
  have hdartPartial :
      evalExpr? config { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    simpa [localsPartial, dart] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsPartial)
        (name := "dart") (value := dart)
        (barkLocalsPartialDue_get_preserved (by decide)
          (barkLocalsLeftoverDue_get_preserved (by decide)
            (barkLocalsLeftoverArt_get_preserved (by decide)
              (barkLocalsDart_get_dart evmUrns evmIlks I out outIlks))))
  have hratePartial :
      evalExpr? config { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks
        (.var "rate") = .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [localsPartial, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsPartial)
        (name := "rate") (value := rate)
        (barkLocalsPartialDue_get_preserved (by decide)
          (barkLocalsLeftoverDue_get_preserved (by decide)
            (barkLocalsLeftoverArt_get_preserved (by decide)
              (barkLocalsDart_get_rate evmUrns evmIlks I out outIlks))))
  have hmulPartial :
      ExecBlock config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (checkedMulUintInto "partialDue" (.var "dart") (.var "rate"))
        (.ok { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks) := by
    simpa [localsDue, localsPartial, dart, rate, partialDue, barkPartialDueWord,
      barkLocalsPartialDue] using
      dogBarkCheckedMulOk (v := v) evmIlks (name := "partialDue")
        (x := .var "dart") (y := .var "rate") (a := dart) (b := rate)
        hdartDue hrateDue hdartPartial hratePartial
        (by simpa [dart, rate] using hfitPartialDue)
  have hpartialDueExpr :
      evalExpr? config { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks
        (.var "partialDue") = .ok (.int (Int.ofNat partialDue.toNat)) := by
    simpa [localsPartial, partialDue, dart, rate, barkPartialDueWord] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsPartial)
        (name := "partialDue") (value := partialDue)
        (barkLocalsPartialDue_get_partialDue evmUrns evmIlks I out outIlks)
  have hdustPartial :
      evalExpr? config { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks
        (.var "dust") = .ok (.int (Int.ofNat dust.toNat)) := by
    simpa [localsPartial, dust] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsPartial)
        (name := "dust") (value := dust)
        (barkLocalsPartialDue_get_preserved (by decide)
          (barkLocalsLeftoverDue_get_preserved (by decide)
            (barkLocalsLeftoverArt_get_preserved (by decide)
              (barkLocalsDart_get_dust evmUrns evmIlks I out outIlks))))
  have hreqExpr :
      evalExpr? config { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks
        (.binary .ge (.var "partialDue") (.var "dust")) = .ok (.bool true) := by
    apply evalExpr_bark_ge_int_true hpartialDueExpr hdustPartial
    exact Int.ofNat_le.mpr (by simpa [partialDue, dart, rate] using hpartialDueOk)
  have helse :
      ExecBlock config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
          [ .require (.binary .ge (.var "partialDue") (.var "dust")) ])
        (.ok { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks) := by
    exact execBlock_append hmulPartial
      (ExecBlock.consNormal (ExecStmt.requireTrue hreqExpr) ExecBlock.nil)
  have hinner :
      ExecBlock config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        [ .ite
            (.binary .lt (.var "leftoverDue") (.var "dust"))
            [ .assign .localVar (varRef "dart") (.var "art") ]
            (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
              [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ]
        (.ok { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hinnerCond helse) ExecBlock.nil
  have hthen :
      ExecBlock config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
          checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
          [ .ite
              (.binary .lt (.var "leftoverDue") (.var "dust"))
              [ .assign .localVar (varRef "dart") (.var "art") ]
              (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
        (.ok { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks) := by
    simpa [List.append_assoc] using execBlock_append hprefix hinner
  exact ExecBlock.consNormal (ExecStmt.iteTrue houter hthen) ExecBlock.nil

theorem dogBarkPartialLeftoverIteRevert {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hleftover :
      (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat <
        (barkVatUrnsArtWord out).toNat)
    (hfitLeftoverDue :
      (barkLeftoverArtWord (barkVatUrnsArtWord out)
        (barkSourceDartWord evmUrns evmIlks I out outIlks)).toNat *
        (barkVatIlksRateWord outIlks).toNat < UInt256.size)
    (hnotDusty :
      (barkVatIlksDustWord outIlks).toNat ≤
        (barkLeftoverDueWord (barkVatUrnsArtWord out)
          (barkSourceDartWord evmUrns evmIlks I out outIlks)
          (barkVatIlksRateWord outIlks)).toNat)
    (hfitPartialDue :
      (barkSourceDartWord evmUrns evmIlks I out outIlks).toNat *
        (barkVatIlksRateWord outIlks).toNat < UInt256.size)
    (hpartialDueBad :
      (barkPartialDueWord (barkSourceDartWord evmUrns evmIlks I out outIlks)
          (barkVatIlksRateWord outIlks)).toNat <
        (barkVatIlksDustWord outIlks).toNat) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks
      [ .ite
          (.binary .gt (.var "art") (.var "dart"))
          (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
            checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
            [ .ite
                (.binary .lt (.var "leftoverDue") (.var "dust"))
                [ .assign .localVar (varRef "dart") (.var "art") ]
                (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                  [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
          [] ]
      .reverted := by
  let locals0 := barkLocalsDart evmUrns evmIlks I out outIlks
  let localsDue := barkLocalsLeftoverDue evmUrns evmIlks I out outIlks
  let localsPartial := barkLocalsPartialDue evmUrns evmIlks I out outIlks
  let art := barkVatUrnsArtWord out
  let dart := barkSourceDartWord evmUrns evmIlks I out outIlks
  let rate := barkVatIlksRateWord outIlks
  let dust := barkVatIlksDustWord outIlks
  let leftoverDue := barkLeftoverDueWord art dart rate
  let partialDue := barkPartialDueWord dart rate
  have hart0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "art") = .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "art") (value := art)
        (barkLocalsDart_get_art evmUrns evmIlks I out outIlks)
  have hdart0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    simpa [locals0, dart] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "dart") (value := dart)
        (barkLocalsDart_get_dart evmUrns evmIlks I out outIlks)
  have houter :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.binary .gt (.var "art") (.var "dart")) = .ok (.bool true) := by
    apply evalExpr_bark_gt_int_true hart0 hdart0
    exact Int.ofNat_lt.mpr (by simpa [art, dart] using hleftover)
  have hprefix :=
    dogBarkLeftoverDuePrefixOk (v := v) evmUrns evmIlks I out outIlks
      hleftover hfitLeftoverDue
  have hleftoverDueExpr :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "leftoverDue") = .ok (.int (Int.ofNat leftoverDue.toNat)) := by
    simpa [localsDue, leftoverDue, art, dart, rate, barkLeftoverDueWord,
      barkLeftoverArtWord] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "leftoverDue") (value := leftoverDue)
        (barkLocalsLeftoverDue_get_leftoverDue evmUrns evmIlks I out outIlks)
  have hdustDue :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "dust") = .ok (.int (Int.ofNat dust.toNat)) := by
    simpa [localsDue, dust] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "dust") (value := dust)
        (barkLocalsLeftoverDue_get_preserved (by decide)
          (barkLocalsLeftoverArt_get_preserved (by decide)
            (barkLocalsDart_get_dust evmUrns evmIlks I out outIlks)))
  have hinnerCond :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.binary .lt (.var "leftoverDue") (.var "dust")) = .ok (.bool false) := by
    apply evalExpr_bark_lt_int_false hleftoverDueExpr hdustDue
    exact not_lt.mpr (Int.ofNat_le.mpr (by simpa [leftoverDue, art, dart, rate] using hnotDusty))
  have hdartDue :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    simpa [localsDue, dart] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "dart") (value := dart)
        (barkLocalsLeftoverDue_get_preserved (by decide)
          (barkLocalsLeftoverArt_get_preserved (by decide)
            (barkLocalsDart_get_dart evmUrns evmIlks I out outIlks)))
  have hrateDue :
      evalExpr? config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (.var "rate") = .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [localsDue, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDue)
        (name := "rate") (value := rate)
        (barkLocalsLeftoverDue_get_preserved (by decide)
          (barkLocalsLeftoverArt_get_preserved (by decide)
            (barkLocalsDart_get_rate evmUrns evmIlks I out outIlks)))
  have hdartPartial :
      evalExpr? config { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    simpa [localsPartial, dart] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsPartial)
        (name := "dart") (value := dart)
        (barkLocalsPartialDue_get_preserved (by decide)
          (barkLocalsLeftoverDue_get_preserved (by decide)
            (barkLocalsLeftoverArt_get_preserved (by decide)
              (barkLocalsDart_get_dart evmUrns evmIlks I out outIlks))))
  have hratePartial :
      evalExpr? config { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks
        (.var "rate") = .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [localsPartial, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsPartial)
        (name := "rate") (value := rate)
        (barkLocalsPartialDue_get_preserved (by decide)
          (barkLocalsLeftoverDue_get_preserved (by decide)
            (barkLocalsLeftoverArt_get_preserved (by decide)
              (barkLocalsDart_get_rate evmUrns evmIlks I out outIlks))))
  have hmulPartial :
      ExecBlock config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (checkedMulUintInto "partialDue" (.var "dart") (.var "rate"))
        (.ok { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks) := by
    simpa [localsDue, localsPartial, dart, rate, partialDue, barkPartialDueWord,
      barkLocalsPartialDue] using
      dogBarkCheckedMulOk (v := v) evmIlks (name := "partialDue")
        (x := .var "dart") (y := .var "rate") (a := dart) (b := rate)
        hdartDue hrateDue hdartPartial hratePartial
        (by simpa [dart, rate] using hfitPartialDue)
  have hpartialDueExpr :
      evalExpr? config { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks
        (.var "partialDue") = .ok (.int (Int.ofNat partialDue.toNat)) := by
    simpa [localsPartial, partialDue, dart, rate, barkPartialDueWord] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsPartial)
        (name := "partialDue") (value := partialDue)
        (barkLocalsPartialDue_get_partialDue evmUrns evmIlks I out outIlks)
  have hdustPartial :
      evalExpr? config { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks
        (.var "dust") = .ok (.int (Int.ofNat dust.toNat)) := by
    simpa [localsPartial, dust] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsPartial)
        (name := "dust") (value := dust)
        (barkLocalsPartialDue_get_preserved (by decide)
          (barkLocalsLeftoverDue_get_preserved (by decide)
            (barkLocalsLeftoverArt_get_preserved (by decide)
              (barkLocalsDart_get_dust evmUrns evmIlks I out outIlks))))
  have hreqExpr :
      evalExpr? config { contract := contract, locals := localsPartial, immutables := immStore v } evmIlks
        (.binary .ge (.var "partialDue") (.var "dust")) = .ok (.bool false) := by
    apply evalExpr_bark_ge_int_false hpartialDueExpr hdustPartial
    exact not_le.mpr (Int.ofNat_lt.mpr (by simpa [partialDue, dart, rate, dust] using hpartialDueBad))
  have helse :
      ExecBlock config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
          [ .require (.binary .ge (.var "partialDue") (.var "dust")) ])
        .reverted :=
    execBlock_append hmulPartial (ExecBlock.consRevert (ExecStmt.requireFalse hreqExpr))
  have hinner :
      ExecBlock config { contract := contract, locals := localsDue, immutables := immStore v } evmIlks
        [ .ite
            (.binary .lt (.var "leftoverDue") (.var "dust"))
            [ .assign .localVar (varRef "dart") (.var "art") ]
            (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
              [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ]
        .reverted :=
    ExecBlock.consRevert (ExecStmt.iteFalse hinnerCond helse)
  have hthen :
      ExecBlock config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
          checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
          [ .ite
              (.binary .lt (.var "leftoverDue") (.var "dust"))
              [ .assign .localVar (varRef "dart") (.var "art") ]
              (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
        .reverted := by
    simpa [List.append_assoc] using
      execBlock_append hprefix hinner
  exact ExecBlock.consRevert (ExecStmt.iteTrue houter hthen)

theorem dogBarkDinkLetOk {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {inkDart art : UInt256}
    (hart : locals.get? "art" = some (.int (Int.ofNat art.toNat)))
    (hartNe : art ≠ ⟨0⟩) :
    ExecBlock config
      { contract := contract, locals := barkLocalsInkDart locals inkDart, immutables := immStore v } evm
      [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")) ]
      (.ok
        { contract := contract,
          locals := barkLocalsDink (barkLocalsInkDart locals inkDart)
            (UInt256.div inkDart art), immutables := immStore v }
        evm) := by
  let locals0 := barkLocalsInkDart locals inkDart
  let dink := UInt256.div inkDart art
  have hinkDart :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm
        (.var "inkDart") = .ok (.int (Int.ofNat inkDart.toNat)) := by
    simpa [locals0] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "inkDart") (value := inkDart)
        (barkLocalsInkDart_get_inkDart locals inkDart)
  have hart0 :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm
        (.var "art") = .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "art") (value := art)
        (barkLocalsInkDart_get_preserved (by decide) hart)
  have hdiv :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evm
        (.binary .div (.var "inkDart") (.var "art")) =
          .ok (.int (Int.ofNat dink.toNat)) := by
    exact evalExpr_bark_div_uint256_ok hinkDart hart0 hartNe (by simp [dink])
  have hlet :
      ExecStmt config { contract := contract, locals := locals0, immutables := immStore v } evm
        (.letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")))
        (.ok { contract := contract, locals := barkLocalsDink locals0 dink, immutables := immStore v } evm) := by
    simpa [locals0, dink, barkLocalsDink] using
      (ExecStmt.letDecl
        (cfg := config) (stele := { contract := contract, locals := locals0, immutables := immStore v })
        (evm := evm) (name := "dink") (ty := some uint256)
        (expr := .binary .div (.var "inkDart") (.var "art"))
        (value := .int (Int.ofNat dink.toNat)) hdiv)
  exact ExecBlock.consNormal hlet ExecBlock.nil

theorem dogBarkDinkGuardOkSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {dink : UInt256}
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hdinkPos : 0 < dink.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      [ .require (.binary .gt (.var "dink") (.intLit 0)) ]
      (.ok { contract := contract, locals := locals, immutables := immStore v } evm) := by
  have hdinkExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "dink") = .ok (.int (Int.ofNat dink.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dink") (value := dink) hdink
  have hzero :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.var "dink") (.intLit 0)) = .ok (.bool true) := by
    apply evalExpr_bark_gt_int_true hdinkExpr hzero
    exact Int.ofNat_lt.mpr hdinkPos
  exact ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil

theorem dogBarkDinkGuardRevertSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {dink : UInt256}
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hdinkNotPos : ¬ 0 < dink.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      [ .require (.binary .gt (.var "dink") (.intLit 0)) ] .reverted := by
  have hdinkExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "dink") = .ok (.int (Int.ofNat dink.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dink") (value := dink) hdink
  have hzero :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .gt (.var "dink") (.intLit 0)) = .ok (.bool false) := by
    apply evalExpr_bark_gt_int_false hdinkExpr hzero
    exact not_lt.mpr (Int.ofNat_le.mpr (Nat.eq_zero_of_not_pos hdinkNotPos ▸ Nat.zero_le _))
  exact ExecBlock.consRevert (ExecStmt.requireFalse hreq)

theorem dogBarkInt256GuardOkSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {dart dink : UInt256}
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat)
    (hdinkBound : dink.toNat ≤ dogInt256LimitWord.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      [ .require
          (.binary .and
            (.binary .le (.var "dart") (.intLit int256Limit))
            (.binary .le (.var "dink") (.intLit int256Limit))) ]
      (.ok { contract := contract, locals := locals, immutables := immStore v } evm) := by
  have hdartExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dart") (value := dart) hdart
  have hdinkExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "dink") = .ok (.int (Int.ofNat dink.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dink") (value := dink) hdink
  have hlimit :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.intLit int256Limit) = .ok (.int (Int.ofNat dogInt256LimitWord.toNat)) := by
    have hnat : Int.ofNat dogInt256LimitWord.toNat = int256Limit := by
      native_decide
    simpa [evalExpr?, pure, hnat]
  have hdartLe :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .le (.var "dart") (.intLit int256Limit)) = .ok (.bool true) := by
    apply evalExpr_bark_le_int_true hdartExpr hlimit
    exact Int.ofNat_le.mpr hdartBound
  have hdinkLe :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .le (.var "dink") (.intLit int256Limit)) = .ok (.bool true) := by
    apply evalExpr_bark_le_int_true hdinkExpr hlimit
    exact Int.ofNat_le.mpr hdinkBound
  have hreq :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .and
          (.binary .le (.var "dart") (.intLit int256Limit))
          (.binary .le (.var "dink") (.intLit int256Limit)) ) = .ok (.bool true) := by
    simpa using evalExpr_bark_and_true_right hdartLe hdinkLe
  exact ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil

theorem dogBarkInt256GuardDartOverflowSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {dart dink : UInt256}
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hdartOverflow : dogInt256LimitWord.toNat < dart.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      [ .require
          (.binary .and
            (.binary .le (.var "dart") (.intLit int256Limit))
            (.binary .le (.var "dink") (.intLit int256Limit))) ]
      .reverted := by
  have hdartExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dart") (value := dart) hdart
  have hlimit :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.intLit int256Limit) = .ok (.int (Int.ofNat dogInt256LimitWord.toNat)) := by
    have hnat : Int.ofNat dogInt256LimitWord.toNat = int256Limit := by
      native_decide
    simpa [evalExpr?, pure, hnat]
  have hdartLe :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .le (.var "dart") (.intLit int256Limit)) = .ok (.bool false) := by
    apply evalExpr_bark_le_int_false hdartExpr hlimit
    exact not_le.mpr (Int.ofNat_lt.mpr hdartOverflow)
  have hreq :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .and
          (.binary .le (.var "dart") (.intLit int256Limit))
          (.binary .le (.var "dink") (.intLit int256Limit)) ) = .ok (.bool false) :=
    evalExpr_bark_and_false_left hdartLe
  exact ExecBlock.consRevert (ExecStmt.requireFalse hreq)

theorem dogBarkInt256GuardDinkOverflowSource {v : DogImmutables} (evm : EVM.State)
    {locals : Store} {dart dink : UInt256}
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hdink : locals.get? "dink" = some (.int (Int.ofNat dink.toNat)))
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat)
    (hdinkOverflow : dogInt256LimitWord.toNat < dink.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      [ .require
          (.binary .and
            (.binary .le (.var "dart") (.intLit int256Limit))
            (.binary .le (.var "dink") (.intLit int256Limit))) ]
      .reverted := by
  have hdartExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "dart") = .ok (.int (Int.ofNat dart.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dart") (value := dart) hdart
  have hdinkExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.var "dink") = .ok (.int (Int.ofNat dink.toNat)) := by
    exact evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
      (name := "dink") (value := dink) hdink
  have hlimit :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.intLit int256Limit) = .ok (.int (Int.ofNat dogInt256LimitWord.toNat)) := by
    have hnat : Int.ofNat dogInt256LimitWord.toNat = int256Limit := by
      native_decide
    simpa [evalExpr?, pure, hnat]
  have hdartLe :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .le (.var "dart") (.intLit int256Limit)) = .ok (.bool true) := by
    apply evalExpr_bark_le_int_true hdartExpr hlimit
    exact Int.ofNat_le.mpr hdartBound
  have hdinkLe :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .le (.var "dink") (.intLit int256Limit)) = .ok (.bool false) := by
    apply evalExpr_bark_le_int_false hdinkExpr hlimit
    exact not_le.mpr (Int.ofNat_lt.mpr hdinkOverflow)
  have hreq :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
        (.binary .and
          (.binary .le (.var "dart") (.intLit int256Limit))
          (.binary .le (.var "dink") (.intLit int256Limit)) ) = .ok (.bool false) :=
    evalExpr_bark_and_true_right hdartLe hdinkLe
  exact ExecBlock.consRevert (ExecStmt.requireFalse hreq)

theorem dogBarkDartCandidateDivZero {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hchopZero :
      solcSlotWordAt (barkIlksChopSlotFor I) evmUrns.accountMap evmUrns.executionEnv = ⟨0⟩) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDartByRate evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks
      [ .letDecl "dartCandidate" (some uint256)
          (.binary .div (.var "dartByRate") (.var "milkChop")) ]
      .reverted := by
  let locals0 := barkLocalsDartByRate evmUrns evmIlks I out outIlks
  let dartByRate := barkSourceDartByRateWord evmUrns evmIlks I outIlks
  let chop := solcSlotWordAt (barkIlksChopSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  have hdartByRate :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "dartByRate") = .ok (.int (Int.ofNat dartByRate.toNat)) := by
    simpa [locals0, dartByRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "dartByRate") (value := dartByRate)
        (barkLocalsDartByRate_get_dartByRate evmUrns evmIlks I out outIlks)
  have hchop :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.var "milkChop") = .ok (.int (Int.ofNat chop.toNat)) := by
    simpa [locals0, chop] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "milkChop") (value := chop)
        (barkLocalsDartByRate_get_milkChop evmUrns evmIlks I out outIlks)
  have hdiv :
      evalExpr? config { contract := contract, locals := locals0, immutables := immStore v } evmIlks
        (.binary .div (.var "dartByRate") (.var "milkChop")) = .revert :=
    evalExpr_bark_div_uint256_revert hdartByRate hchop (by simpa [chop] using hchopZero)
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hdiv)

theorem dogBarkVatIlksRoomWadOverflowSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM config evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : config.externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hfitInk :
      (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat <
        UInt256.size)
    (hfitArt :
      (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat <
        UInt256.size)
    (hspotPos : 0 < (barkVatIlksSpotWord outIlks).toNat)
    (hsafeLt :
      (barkInkSpotWord out outIlks).toNat <
        (barkArtRateUnsafeWord out outIlks).toNat)
    (hlimit :
      (solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv).toNat <
          (solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv).toNat ∧
        (solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat <
          (solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat)
    (hoverRoom :
      UInt256.size ≤ (barkSourceRoomWord evmUrns evmIlks I).toNat * dogWadWord.toNat)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15)
        (.ok { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [locals, evm0] using
      dogBarkVatIlksSuccessDustPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmUrns := evmUrns) (evmIlks := evmIlks) (out := out)
        (outIlks := outIlks) hwv hlive hcodePos hcallUrns hdecUrns hcodePosIlks
        hcallIlks hdecIlks hsz100
  have hInkBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
        (.ok { contract := contract, locals := barkLocalsInkSpot evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    dogBarkInkSpotCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitInk
  have hArtBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsInkSpot evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks, immutables := immStore v }
          evmIlks) :=
    dogBarkArtRateUnsafeCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitArt
  let unsafeGuard : Expr :=
    .binary .and
      (.binary .gt (.var "spot") (.intLit 0))
      (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))
  let limitGuard : Expr :=
    .binary .and
      (.binary .gt (.storage HoleRef) (.storage DirtRef))
      (.binary .gt (.var "milkHole") (.var "milkDirt"))
  let locals2 := barkLocalsArtRateUnsafe evmUrns I out outIlks
  let spot := barkVatIlksSpotWord outIlks
  let inkSpot := barkInkSpotWord out outIlks
  let artRate := barkArtRateUnsafeWord out outIlks
  let hole := solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv
  let dirt := solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv
  let milkHole :=
    solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  let milkDirt :=
    solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  have hspot :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "spot") = .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals2, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsArtRateUnsafe_get_spot evmUrns I out outIlks)
  have hzero :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hinkSpot :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "inkSpot") = .ok (.int (Int.ofNat inkSpot.toNat)) := by
    simpa [locals2, inkSpot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "inkSpot") (value := barkInkSpotWord out outIlks)
        (barkLocalsArtRateUnsafe_get_inkSpot evmUrns I out outIlks)
  have hartRate :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "artRateUnsafe") = .ok (.int (Int.ofNat artRate.toNat)) := by
    simpa [locals2, artRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "artRateUnsafe") (value := barkArtRateUnsafeWord out outIlks)
        (barkLocalsArtRateUnsafe_get_artRateUnsafe evmUrns I out outIlks)
  have hunsafeReq :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        unsafeGuard = .ok (.bool true) := by
    have hgt :
        evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
          (.binary .gt (.var "spot") (.intLit 0)) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hspot hzero
      exact Int.ofNat_lt.mpr (by simpa [spot] using hspotPos)
    have hlt :
        evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
          (.binary .lt (.var "inkSpot") (.var "artRateUnsafe")) = .ok (.bool true) := by
      apply evalExpr_bark_lt_int_true hinkSpot hartRate
      exact Int.ofNat_lt.mpr (by simpa [inkSpot, artRate] using hsafeLt)
    simpa [unsafeGuard] using evalExpr_bark_and_true_right hgt hlt
  have hHoleExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.storage HoleRef) = .ok (.int (Int.ofNat hole.toNat)) := by
    simpa [locals2, hole] using
      evalExpr_barkStorageHole (v := v) (evm := evmIlks) (locals := locals2)
        (barkLocalsArtRateUnsafe_get_Hole evmUrns I out outIlks)
  have hDirtExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt.toNat)) := by
    simpa [locals2, dirt] using
      evalExpr_barkStorageDirt (v := v) (evm := evmIlks) (locals := locals2)
        (barkLocalsArtRateUnsafe_get_Dirt evmUrns I out outIlks)
  have hmilkHoleExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "milkHole") = .ok (.int (Int.ofNat milkHole.toNat)) := by
    simpa [locals2, milkHole] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "milkHole") (value := milkHole)
        (barkLocalsArtRateUnsafe_get_milkHole evmUrns I out outIlks)
  have hmilkDirtExpr :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        (.var "milkDirt") = .ok (.int (Int.ofNat milkDirt.toNat)) := by
    simpa [locals2, milkDirt] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "milkDirt") (value := milkDirt)
        (barkLocalsArtRateUnsafe_get_milkDirt evmUrns I out outIlks)
  have hlimitReq :
      evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        limitGuard = .ok (.bool true) := by
    have hgtGlobal :
        evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
          (.binary .gt (.storage HoleRef) (.storage DirtRef)) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hHoleExpr hDirtExpr
      exact Int.ofNat_lt.mpr (by simpa [dirt, hole] using hlimit.1)
    have hgtMilk :
        evalExpr? config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
          (.binary .gt (.var "milkHole") (.var "milkDirt")) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hmilkHoleExpr hmilkDirtExpr
      exact Int.ofNat_lt.mpr (by simpa [milkDirt, milkHole] using hlimit.2)
    simpa [limitGuard] using evalExpr_bark_and_true_right hgtGlobal hgtMilk
  have hchecked :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    by simpa [locals2] using execBlock_append hInkBlock hArtBlock
  have hunsafeBlock :
      ExecBlock config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        [.require unsafeGuard]
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hunsafeReq) ExecBlock.nil
  have hlimitBlock :
      ExecBlock config { contract := contract, locals := locals2, immutables := immStore v } evmIlks
        [.require limitGuard]
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hlimitReq) ExecBlock.nil
  have hcheckedUnsafe :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        ((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard])
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    execBlock_append hchecked (by simpa [locals2] using hunsafeBlock)
  have hcheckedUnsafeLimit :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard]) ++ [.require limitGuard])
        (.ok { contract := contract, locals := locals2, immutables := immStore v } evmIlks) :=
    execBlock_append hcheckedUnsafe (by simpa [locals2] using hlimitBlock)
  have hglobalBlock :=
    dogBarkGlobalRoomCheckedSubOk (v := v) evmUrns evmIlks I out outIlks hlimit.1
  have htoGlobal :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef))
        (.ok { contract := contract, locals := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append hcheckedUnsafeLimit hglobalBlock
  have hilkBlock :=
    dogBarkIlkRoomCheckedSubOk (v := v) evmUrns evmIlks I out outIlks hlimit.2
  have htoIlk :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt"))
        (.ok { contract := contract, locals := barkLocalsIlkRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append htoGlobal hilkBlock
  have hminStmt :=
    dogBarkRoomMinCallOk (v := v) evmUrns evmIlks I out outIlks
  have hminBlock :
      ExecBlock config
        { contract := contract, locals := barkLocalsIlkRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks
        [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"]
        (.ok { contract := contract, locals := barkLocalsRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) :=
    ExecBlock.consNormal hminStmt ExecBlock.nil
  have htoRoom :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"])
        (.ok { contract := contract, locals := barkLocalsRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append htoIlk hminBlock
  have hroomWadBlock :=
    dogBarkRoomWadCheckedMulOverflow (v := v) evmUrns evmIlks I out outIlks hoverRoom
  have htoRoomWad :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD))
        .reverted := by
    simpa [List.append_assoc] using execBlock_append htoRoom hroomWadBlock
  let afterRoomWad : List Stmt :=
    [ .letDecl "dartByRate" (some uint256)
        (.binary .div (.var "roomWad") (.var "rate")),
      .letDecl "dartCandidate" (some uint256)
        (.binary .div (.var "dartByRate") (.var "milkChop")),
      .internalCall "min" [.var "art", .var "dartCandidate"] "dart",
      .ite
        (.binary .gt (.var "art") (.var "dart"))
        (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
          checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
          [ .ite
              (.binary .lt (.var "leftoverDue") (.var "dust"))
              [ .assign .localVar (varRef "dart") (.var "art") ]
              (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
        [] ] ++
    checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
    [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
      .require (.binary .gt (.var "dink") (.intLit 0)),
      .require
        (.binary .and
          (.binary .le (.var "dart") (.intLit int256Limit))
          (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
    checkedExternalCallStmts vatExpr "grab" (.intLit 0)
      [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
        asInt256 (.unary .neg (asInt256 (.var "dink"))),
        asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet" ++
    checkedMulUintInto "due" (.var "dart") (.var "rate") ++
    checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet" ++
    checkedMulUintInto "tabBase" (.var "due") (.var "milkChop") ++
    [ .letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
    checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab") ++
    [ .assign .storage DirtRef (.var "DirtNew") ] ++
    checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab") ++
    [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] ++
    checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
      [.var "tab", .var "dink", .var "urn", .var "kpr"] "id" ++
    [ .return [.var "id"] ]
  have htail :
      ExecBlock config
        { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++ afterRoomWad)
        .reverted := by
    simpa [List.append_assoc] using
      execBlock_append_term (s2 := afterRoomWad) htoRoomWad (by intro f e h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    have hcombined := execBlock_append hprefix htail
    simpa [unsafeGuard, limitGuard, afterRoomWad, barkTransition, barkBodyRest, nonpayable,
      checkedExternalCallStmts, checkedMulUintInto, checkedSubUintInto, List.append_assoc]
      using hcombined
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksMilkChopZeroSourceBody {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM config evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : config.externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hfitInk :
      (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat <
        UInt256.size)
    (hfitArt :
      (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat <
        UInt256.size)
    (hspotPos : 0 < (barkVatIlksSpotWord outIlks).toNat)
    (hsafeLt :
      (barkInkSpotWord out outIlks).toNat <
        (barkArtRateUnsafeWord out outIlks).toNat)
    (hlimit :
      (solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv).toNat <
          (solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv).toNat ∧
        (solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat <
          (solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat)
    (hfitRoom :
      (barkSourceRoomWord evmUrns evmIlks I).toNat * dogWadWord.toNat < UInt256.size)
    (hrateNe : barkVatIlksRateWord outIlks ≠ ⟨0⟩)
    (hchopZero :
      solcSlotWordAt (barkIlksChopSlotFor I) evmUrns.accountMap evmUrns.executionEnv = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals barkTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15)
        (.ok { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [locals, evm0] using
      dogBarkVatIlksSuccessDustPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmUrns := evmUrns) (evmIlks := evmIlks) (out := out)
        (outIlks := outIlks) hwv hlive hcodePos hcallUrns hdecUrns hcodePosIlks
        hcallIlks hdecIlks hsz100
  have htoRoom :=
    dogBarkVatIlksDustToRoomOk (v := v) evmUrns evmIlks I out outIlks
      hfitInk hfitArt hspotPos hsafeLt hlimit
  have hroomPrefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15 ++
          checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [ .require
              (.binary .and
                (.binary .gt (.var "spot") (.intLit 0))
                (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
          [ .require
              (.binary .and
                (.binary .gt (.storage HoleRef) (.storage DirtRef))
                (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"])
        (.ok { contract := contract, locals := barkLocalsRoom evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append hprefix htoRoom
  have hroomWadBlock :=
    dogBarkRoomWadCheckedMulOk (v := v) evmUrns evmIlks I out outIlks hfitRoom
  have htoRoomWad :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15 ++
          checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [ .require
              (.binary .and
                (.binary .gt (.var "spot") (.intLit 0))
                (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
          [ .require
              (.binary .and
                (.binary .gt (.storage HoleRef) (.storage DirtRef))
                (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD))
        (.ok { contract := contract, locals := barkLocalsRoomWad evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append hroomPrefix hroomWadBlock
  have hdartByRateBlock :=
    dogBarkDartByRateLetOk (v := v) evmUrns evmIlks I out outIlks hrateNe
  have htoDartByRate :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15 ++
          checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [ .require
              (.binary .and
                (.binary .gt (.var "spot") (.intLit 0))
                (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
          [ .require
              (.binary .and
                (.binary .gt (.storage HoleRef) (.storage DirtRef))
                (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
          [ .letDecl "dartByRate" (some uint256)
              (.binary .div (.var "roomWad") (.var "rate")) ])
        (.ok
          { contract := contract, locals := barkLocalsDartByRate evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append htoRoomWad hdartByRateBlock
  have hdartCandidateBlock :=
    dogBarkDartCandidateDivZero (v := v) evmUrns evmIlks I out outIlks hchopZero
  have htoDartCandidate :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15 ++
          checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [ .require
              (.binary .and
                (.binary .gt (.var "spot") (.intLit 0))
                (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
          [ .require
              (.binary .and
                (.binary .gt (.storage HoleRef) (.storage DirtRef))
                (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
          [ .letDecl "dartByRate" (some uint256)
              (.binary .div (.var "roomWad") (.var "rate")) ] ++
          [ .letDecl "dartCandidate" (some uint256)
              (.binary .div (.var "dartByRate") (.var "milkChop")) ])
        .reverted := by
    simpa [List.append_assoc] using execBlock_append htoDartByRate hdartCandidateBlock
  let afterDartCandidate : List Stmt :=
    [ .internalCall "min" [.var "art", .var "dartCandidate"] "dart",
      .ite
        (.binary .gt (.var "art") (.var "dart"))
        (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
          checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
          [ .ite
              (.binary .lt (.var "leftoverDue") (.var "dust"))
              [ .assign .localVar (varRef "dart") (.var "art") ]
              (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
        [] ] ++
    checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
    [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
      .require (.binary .gt (.var "dink") (.intLit 0)),
      .require
        (.binary .and
          (.binary .le (.var "dart") (.intLit int256Limit))
          (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
    checkedExternalCallStmts vatExpr "grab" (.intLit 0)
      [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
        asInt256 (.unary .neg (asInt256 (.var "dink"))),
        asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet" ++
    checkedMulUintInto "due" (.var "dart") (.var "rate") ++
    checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet" ++
    checkedMulUintInto "tabBase" (.var "due") (.var "milkChop") ++
    [ .letDecl "tab" (some uint256) (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
    checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab") ++
    [ .assign .storage DirtRef (.var "DirtNew") ] ++
    checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab") ++
    [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] ++
    checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
      [.var "tab", .var "dink", .var "urn", .var "kpr"] "id" ++
    [ .return [.var "id"] ]
  have htail :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15 ++
          checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [ .require
              (.binary .and
                (.binary .gt (.var "spot") (.intLit 0))
                (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
          [ .require
              (.binary .and
                (.binary .gt (.storage HoleRef) (.storage DirtRef))
                (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
          [ .letDecl "dartByRate" (some uint256)
              (.binary .div (.var "roomWad") (.var "rate")) ] ++
          [ .letDecl "dartCandidate" (some uint256)
              (.binary .div (.var "dartByRate") (.var "milkChop")) ] ++
          afterDartCandidate)
        .reverted := by
    simpa [List.append_assoc] using
      execBlock_append_term (s2 := afterDartCandidate) htoDartCandidate
        (by intro f e h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        barkTransition.body .reverted := by
    simpa [afterDartCandidate, barkTransition, barkBodyRest, nonpayable,
      checkedExternalCallStmts, checkedMulUintInto, checkedSubUintInto, List.append_assoc]
      using htail
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksDartTailSourceBlock {v : DogImmutables}
    {σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    {result : ExecResult}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : solcSlotWordAt ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM config evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : config.externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hfitInk :
      (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat <
        UInt256.size)
    (hfitArt :
      (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat <
        UInt256.size)
    (hspotPos : 0 < (barkVatIlksSpotWord outIlks).toNat)
    (hsafeLt :
      (barkInkSpotWord out outIlks).toNat <
        (barkArtRateUnsafeWord out outIlks).toNat)
    (hlimit :
      (solcSlotWordAt ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv).toNat <
          (solcSlotWordAt ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv).toNat ∧
        (solcSlotWordAt (barkIlksDirtSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat <
          (solcSlotWordAt (barkIlksHoleSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat)
    (hfitRoom :
      (barkSourceRoomWord evmUrns evmIlks I).toNat * dogWadWord.toNat < UInt256.size)
    (hrateNe : barkVatIlksRateWord outIlks ≠ ⟨0⟩)
    (hchopNe : barkSourceMilkChopWord evmUrns I ≠ ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (htail :
      ExecBlock config
        { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks
        ([ .ite
            (.binary .gt (.var "art") (.var "dart"))
            (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
              checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
              [ .ite
                  (.binary .lt (.var "leftoverDue") (.var "dust"))
                  [ .assign .localVar (varRef "dart") (.var "art") ]
                  (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                    [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
            [] ] ++
          checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
          [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
            .require (.binary .gt (.var "dink") (.intLit 0)),
            .require
              (.binary .and
                (.binary .le (.var "dart") (.intLit int256Limit))
                (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
          checkedExternalCallStmts vatExpr "grab" (.intLit 0)
            [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
              asInt256 (.unary .neg (asInt256 (.var "dink"))),
              asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet" ++
          checkedMulUintInto "due" (.var "dart") (.var "rate") ++
          checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet" ++
          checkedMulUintInto "tabBase" (.var "due") (.var "milkChop") ++
          [ .letDecl "tab" (some uint256)
              (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
          checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab") ++
          [ .assign .storage DirtRef (.var "DirtNew") ] ++
          checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab") ++
          [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] ++
          checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
            [.var "tab", .var "dink", .var "urn", .var "kpr"] "id" ++
          [ .return [.var "id"] ])
        result) :
    let locals := barkLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
      barkTransition.body result := by
  intro locals evm0
  have hprefix :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15)
        (.ok { contract := contract, locals := barkLocalsDust evmUrns I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [locals, evm0] using
      dogBarkVatIlksSuccessDustPrefix (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmUrns := evmUrns) (evmIlks := evmIlks) (out := out)
        (outIlks := outIlks) hwv hlive hcodePos hcallUrns hdecUrns hcodePosIlks
        hcallIlks hdecIlks hsz100
  have htoDart :=
    dogBarkVatIlksDustToDartOk (v := v) evmUrns evmIlks I out outIlks
      hfitInk hfitArt hspotPos hsafeLt hlimit hfitRoom hrateNe hchopNe
  have htoTail :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        (barkTransition.body.take 15 ++
          checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [ .require
              (.binary .and
                (.binary .gt (.var "spot") (.intLit 0))
                (.binary .lt (.var "inkSpot") (.var "artRateUnsafe"))) ] ++
          [ .require
              (.binary .and
                (.binary .gt (.storage HoleRef) (.storage DirtRef))
                (.binary .gt (.var "milkHole") (.var "milkDirt"))) ] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"] ++
          checkedMulUintInto "roomWad" (.var "room") (.intLit WAD) ++
          [ .letDecl "dartByRate" (some uint256)
              (.binary .div (.var "roomWad") (.var "rate")) ] ++
          [ .letDecl "dartCandidate" (some uint256)
              (.binary .div (.var "dartByRate") (.var "milkChop")) ] ++
          [.internalCall "min" [.var "art", .var "dartCandidate"] "dart"])
        (.ok { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append hprefix htoDart
  have hcombined := execBlock_append htoTail htail
  simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts,
    checkedMulUintInto, checkedSubUintInto, List.append_assoc] using hcombined

theorem dogBarkDartTailFromLeftoverBlock {v : DogImmutables}
    {evmUrns evmIlks : EVM.State} {I : ExecutionEnv} {out outIlks : ByteArray}
    {localsAfter : Store} {result : ExecResult}
    (hleftover :
      ExecBlock config
        { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
        evmIlks
        [ .ite
            (.binary .gt (.var "art") (.var "dart"))
            (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
              checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
              [ .ite
                  (.binary .lt (.var "leftoverDue") (.var "dust"))
                  [ .assign .localVar (varRef "dart") (.var "art") ]
                  (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                    [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
            [] ]
        (.ok { contract := contract, locals := localsAfter, immutables := immStore v } evmIlks))
    (htail :
      ExecBlock config { contract := contract, locals := localsAfter, immutables := immStore v } evmIlks
        (checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
          [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
            .require (.binary .gt (.var "dink") (.intLit 0)),
            .require
              (.binary .and
                (.binary .le (.var "dart") (.intLit int256Limit))
                (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
          checkedExternalCallStmts vatExpr "grab" (.intLit 0)
            [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
              asInt256 (.unary .neg (asInt256 (.var "dink"))),
              asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet" ++
          checkedMulUintInto "due" (.var "dart") (.var "rate") ++
          checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet" ++
          checkedMulUintInto "tabBase" (.var "due") (.var "milkChop") ++
          [ .letDecl "tab" (some uint256)
              (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
          checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab") ++
          [ .assign .storage DirtRef (.var "DirtNew") ] ++
          checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab") ++
          [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] ++
          checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
            [.var "tab", .var "dink", .var "urn", .var "kpr"] "id" ++
          [ .return [.var "id"] ])
        result) :
    ExecBlock config
      { contract := contract, locals := barkLocalsDart evmUrns evmIlks I out outIlks, immutables := immStore v }
      evmIlks
      ([ .ite
          (.binary .gt (.var "art") (.var "dart"))
          (checkedSubUintInto "leftoverArt" (.var "art") (.var "dart") ++
            checkedMulUintInto "leftoverDue" (.var "leftoverArt") (.var "rate") ++
            [ .ite
                (.binary .lt (.var "leftoverDue") (.var "dust"))
                [ .assign .localVar (varRef "dart") (.var "art") ]
                (checkedMulUintInto "partialDue" (.var "dart") (.var "rate") ++
                  [ .require (.binary .ge (.var "partialDue") (.var "dust")) ]) ])
          [] ] ++
        checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
        [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
          .require (.binary .gt (.var "dink") (.intLit 0)),
          .require
            (.binary .and
              (.binary .le (.var "dart") (.intLit int256Limit))
              (.binary .le (.var "dink") (.intLit int256Limit))) ] ++
        checkedExternalCallStmts vatExpr "grab" (.intLit 0)
          [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
            asInt256 (.unary .neg (asInt256 (.var "dink"))),
            asInt256 (.unary .neg (asInt256 (.var "dart"))) ] "_grabRet" ++
        checkedMulUintInto "due" (.var "dart") (.var "rate") ++
        checkedExternalCallStmts vowAddr "fess" (.intLit 0) [.var "due"] "_fessRet" ++
        checkedMulUintInto "tabBase" (.var "due") (.var "milkChop") ++
        [ .letDecl "tab" (some uint256)
            (.binary .div (.var "tabBase") (.intLit WAD)) ] ++
        checkedAddUintInto "DirtNew" (.storage DirtRef) (.var "tab") ++
        [ .assign .storage DirtRef (.var "DirtNew") ] ++
        checkedAddUintInto "ilkDirtNew" (.var "milkDirt") (.var "tab") ++
        [ .assign .storage (ilksF (.var "ilk") "dirt") (.var "ilkDirtNew") ] ++
        checkedExternalCallStmts (.var "milkClip") "kick" (.intLit 0)
          [.var "tab", .var "dink", .var "urn", .var "kpr"] "id" ++
        [ .return [.var "id"] ])
      result := by
  simpa [List.append_assoc] using execBlock_append hleftover htail

theorem dogBarkPostLeftoverIntGuardOkSource {v : DogImmutables}
    (evm : EVM.State) {locals : Store} {ink dart art : UInt256}
    (hink : locals.get? "ink" = some (.int (Int.ofNat ink.toNat)))
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hart : locals.get? "art" = some (.int (Int.ofNat art.toNat)))
    (hfitInkDart : ink.toNat * dart.toNat < UInt256.size)
    (hartNe : art ≠ ⟨0⟩)
    (hdinkPos : 0 < (barkDinkWord ink dart art).toNat)
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat)
    (hdinkBound : (barkDinkWord ink dart art).toNat ≤ dogInt256LimitWord.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
        [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
          .require (.binary .gt (.var "dink") (.intLit 0)),
          .require
            (.binary .and
              (.binary .le (.var "dart") (.intLit int256Limit))
              (.binary .le (.var "dink") (.intLit int256Limit))) ])
      (.ok
        { contract := contract,
          locals :=
            barkLocalsDink (barkLocalsInkDart locals (barkInkDartWord ink dart))
              (barkDinkWord ink dart art), immutables := immStore v }
        evm) := by
  have hinkDart :=
    dogBarkInkDartCheckedMulOk (v := v) evm hink hdart hfitInkDart
  have hdinkLet :
      ExecBlock config
        { contract := contract, locals := barkLocalsInkDart locals (barkInkDartWord ink dart), immutables := immStore v }
        evm
        [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")) ]
        (.ok
          { contract := contract,
            locals :=
              barkLocalsDink (barkLocalsInkDart locals (barkInkDartWord ink dart))
                (barkDinkWord ink dart art), immutables := immStore v }
          evm) := by
    simpa [barkDinkWord] using
      dogBarkDinkLetOk (v := v) evm (locals := locals)
        (inkDart := barkInkDartWord ink dart) (art := art) hart hartNe
  have htoDink :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
        (checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
          [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")) ])
        (.ok
          { contract := contract,
            locals :=
              barkLocalsDink (barkLocalsInkDart locals (barkInkDartWord ink dart))
                (barkDinkWord ink dart art), immutables := immStore v }
          evm) := by
    simpa [List.append_assoc] using execBlock_append hinkDart hdinkLet
  let localsDink :=
    barkLocalsDink (barkLocalsInkDart locals (barkInkDartWord ink dart))
      (barkDinkWord ink dart art)
  have hdinkGet :
      localsDink.get? "dink" =
        some (.int (Int.ofNat (barkDinkWord ink dart art).toNat)) := by
    change (barkLocalsDink (barkLocalsInkDart locals (barkInkDartWord ink dart))
      (barkDinkWord ink dart art)).get? "dink" = _
    exact barkLocalsDink_get_dink (barkLocalsInkDart locals (barkInkDartWord ink dart))
      (barkDinkWord ink dart art)
  have hdartGet :
      localsDink.get? "dart" = some (.int (Int.ofNat dart.toNat)) := by
    simpa [localsDink] using
      barkLocalsDink_get_preserved (locals := barkLocalsInkDart locals (barkInkDartWord ink dart))
        (dink := barkDinkWord ink dart art) (name := "dart")
        (value := .int (Int.ofNat dart.toNat)) (by decide)
        (barkLocalsInkDart_get_preserved (locals := locals)
          (inkDart := barkInkDartWord ink dart) (name := "dart")
          (value := .int (Int.ofNat dart.toNat)) (by decide) hdart)
  have hdinkGuard :
      ExecBlock config { contract := contract, locals := localsDink, immutables := immStore v } evm
        [ .require (.binary .gt (.var "dink") (.intLit 0)) ]
        (.ok { contract := contract, locals := localsDink, immutables := immStore v } evm) :=
    dogBarkDinkGuardOkSource (v := v) evm hdinkGet hdinkPos
  have hintGuard :
      ExecBlock config { contract := contract, locals := localsDink, immutables := immStore v } evm
        [ .require
            (.binary .and
              (.binary .le (.var "dart") (.intLit int256Limit))
              (.binary .le (.var "dink") (.intLit int256Limit))) ]
        (.ok { contract := contract, locals := localsDink, immutables := immStore v } evm) :=
    dogBarkInt256GuardOkSource (v := v) evm hdartGet hdinkGet hdartBound hdinkBound
  have hguards :
      ExecBlock config { contract := contract, locals := localsDink, immutables := immStore v } evm
        [ .require (.binary .gt (.var "dink") (.intLit 0)),
          .require
            (.binary .and
              (.binary .le (.var "dart") (.intLit int256Limit))
              (.binary .le (.var "dink") (.intLit int256Limit))) ]
        (.ok { contract := contract, locals := localsDink, immutables := immStore v } evm) := by
    simpa using execBlock_append hdinkGuard hintGuard
  simpa [localsDink, List.append_assoc] using execBlock_append htoDink hguards

theorem dogBarkPostLeftoverDinkLetOkSource {v : DogImmutables}
    (evm : EVM.State) {locals : Store} {ink dart art : UInt256}
    (hink : locals.get? "ink" = some (.int (Int.ofNat ink.toNat)))
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hart : locals.get? "art" = some (.int (Int.ofNat art.toNat)))
    (hfitInkDart : ink.toNat * dart.toNat < UInt256.size)
    (hartNe : art ≠ ⟨0⟩) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
        [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")) ])
      (.ok
        { contract := contract,
          locals :=
            barkLocalsDink (barkLocalsInkDart locals (barkInkDartWord ink dart))
              (barkDinkWord ink dart art), immutables := immStore v }
        evm) := by
  have hinkDart :=
    dogBarkInkDartCheckedMulOk (v := v) evm hink hdart hfitInkDart
  have hdinkLet :
      ExecBlock config
        { contract := contract, locals := barkLocalsInkDart locals (barkInkDartWord ink dart), immutables := immStore v }
        evm
        [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")) ]
        (.ok
          { contract := contract,
            locals :=
              barkLocalsDink (barkLocalsInkDart locals (barkInkDartWord ink dart))
                (barkDinkWord ink dart art), immutables := immStore v }
          evm) := by
    simpa [barkDinkWord] using
      dogBarkDinkLetOk (v := v) evm (locals := locals)
        (inkDart := barkInkDartWord ink dart) (art := art) hart hartNe
  simpa [List.append_assoc] using execBlock_append hinkDart hdinkLet

theorem dogBarkPostLeftoverDinkGuardOkSource {v : DogImmutables}
    (evm : EVM.State) {locals : Store} {ink dart art : UInt256}
    (hink : locals.get? "ink" = some (.int (Int.ofNat ink.toNat)))
    (hdart : locals.get? "dart" = some (.int (Int.ofNat dart.toNat)))
    (hart : locals.get? "art" = some (.int (Int.ofNat art.toNat)))
    (hfitInkDart : ink.toNat * dart.toNat < UInt256.size)
    (hartNe : art ≠ ⟨0⟩)
    (hdinkPos : 0 < (barkDinkWord ink dart art).toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm
      (checkedMulUintInto "inkDart" (.var "ink") (.var "dart") ++
        [ .letDecl "dink" (some uint256) (.binary .div (.var "inkDart") (.var "art")),
          .require (.binary .gt (.var "dink") (.intLit 0)) ])
      (.ok
        { contract := contract,
          locals :=
            barkLocalsDink (barkLocalsInkDart locals (barkInkDartWord ink dart))
              (barkDinkWord ink dart art), immutables := immStore v }
        evm) := by
  let localsDink :=
    barkLocalsDink (barkLocalsInkDart locals (barkInkDartWord ink dart))
      (barkDinkWord ink dart art)
  have hprefix :=
    dogBarkPostLeftoverDinkLetOkSource (v := v) evm hink hdart hart hfitInkDart hartNe
  have hdinkGet :
      localsDink.get? "dink" =
        some (.int (Int.ofNat (barkDinkWord ink dart art).toNat)) := by
    simpa [localsDink] using
      barkLocalsDink_get_dink (barkLocalsInkDart locals (barkInkDartWord ink dart))
        (barkDinkWord ink dart art)
  have hguard :
      ExecBlock config { contract := contract, locals := localsDink, immutables := immStore v } evm
        [ .require (.binary .gt (.var "dink") (.intLit 0)) ]
        (.ok { contract := contract, locals := localsDink, immutables := immStore v } evm) :=
    dogBarkDinkGuardOkSource (v := v) evm hdinkGet hdinkPos
  simpa only [List.append_assoc] using execBlock_append hprefix hguard

theorem barkVatUrnsDecode_none_short {out : ByteArray}
    (hshort : out.size < 64) :
    config.externalABI.decode? "urns" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [uint256, uint256] out =
    none
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [uint256, uint256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases hfirst : 32 ≤ out.size
  · have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, hlen]
      omega
    have hscalar0 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
        some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat),
          0 + 32) := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) htake0
    rw [hscalar0]
    have htake32n : ¬ ((out.toList.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    have hscalar1 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 = none := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 32) htake32n
    rw [hscalar1]
    rfl
  · have htake0n : ¬ ((out.toList.drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, hlen]
      omega
    have hscalar0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 = none := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) htake0n
    rw [hscalar0]
    rfl

theorem barkVatUrnsBytesToWord0_eq (out : ByteArray) (hlong : 64 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 0).take 32) = barkVatUrnsInkWord out := by
  rw [decode_word_at_eq_any out 0 (by omega), uInt256OfByteArray_eq]
  unfold barkVatUrnsInkWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 0 32), readBytes_at_toList_any out 0 (by omega)]
  rw [byteArray_toList_eq (out.extract 0 32)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem barkVatUrnsBytesToWord32_eq (out : ByteArray) (hlong : 64 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 32).take 32) = barkVatUrnsArtWord out := by
  rw [decode_word_at_eq_any out 32 (by omega), uInt256OfByteArray_eq]
  unfold barkVatUrnsArtWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 32 32), readBytes_at_toList_any out 32 (by omega)]
  rw [byteArray_toList_eq (out.extract 32 64)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem barkVatUrnsDecode_ok {out : ByteArray}
    (hlong : 64 ≤ out.size) :
    config.externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [uint256, uint256] out =
    some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
      .int (Int.ofNat (barkVatUrnsArtWord out).toNat)]
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [uint256, uint256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hscalar0 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat),
        0 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 0) htake0
  have hscalar1 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 32).take 32)).toNat),
        32 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32
  rw [hscalar0, hscalar1]
  rw [barkVatUrnsBytesToWord0_eq out hlong, barkVatUrnsBytesToWord32_eq out hlong]
  rfl

theorem barkVatIlksDecode_none_short {out : ByteArray}
    (hshort : out.size < 160) :
    config.externalABI.decode? "ilks" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
    [uint256, uint256, uint256, uint256, uint256] out = none
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [uint256, uint256, uint256, uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, uint256, uint256]) (bytes := out.toList)
    (cursor := 0) (total := 32 * [uint256, uint256, uint256, uint256, uint256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases h0 : 32 ≤ out.size
  · have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, hlen]
      omega
    have hscalar0 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
        some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat),
          0 + 32) := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) htake0
    rw [hscalar0]
    by_cases h1 : 64 ≤ out.size
    · have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hlen]
        omega
      have hscalar32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
            some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 32).take 32)).toNat),
              32 + 32) := by
        simpa [uint256, uint256Int] using
          decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) htake32
      rw [hscalar32]
      by_cases h2 : 96 ≤ out.size
      · have htake64 : ((out.toList.drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, hlen]
          omega
        have hscalar64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
              some (.int (Int.ofNat
                (ABI.bytesToWord ((out.toList.drop 64).take 32)).toNat), 64 + 32) := by
          simpa [uint256, uint256Int] using
            decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 64) htake64
        rw [hscalar64]
        by_cases h3 : 128 ≤ out.size
        · have htake96 : ((out.toList.drop 96).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, hlen]
            omega
          have hscalar96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
                some (.int (Int.ofNat
                  (ABI.bytesToWord ((out.toList.drop 96).take 32)).toNat), 96 + 32) := by
            simpa [uint256, uint256Int] using
              decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
                (bytes := out.toList) (start := 96) htake96
          rw [hscalar96]
          have htake128n : ¬ ((out.toList.drop 128).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, hlen]
            omega
          have hscalar128 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 128 =
                none := by
            simpa [uint256, uint256Int] using
              decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
                (bytes := out.toList) (start := 128) htake128n
          rw [hscalar128]
          simp
        · have htake96n : ¬ ((out.toList.drop 96).take 32).length = 32 := by
            rw [List.length_take, List.length_drop, hlen]
            omega
          have hscalar96 :
              decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
                none := by
            simpa [uint256, uint256Int] using
              decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
                (bytes := out.toList) (start := 96) htake96n
          rw [hscalar96]
          simp
      · have htake64n : ¬ ((out.toList.drop 64).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, hlen]
          omega
        have hscalar64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 = none := by
          simpa [uint256, uint256Int] using
            decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 64) htake64n
        rw [hscalar64]
        simp
    · have htake32n : ¬ ((out.toList.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, hlen]
        omega
      have hscalar32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 = none := by
        simpa [uint256, uint256Int] using
          decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) htake32n
      rw [hscalar32]
      simp
  · have htake0n : ¬ ((out.toList.drop 0).take 32).length = 32 := by
      rw [List.drop_zero, List.length_take, hlen]
      omega
    have hscalar0 :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 = none := by
      simpa [uint256, uint256Int] using
        decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
          (bytes := out.toList) (start := 0) htake0n
    rw [hscalar0]
    simp

theorem barkVatIlksBytesToWord0_eq (out : ByteArray) (hlong : 160 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 0).take 32) = barkVatIlksArtWord out := by
  rw [decode_word_at_eq_any out 0 (by omega), uInt256OfByteArray_eq]
  unfold barkVatIlksArtWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 0 32), readBytes_at_toList_any out 0 (by omega)]
  rw [byteArray_toList_eq (out.extract 0 32)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem barkVatIlksBytesToWord32_eq (out : ByteArray) (hlong : 160 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 32).take 32) = barkVatIlksRateWord out := by
  rw [decode_word_at_eq_any out 32 (by omega), uInt256OfByteArray_eq]
  unfold barkVatIlksRateWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 32 32), readBytes_at_toList_any out 32 (by omega)]
  rw [byteArray_toList_eq (out.extract 32 64)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem barkVatIlksBytesToWord64_eq (out : ByteArray) (hlong : 160 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 64).take 32) = barkVatIlksSpotWord out := by
  rw [decode_word_at_eq_any out 64 (by omega), uInt256OfByteArray_eq]
  unfold barkVatIlksSpotWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 64 32), readBytes_at_toList_any out 64 (by omega)]
  rw [byteArray_toList_eq (out.extract 64 96)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem barkVatIlksBytesToWord96_eq (out : ByteArray) (hlong : 160 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 96).take 32) = barkVatIlksLineWord out := by
  rw [decode_word_at_eq_any out 96 (by omega), uInt256OfByteArray_eq]
  unfold barkVatIlksLineWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 96 32), readBytes_at_toList_any out 96 (by omega)]
  rw [byteArray_toList_eq (out.extract 96 128)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem barkVatIlksBytesToWord128_eq (out : ByteArray) (hlong : 160 ≤ out.size) :
    ABI.bytesToWord ((out.toList.drop 128).take 32) = barkVatIlksDustWord out := by
  rw [decode_word_at_eq_any out 128 (by omega), uInt256OfByteArray_eq]
  unfold barkVatIlksDustWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.readBytes 128 32), readBytes_at_toList_any out 128 (by omega)]
  rw [byteArray_toList_eq (out.extract 128 160)]
  simp [ByteArray.data_extract, Array.toList_extract]

theorem barkVatIlksDecode_ok {out : ByteArray}
    (hlong : 160 ≤ out.size) :
    config.externalABI.decode? "ilks" out = some (barkVatIlksReturnValues out) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
    [uint256, uint256, uint256, uint256, uint256] out =
      some (barkVatIlksReturnValues out)
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [uint256, uint256, uint256, uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, uint256, uint256]) (bytes := out.toList)
    (cursor := 0) (total := 32 * [uint256, uint256, uint256, uint256, uint256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake64 : ((out.toList.drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake96 : ((out.toList.drop 96).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake128 : ((out.toList.drop 128).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hscalar0 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat),
        0 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 0) htake0
  have hscalar32 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 32 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 32).take 32)).toNat),
        32 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32
  have hscalar64 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 64 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 64).take 32)).toNat),
        64 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 64) htake64
  have hscalar96 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 96 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 96).take 32)).toNat),
        96 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 96) htake96
  have hscalar128 : decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 128 =
      some (.int (Int.ofNat (ABI.bytesToWord ((out.toList.drop 128).take 32)).toNat),
        128 + 32) := by
    simpa [uint256, uint256Int] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 128) htake128
  rw [hscalar0, hscalar32, hscalar64, hscalar96, hscalar128]
  rw [barkVatIlksBytesToWord0_eq out hlong, barkVatIlksBytesToWord32_eq out hlong,
    barkVatIlksBytesToWord64_eq out hlong, barkVatIlksBytesToWord96_eq out hlong,
    barkVatIlksBytesToWord128_eq out hlong]
  rfl


end Benchmarks.Dss.Dog
