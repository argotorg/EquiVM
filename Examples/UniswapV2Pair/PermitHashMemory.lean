import Examples.UniswapV2Pair.StackRoutines
import Examples.UniswapV2Pair.MutatorDispatch
import Examples.UniswapV2Pair.Routines
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000



namespace UniswapV2Pair

/-! ## Permit runtime hashing helpers -/

theorem wordAt0Mem_size_of_ge32 {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  exact toByteArray_write32_size_of_le mem word 0 mem.size mem.size rfl
    (by omega) (by omega)

theorem wordAt32Mem_size_of_ge64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt32Mem word mem).size = mem.size := by
  unfold wordAt32Mem
  exact toByteArray_write32_size_of_le mem word 32 mem.size mem.size rfl
    (by omega) (by omega)

theorem twoWordHashMem_size_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem
  rw [wordAt32Mem_size_of_ge64 slot]
  · exact wordAt0Mem_size_of_ge32 key (by omega)
  · rw [wordAt0Mem_size_of_ge32 key (by omega)]
    exact hmem

theorem twoWordHashMem_read0_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem twoWordHashMem_read32_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem twoWordHashMem_read64_of_ge96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 = mem.readWithPadding 64 32 := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)
      (by rw [wordAt0Mem_size_of_ge32 key (by omega)]; omega)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by omega) (by omega) (by omega)]

set_option maxHeartbeats 800000 in
theorem twoWordHashMem_read0_64_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [twoWordHashMem_size_of_ge64 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      twoWordHashMem_read0_of_ge64 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      twoWordHashMem_read32_of_ge64 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem twoWordHashMem_mapSlot_of_ge64 {mem : ByteArray} (key baseSlot : UInt256)
    (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      mapSlot key baseSlot := by
  rw [twoWordHashMem_read0_64_of_ge64 key baseSlot hmem]
  simpa [mapSlot, solcMappingSlot] using mappingSlot_single key baseSlot

abbrev permitRuntimeTypehashWord : UInt256 :=
  ⟨49955707469362902507454157297736832118868343942642399513960811609542965143241⟩

noncomputable def permitRuntimeStructHashDataWrites
    (owner spender value nonce deadline : UInt256) : List (Nat × UInt256) :=
  [ (160, permitRuntimeTypehashWord),
    (192, owner),
    (224, spender),
    (256, value),
    (288, nonce),
    (320, deadline) ]

noncomputable def permitRuntimeStructHashDataMem (baseMem : ByteArray)
    (owner spender value nonce deadline : UInt256) : ByteArray :=
  writeCascade baseMem (permitRuntimeStructHashDataWrites owner spender value nonce deadline)

noncomputable def permitRuntimeStructHashLenMem (baseMem : ByteArray)
    (owner spender value nonce deadline : UInt256) : ByteArray :=
  writeCascade (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline)
    [(128, (⟨192⟩ : UInt256))]

noncomputable def permitRuntimeStructHashMem (baseMem : ByteArray)
    (owner spender value nonce deadline : UInt256) : ByteArray :=
  writeCascade (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline)
    [(64, (⟨352⟩ : UInt256))]

noncomputable abbrev permitRuntimeStructHashWord (baseMem : ByteArray)
    (owner spender value nonce deadline : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      (ffi.KEC
        ((permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
          160 192)))

noncomputable def permitRuntimeStructHashDataMem0 (baseMem : ByteArray) : ByteArray :=
  writeCascade baseMem [(160, permitRuntimeTypehashWord)]

noncomputable def permitRuntimeStructHashDataMem1 (baseMem : ByteArray)
    (owner : UInt256) : ByteArray :=
  writeCascade baseMem [(160, permitRuntimeTypehashWord), (192, owner)]

noncomputable def permitRuntimeStructHashDataMem2 (baseMem : ByteArray)
    (owner spender : UInt256) : ByteArray :=
  writeCascade baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender)]

noncomputable def permitRuntimeStructHashDataMem3 (baseMem : ByteArray)
    (owner spender value : UInt256) : ByteArray :=
  writeCascade baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender), (256, value)]

noncomputable def permitRuntimeStructHashDataMem4 (baseMem : ByteArray)
    (owner spender value nonce : UInt256) : ByteArray :=
  writeCascade baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender), (256, value),
      (288, nonce)]

theorem permitRuntimeStructHashDataWrites_gaps
    (owner spender value nonce deadline : UInt256) :
    WriteGapsOk 96
      (permitRuntimeStructHashDataWrites owner spender value nonce deadline) := by
  simp [WriteGapsOk, permitRuntimeStructHashDataWrites]
  exact lt_usize _ (by norm_num)

theorem permitRuntimeStructHashDataWrites_size
    (owner spender value nonce deadline : UInt256) :
    writeCascadeSize 96
      (permitRuntimeStructHashDataWrites owner spender value nonce deadline) = 352 := by
  rfl

theorem permitRuntimeStructHashDataWrites_disjoint64
    (owner spender value nonce deadline : UInt256) :
    WindowDisjointFromWrites 96 64 32
      (permitRuntimeStructHashDataWrites owner spender value nonce deadline) := by
  simp [WindowDisjointFromWrites, permitRuntimeStructHashDataWrites]
  exact lt_usize _ (by norm_num)

theorem permitRuntimeStructHashDataMem_size {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline).size = 352 := by
  unfold permitRuntimeStructHashDataMem
  exact writeCascade_size_of_base baseMem
    (permitRuntimeStructHashDataWrites owner spender value nonce deadline)
    hbaseSize
    (permitRuntimeStructHashDataWrites_gaps owner spender value nonce deadline)
    (permitRuntimeStructHashDataWrites_size owner spender value nonce deadline)

theorem permitRuntimeStructHashDataMem_read64 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨128⟩ : UInt256)) :
    (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨128⟩ : UInt256) := by
  unfold permitRuntimeStructHashDataMem
  rw [writeCascade_read_preserved]
  · exact hbaseRead64
  · rw [hbaseSize]
    exact permitRuntimeStructHashDataWrites_disjoint64 owner spender value nonce deadline

theorem permitRuntimeStructHashDataMem_mload64 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨128⟩ : UInt256)) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
      decide)
    (by native_decide)
    (permitRuntimeStructHashDataMem_read64 owner spender value nonce deadline hbaseSize
      hbaseRead64)

theorem permitRuntimeStructHashLenMem_size {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline).size = 352 := by
  unfold permitRuntimeStructHashLenMem writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le
    (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline)
    (⟨192⟩ : UInt256) 128 352 352
    (permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize)
    (by
      rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
      omega)
    (by norm_num)

theorem permitRuntimeStructHashMem_size {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).size = 352 := by
  unfold permitRuntimeStructHashMem writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le
    (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline)
    (⟨352⟩ : UInt256) 64 352 352
    (permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize)
    (by
      rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
      omega)
    (by norm_num)

theorem permitRuntimeStructHashLenMem_read128 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline).readWithPadding
        128 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold permitRuntimeStructHashLenMem writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_read_back
    (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline)
    (⟨192⟩ : UInt256) 128
    (by
      rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
      omega)

theorem permitRuntimeStructHashMem_read128 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
        128 32 =
      UInt256.toByteArray (⟨192⟩ : UInt256) := by
  unfold permitRuntimeStructHashMem writeCascade Reasoning.Theory.writeWord
  simp only [writeCascade_nil]
  rw [write32_read_above _ _ 64 128 (by rw [toByteArray_size])
      (by
        rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
        omega)
      (by omega)
      (by
        rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
        omega)]
  exact permitRuntimeStructHashLenMem_read128 owner spender value nonce deadline hbaseSize

theorem permitRuntimeStructHashMem_mload128 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (if (⟨128⟩ : UInt256).toNat ≥
          (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
          (⟨128⟩ : UInt256).toNat 32)))
      = ⟨192⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [permitRuntimeStructHashMem_size owner spender value nonce deadline hbaseSize]
      decide)
    (by native_decide)
    (permitRuntimeStructHashMem_read128 owner spender value nonce deadline hbaseSize)

theorem permitRuntimeStructHashMem_read64 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
        64 32 =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  unfold permitRuntimeStructHashMem writeCascade Reasoning.Theory.writeWord
  simp only [writeCascade_nil]
  exact toByteArray_write32_read_back
    (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline)
    (⟨352⟩ : UInt256) 64
    (by
      rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
      omega)

theorem permitRuntimeStructHashMem_mload64 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 11 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨352⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [permitRuntimeStructHashMem_size owner spender value nonce deadline hbaseSize]
      decide)
    (by native_decide)
    (permitRuntimeStructHashMem_read64 owner spender value nonce deadline hbaseSize)

theorem permitRuntimeStructHashDataMem0_size {baseMem : ByteArray}
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem0 baseMem).size = 192 := by
  unfold permitRuntimeStructHashDataMem0
  exact writeCascade_size_of_base baseMem [(160, permitRuntimeTypehashWord)] hbaseSize
    (by simp [WriteGapsOk]; native_decide) (by simp [writeCascadeSize])

theorem permitRuntimeStructHashDataMem1_size {baseMem : ByteArray} (owner : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem1 baseMem owner).size = 224 := by
  unfold permitRuntimeStructHashDataMem1
  exact writeCascade_size_of_base baseMem [(160, permitRuntimeTypehashWord), (192, owner)]
    hbaseSize (by simp [WriteGapsOk]; native_decide) (by simp [writeCascadeSize])

theorem permitRuntimeStructHashDataMem2_size {baseMem : ByteArray}
    (owner spender : UInt256) (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem2 baseMem owner spender).size = 256 := by
  unfold permitRuntimeStructHashDataMem2
  exact writeCascade_size_of_base baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender)] hbaseSize
    (by simp [WriteGapsOk]; native_decide) (by simp [writeCascadeSize])

theorem permitRuntimeStructHashDataMem3_size {baseMem : ByteArray}
    (owner spender value : UInt256) (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem3 baseMem owner spender value).size = 288 := by
  unfold permitRuntimeStructHashDataMem3
  exact writeCascade_size_of_base baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender), (256, value)]
    hbaseSize (by simp [WriteGapsOk]; native_decide) (by simp [writeCascadeSize])

theorem permitRuntimeStructHashDataMem4_size {baseMem : ByteArray}
    (owner spender value nonce : UInt256) (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem4 baseMem owner spender value nonce).size = 320 := by
  unfold permitRuntimeStructHashDataMem4
  exact writeCascade_size_of_base baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender), (256, value),
      (288, nonce)] hbaseSize
    (by simp [WriteGapsOk]; native_decide) (by simp [writeCascadeSize])

theorem permitRuntimeStructHashMem_read160 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
        160 32 =
      UInt256.toByteArray permitRuntimeTypehashWord := by
  rw [permitRuntimeStructHashMem]
  rw [writeCascade_read_preserved_len _ [(64, (⟨352⟩ : UInt256))] 160 32
    (by rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  rw [permitRuntimeStructHashLenMem]
  rw [writeCascade_read_preserved_len _ [(128, (⟨192⟩ : UInt256))] 160 32
    (by rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  unfold permitRuntimeStructHashDataMem
  exact writeCascade_read_word_of_head baseMem 160 permitRuntimeTypehashWord
    [(192, owner), (224, spender), (256, value), (288, nonce), (320, deadline)]
    (by rw [hbaseSize]; native_decide)
    (by rw [hbaseSize]; simp [WindowDisjointFromWrites])

theorem permitRuntimeStructHashMem_read192 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
        192 32 =
      UInt256.toByteArray owner := by
  rw [permitRuntimeStructHashMem]
  rw [writeCascade_read_preserved_len _ [(64, (⟨352⟩ : UInt256))] 192 32
    (by rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  rw [permitRuntimeStructHashLenMem]
  rw [writeCascade_read_preserved_len _ [(128, (⟨192⟩ : UInt256))] 192 32
    (by rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  change (writeCascade (permitRuntimeStructHashDataMem0 baseMem)
      [(192, owner), (224, spender), (256, value), (288, nonce),
        (320, deadline)]).readWithPadding 192 32 =
    UInt256.toByteArray owner
  exact writeCascade_read_word_of_head (permitRuntimeStructHashDataMem0 baseMem)
    192 owner [(224, spender), (256, value), (288, nonce), (320, deadline)]
    (by rw [permitRuntimeStructHashDataMem0_size hbaseSize]; native_decide)
    (by rw [permitRuntimeStructHashDataMem0_size hbaseSize]; simp [WindowDisjointFromWrites])

theorem permitRuntimeStructHashMem_read224 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
        224 32 =
      UInt256.toByteArray spender := by
  rw [permitRuntimeStructHashMem]
  rw [writeCascade_read_preserved_len _ [(64, (⟨352⟩ : UInt256))] 224 32
    (by rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  rw [permitRuntimeStructHashLenMem]
  rw [writeCascade_read_preserved_len _ [(128, (⟨192⟩ : UInt256))] 224 32
    (by rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  change (writeCascade (permitRuntimeStructHashDataMem1 baseMem owner)
      [(224, spender), (256, value), (288, nonce), (320, deadline)]).readWithPadding
        224 32 =
    UInt256.toByteArray spender
  exact writeCascade_read_word_of_head (permitRuntimeStructHashDataMem1 baseMem owner)
    224 spender [(256, value), (288, nonce), (320, deadline)]
    (by
      rw [(permitRuntimeStructHashDataMem1_size owner hbaseSize)]
      simp)
    (by
      rw [(permitRuntimeStructHashDataMem1_size owner hbaseSize)]
      simp [WindowDisjointFromWrites])

theorem permitRuntimeStructHashMem_read256 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
        256 32 =
      UInt256.toByteArray value := by
  rw [permitRuntimeStructHashMem]
  rw [writeCascade_read_preserved_len _ [(64, (⟨352⟩ : UInt256))] 256 32
    (by rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  rw [permitRuntimeStructHashLenMem]
  rw [writeCascade_read_preserved_len _ [(128, (⟨192⟩ : UInt256))] 256 32
    (by rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  change (writeCascade (permitRuntimeStructHashDataMem2 baseMem owner spender)
      [(256, value), (288, nonce), (320, deadline)]).readWithPadding 256 32 =
    UInt256.toByteArray value
  exact writeCascade_read_word_of_head (permitRuntimeStructHashDataMem2 baseMem owner spender)
    256 value [(288, nonce), (320, deadline)]
    (by
      rw [(permitRuntimeStructHashDataMem2_size owner spender hbaseSize)]
      simp)
    (by
      rw [(permitRuntimeStructHashDataMem2_size owner spender hbaseSize)]
      simp [WindowDisjointFromWrites])

theorem permitRuntimeStructHashMem_read288 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
        288 32 =
      UInt256.toByteArray nonce := by
  rw [permitRuntimeStructHashMem]
  rw [writeCascade_read_preserved_len _ [(64, (⟨352⟩ : UInt256))] 288 32
    (by rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  rw [permitRuntimeStructHashLenMem]
  rw [writeCascade_read_preserved_len _ [(128, (⟨192⟩ : UInt256))] 288 32
    (by rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  change (writeCascade (permitRuntimeStructHashDataMem3 baseMem owner spender value)
      [(288, nonce), (320, deadline)]).readWithPadding 288 32 =
    UInt256.toByteArray nonce
  exact writeCascade_read_word_of_head
    (permitRuntimeStructHashDataMem3 baseMem owner spender value)
    288 nonce [(320, deadline)]
    (by
      rw [(permitRuntimeStructHashDataMem3_size owner spender value hbaseSize)]
      simp)
    (by
      rw [(permitRuntimeStructHashDataMem3_size owner spender value hbaseSize)]
      simp [WindowDisjointFromWrites])

theorem permitRuntimeStructHashMem_read320 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
        320 32 =
      UInt256.toByteArray deadline := by
  rw [permitRuntimeStructHashMem]
  rw [writeCascade_read_preserved_len _ [(64, (⟨352⟩ : UInt256))] 320 32
    (by rw [permitRuntimeStructHashLenMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  rw [permitRuntimeStructHashLenMem]
  rw [writeCascade_read_preserved_len _ [(128, (⟨192⟩ : UInt256))] 320 32
    (by rw [permitRuntimeStructHashDataMem_size owner spender value nonce deadline hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  change (writeCascade (permitRuntimeStructHashDataMem4 baseMem owner spender value nonce)
      [(320, deadline)]).readWithPadding 320 32 =
    UInt256.toByteArray deadline
  exact writeCascade_read_word_of_head
    (permitRuntimeStructHashDataMem4 baseMem owner spender value nonce)
    320 deadline []
    (by
      rw [(permitRuntimeStructHashDataMem4_size owner spender value nonce hbaseSize)]
      simp)
    (by
      rw [(permitRuntimeStructHashDataMem4_size owner spender value nonce hbaseSize)]
      simp [WindowDisjointFromWrites])

theorem permitRuntimeStructHashMem_read160_192 {baseMem : ByteArray}
    (owner spender value nonce deadline : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashMem baseMem owner spender value nonce deadline).readWithPadding
        160 192 =
      UInt256.toByteArray permitRuntimeTypehashWord ++ UInt256.toByteArray owner ++
        UInt256.toByteArray spender ++ UInt256.toByteArray value ++ UInt256.toByteArray nonce ++
          UInt256.toByteArray deadline := by
  rw [byteArray_readWithPadding_split _ 160 32 160 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [permitRuntimeStructHashMem_size owner spender value nonce deadline hbaseSize])]
  rw [byteArray_readWithPadding_split _ 192 32 128 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [permitRuntimeStructHashMem_size owner spender value nonce deadline hbaseSize])]
  rw [byteArray_readWithPadding_split _ 224 32 96 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [permitRuntimeStructHashMem_size owner spender value nonce deadline hbaseSize])]
  rw [byteArray_readWithPadding_split _ 256 32 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [permitRuntimeStructHashMem_size owner spender value nonce deadline hbaseSize])]
  rw [byteArray_readWithPadding_split _ 288 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [permitRuntimeStructHashMem_size owner spender value nonce deadline hbaseSize])]
  rw [permitRuntimeStructHashMem_read160 owner spender value nonce deadline hbaseSize,
    permitRuntimeStructHashMem_read192 owner spender value nonce deadline hbaseSize,
    permitRuntimeStructHashMem_read224 owner spender value nonce deadline hbaseSize,
    permitRuntimeStructHashMem_read256 owner spender value nonce deadline hbaseSize,
    permitRuntimeStructHashMem_read288 owner spender value nonce deadline hbaseSize,
    permitRuntimeStructHashMem_read320 owner spender value nonce deadline hbaseSize]
  simp only [ByteArray.append_assoc]

/-! ## Permit digest runtime hashing helpers -/

abbrev permitRuntimeDigestPrefixWord : UInt256 :=
  UInt256.shiftLeft (⟨6401⟩ : UInt256) ⟨240⟩

noncomputable def permitRuntimeDigestDataWrites
    (domain structHash : UInt256) : List (Nat × UInt256) :=
  [ (384, permitRuntimeDigestPrefixWord),
    (386, domain),
    (418, structHash) ]

noncomputable def permitRuntimeDigestDataMem (baseMem : ByteArray)
    (domain structHash : UInt256) : ByteArray :=
  writeCascade baseMem (permitRuntimeDigestDataWrites domain structHash)

noncomputable def permitRuntimeDigestLenMem (baseMem : ByteArray)
    (domain structHash : UInt256) : ByteArray :=
  writeCascade (permitRuntimeDigestDataMem baseMem domain structHash)
    [(352, (⟨66⟩ : UInt256))]

noncomputable def permitRuntimeDigestMem (baseMem : ByteArray)
    (domain structHash : UInt256) : ByteArray :=
  writeCascade (permitRuntimeDigestLenMem baseMem domain structHash)
    [(64, (⟨450⟩ : UInt256))]

noncomputable abbrev permitRuntimeDigestWord (baseMem : ByteArray)
    (domain structHash : UInt256) : UInt256 :=
  UInt256.ofNat
    (fromByteArrayBigEndian
      (ffi.KEC ((permitRuntimeDigestMem baseMem domain structHash).readWithPadding 384 66)))

noncomputable def permitRuntimeDigestDataMem0 (baseMem : ByteArray) : ByteArray :=
  writeCascade baseMem [(384, permitRuntimeDigestPrefixWord)]

noncomputable def permitRuntimeDigestDataMem1 (baseMem : ByteArray)
    (domain : UInt256) : ByteArray :=
  writeCascade baseMem [(384, permitRuntimeDigestPrefixWord), (386, domain)]

theorem permitRuntimeDigestDataWrites_gaps (domain structHash : UInt256) :
    WriteGapsOk 352 (permitRuntimeDigestDataWrites domain structHash) := by
  simp [WriteGapsOk, permitRuntimeDigestDataWrites]
  all_goals native_decide

theorem permitRuntimeDigestDataWrites_size (domain structHash : UInt256) :
    writeCascadeSize 352 (permitRuntimeDigestDataWrites domain structHash) = 450 := by
  rfl

theorem permitRuntimeDigestDataWrites_disjoint64 (domain structHash : UInt256) :
    WindowDisjointFromWrites 352 64 32
      (permitRuntimeDigestDataWrites domain structHash) := by
  simp [WindowDisjointFromWrites, permitRuntimeDigestDataWrites]
  all_goals native_decide

theorem permitRuntimeDigestDataMem_size {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestDataMem baseMem domain structHash).size = 450 := by
  unfold permitRuntimeDigestDataMem
  exact writeCascade_size_of_base baseMem (permitRuntimeDigestDataWrites domain structHash)
    hbaseSize (permitRuntimeDigestDataWrites_gaps domain structHash)
    (permitRuntimeDigestDataWrites_size domain structHash)

theorem permitRuntimeDigestDataMem_read64 {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨352⟩ : UInt256)) :
    (permitRuntimeDigestDataMem baseMem domain structHash).readWithPadding 64 32 =
      UInt256.toByteArray (⟨352⟩ : UInt256) := by
  unfold permitRuntimeDigestDataMem
  rw [writeCascade_read_preserved]
  · exact hbaseRead64
  · rw [hbaseSize]
    exact permitRuntimeDigestDataWrites_disjoint64 domain structHash

theorem permitRuntimeDigestDataMem_mload64 {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨352⟩ : UInt256)) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (permitRuntimeDigestDataMem baseMem domain structHash).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeDigestDataMem baseMem domain structHash).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨352⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [permitRuntimeDigestDataMem_size domain structHash hbaseSize]
      decide)
    (by native_decide)
    (permitRuntimeDigestDataMem_read64 domain structHash hbaseSize hbaseRead64)

theorem permitRuntimeDigestLenMem_size {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestLenMem baseMem domain structHash).size = 450 := by
  unfold permitRuntimeDigestLenMem writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le
    (permitRuntimeDigestDataMem baseMem domain structHash) (⟨66⟩ : UInt256) 352 450 450
    (permitRuntimeDigestDataMem_size domain structHash hbaseSize)
    (by
      rw [permitRuntimeDigestDataMem_size domain structHash hbaseSize]
      omega)
    (by norm_num)

theorem permitRuntimeDigestMem_size {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestMem baseMem domain structHash).size = 450 := by
  unfold permitRuntimeDigestMem writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le
    (permitRuntimeDigestLenMem baseMem domain structHash) (⟨450⟩ : UInt256) 64 450 450
    (permitRuntimeDigestLenMem_size domain structHash hbaseSize)
    (by
      rw [permitRuntimeDigestLenMem_size domain structHash hbaseSize]
      omega)
    (by norm_num)

theorem permitRuntimeDigestLenMem_read352 {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestLenMem baseMem domain structHash).readWithPadding 352 32 =
      UInt256.toByteArray (⟨66⟩ : UInt256) := by
  unfold permitRuntimeDigestLenMem writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_read_back
    (permitRuntimeDigestDataMem baseMem domain structHash) (⟨66⟩ : UInt256) 352
    (by
      rw [permitRuntimeDigestDataMem_size domain structHash hbaseSize]
      omega)

theorem permitRuntimeDigestMem_read352 {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestMem baseMem domain structHash).readWithPadding 352 32 =
      UInt256.toByteArray (⟨66⟩ : UInt256) := by
  unfold permitRuntimeDigestMem writeCascade Reasoning.Theory.writeWord
  simp only [writeCascade_nil]
  rw [write32_read_above _ _ 64 352 (by rw [toByteArray_size])
      (by
        rw [permitRuntimeDigestLenMem_size domain structHash hbaseSize]
        omega)
      (by omega)
      (by
        rw [permitRuntimeDigestLenMem_size domain structHash hbaseSize]
        omega)]
  exact permitRuntimeDigestLenMem_read352 domain structHash hbaseSize

theorem permitRuntimeDigestMem_mload352 {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352) :
    (if (⟨352⟩ : UInt256).toNat ≥
          (permitRuntimeDigestMem baseMem domain structHash).size
        ∨ (⟨352⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeDigestMem baseMem domain structHash).readWithPadding
          (⟨352⟩ : UInt256).toNat 32)))
      = ⟨66⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [permitRuntimeDigestMem_size domain structHash hbaseSize]
      decide)
    (by native_decide)
    (permitRuntimeDigestMem_read352 domain structHash hbaseSize)

theorem permitRuntimeDigestDataMem0_size {baseMem : ByteArray}
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestDataMem0 baseMem).size = 416 := by
  unfold permitRuntimeDigestDataMem0
  exact writeCascade_size_of_base baseMem [(384, permitRuntimeDigestPrefixWord)] hbaseSize
    (by simp [WriteGapsOk]; native_decide) (by simp [writeCascadeSize])

theorem permitRuntimeDigestDataMem1_size {baseMem : ByteArray}
    (domain : UInt256) (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestDataMem1 baseMem domain).size = 418 := by
  unfold permitRuntimeDigestDataMem1
  exact writeCascade_size_of_base baseMem [(384, permitRuntimeDigestPrefixWord), (386, domain)]
    hbaseSize (by simp [WriteGapsOk]; native_decide) (by simp [writeCascadeSize])

theorem permitRuntimeDigestPrefix_read0_2 :
    (UInt256.toByteArray permitRuntimeDigestPrefixWord).extract 0 2 =
      ByteArray.mk #[0x19, 0x01] := by
  native_decide

theorem permitRuntimeDigestMem_read384_2 {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestMem baseMem domain structHash).readWithPadding 384 2 =
      ByteArray.mk #[0x19, 0x01] := by
  rw [permitRuntimeDigestMem]
  rw [writeCascade_read_preserved_len _ [(64, (⟨450⟩ : UInt256))] 384 2
    (by rw [permitRuntimeDigestLenMem_size domain structHash hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  rw [permitRuntimeDigestLenMem]
  rw [writeCascade_read_preserved_len _ [(352, (⟨66⟩ : UInt256))] 384 2
    (by rw [permitRuntimeDigestDataMem_size domain structHash hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  unfold permitRuntimeDigestDataMem
  rw [permitRuntimeDigestDataWrites]
  rw [writeCascade_read_window_of_head baseMem 384 0 2 permitRuntimeDigestPrefixWord
    [(386, domain), (418, structHash)]
    (by rw [hbaseSize]; native_decide)
    (by rw [hbaseSize]; simp [WindowDisjointFromWrites])
    (by norm_num) (by norm_num) (by norm_num)]
  exact permitRuntimeDigestPrefix_read0_2

theorem permitRuntimeDigestMem_read386 {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestMem baseMem domain structHash).readWithPadding 386 32 =
      UInt256.toByteArray domain := by
  rw [permitRuntimeDigestMem]
  rw [writeCascade_read_preserved_len _ [(64, (⟨450⟩ : UInt256))] 386 32
    (by rw [permitRuntimeDigestLenMem_size domain structHash hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  rw [permitRuntimeDigestLenMem]
  rw [writeCascade_read_preserved_len _ [(352, (⟨66⟩ : UInt256))] 386 32
    (by rw [permitRuntimeDigestDataMem_size domain structHash hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  change (writeCascade (permitRuntimeDigestDataMem0 baseMem)
      [(386, domain), (418, structHash)]).readWithPadding 386 32 =
    UInt256.toByteArray domain
  exact writeCascade_read_word_of_head (permitRuntimeDigestDataMem0 baseMem)
    386 domain [(418, structHash)]
    (by rw [permitRuntimeDigestDataMem0_size hbaseSize]; native_decide)
    (by rw [permitRuntimeDigestDataMem0_size hbaseSize]; simp [WindowDisjointFromWrites])

theorem permitRuntimeDigestMem_read418 {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestMem baseMem domain structHash).readWithPadding 418 32 =
      UInt256.toByteArray structHash := by
  rw [permitRuntimeDigestMem]
  rw [writeCascade_read_preserved_len _ [(64, (⟨450⟩ : UInt256))] 418 32
    (by rw [permitRuntimeDigestLenMem_size domain structHash hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  rw [permitRuntimeDigestLenMem]
  rw [writeCascade_read_preserved_len _ [(352, (⟨66⟩ : UInt256))] 418 32
    (by rw [permitRuntimeDigestDataMem_size domain structHash hbaseSize]
        simp [WindowDisjointFromWrites]) (by norm_num) (by norm_num)]
  change (writeCascade (permitRuntimeDigestDataMem1 baseMem domain)
      [(418, structHash)]).readWithPadding 418 32 =
    UInt256.toByteArray structHash
  exact writeCascade_read_word_of_head (permitRuntimeDigestDataMem1 baseMem domain)
    418 structHash []
    (by rw [permitRuntimeDigestDataMem1_size domain hbaseSize]; native_decide)
    (by rw [permitRuntimeDigestDataMem1_size domain hbaseSize]; simp [WindowDisjointFromWrites])

theorem permitRuntimeDigestMem_read384_66 {baseMem : ByteArray}
    (domain structHash : UInt256)
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestMem baseMem domain structHash).readWithPadding 384 66 =
      ByteArray.mk #[0x19, 0x01] ++ UInt256.toByteArray domain ++
        UInt256.toByteArray structHash := by
  rw [byteArray_readWithPadding_split _ 384 2 64 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [permitRuntimeDigestMem_size domain structHash hbaseSize])]
  rw [byteArray_readWithPadding_split _ 386 32 32 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [permitRuntimeDigestMem_size domain structHash hbaseSize])]
  rw [permitRuntimeDigestMem_read384_2 domain structHash hbaseSize,
    permitRuntimeDigestMem_read386 domain structHash hbaseSize,
    permitRuntimeDigestMem_read418 domain structHash hbaseSize]
  simp only [ByteArray.append_assoc]

/-! ## Permit `ecrecover` runtime calldata helpers -/

noncomputable def permitRuntimeEcrecoverInputWrites
    (digest v r s : UInt256) : List (Nat × UInt256) :=
  [ (450, (⟨0⟩ : UInt256)),
    (64, (⟨482⟩ : UInt256)),
    (482, digest),
    (514, v),
    (546, r),
    (578, s) ]

noncomputable def permitRuntimeEcrecoverMem0 (baseMem : ByteArray) : ByteArray :=
  writeCascade baseMem [(450, (⟨0⟩ : UInt256))]

noncomputable def permitRuntimeEcrecoverMem1 (baseMem : ByteArray) : ByteArray :=
  writeCascade (permitRuntimeEcrecoverMem0 baseMem) [(64, (⟨482⟩ : UInt256))]

noncomputable def permitRuntimeEcrecoverMem2 (baseMem : ByteArray)
    (digest : UInt256) : ByteArray :=
  writeCascade (permitRuntimeEcrecoverMem1 baseMem) [(482, digest)]

noncomputable def permitRuntimeEcrecoverMem3 (baseMem : ByteArray)
    (digest v : UInt256) : ByteArray :=
  writeCascade (permitRuntimeEcrecoverMem2 baseMem digest) [(514, v)]

noncomputable def permitRuntimeEcrecoverMem4 (baseMem : ByteArray)
    (digest v r : UInt256) : ByteArray :=
  writeCascade (permitRuntimeEcrecoverMem3 baseMem digest v) [(546, r)]

noncomputable def permitRuntimeEcrecoverInputMem (baseMem : ByteArray)
    (digest v r s : UInt256) : ByteArray :=
  writeCascade (permitRuntimeEcrecoverMem4 baseMem digest v r) [(578, s)]

theorem permitRuntimeEcrecoverInputWrites_gaps (digest v r s : UInt256) :
    WriteGapsOk 450 (permitRuntimeEcrecoverInputWrites digest v r s) := by
  simp [WriteGapsOk, permitRuntimeEcrecoverInputWrites]

theorem permitRuntimeEcrecoverInputWrites_size (digest v r s : UInt256) :
    writeCascadeSize 450 (permitRuntimeEcrecoverInputWrites digest v r s) = 610 := by
  rfl

theorem permitRuntimeEcrecoverMem0_size {baseMem : ByteArray}
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverMem0 baseMem).size = 482 := by
  unfold permitRuntimeEcrecoverMem0 writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le baseMem (⟨0⟩ : UInt256) 450 450 482
    hbaseSize (by rw [hbaseSize]) (by norm_num)

theorem permitRuntimeEcrecoverMem1_size {baseMem : ByteArray}
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverMem1 baseMem).size = 482 := by
  unfold permitRuntimeEcrecoverMem1 writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le (permitRuntimeEcrecoverMem0 baseMem)
    (⟨482⟩ : UInt256) 64 482 482
    (permitRuntimeEcrecoverMem0_size hbaseSize)
    (by
      rw [permitRuntimeEcrecoverMem0_size hbaseSize]
      omega)
    (by norm_num)

theorem permitRuntimeEcrecoverMem2_size {baseMem : ByteArray}
    (digest : UInt256) (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverMem2 baseMem digest).size = 514 := by
  unfold permitRuntimeEcrecoverMem2 writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le (permitRuntimeEcrecoverMem1 baseMem)
    digest 482 482 514
    (permitRuntimeEcrecoverMem1_size hbaseSize)
    (by
      rw [permitRuntimeEcrecoverMem1_size hbaseSize])
    (by norm_num)

theorem permitRuntimeEcrecoverMem3_size {baseMem : ByteArray}
    (digest v : UInt256) (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverMem3 baseMem digest v).size = 546 := by
  unfold permitRuntimeEcrecoverMem3 writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le (permitRuntimeEcrecoverMem2 baseMem digest)
    v 514 514 546
    (permitRuntimeEcrecoverMem2_size digest hbaseSize)
    (by
      rw [permitRuntimeEcrecoverMem2_size digest hbaseSize])
    (by norm_num)

theorem permitRuntimeEcrecoverMem4_size {baseMem : ByteArray}
    (digest v r : UInt256) (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverMem4 baseMem digest v r).size = 578 := by
  unfold permitRuntimeEcrecoverMem4 writeCascade Reasoning.Theory.writeWord
  exact toByteArray_write32_size_of_le (permitRuntimeEcrecoverMem3 baseMem digest v)
    r 546 546 578
    (permitRuntimeEcrecoverMem3_size digest v hbaseSize)
    (by
      rw [permitRuntimeEcrecoverMem3_size digest v hbaseSize])
    (by norm_num)

theorem permitRuntimeEcrecoverInputMem_size {baseMem : ByteArray}
    (digest v r s : UInt256)
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverInputMem baseMem digest v r s).size = 610 := by
  change (writeCascade baseMem
      (permitRuntimeEcrecoverInputWrites digest v r s)).size = 610
  exact writeCascade_size_of_base baseMem (permitRuntimeEcrecoverInputWrites digest v r s)
    hbaseSize (permitRuntimeEcrecoverInputWrites_gaps digest v r s)
    (permitRuntimeEcrecoverInputWrites_size digest v r s)

theorem permitRuntimeEcrecoverInputTail_disjoint64 (digest v r s : UInt256) :
    WindowDisjointFromWrites 482 64 32
      [(482, digest), (514, v), (546, r), (578, s)] := by
  simp [WindowDisjointFromWrites]

theorem permitRuntimeEcrecoverMem1_read64 {baseMem : ByteArray}
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverMem1 baseMem).readWithPadding 64 32 =
      UInt256.toByteArray (⟨482⟩ : UInt256) := by
  unfold permitRuntimeEcrecoverMem1
  exact writeCascade_read_word_of_head (permitRuntimeEcrecoverMem0 baseMem) 64
    (⟨482⟩ : UInt256) []
    (by
      rw [permitRuntimeEcrecoverMem0_size hbaseSize]
      native_decide)
    (by simp [WindowDisjointFromWrites])

theorem permitRuntimeEcrecoverInputMem_read64 {baseMem : ByteArray}
    (digest v r s : UInt256)
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding 64 32 =
      UInt256.toByteArray (⟨482⟩ : UInt256) := by
  change (writeCascade (permitRuntimeEcrecoverMem1 baseMem)
      [(482, digest), (514, v), (546, r), (578, s)]).readWithPadding 64 32 =
    UInt256.toByteArray (⟨482⟩ : UInt256)
  rw [writeCascade_read_preserved]
  · exact permitRuntimeEcrecoverMem1_read64 hbaseSize
  · rw [permitRuntimeEcrecoverMem1_size hbaseSize]
    exact permitRuntimeEcrecoverInputTail_disjoint64 digest v r s

theorem permitRuntimeEcrecoverInputMem_read450_zero {baseMem : ByteArray}
    (digest v r s : UInt256)
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding 450 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  change (writeCascade baseMem (permitRuntimeEcrecoverInputWrites digest v r s)).readWithPadding
    450 32 = UInt256.toByteArray (⟨0⟩ : UInt256)
  exact writeCascade_read_word_of_head baseMem 450 (⟨0⟩ : UInt256)
    [(64, (⟨482⟩ : UInt256)), (482, digest), (514, v), (546, r), (578, s)]
    (by rw [hbaseSize]; native_decide)
    (by simp [WindowDisjointFromWrites])

theorem permitRuntimeEcrecoverInputMem_read450_tail_zero {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450) (_hshort : o.size < 32) :
    (permitRuntimeEcrecoverInputMem baseMem digest v r s).extract (450 + o.size) 482 =
      (UInt256.toByteArray (⟨0⟩ : UInt256)).extract o.size 32 := by
  have hslot := permitRuntimeEcrecoverInputMem_read450_zero digest v r s hbaseSize
  have hslotExtract :
      (permitRuntimeEcrecoverInputMem baseMem digest v r s).extract 450 482 =
        UInt256.toByteArray (⟨0⟩ : UInt256) := by
    rw [← readWithPadding_eq_extract _ 450]
    · exact hslot
    · rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]
      omega
  have h := congrArg (fun b : ByteArray => b.extract o.size 32) hslotExtract
  simpa [extract_extract_BA, _hshort] using h

theorem permitRuntimeEcrecoverInputMem_mload64 {baseMem : ByteArray}
    (digest v r s : UInt256)
    (hbaseSize : baseMem.size = 450) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (permitRuntimeEcrecoverInputMem baseMem digest v r s).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 20 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨482⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]
      decide)
    (by native_decide)
    (permitRuntimeEcrecoverInputMem_read64 digest v r s hbaseSize)

theorem permitRuntimeEcrecoverInputMem_read482 {baseMem : ByteArray}
    (digest v r s : UInt256)
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding 482 32 =
      UInt256.toByteArray digest := by
  change (writeCascade (permitRuntimeEcrecoverMem1 baseMem)
      [(482, digest), (514, v), (546, r), (578, s)]).readWithPadding 482 32 =
    UInt256.toByteArray digest
  exact writeCascade_read_word_of_head (permitRuntimeEcrecoverMem1 baseMem)
    482 digest [(514, v), (546, r), (578, s)]
    (by
      rw [permitRuntimeEcrecoverMem1_size hbaseSize]
      norm_num)
    (by
      rw [permitRuntimeEcrecoverMem1_size hbaseSize]
      simp [WindowDisjointFromWrites])

theorem permitRuntimeEcrecoverInputMem_read514 {baseMem : ByteArray}
    (digest v r s : UInt256)
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding 514 32 =
      UInt256.toByteArray v := by
  change (writeCascade (permitRuntimeEcrecoverMem2 baseMem digest)
      [(514, v), (546, r), (578, s)]).readWithPadding 514 32 =
    UInt256.toByteArray v
  exact writeCascade_read_word_of_head (permitRuntimeEcrecoverMem2 baseMem digest)
    514 v [(546, r), (578, s)]
    (by
      rw [permitRuntimeEcrecoverMem2_size digest hbaseSize]
      norm_num)
    (by
      rw [permitRuntimeEcrecoverMem2_size digest hbaseSize]
      simp [WindowDisjointFromWrites])

theorem permitRuntimeEcrecoverInputMem_read546 {baseMem : ByteArray}
    (digest v r s : UInt256)
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding 546 32 =
      UInt256.toByteArray r := by
  change (writeCascade (permitRuntimeEcrecoverMem3 baseMem digest v)
      [(546, r), (578, s)]).readWithPadding 546 32 =
    UInt256.toByteArray r
  exact writeCascade_read_word_of_head (permitRuntimeEcrecoverMem3 baseMem digest v)
    546 r [(578, s)]
    (by
      rw [permitRuntimeEcrecoverMem3_size digest v hbaseSize]
      norm_num)
    (by
      rw [permitRuntimeEcrecoverMem3_size digest v hbaseSize]
      simp [WindowDisjointFromWrites])

theorem permitRuntimeEcrecoverInputMem_read578 {baseMem : ByteArray}
    (digest v r s : UInt256)
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding 578 32 =
      UInt256.toByteArray s := by
  unfold permitRuntimeEcrecoverInputMem
  exact writeCascade_read_word_of_head (permitRuntimeEcrecoverMem4 baseMem digest v r)
    578 s []
    (by
      rw [permitRuntimeEcrecoverMem4_size digest v r hbaseSize]
      norm_num)
    (by simp [WindowDisjointFromWrites])

theorem permitRuntimeEcrecoverInputMem_read482_128 {baseMem : ByteArray}
    (digest v r s : UInt256)
    (hbaseSize : baseMem.size = 450) :
    (permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding 482 128 =
      UInt256.toByteArray digest ++ UInt256.toByteArray v ++
        UInt256.toByteArray r ++ UInt256.toByteArray s := by
  rw [byteArray_readWithPadding_split _ 482 32 96 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize])]
  rw [byteArray_readWithPadding_split _ 514 32 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize])]
  rw [byteArray_readWithPadding_split _ 546 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize])]
  rw [permitRuntimeEcrecoverInputMem_read482 digest v r s hbaseSize,
    permitRuntimeEcrecoverInputMem_read514 digest v r s hbaseSize,
    permitRuntimeEcrecoverInputMem_read546 digest v r s hbaseSize,
    permitRuntimeEcrecoverInputMem_read578 digest v r s hbaseSize]
  simp only [ByteArray.append_assoc]

noncomputable def permitRuntimeEcrecoverStaticcallMem (baseMem : ByteArray)
    (digest v r s : UInt256) (o : ByteArray) : ByteArray :=
  o.write 0 (permitRuntimeEcrecoverInputMem baseMem digest v r s) 450
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

theorem permitRuntimeEcrecoverStaticcallWriteLen_of_size_ge (o : ByteArray)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 := by
  exact umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) ho32 hoSize

theorem permitRuntimeEcrecoverStaticcallWriteLen_of_size_lt (o : ByteArray)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size := by
  simpa using
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide) hshort hoSize

theorem permitRuntimeEcrecoverStaticcallMem_size_of_size_ge {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).size = 610 := by
  unfold permitRuntimeEcrecoverStaticcallMem
  rw [permitRuntimeEcrecoverStaticcallWriteLen_of_size_ge o ho32 hoSize]
  rw [write32_eq _ _ _ ho32
      (by rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]
  omega

theorem permitRuntimeEcrecoverStaticcallMem_size_of_size_lt {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).size = 610 := by
  unfold permitRuntimeEcrecoverStaticcallMem
  rw [permitRuntimeEcrecoverStaticcallWriteLen_of_size_lt o hshort hoSize]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero,
      permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]
  · rw [write_eq_gen _ _ 450 o.size hzero le_rfl
      (by rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract,
      permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]
    omega

theorem permitRuntimeEcrecoverStaticcallMem_read64_of_size_ge {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).readWithPadding 64 32 =
      UInt256.toByteArray (⟨482⟩ : UInt256) := by
  unfold permitRuntimeEcrecoverStaticcallMem
  rw [permitRuntimeEcrecoverStaticcallWriteLen_of_size_ge o ho32 hoSize]
  rw [write32_read_below _ _ 450 64 ho32
      (by rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]; omega)
      (by omega)]
  exact permitRuntimeEcrecoverInputMem_read64 digest v r s hbaseSize

theorem permitRuntimeEcrecoverStaticcallMem_read64_of_size_lt {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).readWithPadding 64 32 =
      UInt256.toByteArray (⟨482⟩ : UInt256) := by
  unfold permitRuntimeEcrecoverStaticcallMem
  rw [permitRuntimeEcrecoverStaticcallWriteLen_of_size_lt o hshort hoSize]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact permitRuntimeEcrecoverInputMem_read64 digest v r s hbaseSize
  · rw [write_read_below_gen _ _ 450 o.size 64 hzero le_rfl
      (by rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]; omega)
      (by omega)]
    exact permitRuntimeEcrecoverInputMem_read64 digest v r s hbaseSize

theorem permitRuntimeEcrecoverStaticcallMem_mload64_of_size_ge {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 20 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨482⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [permitRuntimeEcrecoverStaticcallMem_size_of_size_ge digest v r s o hbaseSize
        ho32 hoSize]
      decide)
    (by native_decide)
    (permitRuntimeEcrecoverStaticcallMem_read64_of_size_ge digest v r s o hbaseSize
      ho32 hoSize)

theorem permitRuntimeEcrecoverStaticcallMem_mload64_of_size_lt {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 20 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨482⟩ :=
  mloadWordValue_of_readWithPadding
    (by
      rw [permitRuntimeEcrecoverStaticcallMem_size_of_size_lt digest v r s o hbaseSize
        hshort hoSize]
      decide)
    (by native_decide)
    (permitRuntimeEcrecoverStaticcallMem_read64_of_size_lt digest v r s o hbaseSize
      hshort hoSize)

theorem empty_readWithPadding32_eq_zeroWord :
    ByteArray.empty.readWithPadding 0 32 = UInt256.toByteArray (⟨0⟩ : UInt256) := by
  native_decide

theorem byteArray_readWithPadding0_short_eq_extract_zero_tail (o : ByteArray)
    (hzero : o.size ≠ 0) (hshort : o.size < 32) :
    o.readWithPadding 0 32 =
      o.extract 0 o.size ++ (UInt256.toByteArray (⟨0⟩ : UInt256)).extract o.size 32 := by
  symm
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [show (o.readWithPadding 0 32).data.toList = (o.readWithPadding 0 32).toList by
    rw [← byteArray_toList_eq]]
  rw [readWithPadding_zero_toList_of_size_lt32 o hzero hshort]
  rw [ByteArray.toList_data_append]
  rw [show (o.extract 0 o.size).data.toList = o.data.toList by
    rw [← byteArray_toList_eq, byteArray_extract_self, byteArray_toList_eq]]
  rw [byteArray_toList_eq]
  rw [zero_toByteArray_eq_zeroes32]
  rw [ByteArray.data_extract, Array.toList_extract, byteArray_zeroes_toList]
  rw [List.extract_eq_take_drop, List.drop_replicate, List.take_replicate]
  congr 1
  rw [min_self]

theorem permitRuntimeEcrecoverStaticcallMem_read450_of_size_lt {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).readWithPadding 450 32 =
      o.readWithPadding 0 32 := by
  unfold permitRuntimeEcrecoverStaticcallMem
  rw [permitRuntimeEcrecoverStaticcallWriteLen_of_size_lt o hshort hoSize]
  by_cases hzero : o.size = 0
  · have hoempty : o = ByteArray.empty := byteArray_eq_empty_of_size_eq_zero o hzero
    rw [hoempty, show ByteArray.empty.size = 0 by rfl, byteArray_write_len_zero,
      permitRuntimeEcrecoverInputMem_read450_zero digest v r s hbaseSize]
    exact empty_readWithPadding32_eq_zeroWord.symm
  · rw [write_eq_gen _ _ 450 o.size hzero le_rfl
      (by rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]; omega)]
    rw [readWithPadding_eq_extract _ 450]
    · rw [ByteArray.append_assoc]
      rw [extract_append_right_window]
      · have hprefixSize :
            ((permitRuntimeEcrecoverInputMem baseMem digest v r s).extract 0 450).size =
              450 := by
          rw [ByteArray.size_extract,
            permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]
          omega
        have hoExtractSize : (o.extract 0 o.size).size = o.size := by
          rw [ByteArray.size_extract]
          omega
        rw [extract_append_span]
        · rw [hprefixSize, hoExtractSize]
          rw [show 450 - 450 = 0 by omega]
          rw [← hoExtractSize, byteArray_extract_self]
          rw [byteArray_extract_self]
          rw [show 450 + 32 - 450 - o.size = 32 - o.size by omega]
          rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]
          rw [extract_extract_BA]
          rw [show 450 + o.size + 0 = 450 + o.size by omega]
          rw [show min (450 + o.size + (32 - o.size)) 610 = 482 by omega]
          rw [permitRuntimeEcrecoverInputMem_read450_tail_zero digest v r s o hbaseSize
            hshort]
          conv_lhs =>
            rw [← byteArray_extract_self o]
          rw [byteArray_readWithPadding0_short_eq_extract_zero_tail o hzero hshort]
          rw [byteArray_extract_self, hoExtractSize]
        · rw [hprefixSize]
          omega
        · rw [hprefixSize, hoExtractSize]
          omega
      · rw [ByteArray.size_extract]
        rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]
        omega
    · rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract,
        permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]
      omega

theorem permitRuntimeEcrecoverStaticcallMem_mload450_of_size_lt {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size) :
    (if (⟨450⟩ : UInt256).toNat ≥
          (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).size
        ∨ (⟨450⟩ : UInt256) ≥ UInt256.ofNat 20 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).readWithPadding
          (⟨450⟩ : UInt256).toNat 32)))
      =
        UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) := by
  rw [if_neg]
  · rw [show (⟨450⟩ : UInt256).toNat = 450 from by native_decide,
      permitRuntimeEcrecoverStaticcallMem_read450_of_size_lt digest v r s o hbaseSize
        hshort hoSize]
  · rw [not_or]
    constructor
    · rw [permitRuntimeEcrecoverStaticcallMem_size_of_size_lt digest v r s o hbaseSize
        hshort hoSize]
      native_decide
    · native_decide

theorem permitRuntimeEcrecoverStaticcallMem_read450_of_size_ge {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).readWithPadding 450 32 =
      o.extract 0 32 := by
  unfold permitRuntimeEcrecoverStaticcallMem
  rw [permitRuntimeEcrecoverStaticcallWriteLen_of_size_ge o ho32 hoSize]
  exact write32_read_back o (permitRuntimeEcrecoverInputMem baseMem digest v r s) 450 ho32
    (by rw [permitRuntimeEcrecoverInputMem_size digest v r s hbaseSize]; omega)

theorem permitRuntimeEcrecoverStaticcallMem_mload450_of_size_ge {baseMem : ByteArray}
    (digest v r s : UInt256) (o : ByteArray)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (if (⟨450⟩ : UInt256).toNat ≥
          (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).size
        ∨ (⟨450⟩ : UInt256) ≥ UInt256.ofNat 20 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o).readWithPadding
          (⟨450⟩ : UInt256).toNat 32)))
      = UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨450⟩ : UInt256).toNat = 450 from by native_decide,
      permitRuntimeEcrecoverStaticcallMem_read450_of_size_ge digest v r s o hbaseSize
        ho32 hoSize]
  · rw [not_or]
    constructor
    · rw [permitRuntimeEcrecoverStaticcallMem_size_of_size_ge digest v r s o hbaseSize
        ho32 hoSize]
      native_decide
    · native_decide

end UniswapV2Pair
