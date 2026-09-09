import Examples.UniswapV2Pair.MutatorDispatch
import Examples.UniswapV2Pair.Routines
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace Reasoning.Reach

open Reasoning.Theory

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

theorem RD.dup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP12, .none)) (hov : t.length + 13 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (ll :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => dup12_xstep hc hp hdec hs hov)

end Reasoning.Reach

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
    (by decide +native)
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
    (by decide +native)
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
    (by decide +native)
    (permitRuntimeStructHashMem_read64 owner spender value nonce deadline hbaseSize)

theorem permitRuntimeStructHashDataMem0_size {baseMem : ByteArray}
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem0 baseMem).size = 192 := by
  unfold permitRuntimeStructHashDataMem0
  exact writeCascade_size_of_base baseMem [(160, permitRuntimeTypehashWord)] hbaseSize
    (by simp [WriteGapsOk]; decide +native) (by simp [writeCascadeSize])

theorem permitRuntimeStructHashDataMem1_size {baseMem : ByteArray} (owner : UInt256)
    (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem1 baseMem owner).size = 224 := by
  unfold permitRuntimeStructHashDataMem1
  exact writeCascade_size_of_base baseMem [(160, permitRuntimeTypehashWord), (192, owner)]
    hbaseSize (by simp [WriteGapsOk]; decide +native) (by simp [writeCascadeSize])

theorem permitRuntimeStructHashDataMem2_size {baseMem : ByteArray}
    (owner spender : UInt256) (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem2 baseMem owner spender).size = 256 := by
  unfold permitRuntimeStructHashDataMem2
  exact writeCascade_size_of_base baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender)] hbaseSize
    (by simp [WriteGapsOk]; decide +native) (by simp [writeCascadeSize])

theorem permitRuntimeStructHashDataMem3_size {baseMem : ByteArray}
    (owner spender value : UInt256) (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem3 baseMem owner spender value).size = 288 := by
  unfold permitRuntimeStructHashDataMem3
  exact writeCascade_size_of_base baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender), (256, value)]
    hbaseSize (by simp [WriteGapsOk]; decide +native) (by simp [writeCascadeSize])

theorem permitRuntimeStructHashDataMem4_size {baseMem : ByteArray}
    (owner spender value nonce : UInt256) (hbaseSize : baseMem.size = 96) :
    (permitRuntimeStructHashDataMem4 baseMem owner spender value nonce).size = 320 := by
  unfold permitRuntimeStructHashDataMem4
  exact writeCascade_size_of_base baseMem
    [(160, permitRuntimeTypehashWord), (192, owner), (224, spender), (256, value),
      (288, nonce)] hbaseSize
    (by simp [WriteGapsOk]; decide +native) (by simp [writeCascadeSize])

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
    (by rw [hbaseSize]; decide +native)
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
    (by rw [permitRuntimeStructHashDataMem0_size hbaseSize]; decide +native)
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
  all_goals decide +native

theorem permitRuntimeDigestDataWrites_size (domain structHash : UInt256) :
    writeCascadeSize 352 (permitRuntimeDigestDataWrites domain structHash) = 450 := by
  rfl

theorem permitRuntimeDigestDataWrites_disjoint64 (domain structHash : UInt256) :
    WindowDisjointFromWrites 352 64 32
      (permitRuntimeDigestDataWrites domain structHash) := by
  simp [WindowDisjointFromWrites, permitRuntimeDigestDataWrites]
  all_goals decide +native

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
    (by decide +native)
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
    (by decide +native)
    (permitRuntimeDigestMem_read352 domain structHash hbaseSize)

theorem permitRuntimeDigestDataMem0_size {baseMem : ByteArray}
    (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestDataMem0 baseMem).size = 416 := by
  unfold permitRuntimeDigestDataMem0
  exact writeCascade_size_of_base baseMem [(384, permitRuntimeDigestPrefixWord)] hbaseSize
    (by simp [WriteGapsOk]; decide +native) (by simp [writeCascadeSize])

theorem permitRuntimeDigestDataMem1_size {baseMem : ByteArray}
    (domain : UInt256) (hbaseSize : baseMem.size = 352) :
    (permitRuntimeDigestDataMem1 baseMem domain).size = 418 := by
  unfold permitRuntimeDigestDataMem1
  exact writeCascade_size_of_base baseMem [(384, permitRuntimeDigestPrefixWord), (386, domain)]
    hbaseSize (by simp [WriteGapsOk]; decide +native) (by simp [writeCascadeSize])

theorem permitRuntimeDigestPrefix_read0_2 :
    (UInt256.toByteArray permitRuntimeDigestPrefixWord).extract 0 2 =
      ByteArray.mk #[0x19, 0x01] := by
  decide +native

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
    (by rw [hbaseSize]; decide +native)
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
    (by rw [permitRuntimeDigestDataMem0_size hbaseSize]; decide +native)
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
    (by rw [permitRuntimeDigestDataMem1_size domain hbaseSize]; decide +native)
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
      decide +native)
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
    (by rw [hbaseSize]; decide +native)
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
    (by decide +native)
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
    (by decide +native)
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
    (by decide +native)
    (permitRuntimeEcrecoverStaticcallMem_read64_of_size_lt digest v r s o hbaseSize
      hshort hoSize)

theorem empty_readWithPadding32_eq_zeroWord :
    ByteArray.empty.readWithPadding 0 32 = UInt256.toByteArray (⟨0⟩ : UInt256) := by
  decide +native

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
  · rw [show (⟨450⟩ : UInt256).toNat = 450 from by decide +native,
      permitRuntimeEcrecoverStaticcallMem_read450_of_size_lt digest v r s o hbaseSize
        hshort hoSize]
  · rw [not_or]
    constructor
    · rw [permitRuntimeEcrecoverStaticcallMem_size_of_size_lt digest v r s o hbaseSize
        hshort hoSize]
      decide +native
    · decide +native

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
  · rw [show (⟨450⟩ : UInt256).toNat = 450 from by decide +native,
      permitRuntimeEcrecoverStaticcallMem_read450_of_size_ge digest v r s o hbaseSize
        ho32 hoSize]
  · rw [not_or]
    constructor
    · rw [permitRuntimeEcrecoverStaticcallMem_size_of_size_ge digest v r s o hbaseSize
        ho32 hoSize]
      decide +native
    · decide +native

set_option maxHeartbeats 2000000 in
theorem RD.uniswapPermitStructHash {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {nonce owner spender value deadline domain s r v ret : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5589⟩
      (nonce :: ⟨1⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        domain :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hbaseSize : baseMem.size = 96)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨128⟩ : UInt256))
    (hspenderMask : UInt256.land spender solcAddrMask = spender)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5688⟩
      (permitRuntimeStructHashWord baseMem owner spender value nonce deadline ::
        ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ ::
        domain :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeStructHashMem baseMem owner spender value nonce deadline)
      (UInt256.ofNat 11) rdata (cA, σ) k' C' := by
  have hbaseMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ baseMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (baseMem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadWordValue_of_readWithPadding
      (by rw [hbaseSize]; decide)
      (by decide +native)
      hbaseRead64
  have rd5591 := evm_run h with [
    dup3,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hbaseMload64 (by decide +native) (by evm_ov)]
  have rd5624 := rd5591.pushConst permitRuntimeTypehashWord (width := 32) (op := .PUSH32)
    (by decide +native) (by decide +native) (by evm_ov)
  have rd5627 := evm_run rd5624 with [dup2, dup7, add]
  have rd5628 := evm_run rd5627 with [
    raw mstore 9 (permitRuntimeStructHashDataMem0 baseMem)
      (UInt256.ofNat 6) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5634 := evm_run rd5628 with [
    dup1, dup5, add, swap7, swap1, swap7,
    raw mstore 3 (permitRuntimeStructHashDataMem1 baseMem owner)
      (UInt256.ofNat 7) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5638₀ := evm_run rd5634 with [swap6, dup14, and]
  have rd5638 := rd5638₀
  rw [hspenderMask] at rd5638
  have rd5643 := evm_run rd5638 with [
    push1 ⟨96⟩, dup7, add,
    raw mstore 3 (permitRuntimeStructHashDataMem2 baseMem owner spender)
      (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5650 := evm_run rd5643 with [
    push1 ⟨128⟩, dup6, add, dup13, swap1,
    raw mstore 3 (permitRuntimeStructHashDataMem3 baseMem owner spender value)
      (UInt256.ofNat 9) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5658 := evm_run rd5650 with [
    push1 ⟨160⟩, dup6, add, swap6, swap1, swap6,
    raw mstore 3 (permitRuntimeStructHashDataMem4 baseMem owner spender value nonce)
      (UInt256.ofNat 10) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5666 := evm_run rd5658 with [
    push1 ⟨192⟩, dup1, dup6, add, raw dup12 (by decide +native) (by evm_ov), swap1,
    raw mstore 3 (permitRuntimeStructHashDataMem baseMem owner spender value nonce deadline)
      (UInt256.ofNat 11) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5676 := evm_run rd5666 with [
    dup2,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by decide +native)
      mem_cost
      (permitRuntimeStructHashDataMem_mload64 owner spender value nonce deadline hbaseSize
        hbaseRead64)
      (by decide +native) (by evm_ov),
    dup1, dup7, sub, swap1, swap2, add, dup2,
    raw mstore 0 (permitRuntimeStructHashLenMem baseMem owner spender value nonce deadline)
      (UInt256.ofNat 11) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5682 := evm_run rd5676 with [
    push1 ⟨224⟩, dup6, add, dup3,
    raw mstore 0 (permitRuntimeStructHashMem baseMem owner spender value nonce deadline)
      (UInt256.ofNat 11) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5688 := evm_run rd5682 with [
    dup1,
    raw mload 0 ⟨192⟩ (UInt256.ofNat 11) (by decide +native)
      mem_cost
      (permitRuntimeStructHashMem_mload128 owner spender value nonce deadline hbaseSize)
      (by decide +native) (by evm_ov),
    swap1, dup4, add,
    raw keccak256 0
      (permitRuntimeStructHashWord baseMem owner spender value nonce deadline)
      (UInt256.ofNat 11) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  exact ⟨_, _, rd5688⟩

set_option maxHeartbeats 2000000 in
theorem RD.uniswapPermitDigestHash {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {structHash domain s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5688⟩
      (structHash :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ ::
        domain :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 11) rdata (cA, σ) k C)
    (hbaseSize : baseMem.size = 352)
    (hbaseRead64 :
      baseMem.readWithPadding 64 32 = UInt256.toByteArray (⟨352⟩ : UInt256))
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5746⟩
      (permitRuntimeDigestWord baseMem domain structHash ::
        ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ :: ⟨450⟩ ::
        s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeDigestMem baseMem domain structHash)
      (UInt256.ofNat 15) rdata (cA, σ) k' C' := by
  have rd5699 := evm_run h with [
    push2 ⟨6401⟩, push1 ⟨240⟩, shl, push2 ⟨256⟩, dup7, add,
    raw mstore 6 (permitRuntimeDigestDataMem0 baseMem)
      (UInt256.ofNat 13) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5708 := evm_run rd5699 with [
    push2 ⟨258⟩, dup6, add, swap7, swap1, swap7,
    raw mstore 3 (permitRuntimeDigestDataMem1 baseMem domain)
      (UInt256.ofNat 14) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5718 := evm_run rd5708 with [
    push2 ⟨290⟩, dup1, dup6, add, swap7, swap1, swap7,
    raw mstore 3 (permitRuntimeDigestDataMem baseMem domain structHash)
      (UInt256.ofNat 15) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5729 := evm_run rd5718 with [
    dup1,
    raw mload 0 ⟨352⟩ (UInt256.ofNat 15) (by decide +native)
      mem_cost
      (permitRuntimeDigestDataMem_mload64 domain structHash hbaseSize hbaseRead64)
      (by decide +native) (by evm_ov),
    dup1, dup6, sub, swap1, swap7, add, dup7,
    raw mstore 0 (permitRuntimeDigestLenMem baseMem domain structHash)
      (UInt256.ofNat 15) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5737 := evm_run rd5729 with [
    push2 ⟨322⟩, dup5, add, dup1, dup3,
    raw mstore 0 (permitRuntimeDigestMem baseMem domain structHash)
      (UInt256.ofNat 15) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5746 := evm_run rd5737 with [
    dup7,
    raw mload 0 ⟨66⟩ (UInt256.ofNat 15) (by decide +native)
      mem_cost
      (permitRuntimeDigestMem_mload352 domain structHash hbaseSize)
      (by decide +native) (by evm_ov),
    swap7, dup4, add, swap7, swap1, swap7,
    raw keccak256 0
      (permitRuntimeDigestWord baseMem domain structHash)
      (UInt256.ofNat 15) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  exact ⟨_, _, rd5746⟩

set_option maxHeartbeats 2000000 in
theorem RD.uniswapPermitEcrecoverStaticcallMade {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5746⟩
      (digest :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ :: ⟨450⟩ ::
        s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 15) rdata (cA, σ) k C)
    (hbaseSize : baseMem.size = 450)
    (hvMask : UInt256.land (⟨255⟩ : UInt256) v = v)
    (hdepth : ee.depth.val < 1024)
    (hov : R.length + 24 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (o : ByteArray) (A_in : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ ee.blobVersionedHashes cA
          s0.genesisBlockHeader s0.blocks σ s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat ee.codeOwner)) ee.sender
          (AccountAddress.ofUInt256 (⟨1⟩ : UInt256))
          (toExecute σ (AccountAddress.ofUInt256 (⟨1⟩ : UInt256)))
          callGas (UInt256.ofNat ee.gasPrice) ⟨0⟩ ⟨0⟩
          ((permitRuntimeEcrecoverInputMem baseMem digest v r s).readWithPadding 482 128)
          (ee.depth + 1) ee.header false)
      ∧ RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5814⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ ::
            digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
          (o.write 0 (permitRuntimeEcrecoverInputMem baseMem digest v r s) 450
            (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
          (UInt256.ofNat 20) o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  have rd5749 := evm_run h with [
    swap6, dup4, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem0 baseMem)
      (UInt256.ofNat 16) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5757 := evm_run rd5749 with [
    push2 ⟨354⟩, dup5, add, dup1, dup3,
    raw mstore 0 (permitRuntimeEcrecoverMem1 baseMem)
      (UInt256.ofNat 16) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5760 := evm_run rd5757 with [
    dup7, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem2 baseMem digest)
      (UInt256.ofNat 17) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5764₀ := evm_run rd5760 with [push1 ⟨255⟩, dup10, and]
  have rd5764 := rd5764₀
  rw [u256_land_comm v (⟨255⟩ : UInt256)] at rd5764
  rw [hvMask] at rd5764
  have rd5770 := evm_run rd5764 with [
    push2 ⟨386⟩, dup6, add,
    raw mstore 3 (permitRuntimeEcrecoverMem3 baseMem digest v)
      (UInt256.ofNat 18) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5778 := evm_run rd5770 with [
    push2 ⟨418⟩, dup5, add, dup9, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem4 baseMem digest v r)
      (UInt256.ofNat 19) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5787 := evm_run rd5778 with [
    push2 ⟨450⟩, dup5, add, dup8, swap1,
    raw mstore 3 (permitRuntimeEcrecoverInputMem baseMem digest v r s)
      (UInt256.ofNat 20) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  obtain ⟨gasArg, rd5813₀⟩ := evm_run rd5787 with [
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by decide +native)
      mem_cost
      (permitRuntimeEcrecoverInputMem_mload64 digest v r s hbaseSize)
      (by decide +native) (by evm_ov),
    swap2, swap4, swap3, push2 ⟨482⟩, dup1, dup3, add, swap4, push1 ⟨31⟩,
    not, dup2, add, swap3, dup2, swap1, sub, swap1, swap2, add, swap1, dup6, gas]
  have hInSize :
      (⟨482⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨482⟩ = ⟨128⟩ := by
    decide +native
  have hOutOffset : (⟨482⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨450⟩ := by
    decide +native
  have hTail : (⟨128⟩ : UInt256) + ⟨482⟩ = ⟨610⟩ := by
    decide +native
  have rd5813 := rd5813₀
  rw [hInSize, hOutOffset, hTail] at rd5813
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', htheta, rd5814, houtSize⟩ :=
    RD.solcStaticcall rd5813 (by decide +native) hdepth
      (by simp only [List.length_cons]; omega)
  have haw : UInt256.ofNat
        (MachineState.M
          (MachineState.M (UInt256.ofNat 20).toNat (⟨482⟩ : UInt256).toNat
            (⟨128⟩ : UInt256).toNat)
          (⟨450⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) =
      UInt256.ofNat 20 := by
    decide +native
  refine ⟨cA', σ', z, o, A_in, callGas, k', C', ?_, ?_, houtSize⟩
  · simpa using htheta
  · rw [haw] at rd5814
    simpa using rd5814

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverStaticcallDepthReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5746⟩
      (digest :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨1⟩ :: ⟨450⟩ ::
        s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      baseMem (UInt256.ofNat 15) rdata (cA, σ) k C)
    (hbaseSize : baseMem.size = 450)
    (hvMask : UInt256.land (⟨255⟩ : UInt256) v = v)
    (hdepth : ee.depth = 1024)
    (hov : R.length + 24 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd5749 := evm_run h with [
    swap6, dup4, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem0 baseMem)
      (UInt256.ofNat 16) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5757 := evm_run rd5749 with [
    push2 ⟨354⟩, dup5, add, dup1, dup3,
    raw mstore 0 (permitRuntimeEcrecoverMem1 baseMem)
      (UInt256.ofNat 16) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5760 := evm_run rd5757 with [
    dup7, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem2 baseMem digest)
      (UInt256.ofNat 17) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5764₀ := evm_run rd5760 with [push1 ⟨255⟩, dup10, and]
  have rd5764 := rd5764₀
  rw [u256_land_comm v (⟨255⟩ : UInt256)] at rd5764
  rw [hvMask] at rd5764
  have rd5770 := evm_run rd5764 with [
    push2 ⟨386⟩, dup6, add,
    raw mstore 3 (permitRuntimeEcrecoverMem3 baseMem digest v)
      (UInt256.ofNat 18) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5778 := evm_run rd5770 with [
    push2 ⟨418⟩, dup5, add, dup9, swap1,
    raw mstore 3 (permitRuntimeEcrecoverMem4 baseMem digest v r)
      (UInt256.ofNat 19) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rd5787 := evm_run rd5778 with [
    push2 ⟨450⟩, dup5, add, dup8, swap1,
    raw mstore 3 (permitRuntimeEcrecoverInputMem baseMem digest v r s)
      (UInt256.ofNat 20) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  obtain ⟨gasArg, rd5813₀⟩ := evm_run rd5787 with [
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by decide +native)
      mem_cost
      (permitRuntimeEcrecoverInputMem_mload64 digest v r s hbaseSize)
      (by decide +native) (by evm_ov),
    swap2, swap4, swap3, push2 ⟨482⟩, dup1, dup3, add, swap4, push1 ⟨31⟩,
    not, dup2, add, swap3, dup2, swap1, sub, swap1, swap2, add, swap1, dup6, gas]
  have hInSize :
      (⟨482⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨482⟩ = ⟨128⟩ := by
    decide +native
  have hOutOffset : (⟨482⟩ : UInt256) + UInt256.lnot ⟨31⟩ = ⟨450⟩ := by
    decide +native
  have hTail : (⟨128⟩ : UInt256) + ⟨482⟩ = ⟨610⟩ := by
    decide +native
  have rd5813 := rd5813₀
  rw [hInSize, hOutOffset, hTail] at rd5813
  obtain ⟨k', C', rd5814₀⟩ :=
    RD.solcStaticcallDepthLimit rd5813 (by decide +native) hdepth
      (by simp only [List.length_cons]; omega)
  have haw : UInt256.ofNat
        (MachineState.M
          (MachineState.M (UInt256.ofNat 20).toNat (⟨482⟩ : UInt256).toNat
            (⟨128⟩ : UInt256).toNat)
          (⟨450⟩ : UInt256).toNat (⟨32⟩ : UInt256).toNat) =
      UInt256.ofNat 20 := by
    decide +native
  have rd5814 := rd5814₀
  rw [haw] at rd5814
  have rd5814' : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5814⟩
      (⟨0⟩ :: ⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ :: digest :: s :: r :: v :: deadline ::
        value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s ByteArray.empty)
      (UInt256.ofNat 20) ByteArray.empty (cA, σ) k' C' := by
    simpa [permitRuntimeEcrecoverStaticcallMem] using rd5814
  exact RD.solcCallSuccessGuardMissing (okPc := ⟨5830⟩) rd5814' rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native)
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverReturnWordDecoded {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5832⟩
      (⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ :: digest :: s :: r :: v :: deadline :: value ::
        spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) o acc k C)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :: digest :: s :: r :: v ::
        deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) o acc k' C' := by
  have rd5839₀ := evm_run h with [
    pop, push1 ⟨64⟩,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by decide +native)
      mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload64_of_size_ge digest v r s o
        hbaseSize ho32 hoSize)
      (by decide +native) (by evm_ov),
    push1 ⟨31⟩, not, add]
  have hoff : UInt256.lnot (⟨31⟩ : UInt256) + ⟨482⟩ = ⟨450⟩ := by
    decide +native
  have rd5839 := rd5839₀
  rw [hoff] at rd5839
  have rd5844 := evm_run rd5839 with [
    raw mload 0 (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))
      (UInt256.ofNat 20) (by decide +native) mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload450_of_size_ge digest v r s o
        hbaseSize ho32 hoSize)
      (by decide +native) (by evm_ov),
    swap2, pop, pop]
  exact ⟨_, _, rd5844⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverReturnWordDecodedShort {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {baseMem o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5832⟩
      (⟨610⟩ :: ⟨1⟩ :: ⟨0⟩ :: digest :: s :: r :: v :: deadline :: value ::
        spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) o acc k C)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)) ::
        digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) o acc k' C' := by
  have rd5839₀ := evm_run h with [
    pop, push1 ⟨64⟩,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by decide +native)
      mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload64_of_size_lt digest v r s o
        hbaseSize hshort hoSize)
      (by decide +native) (by evm_ov),
    push1 ⟨31⟩, not, add]
  have hoff : UInt256.lnot (⟨31⟩ : UInt256) + ⟨482⟩ = ⟨450⟩ := by
    decide +native
  have rd5839 := rd5839₀
  rw [hoff] at rd5839
  have rd5844 := evm_run rd5839 with [
    raw mload 0 (UInt256.ofNat (fromByteArrayBigEndian (o.readWithPadding 0 32)))
      (UInt256.ofNat 20) (by decide +native) mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload450_of_size_lt digest v r s o
        hbaseSize hshort hoSize)
      (by decide +native) (by evm_ov),
    swap2, pop, pop]
  exact ⟨_, _, rd5844⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardOk {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata acc k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmatch : UInt256.land recovered solcAddrMask = UInt256.land owner solcAddrMask)
    (hov : R.length + 19 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5965⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata acc k' C' := by
  have rd5861₀ := evm_run h with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, iszero, dup1,
    iszero, swap1, push2 ⟨5884⟩]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hcond0 : UInt256.isZero (UInt256.land recovered
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [hmaskConst]
    exact Reasoning.Theory.isZero_eq_zero_of_ne hnz
  have rd5861 := rd5861₀
  rw [hcond0] at rd5861
  have rd5862 := evm_run rd5861 with [jumpiNT (by decide +native), pop]
  have rd5884₀ := evm_run rd5862 with [
    dup9, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup2,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, eq]
  have hmatch' :
      UInt256.land solcAddrMask recovered = UInt256.land solcAddrMask owner := by
    rw [u256_land_comm solcAddrMask recovered, u256_land_comm solcAddrMask owner]
    exact hmatch
  have heqWord : UInt256.eq
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) recovered)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) owner) =
      ⟨1⟩ := by
    rw [hmaskConst, hmatch']
    exact u256_eq_refl _
  have rd5884 := rd5884₀
  rw [heqWord] at rd5884
  have rd5965 := evm_run rd5884 with [
    jumpdest, push2 ⟨5965⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, rd5965⟩

theorem RD.uniswapPermitApproveSetup {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5965⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata (cA, σ) k C)
    (hov : R.length + 19 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7412⟩
      (value :: spender :: owner :: ⟨5976⟩ :: recovered :: digest :: s :: r :: v ::
        deadline :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata (cA, σ) k' C' := by
  have rd7412 := evm_run h with [
    jumpdest, push2 ⟨5976⟩, dup10, dup10, dup10, push2 ⟨7412⟩,
    jump (by jump_dest)]
  exact ⟨_, _, rd7412⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitApproveInnerHash20 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7412⟩
      (value :: spender :: owner :: ret :: R) mem (UInt256.ofNat 20) rdata (cA, σ) k C)
    (hmem : 96 ≤ mem.size)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7441⟩
      (mapSlot owner ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R)
      (twoWordHashMem owner ⟨2⟩ mem)
      (UInt256.ofNat 20) rdata (cA, σ) k' C' := by
  have hwf : solcNestedMappingStoreInnerHashWf UniswapV2Pair.uniswapV2PairBytecode
      (⟨7412⟩ : UInt256) (⟨2⟩ : UInt256) := by
    unfold solcNestedMappingStoreInnerHashWf
    repeat' first | apply And.intro | decide +native
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd7, hd8, hd9, hd10, hd11, hd12, hd14, hd15, hd16,
      hd17, hd19, hd21, hd22, hd23, hd24, hd26, hd27, hd28⟩
  have hmask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) owner =
        owner := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanonOwner
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner (⟨2⟩ : UInt256) mem).readWithPadding 0 64))) =
        mapSlot owner ⟨2⟩ :=
    twoWordHashMem_mapSlot_of_ge64 owner ⟨2⟩ (by omega)
  have rdMasked := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨1⟩ hd1 (by evm_ov),
    raw push1 ⟨1⟩ hd3 (by evm_ov),
    raw push1 ⟨160⟩ hd5 (by evm_ov),
    raw shl hd7 (by evm_ov),
    raw sub hd8 (by evm_ov),
    raw dup1 hd9 (by evm_ov),
    raw dup5 hd10 (by evm_ov),
    raw and hd11 (by evm_ov)]
  rw [u256_land_comm owner
    (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩), hmask] at rdMasked
  have rdMstore0Prefix := evm_run rdMasked with [
    raw push1 ⟨0⟩ hd12 (by evm_ov),
    raw dup2 hd14 (by evm_ov),
    raw dup2 hd15 (by evm_ov)]
  have rdInnerKey := rdMstore0Prefix.mstore 0 (wordAt0Mem owner mem)
    (UInt256.ofNat 20) hd16 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdInnerMemPrefix := evm_run rdInnerKey with [
    raw push1 ⟨2⟩ hd17 (by evm_ov),
    raw push1 ⟨32⟩ hd19 (by evm_ov),
    raw swap1 hd21 (by evm_ov),
    raw dup2 hd22 (by evm_ov)]
  have rdInnerMem := rdInnerMemPrefix.mstore 0 (twoWordHashMem owner ⟨2⟩ mem)
    (UInt256.ofNat 20) hd23 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdInnerHashPrefix := evm_run rdInnerMem with [
    raw push1 ⟨64⟩ hd24 (by evm_ov),
    raw dup1 hd26 (by evm_ov),
    raw dup4 hd27 (by evm_ov)]
  exact ⟨_, _, by
    simpa [solcNestedMappingStoreInnerHashOutPc] using
      rdInnerHashPrefix.keccak256 0 (mapSlot owner ⟨2⟩)
        (UInt256.ofNat 20) hd28 mem_cost hslot (by decide +native) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitApproveStore20 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7441⟩
      (mapSlot owner ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata (cA, σ) k C)
    (hmem : 96 ≤ mem.size)
    (hperm : ee.perm = true)
    (hcanonSpender : spender.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7457⟩
      (⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R)
      (twoWordHashMem spender (mapSlot owner ⟨2⟩) mem)
      (UInt256.ofNat 20) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (mapSlot spender (mapSlot owner ⟨2⟩)) value)
      k' C' := by
  have hwf : solcNestedMappingStoreOuterSstoreWf UniswapV2Pair.uniswapV2PairBytecode
      (⟨7441⟩ : UInt256) := by
    unfold solcNestedMappingStoreOuterSstoreWf
    repeat' first | apply And.intro | decide +native
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd12,
      hd13, hd14, hd15⟩
  have hmask : UInt256.land spender solcAddrMask = spender :=
    solcAddrMask_clean hcanonSpender
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem spender (mapSlot owner ⟨2⟩) mem).readWithPadding 0 64))) =
        mapSlot spender (mapSlot owner ⟨2⟩) :=
    twoWordHashMem_mapSlot_of_ge64 spender (mapSlot owner ⟨2⟩) (by omega)
  have rdMasked := evm_run h with [
    raw swap5 hd0 (by evm_ov),
    raw dup8 hd1 (by evm_ov),
    raw and hd2 (by evm_ov)]
  rw [hmask] at rdMasked
  have rdOuterKeyPrefix := evm_run rdMasked with [
    raw dup1 hd3 (by evm_ov),
    raw dup5 hd4 (by evm_ov)]
  have rdOuterKey := rdOuterKeyPrefix.mstore 0 (wordAt0Mem spender mem)
    (UInt256.ofNat 20) hd5 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdOuterMemPrefix := evm_run rdOuterKey with [
    raw swap5 hd6 (by evm_ov),
    raw dup3 hd7 (by evm_ov)]
  have rdOuterMem := rdOuterMemPrefix.mstore 0
    (twoWordHashMem spender (mapSlot owner ⟨2⟩) mem)
    (UInt256.ofNat 20) hd8 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdHashPrefix := evm_run rdOuterMem with [
    raw swap2 hd9 (by evm_ov),
    raw dup3 hd10 (by evm_ov),
    raw swap1 hd11 (by evm_ov)]
  have rdSlot := rdHashPrefix.keccak256 0 (mapSlot spender (mapSlot owner ⟨2⟩))
    (UInt256.ofNat 20) hd12 mem_cost hslot (by decide +native) (by evm_ov)
  have rdBeforeStore := evm_run rdSlot with [
    raw dup6 hd13 (by evm_ov),
    raw swap1 hd14 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdBeforeStore.sstore hperm hd15
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [solcNestedMappingStoreOuterSstoreOutPc] using rdOut⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitApproveEmitAndJump20 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7457⟩
      (⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R)
      mem (UInt256.ofNat 20) rdata acc k C)
    (hmem : 514 ≤ mem.size)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (hperm : ee.perm = true)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R
      ((UInt256.toByteArray value).write 0 mem 482 32)
      (UInt256.ofNat 20) rdata acc k' C' := by
  have hwf : solcPlainLog3AndJumpWf UniswapV2Pair.uniswapV2PairBytecode
      (⟨7457⟩ : UInt256) uniswapApprovalTopic := by
    unfold solcPlainLog3AndJumpWf
    repeat' first | apply And.intro | decide +native
  rcases hwf with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd40, hd41, hd42, hd43, hd44,
      hd45, hd46, hd47, hd48, hd49, hd50, hd51, hd52⟩
  have hmload :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 20 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨482⟩ := by
    rw [if_neg]
    · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide +native, hfree]
      rw [fromByteArrayBigEndian_toByteArray]
      exact u256_ofNat_toNat (⟨482⟩ : UInt256)
    · rw [not_or]
      exact ⟨by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide +native]; omega,
        by decide +native⟩
  have hlogRead64 :
      ((UInt256.toByteArray value).write 0 mem 482 32).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    rw [write32_read_below _ _ 482 64 (by rw [toByteArray_size])
      (by omega) (by omega)]
    exact hfree
  have hlogMload :
      (if (⟨64⟩ : UInt256).toNat ≥
            ((UInt256.toByteArray value).write 0 mem 482 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 20 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          (((UInt256.toByteArray value).write 0 mem 482 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32)))
        = ⟨482⟩ := by
    rw [if_neg]
    · rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide +native, hlogRead64]
      rw [fromByteArrayBigEndian_toByteArray]
      exact u256_ofNat_toNat (⟨482⟩ : UInt256)
    · rw [not_or]
      constructor
      · have hsize :
            ((UInt256.toByteArray value).write 0 mem 482 32).size = mem.size := by
          exact toByteArray_write32_size_of_le mem value 482 mem.size mem.size rfl
            (by omega) (by omega)
        rw [hsize]
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide +native]
        omega
      · decide +native
  have rd2 := evm_run h with [
    raw dup2 hd0 (by evm_ov),
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) hd1
      mem_cost hmload (by decide +native) (by evm_ov)]
  have rd4 := evm_run rd2 with [raw dup6 hd2 (by evm_ov), raw dup2 hd3 (by evm_ov)]
  have rd5 := rd4.mstore 0 ((UInt256.toByteArray value).write 0 mem 482 32)
    (UInt256.ofNat 20) hd4 mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rd7 := evm_run rd5 with [
    raw swap2 hd5 (by evm_ov),
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) hd6
      mem_cost hlogMload (by decide +native) (by evm_ov)]
  have rd40 := rd7.pushConst uniswapApprovalTopic (width := 32) (op := .PUSH32)
    (by decide) hd7 (by evm_ov)
  have rd48 := evm_run rd40 with [
    raw swap3 hd40 (by evm_ov),
    raw dup2 hd41 (by evm_ov),
    raw swap1 hd42 (by evm_ov),
    raw sub hd43 (by evm_ov),
    raw swap1 hd44 (by evm_ov),
    raw swap2 hd45 (by evm_ov),
    raw add hd46 (by evm_ov),
    raw swap1 hd47 (by evm_ov)]
  have rd49 := rd48.log3 0 (UInt256.ofNat 20) hd48 hperm mem_cost
    (by decide +native) (by simp only [List.length_cons]; omega)
  have rd52 := evm_run rd49 with [
    raw pop hd49 (by evm_ov),
    raw pop hd50 (by evm_ov),
    raw pop hd51 (by evm_ov)]
  exact ⟨_, _, rd52.jump hd52 hret (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitApproveAndReturn20 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {recovered digest s r v deadline value spender owner : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5965⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ⟨570⟩ :: R)
      mem (UInt256.ofNat 20) rdata (cA, σ) k C)
    (hmem : 514 ≤ mem.size)
    (hfree : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256))
    (hperm : ee.perm = true)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hcanonSpender : spender.toNat < EVM.addressModulus)
    (hov : R.length + 23 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0
      (cA, sstoreAccountMap ee.codeOwner σ (mapSlot spender (mapSlot owner ⟨2⟩)) value)
      ByteArray.empty := by
  obtain ⟨_, _, rd7412⟩ := RD.uniswapPermitApproveSetup
    (recovered := recovered) (digest := digest) (s := s) (r := r) (v := v)
    (deadline := deadline) (value := value) (spender := spender) (owner := owner)
    (ret := ⟨570⟩) (R := R) h (by omega)
  let Rtail := recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner ::
    (⟨570⟩ : UInt256) :: R
  obtain ⟨_, _, rd7441⟩ := RD.uniswapPermitApproveInnerHash20
    (value := value) (spender := spender) (owner := owner) (ret := ⟨5976⟩)
    (R := Rtail) rd7412 (by omega) hcanonOwner
    (by simp only [Rtail, List.length_cons]; omega)
  have hinnerSize :
      96 ≤ (twoWordHashMem owner (⟨2⟩ : UInt256) mem).size := by
    rw [twoWordHashMem_size_of_ge64 owner ⟨2⟩ (by omega)]
    omega
  have hinnerFree :
      (twoWordHashMem owner (⟨2⟩ : UInt256) mem).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    rw [twoWordHashMem_read64_of_ge96 owner ⟨2⟩ (by omega)]
    exact hfree
  obtain ⟨_, _, rd7457⟩ := RD.uniswapPermitApproveStore20
    (value := value) (spender := spender) (owner := owner) (ret := ⟨5976⟩)
    (R := Rtail) rd7441 hinnerSize hperm hcanonSpender
    (by simp only [Rtail, List.length_cons]; omega)
  have hstoreSize :
      514 ≤ (twoWordHashMem spender (mapSlot owner ⟨2⟩)
        (twoWordHashMem owner (⟨2⟩ : UInt256) mem)).size := by
    rw [twoWordHashMem_size_of_ge64 spender (mapSlot owner ⟨2⟩) (by omega)]
    rw [twoWordHashMem_size_of_ge64 owner ⟨2⟩ (by omega)]
    exact hmem
  have hstoreFree :
      (twoWordHashMem spender (mapSlot owner ⟨2⟩)
          (twoWordHashMem owner (⟨2⟩ : UInt256) mem)).readWithPadding 64 32 =
        UInt256.toByteArray (⟨482⟩ : UInt256) := by
    rw [twoWordHashMem_read64_of_ge96 spender (mapSlot owner ⟨2⟩) (by omega)]
    exact hinnerFree
  obtain ⟨_, _, rd5976⟩ := RD.uniswapPermitApproveEmitAndJump20
    (value := value) (spender := spender) (owner := owner) (ret := ⟨5976⟩)
    (R := recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner ::
      (⟨570⟩ : UInt256) :: R)
    (by simpa [Rtail] using rd7457) hstoreSize hstoreFree hperm (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd570 := evm_run rd5976 with [
    jumpdest, pop, pop, pop, pop, pop, pop, pop, pop, pop, jump (by jump_dest), jumpdest]
  exact rd570.stop (by decide +native) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitInvalidSignatureReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {digest v r s : UInt256} {stk : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5889⟩ stk
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hov : stk.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let mem := permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o
  have hmem : mem.size = 610 := by
    simpa [mem] using
      permitRuntimeEcrecoverStaticcallMem_size_of_size_ge digest v r s o hbaseSize ho32 hoSize
  have hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [mem] using
      permitRuntimeEcrecoverStaticcallMem_read64_of_size_ge digest v r s o hbaseSize ho32 hoSize
  have rd5893 := evm_run h with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by decide +native)
      mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload64_of_size_ge digest v r s o
        hbaseSize ho32 hoSize)
      (by decide +native) (by evm_ov)]
  let mem0 : ByteArray := (UInt256.toByteArray solcErrorStringSelector).write 0 mem 482 32
  have hmem0 : mem0.size = 610 := by
    unfold mem0
    exact toByteArray_write32_size_of_le mem solcErrorStringSelector 482 610 610
      hmem (by rw [hmem]; omega) (by omega)
  have rd5897 := rd5893.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide +native) (by decide +native) (by evm_ov)
  have rd5901 := evm_run rd5897 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 0 mem0 (UInt256.ofNat 20)
      (by decide +native) mem_cost
      (by unfold mem0 solcErrorStringSelector; rfl) (by decide +native) (by evm_ov)]
  let mem1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem0 486 32
  have hmem1 : mem1.size = 610 := by
    unfold mem1
    exact toByteArray_write32_size_of_le mem0 (⟨32⟩ : UInt256) 486 610 610
      hmem0 (by rw [hmem0]; omega) (by omega)
  have rd5908 := evm_run rd5901 with [
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 0 mem1 (UInt256.ofNat 20)
      (by decide +native) mem_cost (by unfold mem1; rfl) (by decide +native) (by evm_ov)]
  let mem2 : ByteArray := (UInt256.toByteArray (⟨28⟩ : UInt256)).write 0 mem1 518 32
  have hmem2 : mem2.size = 610 := by
    unfold mem2
    exact toByteArray_write32_size_of_le mem1 (⟨28⟩ : UInt256) 518 610 610
      hmem1 (by rw [hmem1]; omega) (by omega)
  have rd5915 := evm_run rd5908 with [
    push1 ⟨28⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 0 mem2 (UInt256.ofNat 20)
      (by decide +native) mem_cost (by unfold mem2; rfl) (by decide +native) (by evm_ov)]
  let invalidSignatureWord : UInt256 :=
    ⟨38641673103035791731704587899846419028922750264491344903186080211751768424448⟩
  let mem3 : ByteArray := (UInt256.toByteArray invalidSignatureWord).write 0 mem2 550 32
  have hmem3 : mem3.size = 610 := by
    unfold mem3
    exact toByteArray_write32_size_of_le mem2 invalidSignatureWord 550 610 610
      hmem2 (by rw [hmem2]; omega) (by omega)
  have hread64_mem0 :
      mem0.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem0
    rw [write32_read_below _ _ 482 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega)]
    exact hread64
  have hread64_mem1 :
      mem1.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem1
    rw [write32_read_below _ _ 486 64 (by rw [toByteArray_size])
      (by rw [hmem0]; omega) (by omega)]
    exact hread64_mem0
  have hread64_mem2 :
      mem2.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem2
    rw [write32_read_below _ _ 518 64 (by rw [toByteArray_size])
      (by rw [hmem1]; omega) (by omega)]
    exact hread64_mem1
  have hread64_mem3 :
      mem3.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem3
    rw [write32_read_below _ _ 550 64 (by rw [toByteArray_size])
      (by rw [hmem2]; omega) (by omega)]
    exact hread64_mem2
  have rd5949 := rd5915.pushConst invalidSignatureWord
    (width := 32) (op := .PUSH32) (by decide +native) (by decide +native) (by evm_ov)
  exact evm_run rd5949 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 0 mem3 (UInt256.ofNat 20)
      (by decide +native) mem_cost (by unfold mem3; rfl) (by decide +native) (by evm_ov),
    swap1,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by decide +native)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [hmem3]; decide) (by decide +native) hread64_mem3)
      (by decide +native) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by decide +native) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitInvalidSignatureRevertsShort {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {digest v r s : UInt256} {stk : List UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5889⟩ stk
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hov : stk.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  let mem := permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o
  have hmem : mem.size = 610 := by
    simpa [mem] using
      permitRuntimeEcrecoverStaticcallMem_size_of_size_lt digest v r s o hbaseSize hshort
        hoSize
  have hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    simpa [mem] using
      permitRuntimeEcrecoverStaticcallMem_read64_of_size_lt digest v r s o hbaseSize hshort
        hoSize
  have rd5893 := evm_run h with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by decide +native)
      mem_cost
      (permitRuntimeEcrecoverStaticcallMem_mload64_of_size_lt digest v r s o
        hbaseSize hshort hoSize)
      (by decide +native) (by evm_ov)]
  let mem0 : ByteArray := (UInt256.toByteArray solcErrorStringSelector).write 0 mem 482 32
  have hmem0 : mem0.size = 610 := by
    unfold mem0
    exact toByteArray_write32_size_of_le mem solcErrorStringSelector 482 610 610
      hmem (by rw [hmem]; omega) (by omega)
  have rd5897 := rd5893.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide +native) (by decide +native) (by evm_ov)
  have rd5901 := evm_run rd5897 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 0 mem0 (UInt256.ofNat 20)
      (by decide +native) mem_cost
      (by unfold mem0 solcErrorStringSelector; rfl) (by decide +native) (by evm_ov)]
  let mem1 : ByteArray := (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem0 486 32
  have hmem1 : mem1.size = 610 := by
    unfold mem1
    exact toByteArray_write32_size_of_le mem0 (⟨32⟩ : UInt256) 486 610 610
      hmem0 (by rw [hmem0]; omega) (by omega)
  have rd5908 := evm_run rd5901 with [
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 0 mem1 (UInt256.ofNat 20)
      (by decide +native) mem_cost (by unfold mem1; rfl) (by decide +native) (by evm_ov)]
  let mem2 : ByteArray := (UInt256.toByteArray (⟨28⟩ : UInt256)).write 0 mem1 518 32
  have hmem2 : mem2.size = 610 := by
    unfold mem2
    exact toByteArray_write32_size_of_le mem1 (⟨28⟩ : UInt256) 518 610 610
      hmem1 (by rw [hmem1]; omega) (by omega)
  have rd5915 := evm_run rd5908 with [
    push1 ⟨28⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 0 mem2 (UInt256.ofNat 20)
      (by decide +native) mem_cost (by unfold mem2; rfl) (by decide +native) (by evm_ov)]
  let invalidSignatureWord : UInt256 :=
    ⟨38641673103035791731704587899846419028922750264491344903186080211751768424448⟩
  let mem3 : ByteArray := (UInt256.toByteArray invalidSignatureWord).write 0 mem2 550 32
  have hmem3 : mem3.size = 610 := by
    unfold mem3
    exact toByteArray_write32_size_of_le mem2 invalidSignatureWord 550 610 610
      hmem2 (by rw [hmem2]; omega) (by omega)
  have hread64_mem0 :
      mem0.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem0
    rw [write32_read_below _ _ 482 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega)]
    exact hread64
  have hread64_mem1 :
      mem1.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem1
    rw [write32_read_below _ _ 486 64 (by rw [toByteArray_size])
      (by rw [hmem0]; omega) (by omega)]
    exact hread64_mem0
  have hread64_mem2 :
      mem2.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem2
    rw [write32_read_below _ _ 518 64 (by rw [toByteArray_size])
      (by rw [hmem1]; omega) (by omega)]
    exact hread64_mem1
  have hread64_mem3 :
      mem3.readWithPadding 64 32 = UInt256.toByteArray (⟨482⟩ : UInt256) := by
    unfold mem3
    rw [write32_read_below _ _ 550 64 (by rw [toByteArray_size])
      (by rw [hmem2]; omega) (by omega)]
    exact hread64_mem2
  have rd5949 := rd5915.pushConst invalidSignatureWord
    (width := 32) (op := .PUSH32) (by decide +native) (by decide +native) (by evm_ov)
  exact evm_run rd5949 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore 0 mem3 (UInt256.ofNat 20)
      (by decide +native) mem_cost (by unfold mem3; rfl) (by decide +native) (by evm_ov),
    swap1,
    raw mload 0 ⟨482⟩ (UInt256.ofNat 20) (by decide +native)
      mem_cost
      (mloadWordValue_of_readWithPadding
        (by rw [hmem3]; decide) (by decide +native) hread64_mem3)
      (by decide +native) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by decide +native) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardZeroReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hzero : UInt256.land recovered solcAddrMask = ⟨0⟩)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hov : R.length + 19 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd5861₀ := evm_run h with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, iszero, dup1,
    iszero, swap1, push2 ⟨5884⟩]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hcond1 : UInt256.isZero (UInt256.land recovered
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨1⟩ := by
    rw [hmaskConst, hzero]
    decide
  have rd5861 := rd5861₀
  rw [hcond1] at rd5861
  have rd5884₀ := evm_run rd5861 with [jumpiT one_ne_zero_uint (by jump_dest)]
  have hzeroBit : UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ := by
    decide +native
  have rd5884 := rd5884₀
  rw [hzeroBit] at rd5884
  have rd5889 := evm_run rd5884 with [
    jumpdest, push2 ⟨5965⟩, jumpiNT (by decide +native)]
  exact RD.uniswapPermitInvalidSignatureReverts
    (baseMem := baseMem) (digest := digest) (v := v) (r := r) (s := s)
    (o := o) rd5889 hbaseSize ho32 hoSize
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardMismatchReverts {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmismatch : UInt256.land recovered solcAddrMask ≠ UInt256.land owner solcAddrMask)
    (hbaseSize : baseMem.size = 450)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hov : R.length + 19 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd5861₀ := evm_run h with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, iszero, dup1,
    iszero, swap1, push2 ⟨5884⟩]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hcond0 : UInt256.isZero (UInt256.land recovered
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [hmaskConst]
    exact Reasoning.Theory.isZero_eq_zero_of_ne hnz
  have rd5861 := rd5861₀
  rw [hcond0] at rd5861
  have rd5862 := evm_run rd5861 with [jumpiNT (by decide +native), pop]
  have rd5884₀ := evm_run rd5862 with [
    dup9, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup2,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, eq]
  have hneq' :
      UInt256.land solcAddrMask recovered ≠ UInt256.land solcAddrMask owner := by
    intro hsame
    apply hmismatch
    simpa [u256_land_comm] using hsame
  have heqWord : UInt256.eq
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) recovered)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) owner) =
      ⟨0⟩ := by
    rw [hmaskConst]
    exact u256_eq_of_ne hneq'
  have rd5884 := rd5884₀
  rw [heqWord] at rd5884
  have rd5889 := evm_run rd5884 with [
    jumpdest, push2 ⟨5965⟩, jumpiNT (by decide +native)]
  exact RD.uniswapPermitInvalidSignatureReverts
    (baseMem := baseMem) (digest := digest) (v := v) (r := r) (s := s)
    (o := o) rd5889 hbaseSize ho32 hoSize
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardZeroRevertsShort {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hzero : UInt256.land recovered solcAddrMask = ⟨0⟩)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hov : R.length + 19 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd5861₀ := evm_run h with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, iszero, dup1,
    iszero, swap1, push2 ⟨5884⟩]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hcond1 : UInt256.isZero (UInt256.land recovered
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨1⟩ := by
    rw [hmaskConst, hzero]
    decide
  have rd5861 := rd5861₀
  rw [hcond1] at rd5861
  have rd5884₀ := evm_run rd5861 with [jumpiT one_ne_zero_uint (by jump_dest)]
  have hzeroBit : UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ := by
    decide +native
  have rd5884 := rd5884₀
  rw [hzeroBit] at rd5884
  have rd5889 := evm_run rd5884 with [
    jumpdest, push2 ⟨5965⟩, jumpiNT (by decide +native)]
  exact RD.uniswapPermitInvalidSignatureRevertsShort
    (baseMem := baseMem) (digest := digest) (v := v) (r := r) (s := s)
    (o := o) rd5889 hbaseSize hshort hoSize
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapPermitEcrecoverSignatureGuardMismatchRevertsShort {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {baseMem o rdata : ByteArray}
    {recovered digest s r v deadline value spender owner ret : UInt256}
    {R : List UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨5844⟩
      (recovered :: digest :: s :: r :: v :: deadline :: value :: spender :: owner :: ret :: R)
      (permitRuntimeEcrecoverStaticcallMem baseMem digest v r s o)
      (UInt256.ofNat 20) rdata acc k C)
    (hnz : UInt256.land recovered solcAddrMask ≠ ⟨0⟩)
    (hmismatch : UInt256.land recovered solcAddrMask ≠ UInt256.land owner solcAddrMask)
    (hbaseSize : baseMem.size = 450)
    (hshort : o.size < 32) (hoSize : o.size < UInt256.size)
    (hov : R.length + 19 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have rd5861₀ := evm_run h with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, iszero, dup1,
    iszero, swap1, push2 ⟨5884⟩]
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hcond0 : UInt256.isZero (UInt256.land recovered
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
    rw [hmaskConst]
    exact Reasoning.Theory.isZero_eq_zero_of_ne hnz
  have rd5861 := rd5861₀
  rw [hcond0] at rd5861
  have rd5862 := evm_run rd5861 with [jumpiNT (by decide +native), pop]
  have rd5884₀ := evm_run rd5862 with [
    dup9, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup2,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, eq]
  have hneq' :
      UInt256.land solcAddrMask recovered ≠ UInt256.land solcAddrMask owner := by
    intro hsame
    apply hmismatch
    simpa [u256_land_comm] using hsame
  have heqWord : UInt256.eq
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) recovered)
        (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) owner) =
      ⟨0⟩ := by
    rw [hmaskConst]
    exact u256_eq_of_ne hneq'
  have rd5884 := rd5884₀
  rw [heqWord] at rd5884
  have rd5889 := evm_run rd5884 with [
    jumpdest, push2 ⟨5965⟩, jumpiNT (by decide +native)]
  exact RD.uniswapPermitInvalidSignatureRevertsShort
    (baseMem := baseMem) (digest := digest) (v := v) (r := r) (s := s)
    (o := o) rd5889 hbaseSize hshort hoSize
    (by simp only [List.length_cons]; omega)

end UniswapV2Pair
