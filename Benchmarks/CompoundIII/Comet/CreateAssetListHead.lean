import Benchmarks.CompoundIII.Comet.CreateAssetListMemory
import Benchmarks.CompoundIII.Comet.CreationBlocks_004

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: bounded natural addition before packing an EVM word.
theorem u256_ofNat_add_eq {a b : Nat} (h : a + b < UInt256.size) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
  apply u256_inj
  exact (uadd_ofNat_toNat (by omega) (by omega) h).trans (UInt256.toNat_ofNat_of_lt h).symm

def createAssetListEvmStack (c : ConstructorConfig) (ptr : Nat) (factory : UInt256)
    (i : Nat) (R : List UInt256) : List UInt256 :=
  UInt256.ofNat i :: UInt256.ofNat c.assetConfigs.length ::
    UInt256.ofNat (constructorAssetEntry c i) :: UInt256.ofNat (ptr + 68 + 224 * i) ::
    UInt256.ofNat ptr :: factory :: UInt256.ofNat ptr :: R

theorem createAssetListHead_eq {c : ConstructorConfig} {mem : ByteArray} {ptr : Nat}
    (hm : ConstructorDataMemory c mem) (hn : c.assetConfigs.length ≤ 24)
    (hlo : constructorAssetFree c c.assetConfigs.length ≤ ptr) (hp : ptr + 68 < 2^64)
    (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr)
    (factory : UInt256) (R : List UInt256) :
    cometWithExtendedAssetListCreation_block_1308_stack (mem := mem)
      (x1 := UInt256.ofNat (constructorRecordBase c)) (x2 := factory) (R := R) =
        createAssetListEvmStack c ptr factory 0 R ∧
    cometWithExtendedAssetListCreation_block_1308_memory (mem := mem)
      (x1 := UInt256.ofNat (constructorRecordBase c)) = createAssetListHeadMemory c mem ptr := by
  have hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size := by
    change _ < 2^256
    omega
  have ha := hm.assets hsize
  rw [← u256_add_comm (UInt256.ofNat 640)] at ha
  have hpn : (UInt256.ofNat ptr).toNat = ptr :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hadd (n : Nat) (hn : n ≤ 68) :
      (UInt256.ofNat ptr + UInt256.ofNat n).toNat = ptr + n := by
    exact uadd_ofNat_toNat (by change _ < 2^256; omega) (by change _ < 2^256; omega)
      (by change _ < 2^256; omega)
  have hm1 := hm.writeAbove createAssetListSelectorWord hlo
  have hm2 := hm1.writeAbove (UInt256.ofNat 32) (off := ptr + 4) (by omega)
  have hc := hm2.assetCount hsize
  unfold createAssetListSelectorWord at hc
  have hwrite (mem : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 mem off 32 = writeWord mem off word := rfl
  unfold cometWithExtendedAssetListCreation_block_1308_stack
    cometWithExtendedAssetListCreation_block_1308_memory
  simp (disch := decide) only [ha, hptr, hpn, hwrite, hadd, hc]
  constructor
  · rw [u256_ofNat_add_eq (show constructorArrayBase c + 32 < UInt256.size by
      unfold constructorArrayBase constructorRecordBase; change _ < 2^256; omega),
      u256_ofNat_add_eq (show ptr + 68 < UInt256.size by change _ < 2^256; omega)]
    rfl
  · unfold createAssetListHeadMemory callTwoWordMemory callWordMemory createAssetListSelectorWord
    rw [hpn, hadd 4 (by decide), hadd 36 (by decide)]

theorem cometCreateAssetListHead {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {c : ConstructorConfig} {ptr : Nat} {factory : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hm : ConstructorDataMemory c mem)
    (hn : c.assetConfigs.length ≤ 24) (hlo : constructorAssetFree c c.assetConfigs.length ≤ ptr)
    (hp : ptr + 68 < 2^64) (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1308⟩
      (UInt256.ofNat 640 :: UInt256.ofNat (constructorRecordBase c) :: factory :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1358⟩
      (createAssetListEvmStack c ptr factory 0 R) (createAssetListEvmMemory c mem ptr 0)
      aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h'⟩ := cometWithExtendedAssetListCreation_block_1308_packed hstack h
  have he := createAssetListHead_eq hm hn hlo hp hptr factory R
  rw [he.1, he.2] at h'
  exact ⟨aw', k', C', h'⟩

end Benchmarks.CompoundIII.Comet
