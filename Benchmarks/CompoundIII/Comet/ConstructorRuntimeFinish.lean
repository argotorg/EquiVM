import Benchmarks.CompoundIII.Comet.ConstructorFinalImms

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem constructorRuntimeWords_key (w : Nat → UInt256) {i : Nat} (hi : i < 25) :
    constructorRuntimeWords w ((immutableReferences.map Prod.fst).getD i "") =
      w (128 + 32 * i) := by
  interval_cases i <;> rfl

theorem constructorFinalMemory_runtime {c : ConstructorConfig} {w : UInt256}
    {out feed factoryOut assetOut : ByteArray} (hn : c.assetConfigs.length ≤ 24)
    (hw : w.toNat ≤ 18) (ha : (calldataWord assetOut 0).toNat < 2^160)
    (hout : out.size < UInt256.size) (hfeed : feed.size < UInt256.size)
    (hf : factoryOut.size < UInt256.size) (hasize : assetOut.size < UInt256.size) :
    immutableLayout.runtime cometWithExtendedAssetListBytecode
      (constructorRuntimeWords fun off ↦
        memLoad (UInt256.ofNat off) (constructorFinalMemory c w out feed factoryOut assetOut)) =
    immutableLayout.deployed cometWithExtendedAssetListBytecode
      (constructorFinalImms c w (calldataWord assetOut 0)) := by
  have hkeys : ∀ site ∈ immutableLayout.sites, ∃ i : Fin 25,
      site.2.2 = (immutableReferences.map Prod.fst).getD i.val "" := by decide
  apply Layout.runtime_congr
  intro site hsite
  obtain ⟨i, hi⟩ := hkeys site hsite
  rw [hi, constructorRuntimeWords_key _ i.isLt]
  exact (constructorFinalMemory_word i.isLt hn hout hfeed hf hasize).trans
    (constructorFinalImms_word i.isLt hw ha).symm

theorem cometConstructorDeployReturn {c : ConstructorConfig} {w : UInt256}
    {out feed factoryOut assetOut tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {aw discard : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hn : c.assetConfigs.length ≤ 24) (hw : w.toNat ≤ 18)
    (ha : (calldataWord assetOut 0).toNat < 2^160) (hout : out.size < UInt256.size)
    (hfeed : feed.size < UInt256.size) (hf : factoryOut.size < UInt256.size)
    (hasize : assetOut.size < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1410⟩
      (discard :: calldataWord assetOut 0 :: R)
      (constructorFactoryReturnMemory (constructorAssetsInputMemory c w out feed factoryOut)
        assetOut (UInt256.ofNat (constructorAssetsPtr c))) aw assetOut σ k C) :
    RDret (cometWithExtendedAssetListCreationBytecode ++ tail) g s0 σ
      (immutableLayout.deployed cometWithExtendedAssetListBytecode
        (constructorFinalImms c w (calldataWord assetOut 0))) := by
  let ptr := UInt256.ofNat (constructorAssetsPtr c) + UInt256.ofNat 32
  have hb := constructorAssetsPtr_fits hn
  have hp : ptr.toNat = constructorAssetsPtr c + 32 := by
    dsimp only [ptr]
    rw [uadd_word_ofNat_toNat _ _ (by
      rw [constructorAssetsPtr_toNat hn]; change _ < 2^256; omega),
      constructorAssetsPtr_toNat hn]
  have hlo : 928 ≤ ptr.toNat := by
    rw [hp]
    unfold constructorAssetsPtr constructorAssetFree constructorArrayEnd constructorArrayBase
      constructorRecordBase
    omega
  have hinput := constructorAssetsInputMemory_size (w := w) (out := out) (feed := feed)
    (factoryOut := factoryOut) hn
  have hin : ptr.toNat ≤
      (constructorFactoryReturnMemory (constructorAssetsInputMemory c w out feed factoryOut)
        assetOut (UInt256.ofNat (constructorAssetsPtr c))).size := by
    unfold constructorFactoryReturnMemory
    rw [writeWord_sparse_size, callOutput32_size _ _ _ hasize (by
      rw [constructorAssetsPtr_toNat hn]; omega), hp]
    omega
  have hptr : memLoad (UInt256.ofNat 64)
      (constructorFactoryReturnMemory (constructorAssetsInputMemory c w out feed factoryOut)
        assetOut (UInt256.ofNat (constructorAssetsPtr c))) = ptr :=
    memLoad_writeWord_self _ (UInt256.ofNat 64) ptr
  have hr := cometConstructorRuntimeReturn
    (w := fun off ↦ memLoad (UInt256.ofNat off)
      (constructorFinalMemory c w out feed factoryOut assetOut)) hstack
    (le_trans hlo hin) hlo hin (by rw [hp]; change _ < 2^256; omega) hptr
    (fun _ _ _ ↦ rfl) h
  rwa [constructorFinalMemory_runtime hn hw ha hout hfeed hf hasize] at hr

end Benchmarks.CompoundIII.Comet
