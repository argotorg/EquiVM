import Benchmarks.UniswapV3Pool.BurnPositionUpdate

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev burnPositionUpdateRevertFreePtr : UInt256 :=
  burnPositionKeyNewFreePtrWord + (⟨160⟩ : UInt256)

def burnPositionUpdateNpRevertWord : UInt256 :=
  UInt256.shiftLeft (⟨1253⟩ : UInt256) ⟨244⟩

noncomputable abbrev burnPositionUpdateNpRevertMem0 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) : ByteArray :=
  writeWord (burnPositionUpdateMem5 σ I pos0 posBase)
    burnPositionUpdateRevertFreePtr.toNat solcErrorStringSelector

noncomputable abbrev burnPositionUpdateNpRevertMem1 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) : ByteArray :=
  writeWord (burnPositionUpdateNpRevertMem0 σ I pos0 posBase)
    (burnPositionUpdateRevertFreePtr + (⟨4⟩ : UInt256)).toNat (⟨32⟩ : UInt256)

noncomputable abbrev burnPositionUpdateNpRevertMem2 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) : ByteArray :=
  writeWord (burnPositionUpdateNpRevertMem1 σ I pos0 posBase)
    (burnPositionUpdateRevertFreePtr + (⟨36⟩ : UInt256)).toNat (⟨2⟩ : UInt256)

noncomputable abbrev burnPositionUpdateNpRevertMem3 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) : ByteArray :=
  writeWord (burnPositionUpdateNpRevertMem2 σ I pos0 posBase)
    (burnPositionUpdateRevertFreePtr + (⟨68⟩ : UInt256)).toNat
    burnPositionUpdateNpRevertWord

theorem burnPositionUpdateNpRevertMem0_size (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateNpRevertMem0 σ I pos0 posBase).size = 730 := by
  unfold burnPositionUpdateNpRevertMem0 burnPositionUpdateRevertFreePtr
  rw [writeWord_size _ _ _
    (by rw [burnPositionUpdateMem5_size σ I pos0 posBase]; native_decide)]
  rw [burnPositionUpdateMem5_size σ I pos0 posBase]
  native_decide

theorem burnPositionUpdateNpRevertMem1_size (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateNpRevertMem1 σ I pos0 posBase).size = 734 := by
  unfold burnPositionUpdateNpRevertMem1 burnPositionUpdateRevertFreePtr
  rw [writeWord_size _ _ _
    (by rw [burnPositionUpdateNpRevertMem0_size σ I pos0 posBase]; native_decide)]
  rw [burnPositionUpdateNpRevertMem0_size σ I pos0 posBase]
  native_decide

theorem burnPositionUpdateNpRevertMem2_size (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateNpRevertMem2 σ I pos0 posBase).size = 766 := by
  unfold burnPositionUpdateNpRevertMem2 burnPositionUpdateRevertFreePtr
  rw [writeWord_size _ _ _
    (by rw [burnPositionUpdateNpRevertMem1_size σ I pos0 posBase]; native_decide)]
  rw [burnPositionUpdateNpRevertMem1_size σ I pos0 posBase]
  native_decide

theorem burnPositionUpdateNpRevertMem3_size (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateNpRevertMem3 σ I pos0 posBase).size = 798 := by
  unfold burnPositionUpdateNpRevertMem3 burnPositionUpdateRevertFreePtr
  rw [writeWord_size _ _ _
    (by rw [burnPositionUpdateNpRevertMem2_size σ I pos0 posBase]; native_decide)]
  rw [burnPositionUpdateNpRevertMem2_size σ I pos0 posBase]
  native_decide

theorem burnPositionUpdateNpRevertMem3_read64 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (burnPositionUpdateNpRevertMem3 σ I pos0 posBase).readWithPadding 64 32 =
      UInt256.toByteArray burnPositionUpdateRevertFreePtr := by
  unfold burnPositionUpdateNpRevertMem3
  rw [writeWord_read_preserved
    (burnPositionUpdateNpRevertMem2 σ I pos0 posBase)
    (burnPositionUpdateRevertFreePtr + (⟨68⟩ : UInt256)).toNat
    64 burnPositionUpdateNpRevertWord
    (by rw [burnPositionUpdateNpRevertMem2_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateNpRevertMem2_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateNpRevertMem2
  rw [writeWord_read_preserved
    (burnPositionUpdateNpRevertMem1 σ I pos0 posBase)
    (burnPositionUpdateRevertFreePtr + (⟨36⟩ : UInt256)).toNat
    64 (⟨2⟩ : UInt256)
    (by rw [burnPositionUpdateNpRevertMem1_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateNpRevertMem1_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateNpRevertMem1
  rw [writeWord_read_preserved
    (burnPositionUpdateNpRevertMem0 σ I pos0 posBase)
    (burnPositionUpdateRevertFreePtr + (⟨4⟩ : UInt256)).toNat
    64 (⟨32⟩ : UInt256)
    (by rw [burnPositionUpdateNpRevertMem0_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateNpRevertMem0_size σ I pos0 posBase]; native_decide)]
  unfold burnPositionUpdateNpRevertMem0
  rw [writeWord_read_preserved
    (burnPositionUpdateMem5 σ I pos0 posBase)
    burnPositionUpdateRevertFreePtr.toNat
    64 solcErrorStringSelector
    (by rw [burnPositionUpdateMem5_size σ I pos0 posBase]; native_decide)
    (by rw [burnPositionUpdateMem5_size σ I pos0 posBase]; native_decide)]
  simpa [burnPositionUpdateRevertFreePtr] using
    burnPositionUpdateMem5_read64 σ I pos0 posBase

theorem burnPositionUpdateNpRevertMem3_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (pos0 posBase : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (burnPositionUpdateNpRevertMem3 σ I pos0 posBase).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 25 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnPositionUpdateNpRevertMem3 σ I pos0 posBase).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      burnPositionUpdateRevertFreePtr := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionUpdateNpRevertMem3 σ I pos0 posBase) (aw := UInt256.ofNat 25)
    (off := ⟨64⟩) (v := burnPositionUpdateRevertFreePtr)
    (by rw [burnPositionUpdateNpRevertMem3_size σ I pos0 posBase]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using burnPositionUpdateNpRevertMem3_read64 σ I pos0 posBase)

private theorem uniswapV3PoolBurnPositionUpdateRevertDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 21661 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21801) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 21801 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

private theorem uniswapV3PoolBurnPositionUpdateNpRevertTailWf
    {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    solcErrorStringRevertTailWf code ⟨21661⟩ ⟨2⟩ ⟨1253⟩ ⟨244⟩ .PUSH2 2 := by
  dsimp [solcErrorStringRevertTailWf]
  repeat' constructor
  all_goals
    rw [uniswapV3PoolBurnPositionUpdateRevertDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide

theorem uniswapV3PoolBurnPositionUpdateNpRevertTail {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pos0 posBase : UInt256} {stk : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21661⟩ stk
      (burnPositionUpdateMem5 σ ee pos0 posBase) (UInt256.ofNat 22)
      rdata (cA, σ) k C)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases uniswapV3PoolBurnPositionUpdateNpRevertTailWf hpatch with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 burnPositionUpdateRevertFreePtr (UInt256.ofNat 22) hd3
      mem_cost
      (by
        simpa [burnPositionUpdateRevertFreePtr] using
          burnPositionUpdateMem5_mload64 σ ee pos0 posBase)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 4 (burnPositionUpdateNpRevertMem0 σ ee pos0 posBase)
      (UInt256.ofNat 23) hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (burnPositionUpdateNpRevertMem1 σ ee pos0 posBase)
      (UInt256.ofNat 23) hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨2⟩ hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (burnPositionUpdateNpRevertMem2 σ ee pos0 posBase)
      (UInt256.ofNat 24) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst (⟨1253⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) hd27
    (by simp only [List.length_cons]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨244⟩ hdRawOut (by evm_ov),
    raw shl hdShl (by evm_ov)]
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd68 (by evm_ov),
    raw dup3 hdDup3 (by evm_ov),
    raw add hdAdd (by evm_ov),
    raw mstore 3 (burnPositionUpdateNpRevertMem3 σ ee pos0 posBase)
      (UInt256.ofNat 25) hdMstore3 mem_cost
      (by rfl)
      (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 burnPositionUpdateRevertFreePtr (UInt256.ofNat 25) hdMload
      mem_cost
      (burnPositionUpdateNpRevertMem3_mload64 σ ee pos0 posBase)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

end Benchmarks.UniswapV3Pool
