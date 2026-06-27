import Examples.UniswapV2Pair.Common
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `getReserves()` getter -/

abbrev getReservesSlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  uniswapSlotWord ⟨8⟩ σ I

abbrev reserve0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (getReservesSlotWord σ I) reserve112Mask

abbrev reserve1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (getReservesSlotWord σ I) reserve112Shift) reserve112Mask

abbrev blockTimestampLastWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (getReservesSlotWord σ I) reserve224Shift) reserve32Mask

theorem reserve112Word_lt (w : UInt256) :
    (UInt256.land w reserve112Mask).toNat < EVM.twoPow 112 := by
  rw [uland_toNat]
  have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by native_decide
  rw [hmask]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num [EVM.twoPow])

theorem reserve32Word_lt (w : UInt256) :
    (UInt256.land w reserve32Mask).toNat < EVM.twoPow 32 := by
  rw [uland_toNat]
  have hmask : reserve32Mask.toNat = 2 ^ 32 - 1 := by native_decide
  rw [hmask]
  exact lt_of_le_of_lt Nat.and_le_right (by norm_num [EVM.twoPow])

theorem reserve112Mask_clean_of_lt (w : UInt256) (h : w.toNat < EVM.twoPow 112) :
    UInt256.land w reserve112Mask = w := by
  apply u256_inj
  rw [uland_toNat]
  have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by native_decide
  rw [hmask]
  change Nat.land w.toNat (2 ^ 112 - 1) = w.toNat
  rw [nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow] using h)

theorem reserve32Mask_clean_of_lt (w : UInt256) (h : w.toNat < EVM.twoPow 32) :
    UInt256.land w reserve32Mask = w := by
  apply u256_inj
  rw [uland_toNat]
  have hmask : reserve32Mask.toNat = 2 ^ 32 - 1 := by native_decide
  rw [hmask]
  change Nat.land w.toNat (2 ^ 32 - 1) = w.toNat
  rw [nat_land_mask_eq_mod]
  exact Nat.mod_eq_of_lt (by simpa [EVM.twoPow] using h)

theorem getReservesReturnEncoding (r0 r1 ts : UInt256)
    (hr0 : r0.toNat < EVM.twoPow 112)
    (hr1 : r1.toNat < EVM.twoPow 112)
    (hts : ts.toNat < EVM.twoPow 32) :
    encodeReturnValue? (.tuple [uint112, uint112, uint32])
      (.tuple [.int (Int.ofNat r0.toNat), .int (Int.ofNat r1.toNat),
        .int (Int.ofNat ts.toNat)]) =
      some (UInt256.toByteArray r0 ++ UInt256.toByteArray r1 ++ UInt256.toByteArray ts) := by
  have hword0 : EVM.word r0.toNat = r0 := u256_ofNat_toNat r0
  have hword1 : EVM.word r1.toNat = r1 := u256_ofNat_toNat r1
  have hwordTs : EVM.word ts.toNat = ts := u256_ofNat_toNat ts
  have henc0 :
      encodeABIValue? uint112 (.int (Int.ofNat r0.toNat)) =
        some (EVM.Word.toBytesBE r0) := by
    simp [uint112, uint112Int, encodeABIValue?, encodeABIWord?, hword0, hr0]
  have henc1 :
      encodeABIValue? uint112 (.int (Int.ofNat r1.toNat)) =
        some (EVM.Word.toBytesBE r1) := by
    simp [uint112, uint112Int, encodeABIValue?, encodeABIWord?, hword1, hr1]
  have hencTs :
      encodeABIValue? uint32 (.int (Int.ofNat ts.toNat)) =
        some (EVM.Word.toBytesBE ts) := by
    simp [uint32, uint32Int, encodeABIValue?, encodeABIWord?, hwordTs, hts]
  have hheadInner : abiTupleHeadSize? [uint112, uint112, uint32] = some 96 := by
    native_decide
  have hheadOuter : abiTupleHeadSize? [(.tuple [uint112, uint112, uint32])] = some 96 := by
    native_decide
  have hdyn112 : isDynamicABIType uint112 = false := by native_decide
  have hdyn32 : isDynamicABIType uint32 = false := by native_decide
  have hdynTuple : isDynamicABIType (.tuple [uint112, uint112, uint32]) = false := by
    native_decide
  have hinner :
      encodeABIValue? (.tuple [uint112, uint112, uint32])
        (.tuple [.int (Int.ofNat r0.toNat), .int (Int.ofNat r1.toNat),
          .int (Int.ofNat ts.toNat)]) =
        some (EVM.Word.toBytesBE r0 ++ EVM.Word.toBytesBE r1 ++
          EVM.Word.toBytesBE ts) := by
    simp only [encodeABIValue?, encodeABIValues?, encodeABIValuesFrom?, hheadInner, henc0,
      henc1, hencTs, hdyn112, hdyn32, bind, Option.bind, Bool.false_eq_true, if_false,
      List.nil_append, List.append_nil]
  rw [toByteArray_eq_toBytesBE r0, toByteArray_eq_toBytesBE r1, toByteArray_eq_toBytesBE ts]
  simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?,
    hheadOuter, hinner, hdynTuple, bind, Option.bind, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem uniswapDecode_getReserves {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (getReservesTransition.params.map Param.name)
      (transitionSignature getReservesTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- The Solm `getReserves()` body returns the three packed values from slot 8. -/
theorem uniswapGetReservesBodyReturns (evm : EVM.State)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm ∅ getReservesTransition.body
      (.returned { contract := contract, locals := ∅ } evm
        (some (.tuple [
          .int (Int.ofNat (UInt256.land
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) reserve112Mask).toNat),
          .int (Int.ofNat (UInt256.land
            (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
              reserve112Shift) reserve112Mask).toNat),
          .int (Int.ofNat (UInt256.land
            (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
              reserve224Shift) reserve32Mask).toNat)]))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have hload0 :
          storageLocLoad evm (uint112Loc0 ⟨8⟩) =
            .int (Int.ofNat (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
              reserve112Mask).toNat) := by
        simpa using uniswapStorageLocLoad_uint112_offset0 evm ⟨8⟩
      have hload1 :
          storageLocLoad evm (uint112Loc14 ⟨8⟩) =
            .int (Int.ofNat (UInt256.land
              (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
                reserve112Shift) reserve112Mask).toNat) := by
        simpa using uniswapStorageLocLoad_uint112_offset14 evm ⟨8⟩
      have hloadTs :
          storageLocLoad evm (uint32Loc28 ⟨8⟩) =
            .int (Int.ofNat (UInt256.land
              (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩)
                reserve224Shift) reserve32Mask).toNat) := by
        simpa using uniswapStorageLocLoad_uint32_offset28 evm ⟨8⟩
      rw [evalExpr?, evalExprList?,
        evalExpr_storage_scalar (t := .int uint112Int) (slot := reserve0Ref)
          (er := ({ base := "reserve0", steps := [] } : EvaledStorageRef))
          (loc := uint112Loc0 ⟨8⟩)
          (hbase := by simp [reserve0Ref])
          (her := by simp [evalStorageRef, evalStorageRefSteps, reserve0Ref, EvalResult.bind,
            pure, bind])
          (hty := by rfl)
          (hloc := by rfl)]
      rw [evalExprList?,
        evalExpr_storage_scalar (t := .int uint112Int) (slot := reserve1Ref)
          (er := ({ base := "reserve1", steps := [] } : EvaledStorageRef))
          (loc := uint112Loc14 ⟨8⟩)
          (hbase := by simp [reserve1Ref])
          (her := by simp [evalStorageRef, evalStorageRefSteps, reserve1Ref, EvalResult.bind,
            pure, bind])
          (hty := by rfl)
          (hloc := by rfl)]
      rw [evalExprList?,
        evalExpr_storage_scalar (t := .int uint32Int) (slot := blockTimestampLastRef)
          (er := ({ base := "blockTimestampLast", steps := [] } : EvaledStorageRef))
          (loc := uint32Loc28 ⟨8⟩)
          (hbase := by simp [blockTimestampLastRef])
          (her := by simp [evalStorageRef, evalStorageRefSteps, blockTimestampLastRef,
            EvalResult.bind, pure, bind])
          (hty := by rfl)
          (hloc := by rfl)]
      simp [evalExprList?, EvalResult.bind, bind, pure, hload0, hload1, hloadTs])

/-! ## Return wrapper memory -/

noncomputable def getReservesReturn0Mem (r0 : UInt256) : ByteArray :=
  (UInt256.toByteArray r0).write 0 solcFreePtrMem 128 32

noncomputable def getReservesReturn1Mem (r0 r1 : UInt256) : ByteArray :=
  (UInt256.toByteArray r1).write 0 (getReservesReturn0Mem r0) 160 32

noncomputable def getReservesReturnMem (r0 r1 ts : UInt256) : ByteArray :=
  (UInt256.toByteArray ts).write 0 (getReservesReturn1Mem r0 r1) 192 32

theorem getReservesReturn0Mem_size (r0 : UInt256) :
    (getReservesReturn0Mem r0).size = 160 := by
  unfold getReservesReturn0Mem
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem getReservesReturn1Mem_size (r0 r1 : UInt256) :
    (getReservesReturn1Mem r0 r1).size = 192 := by
  unfold getReservesReturn1Mem
  rw [toByteArray_write_eq _ _ _ (by rw [getReservesReturn0Mem_size])
      (by rw [getReservesReturn0Mem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, getReservesReturn0Mem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem getReservesReturnMem_size (r0 r1 ts : UInt256) :
    (getReservesReturnMem r0 r1 ts).size = 224 := by
  unfold getReservesReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [getReservesReturn1Mem_size])
      (by rw [getReservesReturn1Mem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, getReservesReturn1Mem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (192 - 192)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem getReservesReturn0Mem_read64 (r0 : UInt256) :
    (getReservesReturn0Mem r0).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold getReservesReturn0Mem
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, solcFreePtrMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [solcFreePtrMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [solcFreePtrMem_size]), solcFreePtrMem_read64]

theorem getReservesReturnMem_read64 (r0 r1 ts : UInt256) :
    (getReservesReturnMem r0 r1 ts).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold getReservesReturnMem
  rw [write32_read_below _ _ 192 64 (by rw [toByteArray_size])
      (by rw [getReservesReturn1Mem_size]) (by omega)]
  unfold getReservesReturn1Mem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
      (by rw [getReservesReturn0Mem_size]) (by omega)]
  exact getReservesReturn0Mem_read64 r0

theorem getReservesReturnMem_mload64 (r0 r1 ts : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (getReservesReturnMem r0 r1 ts).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((getReservesReturnMem r0 r1 ts).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [getReservesReturnMem_size]; decide) (by decide)
    (getReservesReturnMem_read64 r0 r1 ts)

set_option maxHeartbeats 800000 in
theorem getReservesReturnMem_read128_96 (r0 r1 ts : UInt256) :
    (getReservesReturnMem r0 r1 ts).readWithPadding 128 96 =
      UInt256.toByteArray r0 ++ UInt256.toByteArray r1 ++ UInt256.toByteArray ts := by
  rw [readWithPadding_eq_extract' _ 128 96 (by norm_num) (by norm_num)
      (by rw [getReservesReturnMem_size])]
  unfold getReservesReturnMem
  rw [toByteArray_write_eq _ _ _ (by rw [getReservesReturn1Mem_size])
      (by rw [getReservesReturn1Mem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_span
      (getReservesReturn1Mem r0 r1 ++
        ffi.ByteArray.zeroes (USize.ofNat (192 - (getReservesReturn1Mem r0 r1).size)))
      (UInt256.toByteArray ts) 128 224 (by
        rw [ByteArray.size_append, getReservesReturn1Mem_size, ByteArray_zeroes_size,
          show (USize.ofNat (192 - 192)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega) (by
        rw [ByteArray.size_append, getReservesReturn1Mem_size, ByteArray_zeroes_size,
          show (USize.ofNat (192 - 192)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega)]
  rw [ByteArray.size_append, getReservesReturn1Mem_size, ByteArray_zeroes_size,
    show (USize.ofNat (192 - 192)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  rw [show ffi.ByteArray.zeroes (USize.ofNat (192 - 192)) = ByteArray.empty by
      exact zeroes_zero (n := USize.ofNat 0)
        (by exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)))]
  simp
  unfold getReservesReturn1Mem
  rw [toByteArray_write_eq _ _ _ (by rw [getReservesReturn0Mem_size])
      (by rw [getReservesReturn0Mem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_span
      (getReservesReturn0Mem r0 ++
        ffi.ByteArray.zeroes (USize.ofNat (160 - (getReservesReturn0Mem r0).size)))
      (UInt256.toByteArray r1) 128 192 (by
        rw [ByteArray.size_append, getReservesReturn0Mem_size, ByteArray_zeroes_size,
          show (USize.ofNat (160 - 160)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega) (by
        rw [ByteArray.size_append, getReservesReturn0Mem_size, ByteArray_zeroes_size,
          show (USize.ofNat (160 - 160)).toNat = 0 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
        omega)]
  rw [ByteArray.size_append, getReservesReturn0Mem_size, ByteArray_zeroes_size,
    show (USize.ofNat (160 - 160)).toNat = 0 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  rw [show ffi.ByteArray.zeroes (USize.ofNat (160 - 160)) = ByteArray.empty by
      exact zeroes_zero (n := USize.ofNat 0)
        (by exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)))]
  simp
  unfold getReservesReturn0Mem
  rw [toByteArray_write_eq _ _ _ (by rw [solcFreePtrMem_size]; omega)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by norm_num))]
  rw [extract_append_right_window
      (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat (128 - solcFreePtrMem.size)))
      (UInt256.toByteArray r0) 128 160 (by
        rw [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  repeat'
    first
    | rw [show (UInt256.toByteArray r0).extract 0 32 = UInt256.toByteArray r0 from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray r0).size ≤ 32
          rw [toByteArray_size])]
    | rw [show (UInt256.toByteArray r1).extract 0 32 = UInt256.toByteArray r1 from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray r1).size ≤ 32
          rw [toByteArray_size])]
    | rw [show (UInt256.toByteArray ts).extract 0 32 = UInt256.toByteArray ts from by
        apply ByteArray.ext
        rw [ByteArray.data_extract]
        exact Array.extract_eq_self_of_le (by
          change (UInt256.toByteArray ts).size ≤ 32
          rw [toByteArray_size])]

theorem getReservesRetLen_toNat :
    ((⟨96⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 96 := by
  decide

end UniswapV2Pair

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

/-! ## `getReserves()` runtime routines -/

set_option maxHeartbeats 1000000 in
theorem RD.uniswapGetReservesRoutine {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2852⟩ (ret :: R) mem aw rdata
        (cA, σ) k C)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (UniswapV2Pair.blockTimestampLastWord σ ee :: UniswapV2Pair.reserve1Word σ ee ::
        UniswapV2Pair.reserve0Word σ ee :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd2855 := evm_run h with [jumpdest, push1 ⟨8⟩]
  obtain ⟨_, _, rd2856⟩ := rd2855.sload (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2893 := evm_run rd2856 with [
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup1, dup3, and, swap3,
    push1 ⟨1⟩, push1 ⟨112⟩, shl, dup4, div, swap1, swap2, and, swap2,
    push1 ⟨1⟩, push1 ⟨224⟩, shl, swap1, div, push4 ⟨0xffffffff⟩, and, swap1]
  have rdRet := rd2893.jump (by native_decide) hret (by simp only [List.length_cons]; omega)
  rw [u256_land_comm UniswapV2Pair.reserve32Mask] at rdRet
  rw [u256_land_comm UniswapV2Pair.reserve112Mask] at rdRet
  exact ⟨_, _, by simpa [UniswapV2Pair.blockTimestampLastWord,
    UniswapV2Pair.reserve1Word, UniswapV2Pair.reserve0Word,
    UniswapV2Pair.getReservesSlotWord, UniswapV2Pair.uniswapSlotWord] using rdRet⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapReturnGetReserves705 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ts r1 r0 : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨705⟩ (ts :: r1 :: r0 :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 10 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc
      (UInt256.toByteArray (UInt256.land r0 UniswapV2Pair.reserve112Mask) ++
        UInt256.toByteArray (UInt256.land r1 UniswapV2Pair.reserve112Mask) ++
        UInt256.toByteArray (UInt256.land ts UniswapV2Pair.reserve32Mask)) := by
  let r0' := UInt256.land r0 UniswapV2Pair.reserve112Mask
  let r1' := UInt256.land r1 UniswapV2Pair.reserve112Mask
  let ts' := UInt256.land ts UniswapV2Pair.reserve32Mask
  have hmask112 : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ =
      UniswapV2Pair.reserve112Mask := by rfl
  have hmask32 : (⟨0xffffffff⟩ : UInt256) = UniswapV2Pair.reserve32Mask := by rfl
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, swap5, dup6, and, dup2,
    raw mstore 6 (UniswapV2Pair.getReservesReturn0Mem r0') (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [hmask112, u256_land_comm UniswapV2Pair.reserve112Mask r0]; rfl)
      (by decide) (by evm_ov),
    swap3, swap1, swap4, and, push1 ⟨32⟩, dup4, add,
    raw mstore 3 (UniswapV2Pair.getReservesReturn1Mem r0' r1') (UInt256.ofNat 6)
      (by decide) mem_cost
      (by
        rw [hmask112, u256_land_comm UniswapV2Pair.reserve112Mask r1,
          show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide]
        rfl)
      (by decide) (by evm_ov),
    push4 ⟨0xffffffff⟩, and, dup2, dup4, add,
    raw mstore 3 (UniswapV2Pair.getReservesReturnMem r0' r1' ts') (UInt256.ofNat 7)
      (by decide) mem_cost
      (by
        rw [hmask32, u256_land_comm UniswapV2Pair.reserve32Mask ts,
          show ((⟨64⟩ : UInt256) + ⟨128⟩).toNat = 192 from by decide]
        rfl)
      (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide)
      mem_cost
      (UniswapV2Pair.getReservesReturnMem_mload64 r0' r1' ts')
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨96⟩, add, swap1,
    raw ret 0 (UInt256.toByteArray r0' ++ UInt256.toByteArray r1' ++ UInt256.toByteArray ts')
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          UniswapV2Pair.getReservesRetLen_toNat]
        exact UniswapV2Pair.getReservesReturnMem_read128_96 r0' r1' ts')
      (by evm_ov)]

end Reasoning.Reach

namespace UniswapV2Pair

/-! ## EVM trace and refinement bridge -/

/-- From `getReserves()`'s external body entry (pc 697), the bytecode returns the packed values. -/
theorem uniswapX_getReserves {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD uniswapV2PairBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨697⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret uniswapV2PairBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (reserve0Word σ I) ++ UInt256.toByteArray (reserve1Word σ I) ++
        UInt256.toByteArray (blockTimestampLastWord σ I)) := by
  obtain ⟨_, _, rd2852⟩ := RD.uniswapGetterThunk (returnPc := ⟨705⟩) (routine := ⟨2852⟩)
    hreach uniswap_getter_entry_wf (by jump_dest)
  obtain ⟨_, _, rd705⟩ := RD.uniswapGetReservesRoutine (ret := ⟨705⟩) (R := [sel])
    rd2852 (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hret := RD.uniswapReturnGetReserves705
    (ts := blockTimestampLastWord σ I) (r1 := reserve1Word σ I) (r0 := reserve0Word σ I)
    (R := [sel]) rd705 (by simp only [List.length_singleton]; omega)
  have hclean0 : UInt256.land (reserve0Word σ I) reserve112Mask = reserve0Word σ I := by
    exact reserve112Mask_clean_of_lt _ (by
      simpa [reserve0Word] using reserve112Word_lt (getReservesSlotWord σ I))
  have hclean1 : UInt256.land (reserve1Word σ I) reserve112Mask = reserve1Word σ I := by
    exact reserve112Mask_clean_of_lt _ (by
      simpa [reserve1Word] using
        reserve112Word_lt (UInt256.div (getReservesSlotWord σ I) reserve112Shift))
  have hcleanTs :
      UInt256.land (blockTimestampLastWord σ I) reserve32Mask = blockTimestampLastWord σ I := by
    exact reserve32Mask_clean_of_lt _ (by
      simpa [blockTimestampLastWord] using
        reserve32Word_lt (UInt256.div (getReservesSlotWord σ I) reserve224Shift))
  simpa [hclean0, hclean1, hcleanTs] using hret

/-- `getReserves()` body core, parameterized by dispatcher/decode facts owned by `Correct`. -/
theorem uniswapGetReservesBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some getReservesTransition)
    (hdecode :
      decodeCalldata (getReservesTransition.params.map Param.name)
        (transitionSignature getReservesTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨697⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : getReservesSlotWord σ_evm I = getReservesSlotWord σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅
        getReservesTransition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some (.tuple [
            .int (Int.ofNat (reserve0Word σ_solm I).toNat),
            .int (Int.ofNat (reserve1Word σ_solm I).toNat),
            .int (Int.ofNat (blockTimestampLastWord σ_solm I).toNat)]))) := by
    simpa [reserve0Word, reserve1Word, blockTimestampLastWord, getReservesSlotWord,
      initState, Solm.EVM.storageLoad, State.lookupAccount] using
      uniswapGetReservesBodyReturns
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (by simp only [initState]; exact hwv)
  have hval :
      some (Value.tuple [
          .int (Int.ofNat (reserve0Word σ_solm I).toNat),
          .int (Int.ofNat (reserve1Word σ_solm I).toNat),
          .int (Int.ofNat (blockTimestampLastWord σ_solm I).toNat)]) =
        some (Value.tuple [
          .int (Int.ofNat (reserve0Word σ_evm I).toNat),
          .int (Int.ofNat (reserve1Word σ_evm I).toNat),
          .int (Int.ofNat (blockTimestampLastWord σ_evm I).toNat)]) := by
    have hslot : getReservesSlotWord σ_solm I = getReservesSlotWord σ_evm I := hword.symm
    simp [reserve0Word, reserve1Word, blockTimestampLastWord, hslot]
  have henc :
      returnEquiv
        (UInt256.toByteArray (reserve0Word σ_evm I) ++
          UInt256.toByteArray (reserve1Word σ_evm I) ++
          UInt256.toByteArray (blockTimestampLastWord σ_evm I))
        (some (.tuple [
          .int (Int.ofNat (reserve0Word σ_evm I).toNat),
          .int (Int.ofNat (reserve1Word σ_evm I).toNat),
          .int (Int.ofNat (blockTimestampLastWord σ_evm I).toNat)]))
        getReservesTransition.returnType := by
    rw [show getReservesTransition.returnType = some (.tuple [uint112, uint112, uint32]) from rfl]
    exact returnEquiv_of_encode
      (getReservesReturnEncoding (reserve0Word σ_evm I) (reserve1Word σ_evm I)
        (blockTimestampLastWord σ_evm I)
        (by simpa [reserve0Word] using reserve112Word_lt (getReservesSlotWord σ_evm I))
        (by
          simpa [reserve1Word] using
            reserve112Word_lt (UInt256.div (getReservesSlotWord σ_evm I) reserve112Shift))
        (by
          simpa [blockTimestampLastWord] using
            reserve32Word_lt (UInt256.div (getReservesSlotWord σ_evm I) reserve224Shift)))
  exact (uniswapX_getReserves (g := Sat256.ofUInt256 g) hreach)
    |>.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

end UniswapV2Pair
