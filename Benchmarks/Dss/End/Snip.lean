import Reasoning.SolcRoutines
import Reasoning.Storage
import Reasoning.ABIComposite
import Reasoning.Stepping
import Reasoning.Reach
import Benchmarks.Dss.End.Dispatch
import Benchmarks.Dss.End.Flow
import Benchmarks.Dss.End.Free

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.End

theorem endSnip_solcErrorStringMem0_size_of_size320 {mem : ByteArray}
    (hmem : mem.size = 320) :
    (solcErrorStringMem0 mem).size = 320 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract, hmem]

theorem endSnip_solcErrorStringMem1_size_of_size320 {mem : ByteArray}
    (hmem : mem.size = 320) :
    (solcErrorStringMem1 mem).size = 320 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endSnip_solcErrorStringMem0_size_of_size320 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    endSnip_solcErrorStringMem0_size_of_size320 hmem]

theorem endSnip_solcErrorStringMem2_size_of_size320 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 320) :
    (solcErrorStringMem2 len mem).size = 320 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endSnip_solcErrorStringMem1_size_of_size320 hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    endSnip_solcErrorStringMem1_size_of_size320 hmem]

theorem endSnip_solcErrorStringMem3_size_of_size320 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 320) :
    (solcErrorStringMem3 len word mem).size = 320 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endSnip_solcErrorStringMem2_size_of_size320 len hmem]; omega)]
  simp [toByteArray_size, ByteArray.size_append, ByteArray.size_extract,
    endSnip_solcErrorStringMem2_size_of_size320 len hmem]

theorem endSnip_solcErrorStringMem3_read64_of_size320 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [endSnip_solcErrorStringMem2_size_of_size320 len hmem]; omega) (by omega)
      (by
        rw [endSnip_solcErrorStringMem2_size_of_size320 len hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [endSnip_solcErrorStringMem1_size_of_size320 hmem]; omega) (by omega)
      (by
        rw [endSnip_solcErrorStringMem1_size_of_size320 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [endSnip_solcErrorStringMem0_size_of_size320 hmem]; omega) (by omega)
      (by
        rw [endSnip_solcErrorStringMem0_size_of_size320 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem endSnip_solcErrorStringMem3_mload64_of_size320 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [endSnip_solcErrorStringMem3_size_of_size320 len word hmem]; decide)
      (endSnip_solcErrorStringMem3_read64_of_size320 len word hmem hread64)

set_option maxHeartbeats 1000000 in
theorem endSnip_solcErrorStringRevertTail_aw10 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 10) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 320)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hdRawOut, hdShl, hd68,
      hdDup3, hdAdd, hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3,
      hdSub, hd100, hdAdd2, hdSwap4, hdRev⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 10)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 10)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 10) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
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
    raw mstore 0 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 10) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) hdMload
      mem_cost
      (endSnip_solcErrorStringMem3_mload64_of_size320 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

end Benchmarks.Dss.End

end

namespace Benchmarks.Dss.End

/-! ## `snip(bytes32,uint256)` transition -/

abbrev endSnipConcreteSelector : ByteArray := selectorBytes 0x38 0xc6 0xde 0x40

abbrev endSnipIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endSnipIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endSnipIdWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36

def endSnipStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (endSnipIlkBytes I))).insert
    "id" (.int (Int.ofNat (endSnipIdWord I).toNat))

theorem endSnipStore_get_ilk (I : ExecutionEnv) :
    (endSnipStore I).get? "ilk" = some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStore, store_get_ne _ _ (by native_decide), store_get_self]

abbrev endSnipIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endSnipTagEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "tag", steps := [.mindex (endSnipIlkKey I)] }

abbrev endSnipTagSlot (I : ExecutionEnv) : UInt256 := tagSlot (endSnipIlkKey I)

abbrev endSnipTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt (endSnipTagSlot I) σ I

abbrev endSnipDogWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWordAt ⟨3⟩ σ I) solcAddrMask

abbrev endSnipDogAddr (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (endSnipDogWord σ I).toNat

abbrev endSnipDogIlkClipWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev endSnipDogIlkChopWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev endSnipDogIlkHoleWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 64 96))

abbrev endSnipDogIlkDirtWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 96 128))

abbrev endSnipDogIlkClipAddr (out : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (endSnipDogIlkClipWord out).toNat

def endSnipStoreDogIlk (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endSnipStore I).insert "dogIlk"
    (.tuple [.address (endSnipDogIlkClipAddr out),
      .int (Int.ofNat (endSnipDogIlkChopWord out).toNat),
      .int (Int.ofNat (endSnipDogIlkHoleWord out).toNat),
      .int (Int.ofNat (endSnipDogIlkDirtWord out).toNat)])

def endSnipStoreClip (I : ExecutionEnv) (out : ByteArray) : Store :=
  (endSnipStoreDogIlk I out).insert "clip" (.address (endSnipDogIlkClipAddr out))

def endSnipDogIlksBaseMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (endSnipIlkWord I) ⟨12⟩ solcFreePtrMem

def endSnipDogIlksCalldataMem (I : ExecutionEnv) : ByteArray :=
  endFlowVatIlksCalldataMem I (endSnipDogIlksBaseMem I)

abbrev endSnipDogIlksOutSize : UInt256 := ⟨128⟩

def endSnipDogIlksPostCallMem (I : ExecutionEnv) (out : ByteArray) :
    ByteArray :=
  out.write 0 (endSnipDogIlksCalldataMem I) endFlowVatIlksOutPtr.toNat
    (min endSnipDogIlksOutSize.toNat out.size)

def endSnipStoreVatIlk (I : ExecutionEnv) (dogOut vatOut : ByteArray) : Store :=
  (endSnipStoreClip I dogOut).insert "vatIlk"
    (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord vatOut).toNat),
      .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat),
      .int (Int.ofNat (endFlowVatIlkSpotWord vatOut).toNat),
      .int (Int.ofNat (endFlowVatIlkLineWord vatOut).toNat),
      .int (Int.ofNat (endFlowVatIlkDustWord vatOut).toNat)])

def endSnipStoreRate (I : ExecutionEnv) (dogOut vatOut : ByteArray) : Store :=
  (endSnipStoreVatIlk I dogOut vatOut).insert "rate"
    (.int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat))

def endSnipVatIlksCalldataMem (I : ExecutionEnv) (dogOut : ByteArray) :
    ByteArray :=
  endFlowVatIlksCalldataMem I (endSnipDogIlksPostCallMem I dogOut)

def endSnipVatIlksPostCallMem (I : ExecutionEnv) (dogOut vatOut : ByteArray) :
    ByteArray :=
  vatOut.write 0 (endSnipVatIlksCalldataMem I dogOut) endFlowVatIlksOutPtr.toNat
    (min endFlowVatIlksOutSize.toNat vatOut.size)

abbrev endSnipSalesSelectorWord : UInt256 := ⟨0xb5f522f7⟩

abbrev endSnipSalesSelectorShifted : UInt256 :=
  ⟨0xb5f522f700000000000000000000000000000000000000000000000000000000⟩

abbrev endSnipSalesOutSize : UInt256 := ⟨192⟩

abbrev endSnipSalesClipWord (dogOut : ByteArray) : UInt256 :=
  UInt256.land solcAddrMask (endSnipDogIlkClipWord dogOut)

def endSnipSalesSelectorMem (I : ExecutionEnv) (dogOut vatOut : ByteArray) :
    ByteArray :=
  endSnipSalesSelectorShifted.toByteArray.write 0
    (endSnipVatIlksPostCallMem I dogOut vatOut) endFlowVatIlksOutPtr.toNat 32

def endSnipSalesCalldataMem (I : ExecutionEnv) (dogOut vatOut : ByteArray) :
    ByteArray :=
  (endSnipIdWord I).toByteArray.write 0 (endSnipSalesSelectorMem I dogOut vatOut)
    (endFlowVatIlksOutPtr + ⟨4⟩).toNat 32

def endSnipSalesPostCallMem
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  saleOut.write 0 (endSnipSalesCalldataMem I dogOut vatOut)
    endFlowVatIlksOutPtr.toNat (min endSnipSalesOutSize.toNat saleOut.size)

abbrev endSnipSalePosWord (saleOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (saleOut.extract 0 32))

abbrev endSnipSaleTabWord (saleOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (saleOut.extract 32 64))

abbrev endSnipSaleLotWord (saleOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (saleOut.extract 64 96))

abbrev endSnipSaleUsrWord (saleOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (saleOut.extract 96 128))

abbrev endSnipSaleUsrAddr (saleOut : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (endSnipSaleUsrWord saleOut).toNat

abbrev endSnipSaleUsrAddrWord (saleOut : ByteArray) : UInt256 :=
  UInt256.land solcAddrMask (endSnipSaleUsrWord saleOut)

abbrev endSnipSaleTicWord (saleOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (saleOut.extract 128 160))

abbrev endSnipSaleTopWord (saleOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (saleOut.extract 160 192))

def endSnipStoreClipSale (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) :
    Store :=
  (endSnipStoreRate I dogOut vatOut).insert "clipSale"
    (.tuple [.int (Int.ofNat (endSnipSalePosWord saleOut).toNat),
      .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat),
      .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
      .address (endSnipSaleUsrAddr saleOut),
      .int (Int.ofNat ((endSnipSaleTicWord saleOut).toNat % EVM.twoPow 96)),
      .int (Int.ofNat (endSnipSaleTopWord saleOut).toNat)])

def endSnipStoreTab (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) : Store :=
  (endSnipStoreClipSale I dogOut vatOut saleOut).insert "tab"
    (.int (Int.ofNat (endSnipSaleTabWord saleOut).toNat))

def endSnipStoreLot (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) : Store :=
  (endSnipStoreTab I dogOut vatOut saleOut).insert "lot"
    (.int (Int.ofNat (endSnipSaleLotWord saleOut).toNat))

def endSnipStoreUsr (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) : Store :=
  (endSnipStoreLot I dogOut vatOut saleOut).insert "usr"
    (.address (endSnipSaleUsrAddr saleOut))

abbrev endSnipSuckSelectorWord : UInt256 := ⟨0xf24e23eb⟩
abbrev endSnipSuckSelectorShifted : UInt256 :=
  ⟨0xf24e23eb00000000000000000000000000000000000000000000000000000000⟩
abbrev endSnipSuckOutPtr : UInt256 := ⟨128⟩
abbrev endSnipSuckInSize : UInt256 := ⟨100⟩
abbrev endSnipSuckOutSize : UInt256 := ⟨0⟩
abbrev endSnipSuckEndPtr : UInt256 := ⟨228⟩

abbrev endSnipYankSelectorWord : UInt256 := ⟨0x26e027f1⟩
abbrev endSnipYankSelectorShifted : UInt256 :=
  ⟨0x26e027f100000000000000000000000000000000000000000000000000000000⟩
abbrev endSnipYankOutPtr : UInt256 := ⟨128⟩
abbrev endSnipYankInSize : UInt256 := ⟨36⟩
abbrev endSnipYankOutSize : UInt256 := ⟨0⟩
abbrev endSnipYankEndPtr : UInt256 := ⟨164⟩

def endSnipStoreSuck (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) :
    Store :=
  (endSnipStoreUsr I dogOut vatOut saleOut).insert "_suck" (collapseReturns [])

def endSnipStoreYank (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) :
    Store :=
  (endSnipStoreSuck I dogOut vatOut saleOut).insert "_yank" (collapseReturns [])

abbrev endSnipArtWord (vatOut saleOut : ByteArray) : UInt256 :=
  UInt256.div (endSnipSaleTabWord saleOut) (endFlowVatIlkRateWord vatOut)

def endSnipStoreArt (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) :
    Store :=
  (endSnipStoreYank I dogOut vatOut saleOut).insert "art"
    (.int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat))

abbrev endSnipArtSlot (I : ExecutionEnv) : UInt256 := ArtSlot (endSnipIlkKey I)

abbrev endSnipArtOldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt (endSnipArtSlot I) σ I

abbrev endSnipArtNewWord (σ : AccountMap) (I : ExecutionEnv)
    (vatOut saleOut : ByteArray) : UInt256 :=
  endSnipArtOldWord σ I + endSnipArtWord vatOut saleOut

def endSnipStoreArtNew (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : Store :=
  (endSnipStoreArt I dogOut vatOut saleOut).insert "ArtNew"
    (.int (Int.ofNat (endSnipArtNewWord σ I vatOut saleOut).toNat))

theorem endSnipStoreDogIlk_get_ne (I : ExecutionEnv) (dogOut : ByteArray)
    {name : Ident} (hne : ("dogIlk" == name) = false) :
    (endSnipStoreDogIlk I dogOut).get? name = (endSnipStore I).get? name := by
  rw [endSnipStoreDogIlk, store_get_ne _ _ hne]

theorem endSnipStoreClip_get_ne (I : ExecutionEnv) (dogOut : ByteArray)
    {name : Ident} (hne : ("clip" == name) = false) :
    (endSnipStoreClip I dogOut).get? name = (endSnipStoreDogIlk I dogOut).get? name := by
  rw [endSnipStoreClip, store_get_ne _ _ hne]

theorem endSnipStoreVatIlk_get_ne (I : ExecutionEnv) (dogOut vatOut : ByteArray)
    {name : Ident} (hne : ("vatIlk" == name) = false) :
    (endSnipStoreVatIlk I dogOut vatOut).get? name =
      (endSnipStoreClip I dogOut).get? name := by
  rw [endSnipStoreVatIlk, store_get_ne _ _ hne]

theorem endSnipStoreRate_get_ne (I : ExecutionEnv) (dogOut vatOut : ByteArray)
    {name : Ident} (hne : ("rate" == name) = false) :
    (endSnipStoreRate I dogOut vatOut).get? name =
      (endSnipStoreVatIlk I dogOut vatOut).get? name := by
  rw [endSnipStoreRate, store_get_ne _ _ hne]

theorem endSnipStoreClipSale_get_ne (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) {name : Ident}
    (hne : ("clipSale" == name) = false) :
    (endSnipStoreClipSale I dogOut vatOut saleOut).get? name =
      (endSnipStoreRate I dogOut vatOut).get? name := by
  rw [endSnipStoreClipSale, store_get_ne _ _ hne]

theorem endSnipStoreTab_get_ne (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    {name : Ident} (hne : ("tab" == name) = false) :
    (endSnipStoreTab I dogOut vatOut saleOut).get? name =
      (endSnipStoreClipSale I dogOut vatOut saleOut).get? name := by
  rw [endSnipStoreTab, store_get_ne _ _ hne]

theorem endSnipStoreLot_get_ne (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    {name : Ident} (hne : ("lot" == name) = false) :
    (endSnipStoreLot I dogOut vatOut saleOut).get? name =
      (endSnipStoreTab I dogOut vatOut saleOut).get? name := by
  rw [endSnipStoreLot, store_get_ne _ _ hne]

theorem endSnipStoreUsr_get_ne (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    {name : Ident} (hne : ("usr" == name) = false) :
    (endSnipStoreUsr I dogOut vatOut saleOut).get? name =
      (endSnipStoreLot I dogOut vatOut saleOut).get? name := by
  rw [endSnipStoreUsr, store_get_ne _ _ hne]

theorem endSnipStoreSuck_get_ne (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    {name : Ident} (hne : ("_suck" == name) = false) :
    (endSnipStoreSuck I dogOut vatOut saleOut).get? name =
      (endSnipStoreUsr I dogOut vatOut saleOut).get? name := by
  rw [endSnipStoreSuck, store_get_ne _ _ hne]

theorem endSnipStoreYank_get_ne (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    {name : Ident} (hne : ("_yank" == name) = false) :
    (endSnipStoreYank I dogOut vatOut saleOut).get? name =
      (endSnipStoreSuck I dogOut vatOut saleOut).get? name := by
  rw [endSnipStoreYank, store_get_ne _ _ hne]

theorem endSnipStoreArt_get_ne (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    {name : Ident} (hne : ("art" == name) = false) :
    (endSnipStoreArt I dogOut vatOut saleOut).get? name =
      (endSnipStoreYank I dogOut vatOut saleOut).get? name := by
  rw [endSnipStoreArt, store_get_ne _ _ hne]

theorem endSnipStoreArtNew_get_ne (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) {name : Ident}
    (hne : ("ArtNew" == name) = false) :
    (endSnipStoreArtNew σ I dogOut vatOut saleOut).get? name =
      (endSnipStoreArt I dogOut vatOut saleOut).get? name := by
  rw [endSnipStoreArtNew, store_get_ne _ _ hne]

theorem endSnipStoreRate_get_base (I : ExecutionEnv) (dogOut vatOut : ByteArray)
    {name : Ident}
    (hdogIlk : ("dogIlk" == name) = false) (hclip : ("clip" == name) = false)
    (hvatIlk : ("vatIlk" == name) = false) (hrate : ("rate" == name) = false) :
    (endSnipStoreRate I dogOut vatOut).get? name = (endSnipStore I).get? name := by
  rw [endSnipStoreRate_get_ne _ _ _ hrate, endSnipStoreVatIlk_get_ne _ _ _ hvatIlk,
    endSnipStoreClip_get_ne _ _ hclip, endSnipStoreDogIlk_get_ne _ _ hdogIlk]

theorem endSnipStoreUsr_get_rate (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) {name : Ident}
    (hclipSale : ("clipSale" == name) = false) (htab : ("tab" == name) = false)
    (hlot : ("lot" == name) = false) (husr : ("usr" == name) = false) :
    (endSnipStoreUsr I dogOut vatOut saleOut).get? name =
      (endSnipStoreRate I dogOut vatOut).get? name := by
  rw [endSnipStoreUsr_get_ne _ _ _ _ husr, endSnipStoreLot_get_ne _ _ _ _ hlot,
    endSnipStoreTab_get_ne _ _ _ _ htab,
    endSnipStoreClipSale_get_ne _ _ _ _ hclipSale]

theorem endSnipStoreArtNew_get_usr (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) {name : Ident}
    (hsuck : ("_suck" == name) = false) (hyank : ("_yank" == name) = false)
    (hart : ("art" == name) = false) (hartNew : ("ArtNew" == name) = false) :
    (endSnipStoreArtNew σ I dogOut vatOut saleOut).get? name =
      (endSnipStoreUsr I dogOut vatOut saleOut).get? name := by
  rw [endSnipStoreArtNew_get_ne _ _ _ _ _ hartNew,
    endSnipStoreArt_get_ne _ _ _ _ hart, endSnipStoreYank_get_ne _ _ _ _ hyank,
    endSnipStoreSuck_get_ne _ _ _ _ hsuck]

theorem endSnipStoreArtNew_get_vat_none (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    (endSnipStoreArtNew σ I dogOut vatOut saleOut).get? "vat" = none := by
  rw [endSnipStoreArtNew_get_usr _ _ _ _ _ (by native_decide) (by native_decide)
      (by native_decide) (by native_decide),
    endSnipStoreUsr_get_rate _ _ _ _ (by native_decide) (by native_decide)
      (by native_decide) (by native_decide),
    endSnipStoreRate_get_base _ _ _ (by native_decide) (by native_decide)
      (by native_decide) (by native_decide),
    endSnipStore, store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide)]
  simp

theorem endSnipStoreArtNew_get_vow_none (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    (endSnipStoreArtNew σ I dogOut vatOut saleOut).get? "vow" = none := by
  rw [endSnipStoreArtNew_get_usr _ _ _ _ _ (by native_decide) (by native_decide)
      (by native_decide) (by native_decide),
    endSnipStoreUsr_get_rate _ _ _ _ (by native_decide) (by native_decide)
      (by native_decide) (by native_decide),
    endSnipStoreRate_get_base _ _ _ (by native_decide) (by native_decide)
      (by native_decide) (by native_decide),
    endSnipStore, store_get_ne _ _ (by native_decide),
    store_get_ne _ _ (by native_decide)]
  simp

def endSnipPostArtState (evm : EVM.State) (I : ExecutionEnv)
    (artNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endSnipArtSlot I) artNew

def endSnipPostArtAccountMap (σ : AccountMap) (I : ExecutionEnv) (artNew : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (endSnipArtSlot I) artNew


def endSnipStoreGrab (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : Store :=
  (endSnipStoreArtNew σ I dogOut vatOut saleOut).insert "_grab" (collapseReturns [])

abbrev endSnipThisWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.codeOwner.val

def endSnipSuckCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeCascade (endSnipSalesPostCallMem I dogOut vatOut saleOut)
    [ (128, endSnipSuckSelectorShifted),
      (132, endPackVowWord σ I),
      (164, endPackVowWord σ I),
      (196, endSnipSaleTabWord saleOut) ]

def endSnipSuckMem1 (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipSalesPostCallMem I dogOut vatOut saleOut) 128
    endSnipSuckSelectorShifted

def endSnipSuckMem2 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipSuckMem1 I dogOut vatOut saleOut) 132 (endPackVowWord σ I)

def endSnipSuckMem3 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipSuckMem2 σ I dogOut vatOut saleOut) 164 (endPackVowWord σ I)

def endSnipSuckPostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSnipSuckCalldataMem σ I dogOut vatOut saleOut)
    endSnipSuckOutPtr.toNat (min endSnipSuckOutSize (UInt256.ofNat ret.size)).toNat

def endSnipYankCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeCascade (endSnipSuckCalldataMem σ I dogOut vatOut saleOut)
    [ (128, endSnipYankSelectorShifted), (132, endSnipIdWord I) ]

def endSnipYankMem1 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipSuckCalldataMem σ I dogOut vatOut saleOut) 128
    endSnipYankSelectorShifted

def endSnipYankPostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSnipYankCalldataMem σ I dogOut vatOut saleOut)
    endSnipYankOutPtr.toNat (min endSnipYankOutSize (UInt256.ofNat ret.size)).toNat

def endSnipArtHashMem (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  twoWordHashMem (endSnipIlkWord I) ⟨14⟩
    (endSnipYankPostCallMem σ I dogOut vatOut saleOut ByteArray.empty)

def endSnipArtStoreHashMem (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  twoWordHashMem (endSnipIlkWord I) ⟨14⟩
    (endSnipArtHashMem σ I dogOut vatOut saleOut)

def endSnipGrabWritesFor (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : List (Nat × UInt256) :=
  [ (128, endFreeGrabSelectorShifted),
    (132, endSnipIlkWord I),
    (164, endSnipSaleUsrAddrWord saleOut),
    (196, endSnipThisWord I),
    (228, endPackVowWord σCall I),
    (260, endSnipSaleLotWord saleOut),
    (292, endSnipArtWord vatOut saleOut) ]

def endSnipGrabCalldataMemFor (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeCascade (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
    (endSnipGrabWritesFor σCall σLoc I dogOut vatOut saleOut)

def endSnipGrabMem1 (σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) 128
    endFreeGrabSelectorShifted

def endSnipGrabMem2 (σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipGrabMem1 σLoc I dogOut vatOut saleOut) 132
    (endSnipIlkWord I)

def endSnipGrabMem3 (σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipGrabMem2 σLoc I dogOut vatOut saleOut) 164
    (endSnipSaleUsrAddrWord saleOut)

def endSnipGrabMem4 (σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipGrabMem3 σLoc I dogOut vatOut saleOut) 196
    (endSnipThisWord I)

def endSnipGrabMem5For (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipGrabMem4 σLoc I dogOut vatOut saleOut) 228
    (endPackVowWord σCall I)

def endSnipGrabMem6For (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipGrabMem5For σCall σLoc I dogOut vatOut saleOut) 260
    (endSnipSaleLotWord saleOut)

def endSnipGrabMem7For (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) : ByteArray :=
  writeWord (endSnipGrabMem6For σCall σLoc I dogOut vatOut saleOut) 292
    (endSnipArtWord vatOut saleOut)

def endSnipGrabPostCallMemFor (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut)
    endFreeGrabOutPtr.toNat (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat

def endSnipLogDataMemFor (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray) : ByteArray :=
  (endSnipSaleTabWord saleOut).toByteArray.write 0
    (endSnipGrabPostCallMemFor σCall σLoc I dogOut vatOut saleOut ret) 128 32

def endSnipLogDataMem2For (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray) : ByteArray :=
  (endSnipSaleLotWord saleOut).toByteArray.write 0
    (endSnipLogDataMemFor σCall σLoc I dogOut vatOut saleOut ret) 160 32

def endSnipLogDataMem3For (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray) : ByteArray :=
  (endSnipArtWord vatOut saleOut).toByteArray.write 0
    (endSnipLogDataMem2For σCall σLoc I dogOut vatOut saleOut ret) 192 32

abbrev endSnipEntryPc : UInt256 := ⟨600⟩
abbrev endSnipReturnPc : UInt256 := ⟨562⟩
abbrev endSnipDecodedPc : UInt256 := ⟨622⟩
abbrev endSnipBodyPc : UInt256 := ⟨1649⟩

theorem endSnipTagSlot_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    endSnipTagSlot I = solcMappingSlot ⟨12⟩ (endSnipIlkWord I) := by
  unfold endSnipTagSlot endSnipIlkKey tagSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endSnipDogIlksEncode_eq (I : ExecutionEnv) {mem : ByteArray}
    (hsz68 : 68 ≤ I.calldata.size) (hmem : mem.size = 96) :
    config.externalABI.encode? "dogIlks" [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
      some ((endFlowVatIlksCalldataMem I mem).readWithPadding
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat) := by
  change config.externalABI.encode? "dogIlks"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
    some ((endFlowVatIlksCalldataMem I mem).readWithPadding 128 36)
  rw [endFlowVatIlksCalldataMem_read128_36 I hmem]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endSnipIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) (by omega)
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endSnipIlkWord I := by
      simpa [endBytes32ArgBytes, endSnipIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by omega))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hlen : (EVM.Word.toBytesBE (endSnipIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endSnipIlkWord I)
  simp [config, externalABI, ilksEncode?, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, ilksSelector,
    selectorBytes, hbytes, hlen, ABI.zeroBytes, word_toBytesBE_toByteArray_eq_toByteArray]

theorem endSnipDogIlksBaseMem_size (I : ExecutionEnv) :
    (endSnipDogIlksBaseMem I).size = 96 := by
  rw [endSnipDogIlksBaseMem]
  exact twoWordHashMem_size_96 (endSnipIlkWord I) ⟨12⟩ solcFreePtrMem_size

theorem endSnipDogIlksBaseMem_read64 (I : ExecutionEnv) :
    (endSnipDogIlksBaseMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endSnipDogIlksBaseMem]
  exact twoWordHashMem_read64 (endSnipIlkWord I) ⟨12⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem endSnipDogIlksCalldataMem_size (I : ExecutionEnv) :
    (endSnipDogIlksCalldataMem I).size = 164 := by
  rw [endSnipDogIlksCalldataMem]
  exact endFlowVatIlksCalldataMem_size I (endSnipDogIlksBaseMem_size I)

theorem endSnipDogIlksCalldataMem_read64 (I : ExecutionEnv) :
    (endSnipDogIlksCalldataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endSnipDogIlksCalldataMem]
  exact endFlowVatIlksCalldataMem_read64 I (endSnipDogIlksBaseMem_size I)
    (endSnipDogIlksBaseMem_read64 I)

theorem endSnipDogIlksWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endSnipDogIlksOutSize (UInt256.ofNat out.size)).toNat = min 128 out.size := by
  change (min (UInt256.ofNat 128) (UInt256.ofNat out.size)).toNat = min 128 out.size
  by_cases hle : 128 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 128) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 128 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 128)]
    exact umin_ofNat_right_toNat_of_lt (c := 128) (n := out.size) (by decide) hlt hout

theorem endSnipDogIlksPostCallMem_size_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 128 ≤ out.size) :
    (endSnipDogIlksPostCallMem I out).size = 256 := by
  unfold endSnipDogIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    Nat.min_eq_left hlo]
  rw [write_eq_gen_extend out (endSnipDogIlksCalldataMem I) 128 128
    (by omega) (by omega)
    (by rw [endSnipDogIlksCalldataMem_size I]; omega)
    (by rw [endSnipDogIlksCalldataMem_size I]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endSnipDogIlksCalldataMem_size I]
  omega

theorem endSnipDogIlksPostCallMem_read64 (I : ExecutionEnv) (out : ByteArray) :
    (endSnipDogIlksPostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipDogIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide]
  by_cases hlen0 : min 128 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endSnipDogIlksCalldataMem_read64 I
  · rw [write_read_below_gen_extend out (endSnipDogIlksCalldataMem I)
      128 (min 128 out.size) 64 hlen0
      (Nat.min_le_right _ _)
      (by
        rw [endSnipDogIlksCalldataMem_size I]
        omega)
      (by native_decide)]
    exact endSnipDogIlksCalldataMem_read64 I

theorem endSnipDogIlksPostCallMem_mload64 (I : ExecutionEnv) (out : ByteArray) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSnipDogIlksPostCallMem I out).size then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSnipDogIlksPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      unfold endSnipDogIlksPostCallMem
      rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide]
      by_cases hlen0 : min 128 out.size = 0
      · rw [hlen0, byteArray_write_len_zero, endSnipDogIlksCalldataMem_size I]
        decide
      · by_cases hin : 128 + min 128 out.size ≤ (endSnipDogIlksCalldataMem I).size
        · rw [write_eq_gen out (endSnipDogIlksCalldataMem I) 128 (min 128 out.size)
            hlen0 (Nat.min_le_right _ _) hin]
          rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
            ByteArray.size_extract, ByteArray.size_extract, endSnipDogIlksCalldataMem_size I]
          have hle128 : min 128 out.size ≤ 128 := Nat.min_le_left _ _
          omega
        · rw [write_eq_gen_extend out (endSnipDogIlksCalldataMem I) 128
            (min 128 out.size) hlen0 (Nat.min_le_right _ _)
            (by rw [endSnipDogIlksCalldataMem_size I]; omega) (Nat.lt_of_not_ge hin)]
          rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
            endSnipDogIlksCalldataMem_size I]
          have hle128 : min 128 out.size ≤ 128 := Nat.min_le_left _ _
          have hpos : 0 < min 128 out.size := Nat.pos_of_ne_zero hlen0
          omega)
    (endSnipDogIlksPostCallMem_read64 I out)

theorem endSnipDogIlksPostCallMem_read128_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 128 ≤ out.size) :
    (endSnipDogIlksPostCallMem I out).readWithPadding 128 32 = out.extract 0 32 := by
  unfold endSnipDogIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    Nat.min_eq_left hlo]
  rw [write_eq_gen_extend out (endSnipDogIlksCalldataMem I) 128 128
    (by omega) (by omega)
    (by rw [endSnipDogIlksCalldataMem_size I]; omega)
    (by rw [endSnipDogIlksCalldataMem_size I]; omega)]
  have hprefix : ((endSnipDogIlksCalldataMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSnipDogIlksCalldataMem_size I]
    omega
  have hsrc : (out.extract 0 128).size = 128 := by
    rw [ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract' _ 128 32 (by omega) (by omega)
    (by
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        endSnipDogIlksCalldataMem_size I]
      omega)]
  rw [extract_append_right_window _ _ 128 160 (by rw [hprefix])]
  rw [hprefix]
  rw [extract_extract_BA, show (128 - 128 : ℕ) = 0 from rfl,
    show min (0 + (160 - 128)) 128 = 32 from by omega]

theorem endSnipDogIlksPostCallMem_mload128_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 128 ≤ out.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (endSnipDogIlksPostCallMem I out).size then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSnipDogIlksPostCallMem I out).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      endSnipDogIlkClipWord out := by
  rw [if_neg]
  · change UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSnipDogIlksPostCallMem I out).readWithPadding 128 32)) =
        endSnipDogIlkClipWord out
    rw [endSnipDogIlksPostCallMem_read128_long I out hlo]
  · rw [endSnipDogIlksPostCallMem_size_long I out hlo]
    native_decide

theorem endSnipDogIlksDecode_ok {out : ByteArray} (hlo : 128 ≤ out.size) :
    config.externalABI.decode? "dogIlks" out =
      some [.address (endSnipDogIlkClipAddr out),
        .int (Int.ofNat (endSnipDogIlkChopWord out).toNat),
        .int (Int.ofNat (endSnipDogIlkHoleWord out).toNat),
        .int (Int.ofNat (endSnipDogIlkDirtWord out).toNat)] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
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
  have hword0 := bytesToWord_drop_take32_eq_extract' out 0
  have hword32 := bytesToWord_drop_take32_eq_extract' out 32
  have hword64 := bytesToWord_drop_take32_eq_extract' out 64
  have hword96 := bytesToWord_drop_take32_eq_extract' out 96
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
      [addr, uint256, uint256, uint256] out =
    some [.address (endSnipDogIlkClipAddr out),
      .int (Int.ofNat (endSnipDogIlkChopWord out).toNat),
      .int (Int.ofNat (endSnipDogIlkHoleWord out).toNat),
      .int (Int.ofNat (endSnipDogIlkDirtWord out).toNat)]
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [addr, uint256, uint256, uint256])
    (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256, uint256, uint256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [addr, uint256, uint256, uint256].length) (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  have haddrDec :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat), 0 + 32) := by
    simpa [addr, abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0) htake0
  rw [haddrDec]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have huint32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList (0 + 32) =
        some (.int (Int.ofNat
          (ABI.bytesToWord ((out.toList.drop 32).take 32)).toNat), 32 + 32) := by
    simpa [uint256, abiUInt256] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32
  rw [huint32]
  simp only [Option.bind_some]
  have huint64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList (32 + 32) =
        some (.int (Int.ofNat
          (ABI.bytesToWord ((out.toList.drop 64).take 32)).toNat), 64 + 32) := by
    simpa [uint256, abiUInt256] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 64) htake64
  rw [huint64]
  simp only [Option.bind_some]
  have huint96 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList (64 + 32) =
        some (.int (Int.ofNat
          (ABI.bytesToWord ((out.toList.drop 96).take 32)).toNat), 96 + 32) := by
    simpa [uint256, abiUInt256] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 96) htake96
  rw [huint96]
  simp only [Option.bind_some]
  rw [hword0, hword32, hword64, hword96]

theorem endSnipDogIlksDecode_none_short {out : ByteArray} (hshort : out.size < 128) :
    config.externalABI.decode? "dogIlks" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
      [addr, uint256, uint256, uint256] out = none
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [addr, uint256, uint256, uint256])
    (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256, uint256, uint256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [addr, uint256, uint256, uint256].length) (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases htake0 : ((out.toList.drop 0).take 32).length = 32
  · have haddrDec :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 =
          some (.address (AccountAddress.ofNat
            (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat), 0 + 32) := by
      simpa [addr, abiAddress] using
        decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 0)
          (by simpa using htake0)
    rw [haddrDec]
    simp only [Option.bind_eq_bind, Option.bind_some]
    by_cases htake32 : ((out.toList.drop 32).take 32).length = 32
    · have huint32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList (0 + 32) =
            some (.int (Int.ofNat
              (ABI.bytesToWord ((out.toList.drop 32).take 32)).toNat), 32 + 32) := by
        simpa [uint256, abiUInt256] using
          decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) htake32
      rw [huint32]
      simp only [Option.bind_some]
      by_cases htake64 : ((out.toList.drop 64).take 32).length = 32
      · have huint64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList
                (32 + 32) =
              some (.int (Int.ofNat
                (ABI.bytesToWord ((out.toList.drop 64).take 32)).toNat), 64 + 32) := by
          simpa [uint256, abiUInt256] using
            decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 64) htake64
        rw [huint64]
        simp only [Option.bind_some]
        have htake96 : ¬ ((out.toList.drop 96).take 32).length = 32 := by
          rw [List.length_take, List.length_drop, hlen]
          omega
        have huint96 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList
                (64 + 32) = none := by
          simpa [uint256, abiUInt256] using
            decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 96) htake96
        rw [huint96]
        simp
      · have huint64 :
            decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList
                (32 + 32) = none := by
          simpa [uint256, abiUInt256] using
            decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
              (bytes := out.toList) (start := 64) htake64
        rw [huint64]
        simp
    · have huint32 :
          decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList (0 + 32) =
            none := by
        simpa [uint256, abiUInt256] using
          decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
            (bytes := out.toList) (start := 32) htake32
      rw [huint32]
      simp
  · have haddrShort :
        decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 0 = none := by
      simpa [addr, abiAddress] using
        decodeScalarWord_legacyAddress_none_short (bytes := out.toList) (start := 0)
          (by simpa using htake0)
    rw [haddrShort]
    simp

theorem endSnipVatIlksBaseMem_size_long (I : ExecutionEnv) (dogOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) :
    (endSnipDogIlksPostCallMem I dogOut).size = 256 :=
  endSnipDogIlksPostCallMem_size_long I dogOut hloDog

theorem endSnipVatIlksSelectorMem_size_long (I : ExecutionEnv) (dogOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) :
    (endFlowVatIlksSelectorMem (endSnipDogIlksPostCallMem I dogOut)).size = 256 := by
  unfold endFlowVatIlksSelectorMem
  exact toByteArray_write32_size_of_le (endSnipDogIlksPostCallMem I dogOut)
    endFlowVatIlksSelectorShifted 128 256 256
    (endSnipVatIlksBaseMem_size_long I dogOut hloDog)
    (by rw [endSnipVatIlksBaseMem_size_long I dogOut hloDog]; omega)
    (by native_decide)

theorem endSnipVatIlksCalldataMem_size_long (I : ExecutionEnv) (dogOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) :
    (endSnipVatIlksCalldataMem I dogOut).size = 256 := by
  unfold endSnipVatIlksCalldataMem endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  exact toByteArray_write32_size_of_le
    (endFlowVatIlksSelectorMem (endSnipDogIlksPostCallMem I dogOut))
    (endFlowIlkWord I) 132 256 256
    (endSnipVatIlksSelectorMem_size_long I dogOut hloDog)
    (by rw [endSnipVatIlksSelectorMem_size_long I dogOut hloDog]; omega)
    (by native_decide)

theorem endSnipVatIlksSelectorMem_read64_long (I : ExecutionEnv) (dogOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) :
    (endFlowVatIlksSelectorMem (endSnipDogIlksPostCallMem I dogOut)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endFlowVatIlksSelectorMem
  change (endFlowVatIlksSelectorShifted.toByteArray.write 0
      (endSnipDogIlksPostCallMem I dogOut) 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap endFlowVatIlksSelectorShifted
    (endSnipDogIlksPostCallMem I dogOut) 128 64
    (by rw [endSnipVatIlksBaseMem_size_long I dogOut hloDog]; omega)
    (by omega)
    (by rw [endSnipVatIlksBaseMem_size_long I dogOut hloDog]; native_decide)]
  exact endSnipDogIlksPostCallMem_read64 I dogOut

theorem endSnipVatIlksCalldataMem_read64_long (I : ExecutionEnv) (dogOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) :
    (endSnipVatIlksCalldataMem I dogOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipVatIlksCalldataMem endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [endSnipVatIlksSelectorMem_size_long I dogOut hloDog]; omega) (by omega)]
  exact endSnipVatIlksSelectorMem_read64_long I dogOut hloDog

theorem endSnipVatIlksSelectorMem_extract128_132_long (I : ExecutionEnv)
    (dogOut : ByteArray) (hloDog : 128 ≤ dogOut.size) :
    (endFlowVatIlksSelectorMem (endSnipDogIlksPostCallMem I dogOut)).extract 128 132 =
      ilksSelector := by
  have hread :
      (endFlowVatIlksSelectorMem (endSnipDogIlksPostCallMem I dogOut)).readWithPadding
        128 4 = ilksSelector := by
    unfold endFlowVatIlksSelectorMem
    change (endFlowVatIlksSelectorShifted.toByteArray.write 0
        (endSnipDogIlksPostCallMem I dogOut) 128 32).readWithPadding (128 + 0) 4 =
      ilksSelector
    rw [toByteArray_write_read_window_of_gap endFlowVatIlksSelectorShifted
      (endSnipDogIlksPostCallMem I dogOut) 128 0 4
      (by omega) (by omega) (by native_decide)
      (by rw [endSnipVatIlksBaseMem_size_long I dogOut hloDog]; native_decide)]
    native_decide
  rw [← hread]
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
    (by rw [endSnipVatIlksSelectorMem_size_long I dogOut hloDog]; omega)]

theorem endSnipVatIlksCalldataMem_read128_36_long (I : ExecutionEnv)
    (dogOut : ByteArray) (hloDog : 128 ≤ dogOut.size) :
    (endSnipVatIlksCalldataMem I dogOut).readWithPadding 128 36 =
      ilksSelector ++ (endSnipIlkWord I).toByteArray := by
  unfold endSnipVatIlksCalldataMem endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  let selMem := endFlowVatIlksSelectorMem (endSnipDogIlksPostCallMem I dogOut)
  have hselSize : selMem.size = 256 := by
    simpa [selMem] using endSnipVatIlksSelectorMem_size_long I dogOut hloDog
  have hfinalSize : ((endFlowIlkWord I).toByteArray.write 0 selMem 132 32).size = 256 := by
    exact toByteArray_write32_size_of_le selMem (endFlowIlkWord I) 132 256 256
      hselSize (by rw [hselSize]; omega) (by native_decide)
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
    (by rw [hfinalSize]; omega)]
  rw [write32_eq _ _ 132 (by rw [toByteArray_size]) (by rw [hselSize]; omega)]
  change ((selMem.extract 0 132 ++ (endFlowIlkWord I).toByteArray.extract 0 32 ++
      selMem.extract (132 + 32) selMem.size).extract 128 (128 + 36)) =
    ilksSelector ++ (endSnipIlkWord I).toByteArray
  rw [show 132 + 32 = 164 by omega]
  rw [ByteArray.append_assoc]
  have hA : (selMem.extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, hselSize]
    omega
  rw [extract_append_span (selMem.extract 0 132)
    ((endFlowIlkWord I).toByteArray.extract 0 32 ++ selMem.extract 164 selMem.size)
    128 164 (by rw [hA]; omega) (by rw [hA]; omega)]
  rw [hA]
  rw [extract_extract_BA]
  rw [show (0 : ℕ) + 128 = 128 by omega,
    show min (0 + 132) 132 = 132 by omega]
  have hselExtract :
      selMem.extract 128 132 = ilksSelector := by
    simpa [selMem] using
      endSnipVatIlksSelectorMem_extract128_132_long I dogOut hloDog
  rw [hselExtract]
  rw [show 164 - 132 = 32 by omega]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_extract, toByteArray_size]
    omega)]
  rw [extract_extract_BA]
  rw [show (0 : ℕ) + 0 = 0 by omega,
    show min (0 + 32) 32 = 32 by omega]
  have hWfull :
      (endFlowIlkWord I).toByteArray.extract 0 32 = (endFlowIlkWord I).toByteArray := by
    have h := @ByteArray.extract_zero_size (endFlowIlkWord I).toByteArray
    rwa [toByteArray_size] at h
  rw [hWfull]

theorem endSnipVatIlksEncode_eq (I : ExecutionEnv) (dogOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size) (hloDog : 128 ≤ dogOut.size) :
    config.externalABI.encode? "vatIlks" [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
      some ((endSnipVatIlksCalldataMem I dogOut).readWithPadding
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat) := by
  change config.externalABI.encode? "vatIlks"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
    some ((endSnipVatIlksCalldataMem I dogOut).readWithPadding 128 36)
  rw [endSnipVatIlksCalldataMem_read128_36_long I dogOut hloDog]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endSnipIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) (by omega)
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endSnipIlkWord I := by
      simpa [endBytes32ArgBytes, endSnipIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by omega))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hlen : (EVM.Word.toBytesBE (endSnipIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endSnipIlkWord I)
  simp [config, externalABI, ilksEncode?, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, ilksSelector,
    selectorBytes, hbytes, hlen, ABI.zeroBytes, word_toBytesBE_toByteArray_eq_toByteArray]

theorem endSnipVatIlksWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endFlowVatIlksOutSize (UInt256.ofNat out.size)).toNat = min 160 out.size := by
  simpa [endFlowVatIlksOutSize] using endFlowVatIlksWriteLen_eq (out := out) hout

theorem endSnipVatIlksPostCallMem_size_long (I : ExecutionEnv) (dogOut vatOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size) :
    (endSnipVatIlksPostCallMem I dogOut vatOut).size = 288 := by
  unfold endSnipVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hloVat]
  rw [write_eq_gen_extend vatOut (endSnipVatIlksCalldataMem I dogOut) 128 160
    (by omega) (by omega)
    (by rw [endSnipVatIlksCalldataMem_size_long I dogOut hloDog]; omega)
    (by rw [endSnipVatIlksCalldataMem_size_long I dogOut hloDog]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
  rw [endSnipVatIlksCalldataMem_size_long I dogOut hloDog]
  omega

theorem endSnipVatIlksPostCallMem_read64 (I : ExecutionEnv) (dogOut vatOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) :
    (endSnipVatIlksPostCallMem I dogOut vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  by_cases hlen0 : min 160 vatOut.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endSnipVatIlksCalldataMem_read64_long I dogOut hloDog
  · rw [write_read_below_gen_extend vatOut (endSnipVatIlksCalldataMem I dogOut)
      128 (min 160 vatOut.size) 64 hlen0 (Nat.min_le_right _ _)
      (by rw [endSnipVatIlksCalldataMem_size_long I dogOut hloDog]; omega)
      (by native_decide)]
    exact endSnipVatIlksCalldataMem_read64_long I dogOut hloDog

theorem endSnipVatIlksPostCallMem_size_gt64 (I : ExecutionEnv) (dogOut vatOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) :
    64 < (endSnipVatIlksPostCallMem I dogOut vatOut).size := by
  unfold endSnipVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  by_cases hlen0 : min 160 vatOut.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    rw [endSnipVatIlksCalldataMem_size_long I dogOut hloDog]
    omega
  · by_cases hext :
        (endSnipVatIlksCalldataMem I dogOut).size < 128 + min 160 vatOut.size
    · rw [write_eq_gen_extend vatOut (endSnipVatIlksCalldataMem I dogOut)
        128 (min 160 vatOut.size) hlen0 (Nat.min_le_right _ _)
        (by rw [endSnipVatIlksCalldataMem_size_long I dogOut hloDog]; omega) hext]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        endSnipVatIlksCalldataMem_size_long I dogOut hloDog]
      omega
    · have hin : 128 + min 160 vatOut.size ≤
          (endSnipVatIlksCalldataMem I dogOut).size := by omega
      rw [write_eq_gen vatOut (endSnipVatIlksCalldataMem I dogOut)
        128 (min 160 vatOut.size) hlen0 (Nat.min_le_right _ _) hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract,
        endSnipVatIlksCalldataMem_size_long I dogOut hloDog]
      omega

theorem endSnipVatIlksPostCallMem_mload64 (I : ExecutionEnv) (dogOut vatOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSnipVatIlksPostCallMem I dogOut vatOut).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSnipVatIlksPostCallMem I dogOut vatOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (endSnipVatIlksPostCallMem_size_gt64 I dogOut vatOut hloDog)
    (endSnipVatIlksPostCallMem_read64 I dogOut vatOut hloDog)

theorem endSnipVatIlksPostCallMem_read160_long (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSnipVatIlksPostCallMem I dogOut vatOut).readWithPadding 160 32 =
      vatOut.extract 32 64 := by
  unfold endSnipVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endFlowVatIlksOutSize.toNat = 160 by native_decide]
  rw [Nat.min_eq_left hloVat]
  rw [write_eq_gen_extend vatOut (endSnipVatIlksCalldataMem I dogOut) 128 160
    (by omega) (by omega)
    (by rw [endSnipVatIlksCalldataMem_size_long I dogOut hloDog]; omega)
    (by rw [endSnipVatIlksCalldataMem_size_long I dogOut hloDog]; omega)]
  have hprefix : ((endSnipVatIlksCalldataMem I dogOut).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSnipVatIlksCalldataMem_size_long I dogOut hloDog]
    omega
  have hsrc : (vatOut.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((endSnipVatIlksCalldataMem I dogOut).extract 0 128 ++
        vatOut.extract 0 160).size = 288 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      160 + 32 ≤ ((endSnipVatIlksCalldataMem I dogOut).extract 0 128 ++
        vatOut.extract 0 160).size := by
    rw [hmemSize]
    norm_num
  rw [readWithPadding_eq_extract _ 160 hreadIn]
  rw [show 160 + 32 = 192 by omega]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem endSnipVatIlksPostCallMem_mload160_long (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (endSnipVatIlksPostCallMem I dogOut vatOut).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSnipVatIlksPostCallMem I dogOut vatOut).readWithPadding
          (⟨160⟩ : UInt256).toNat 32))) =
      endFlowVatIlkRateWord vatOut := by
  unfold endFlowVatIlkRateWord
  rw [if_neg (by rw [endSnipVatIlksPostCallMem_size_long I dogOut vatOut hloDog hloVat]; decide)]
  change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSnipVatIlksPostCallMem I dogOut vatOut).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (vatOut.extract 32 64))
  rw [endSnipVatIlksPostCallMem_read160_long I dogOut vatOut hloDog hloVat]

theorem endSnipSalesClipAddr_eq_ofUInt256 (dogOut : ByteArray) :
    endSnipDogIlkClipAddr dogOut =
      AccountAddress.ofUInt256 (endSnipSalesClipWord dogOut) := by
  have hval :
      Solm.Value.address (endSnipDogIlkClipAddr dogOut) =
        Solm.Value.address (AccountAddress.ofUInt256 (endSnipSalesClipWord dogOut)) := by
    simpa [endSnipDogIlkClipAddr, endSnipSalesClipWord,
      accountAddress_ofUInt256_eq_ofNat_toNat] using
      solcAddressValue_masked (endSnipDogIlkClipWord dogOut)
  exact Solm.Value.address.inj hval

theorem endSnipSalesSelectorMem_size_long (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSnipSalesSelectorMem I dogOut vatOut).size = 288 := by
  unfold endSnipSalesSelectorMem
  exact toByteArray_write32_size_of_le (endSnipVatIlksPostCallMem I dogOut vatOut)
    endSnipSalesSelectorShifted 128 288 288
    (endSnipVatIlksPostCallMem_size_long I dogOut vatOut hloDog hloVat)
    (by rw [endSnipVatIlksPostCallMem_size_long I dogOut vatOut hloDog hloVat]; omega)
    (by native_decide)

theorem endSnipSalesCalldataMem_size_long (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSnipSalesCalldataMem I dogOut vatOut).size = 288 := by
  unfold endSnipSalesCalldataMem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  exact toByteArray_write32_size_of_le (endSnipSalesSelectorMem I dogOut vatOut)
    (endSnipIdWord I) 132 288 288
    (endSnipSalesSelectorMem_size_long I dogOut vatOut hloDog hloVat)
    (by rw [endSnipSalesSelectorMem_size_long I dogOut vatOut hloDog hloVat]; omega)
    (by native_decide)

theorem endSnipSalesSelectorMem_read64_long (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSnipSalesSelectorMem I dogOut vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipSalesSelectorMem
  change (endSnipSalesSelectorShifted.toByteArray.write 0
      (endSnipVatIlksPostCallMem I dogOut vatOut) 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write32_read_below endSnipSalesSelectorShifted.toByteArray
    (endSnipVatIlksPostCallMem I dogOut vatOut) 128 64
    (by rw [toByteArray_size])
    (by rw [endSnipVatIlksPostCallMem_size_long I dogOut vatOut hloDog hloVat]; omega)
    (by omega)]
  exact endSnipVatIlksPostCallMem_read64 I dogOut vatOut hloDog

theorem endSnipSalesCalldataMem_read64_long (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSnipSalesCalldataMem I dogOut vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipSalesCalldataMem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [endSnipSalesSelectorMem_size_long I dogOut vatOut hloDog hloVat]; omega)
    (by omega)]
  exact endSnipSalesSelectorMem_read64_long I dogOut vatOut hloDog hloVat

theorem endSnipSalesSelectorMem_extract128_132_long (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSnipSalesSelectorMem I dogOut vatOut).extract 128 132 = salesSelector := by
  have hread :
      (endSnipSalesSelectorMem I dogOut vatOut).readWithPadding 128 4 =
        salesSelector := by
    unfold endSnipSalesSelectorMem
    change (endSnipSalesSelectorShifted.toByteArray.write 0
        (endSnipVatIlksPostCallMem I dogOut vatOut) 128 32).readWithPadding 128 4 =
      salesSelector
    rw [write32_read_prefix_len _ _ 128 4 (by rw [toByteArray_size])
      (by rw [endSnipVatIlksPostCallMem_size_long I dogOut vatOut hloDog hloVat]; omega)
      (by omega) (by omega) (by omega)]
    native_decide
  rw [← hread]
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
    (by rw [endSnipSalesSelectorMem_size_long I dogOut vatOut hloDog hloVat]; omega)]

theorem endSnipSalesCalldataMem_read128_36_long (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSnipSalesCalldataMem I dogOut vatOut).readWithPadding 128 36 =
      salesSelector ++ (endSnipIdWord I).toByteArray := by
  unfold endSnipSalesCalldataMem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by native_decide]
  let selMem := endSnipSalesSelectorMem I dogOut vatOut
  have hselSize : selMem.size = 288 := by
    simpa [selMem] using endSnipSalesSelectorMem_size_long I dogOut vatOut hloDog hloVat
  have hfinalSize : ((endSnipIdWord I).toByteArray.write 0 selMem 132 32).size = 288 := by
    exact toByteArray_write32_size_of_le selMem (endSnipIdWord I) 132 288 288
      hselSize (by rw [hselSize]; omega) (by native_decide)
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
    (by rw [hfinalSize]; omega)]
  rw [write32_eq _ _ 132 (by rw [toByteArray_size]) (by rw [hselSize]; omega)]
  change ((selMem.extract 0 132 ++ (endSnipIdWord I).toByteArray.extract 0 32 ++
      selMem.extract (132 + 32) selMem.size).extract 128 (128 + 36)) =
    salesSelector ++ (endSnipIdWord I).toByteArray
  rw [show 132 + 32 = 164 by omega]
  rw [ByteArray.append_assoc]
  have hA : (selMem.extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, hselSize]
    omega
  rw [extract_append_span (selMem.extract 0 132)
    ((endSnipIdWord I).toByteArray.extract 0 32 ++ selMem.extract 164 selMem.size)
    128 164 (by rw [hA]; omega) (by rw [hA]; omega)]
  rw [hA]
  rw [extract_extract_BA]
  rw [show (0 : ℕ) + 128 = 128 by omega,
    show min (0 + 132) 132 = 132 by omega]
  have hselExtract :
      selMem.extract 128 132 = salesSelector := by
    simpa [selMem] using
      endSnipSalesSelectorMem_extract128_132_long I dogOut vatOut hloDog hloVat
  rw [hselExtract]
  rw [show 164 - 132 = 32 by omega]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_extract, toByteArray_size]
    omega)]
  rw [extract_extract_BA]
  rw [show (0 : ℕ) + 0 = 0 by omega,
    show min (0 + 32) 32 = 32 by omega]
  have hWfull :
      (endSnipIdWord I).toByteArray.extract 0 32 = (endSnipIdWord I).toByteArray := by
    have h := @ByteArray.extract_zero_size (endSnipIdWord I).toByteArray
    rwa [toByteArray_size] at h
  rw [hWfull]

theorem endSnipSalesEncode_eq (I : ExecutionEnv) (dogOut vatOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size) :
    config.externalABI.encode? "sales" [.int (Int.ofNat (endSnipIdWord I).toNat)] =
      some ((endSnipSalesCalldataMem I dogOut vatOut).readWithPadding
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat) := by
  change config.externalABI.encode? "sales" [.int (Int.ofNat (endSnipIdWord I).toNat)] =
    some ((endSnipSalesCalldataMem I dogOut vatOut).readWithPadding 128 36)
  rw [endSnipSalesCalldataMem_read128_36_long I dogOut vatOut hloDog hloVat]
  have hidLt : (endSnipIdWord I).toNat < EVM.twoPow 256 := (endSnipIdWord I).val.isLt
  have hidWord : EVM.word (endSnipIdWord I).toNat = endSnipIdWord I := by
    show UInt256.ofNat (endSnipIdWord I).toNat = endSnipIdWord I
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, uint256, uint256Int, salesSelector,
    selectorBytes, hidLt, hidWord, word_toBytesBE_toByteArray_eq_toByteArray]

theorem endSnipSalesWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endSnipSalesOutSize (UInt256.ofNat out.size)).toNat = min 192 out.size := by
  change (min (UInt256.ofNat 192) (UInt256.ofNat out.size)).toNat = min 192 out.size
  by_cases hle : 192 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 192) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 192 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 192)]
    exact umin_ofNat_right_toNat_of_lt (c := 192) (n := out.size) (by decide) hlt hout

theorem endSnipSalesPostCallMem_size_long (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSalesPostCallMem I dogOut vatOut saleOut).size = 320 := by
  unfold endSnipSalesPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endSnipSalesOutSize.toNat = 192 by native_decide]
  rw [Nat.min_eq_left hloSale]
  rw [write_eq_gen_extend saleOut (endSnipSalesCalldataMem I dogOut vatOut) 128 192
    (by omega) (by omega)
    (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; omega)
    (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]
  omega

theorem endSnipSalesPostCallMem_read64 (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipSalesPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endSnipSalesOutSize.toNat = 192 by native_decide]
  by_cases hlen0 : min 192 saleOut.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endSnipSalesCalldataMem_read64_long I dogOut vatOut hloDog hloVat
  · rw [write_read_below_gen_extend saleOut (endSnipSalesCalldataMem I dogOut vatOut)
      128 (min 192 saleOut.size) 64 hlen0 (Nat.min_le_right _ _)
      (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; omega)
      (by native_decide)]
    exact endSnipSalesCalldataMem_read64_long I dogOut vatOut hloDog hloVat

theorem endSnipSalesPostCallMem_size_gt64 (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    64 < (endSnipSalesPostCallMem I dogOut vatOut saleOut).size := by
  unfold endSnipSalesPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endSnipSalesOutSize.toNat = 192 by native_decide]
  by_cases hlen0 : min 192 saleOut.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]
    omega
  · by_cases hext :
        (endSnipSalesCalldataMem I dogOut vatOut).size < 128 + min 192 saleOut.size
    · rw [write_eq_gen_extend saleOut (endSnipSalesCalldataMem I dogOut vatOut)
        128 (min 192 saleOut.size) hlen0 (Nat.min_le_right _ _)
        (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; omega)
        hext]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]
      omega
    · have hin : 128 + min 192 saleOut.size ≤
          (endSnipSalesCalldataMem I dogOut vatOut).size := by omega
      rw [write_eq_gen saleOut (endSnipSalesCalldataMem I dogOut vatOut)
        128 (min 192 saleOut.size) hlen0 (Nat.min_le_right _ _) hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract,
        endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]
      omega

theorem endSnipSalesCalldataMem_mload64_long (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSnipSalesCalldataMem I dogOut vatOut).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSnipSalesCalldataMem I dogOut vatOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; decide)
    (endSnipSalesCalldataMem_read64_long I dogOut vatOut hloDog hloVat)

theorem endSnipSalesPostCallMem_mload64 (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSnipSalesPostCallMem I dogOut vatOut saleOut).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (endSnipSalesPostCallMem_size_gt64 I dogOut vatOut saleOut hloDog hloVat)
    (endSnipSalesPostCallMem_read64 I dogOut vatOut saleOut hloDog hloVat)

theorem endSnipSalesPostCallMem_read160_long (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding 160 32 =
      saleOut.extract 32 64 := by
  unfold endSnipSalesPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endSnipSalesOutSize.toNat = 192 by native_decide]
  rw [Nat.min_eq_left hloSale]
  rw [write_eq_gen_extend saleOut (endSnipSalesCalldataMem I dogOut vatOut) 128 192
    (by omega) (by omega)
    (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; omega)
    (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; omega)]
  have hprefix : ((endSnipSalesCalldataMem I dogOut vatOut).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]
    omega
  have hsrc : (saleOut.extract 0 192).size = 192 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((endSnipSalesCalldataMem I dogOut vatOut).extract 0 128 ++
        saleOut.extract 0 192).size = 320 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  rw [readWithPadding_eq_extract _ 160 (by rw [hmemSize]; norm_num)]
  rw [show 160 + 32 = 192 by omega]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem endSnipSalesPostCallMem_read192_long (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding 192 32 =
      saleOut.extract 64 96 := by
  unfold endSnipSalesPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endSnipSalesOutSize.toNat = 192 by native_decide]
  rw [Nat.min_eq_left hloSale]
  rw [write_eq_gen_extend saleOut (endSnipSalesCalldataMem I dogOut vatOut) 128 192
    (by omega) (by omega)
    (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; omega)
    (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; omega)]
  have hprefix : ((endSnipSalesCalldataMem I dogOut vatOut).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]
    omega
  have hsrc : (saleOut.extract 0 192).size = 192 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((endSnipSalesCalldataMem I dogOut vatOut).extract 0 128 ++
        saleOut.extract 0 192).size = 320 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  rw [readWithPadding_eq_extract _ 192 (by rw [hmemSize]; norm_num)]
  rw [show 192 + 32 = 224 by omega]
  rw [extract_append_right_window _ _ 192 224 (by rw [hprefix]; omega), hprefix]
  rw [show 192 - 128 = 64 by omega, show 224 - 128 = 96 by omega]
  rw [extract_extract_BA]
  norm_num

theorem endSnipSalesPostCallMem_read224_long (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding 224 32 =
      saleOut.extract 96 128 := by
  unfold endSnipSalesPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by native_decide,
    show endSnipSalesOutSize.toNat = 192 by native_decide]
  rw [Nat.min_eq_left hloSale]
  rw [write_eq_gen_extend saleOut (endSnipSalesCalldataMem I dogOut vatOut) 128 192
    (by omega) (by omega)
    (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; omega)
    (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; omega)]
  have hprefix : ((endSnipSalesCalldataMem I dogOut vatOut).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]
    omega
  have hsrc : (saleOut.extract 0 192).size = 192 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((endSnipSalesCalldataMem I dogOut vatOut).extract 0 128 ++
        saleOut.extract 0 192).size = 320 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  rw [readWithPadding_eq_extract _ 224 (by rw [hmemSize]; norm_num)]
  rw [show 224 + 32 = 256 by omega]
  rw [extract_append_right_window _ _ 224 256 (by rw [hprefix]; omega), hprefix]
  rw [show 224 - 128 = 96 by omega, show 256 - 128 = 128 by omega]
  rw [extract_extract_BA]
  norm_num

theorem endSnipSalesPostCallMem_mload160_long (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (endSnipSalesPostCallMem I dogOut vatOut saleOut).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding
          (⟨160⟩ : UInt256).toNat 32))) =
      endSnipSaleTabWord saleOut := by
  unfold endSnipSaleTabWord
  rw [if_neg (by rw [endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut hloDog hloVat hloSale]; decide)]
  change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (saleOut.extract 32 64))
  rw [endSnipSalesPostCallMem_read160_long I dogOut vatOut saleOut hloDog hloVat hloSale]

theorem endSnipSalesPostCallMem_mload192_long (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (if (⟨192⟩ : UInt256).toNat ≥ (endSnipSalesPostCallMem I dogOut vatOut saleOut).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding
          (⟨192⟩ : UInt256).toNat 32))) =
      endSnipSaleLotWord saleOut := by
  unfold endSnipSaleLotWord
  rw [if_neg (by rw [endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut hloDog hloVat hloSale]; decide)]
  change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding 192 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (saleOut.extract 64 96))
  rw [endSnipSalesPostCallMem_read192_long I dogOut vatOut saleOut hloDog hloVat hloSale]

theorem endSnipSalesPostCallMem_mload224_long (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (if (⟨224⟩ : UInt256).toNat ≥ (endSnipSalesPostCallMem I dogOut vatOut saleOut).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding
          (⟨224⟩ : UInt256).toNat 32))) =
      endSnipSaleUsrWord saleOut := by
  unfold endSnipSaleUsrWord
  rw [if_neg (by rw [endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut hloDog hloVat hloSale]; decide)]
  change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding 224 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (saleOut.extract 96 128))
  rw [endSnipSalesPostCallMem_read224_long I dogOut vatOut saleOut hloDog hloVat hloSale]


theorem endSnipSalesDecode_ok {out : ByteArray} (hlo : 192 ≤ out.size) :
    config.externalABI.decode? "sales" out =
      some [.int (Int.ofNat (endSnipSalePosWord out).toNat),
        .int (Int.ofNat (endSnipSaleTabWord out).toNat),
        .int (Int.ofNat (endSnipSaleLotWord out).toNat),
        .address (endSnipSaleUsrAddr out),
        .int (Int.ofNat ((endSnipSaleTicWord out).toNat % EVM.twoPow 96)),
        .int (Int.ofNat (endSnipSaleTopWord out).toNat)] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
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
  have htake160 : ((out.toList.drop 160).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword0 := bytesToWord_drop_take32_eq_extract' out 0
  have hword32 := bytesToWord_drop_take32_eq_extract' out 32
  have hword64 := bytesToWord_drop_take32_eq_extract' out 64
  have hword96 := bytesToWord_drop_take32_eq_extract' out 96
  have hword128 := bytesToWord_drop_take32_eq_extract' out 128
  have hword160 := bytesToWord_drop_take32_eq_extract' out 160
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
      [uint256, uint256, uint256, addr, uint96, uint256] out = _
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [uint256, uint256, uint256, addr, uint96, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, addr, uint96, uint256])
    (bytes := out.toList) (cursor := 0)
    (total := 32 * [uint256, uint256, uint256, addr, uint96, uint256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  have huint0 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList 0 =
        some (.int (Int.ofNat
          (ABI.bytesToWord ((out.toList.drop 0).take 32)).toNat), 0 + 32) := by
    simpa [uint256, abiUInt256] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 0) htake0
  rw [huint0]
  simp only [Option.bind_eq_bind, Option.bind_some]
  have huint32 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList (0 + 32) =
        some (.int (Int.ofNat
          (ABI.bytesToWord ((out.toList.drop 32).take 32)).toNat), 32 + 32) := by
    simpa [uint256, abiUInt256] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 32) htake32
  rw [huint32]
  simp only [Option.bind_some]
  have huint64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList (0 + 32 + 32) =
        some (.int (Int.ofNat
          (ABI.bytesToWord ((out.toList.drop 64).take 32)).toNat), 64 + 32) := by
    simpa [uint256, abiUInt256] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 64) htake64
  rw [huint64]
  simp only [Option.bind_some]
  have haddr :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList 96 =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((out.toList.drop 96).take 32)).toNat), 96 + 32) := by
    simpa [addr, abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 96) htake96
  rw [haddr]
  simp only [Option.bind_some]
  erw [decodeScalarWordWithMode_legacy_uint96_ok (bytes := out.toList) (start := 128)
    htake128]
  simp only [Option.bind_some]
  have huint160 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList
          (0 + 32 + 32 + 32 + 32 + 32) =
        some (.int (Int.ofNat
          (ABI.bytesToWord ((out.toList.drop 160).take 32)).toNat), 160 + 32) := by
    simpa [uint256, abiUInt256] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 160) htake160
  rw [huint160]
  simp only [Option.bind_some]
  rw [hword0, hword32, hword64, hword96, hword128, hword160]

theorem endSnipSalesDecode_none_short {out : ByteArray} (hshort : out.size < 192) :
    config.externalABI.decode? "sales" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
      [uint256, uint256, uint256, addr, uint96, uint256] out = none
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [uint256, uint256, uint256, addr, uint96, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, uint256, addr, uint96, uint256])
    (bytes := out.toList) (cursor := 0)
    (total := 32 * [uint256, uint256, uint256, addr, uint96, uint256].length)
    (by decide) (by simp)]
  cases hdec : decodeScalarWordsWithMode? DecodeMode.legacySolc05
      [uint256, uint256, uint256, addr, uint96, uint256] out.toList 0 with
  | none =>
      simp [hdec]
  | some values =>
      have hlenDec := decodeScalarWordsWithMode?_some_length
        (mode := DecodeMode.legacySolc05)
        (types := [uint256, uint256, uint256, addr, uint96, uint256])
        (bytes := out.toList) (cursor := 0) (values := values) (by omega) hdec
      rw [hlen] at hlenDec
      norm_num at hlenDec
      omega

theorem endSnipSuckCalldataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSuckCalldataMem σ I dogOut vatOut saleOut).size = 320 := by
  unfold endSnipSuckCalldataMem
  exact writeCascade_size_of_base (endSnipSalesPostCallMem I dogOut vatOut saleOut)
    [ (128, endSnipSuckSelectorShifted),
      (132, endPackVowWord σ I),
      (164, endPackVowWord σ I),
      (196, endSnipSaleTabWord saleOut) ]
    (endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut hloDog hloVat hloSale)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSnipSuckCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSuckCalldataMem σ I dogOut vatOut saleOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipSuckCalldataMem
  rw [writeCascade_read_preserved_of_base (endSnipSalesPostCallMem I dogOut vatOut saleOut)
    [ (128, endSnipSuckSelectorShifted),
      (132, endPackVowWord σ I),
      (164, endPackVowWord σ I),
      (196, endSnipSaleTabWord saleOut) ]
    (endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut hloDog hloVat hloSale)
    (by simp [WindowDisjointFromWrites])]
  exact endSnipSalesPostCallMem_read64 I dogOut vatOut saleOut hloDog hloVat

theorem endSnipSuckPostCallMem_eq (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray) :
    endSnipSuckPostCallMem σ I dogOut vatOut saleOut ret =
      endSnipSuckCalldataMem σ I dogOut vatOut saleOut := by
  unfold endSnipSuckPostCallMem
  have hmin : (min endSnipSuckOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endSnipSuckOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret
    (endSnipSuckCalldataMem σ I dogOut vatOut saleOut) 0 endSnipSuckOutPtr.toNat

theorem endSnipSuckCalldataMem_read128_4 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSuckCalldataMem σ I dogOut vatOut saleOut).readWithPadding 128 4 =
      suckSelector := by
  unfold endSnipSuckCalldataMem
  rw [writeCascade_read_window_of_head (endSnipSalesPostCallMem I dogOut vatOut saleOut)
    128 0 4 endSnipSuckSelectorShifted
    [ (132, endPackVowWord σ I),
      (164, endPackVowWord σ I),
      (196, endSnipSaleTabWord saleOut) ]]
  · unfold endSnipSuckSelectorShifted suckSelector selectorBytes
    native_decide
  · rw [endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut hloDog hloVat hloSale]
    native_decide
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endSnipSuckCalldataMem_read132_32 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSuckCalldataMem σ I dogOut vatOut saleOut).readWithPadding 132 32 =
      (endPackVowWord σ I).toByteArray := by
  unfold endSnipSuckCalldataMem
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (endSnipSalesPostCallMem I dogOut vatOut saleOut) 128
      endSnipSuckSelectorShifted)
    (word := endPackVowWord σ I)
    (rest := [ (164, endPackVowWord σ I), (196, endSnipSaleTabWord saleOut) ])
    (hbase := by
      rw [writeWord_size]
      · rw [endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut hloDog hloVat hloSale]
        native_decide)
    (hgap := by
      rw [endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut hloDog hloVat hloSale]
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSnipSuckCalldataMem_read164_32 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSuckCalldataMem σ I dogOut vatOut saleOut).readWithPadding 164 32 =
      (endPackVowWord σ I).toByteArray := by
  unfold endSnipSuckCalldataMem
  rw [writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (endSnipSalesPostCallMem I dogOut vatOut saleOut) 128
        endSnipSuckSelectorShifted)
      132 (endPackVowWord σ I))
    (word := endPackVowWord σ I)
    (rest := [ (196, endSnipSaleTabWord saleOut) ])
    (hbase := by
      change (writeCascade (endSnipSalesPostCallMem I dogOut vatOut saleOut)
        [(128, endSnipSuckSelectorShifted), (132, endPackVowWord σ I)]).size = 320
      exact writeCascade_size_of_base (endSnipSalesPostCallMem I dogOut vatOut saleOut)
        [(128, endSnipSuckSelectorShifted), (132, endPackVowWord σ I)]
        (endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut hloDog hloVat hloSale)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSnipSuckCalldataMem_read196_32 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSuckCalldataMem σ I dogOut vatOut saleOut).readWithPadding 196 32 =
      (endSnipSaleTabWord saleOut).toByteArray := by
  unfold endSnipSuckCalldataMem
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord (endSnipSalesPostCallMem I dogOut vatOut saleOut) 128
          endSnipSuckSelectorShifted)
        132 (endPackVowWord σ I))
      164 (endPackVowWord σ I))
    (word := endSnipSaleTabWord saleOut)
    (rest := [])
    (hbase := by
      change (writeCascade (endSnipSalesPostCallMem I dogOut vatOut saleOut)
        [(128, endSnipSuckSelectorShifted), (132, endPackVowWord σ I),
          (164, endPackVowWord σ I)]).size = 320
      exact writeCascade_size_of_base (endSnipSalesPostCallMem I dogOut vatOut saleOut)
        [(128, endSnipSuckSelectorShifted), (132, endPackVowWord σ I),
          (164, endPackVowWord σ I)]
        (endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut hloDog hloVat hloSale)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSnipSuckCalldataMem_read128_100 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipSuckCalldataMem σ I dogOut vatOut saleOut).readWithPadding 128 100 =
      suckSelector ++ (endPackVowWord σ I).toByteArray ++
        (endPackVowWord σ I).toByteArray ++
        (endSnipSaleTabWord saleOut).toByteArray := by
  have hsize :
      (endSnipSuckCalldataMem σ I dogOut vatOut saleOut).size = 320 :=
    endSnipSuckCalldataMem_size σ I dogOut vatOut saleOut hloDog hloVat hloSale
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (endSnipSuckCalldataMem σ I dogOut vatOut saleOut)
      128 4 96 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (endSnipSuckCalldataMem σ I dogOut vatOut saleOut)
      132 32 64 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (endSnipSuckCalldataMem σ I dogOut vatOut saleOut)
      164 32 32 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [endSnipSuckCalldataMem_read128_4 σ I dogOut vatOut saleOut hloDog hloVat hloSale,
    endSnipSuckCalldataMem_read132_32 σ I dogOut vatOut saleOut hloDog hloVat hloSale,
    endSnipSuckCalldataMem_read164_32 σ I dogOut vatOut saleOut hloDog hloVat hloSale,
    endSnipSuckCalldataMem_read196_32 σ I dogOut vatOut saleOut hloDog hloVat hloSale]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endSnipYankCalldataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipYankCalldataMem σ I dogOut vatOut saleOut).size = 320 := by
  unfold endSnipYankCalldataMem
  exact writeCascade_size_of_base (endSnipSuckCalldataMem σ I dogOut vatOut saleOut)
    [ (128, endSnipYankSelectorShifted), (132, endSnipIdWord I) ]
    (endSnipSuckCalldataMem_size σ I dogOut vatOut saleOut hloDog hloVat hloSale)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSnipYankCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipYankCalldataMem σ I dogOut vatOut saleOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipYankCalldataMem
  rw [writeCascade_read_preserved_of_base (endSnipSuckCalldataMem σ I dogOut vatOut saleOut)
    [ (128, endSnipYankSelectorShifted), (132, endSnipIdWord I) ]
    (endSnipSuckCalldataMem_size σ I dogOut vatOut saleOut hloDog hloVat hloSale)
    (by simp [WindowDisjointFromWrites])]
  exact endSnipSuckCalldataMem_read64 σ I dogOut vatOut saleOut hloDog hloVat hloSale

theorem endSnipYankPostCallMem_eq (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray) :
    endSnipYankPostCallMem σ I dogOut vatOut saleOut ret =
      endSnipYankCalldataMem σ I dogOut vatOut saleOut := by
  unfold endSnipYankPostCallMem
  have hmin : (min endSnipYankOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endSnipYankOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret
    (endSnipYankCalldataMem σ I dogOut vatOut saleOut) 0 endSnipYankOutPtr.toNat

theorem endSnipYankCalldataMem_read128_4 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipYankCalldataMem σ I dogOut vatOut saleOut).readWithPadding 128 4 =
      yankSelector := by
  unfold endSnipYankCalldataMem
  rw [writeCascade_read_window_of_head (endSnipSuckCalldataMem σ I dogOut vatOut saleOut)
    128 0 4 endSnipYankSelectorShifted [ (132, endSnipIdWord I) ]]
  · unfold endSnipYankSelectorShifted yankSelector selectorBytes
    native_decide
  · rw [endSnipSuckCalldataMem_size σ I dogOut vatOut saleOut hloDog hloVat hloSale]
    native_decide
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endSnipYankCalldataMem_read132_32 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipYankCalldataMem σ I dogOut vatOut saleOut).readWithPadding 132 32 =
      (endSnipIdWord I).toByteArray := by
  unfold endSnipYankCalldataMem
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (endSnipSuckCalldataMem σ I dogOut vatOut saleOut) 128
      endSnipYankSelectorShifted)
    (word := endSnipIdWord I) (rest := [])
    (hbase := by
      rw [writeWord_size]
      · rw [endSnipSuckCalldataMem_size σ I dogOut vatOut saleOut hloDog hloVat hloSale]
        native_decide)
    (hgap := by
      rw [endSnipSuckCalldataMem_size σ I dogOut vatOut saleOut hloDog hloVat hloSale]
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSnipYankCalldataMem_read128_36 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipYankCalldataMem σ I dogOut vatOut saleOut).readWithPadding 128 36 =
      yankSelector ++ (endSnipIdWord I).toByteArray := by
  have hsize :
      (endSnipYankCalldataMem σ I dogOut vatOut saleOut).size = 320 :=
    endSnipYankCalldataMem_size σ I dogOut vatOut saleOut hloDog hloVat hloSale
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split (endSnipYankCalldataMem σ I dogOut vatOut saleOut)
      128 4 32 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [endSnipYankCalldataMem_read128_4 σ I dogOut vatOut saleOut hloDog hloVat hloSale,
    endSnipYankCalldataMem_read132_32 σ I dogOut vatOut saleOut hloDog hloVat hloSale]

theorem endSnipVowWordOfAddr (σ : AccountMap) (I : ExecutionEnv) :
    EVM.word ↑(endPackVowAddr σ I) = endPackVowWord σ I := by
  have hvowCanon : (endPackVowWord σ I).toNat < EVM.addressModulus := by
    simpa [endPackVowWord] using
      solcAddrMask_result_canonical (solcSlotWordAt ⟨4⟩ σ I)
  have hvowVal :
      (endPackVowAddr σ I).val = (endPackVowWord σ I).toNat := by
    unfold endPackVowAddr AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hvowCanon
  change UInt256.ofNat (endPackVowAddr σ I).val = endPackVowWord σ I
  rw [hvowVal]
  exact u256_ofNat_toNat _

theorem endSnipSuckEncode_eq (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    config.externalABI.encode? "suck"
        [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)] =
      some ((endSnipSuckCalldataMem σ I dogOut vatOut saleOut).readWithPadding
        endSnipSuckOutPtr.toNat endSnipSuckInSize.toNat) := by
  change config.externalABI.encode? "suck"
      [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
        .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)] =
    some ((endSnipSuckCalldataMem σ I dogOut vatOut saleOut).readWithPadding 128 100)
  rw [endSnipSuckCalldataMem_read128_100 σ I dogOut vatOut saleOut hloDog hloVat hloSale]
  have hvowWord : EVM.word ↑(endPackVowAddr σ I) = endPackVowWord σ I :=
    endSnipVowWordOfAddr σ I
  have htabLt : (endSnipSaleTabWord saleOut).toNat < EVM.twoPow 256 :=
    (endSnipSaleTabWord saleOut).val.isLt
  have htabWord : EVM.word (endSnipSaleTabWord saleOut).toNat =
      endSnipSaleTabWord saleOut := by
    show UInt256.ofNat (endSnipSaleTabWord saleOut).toNat = endSnipSaleTabWord saleOut
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr,
    uint256, uint256Int, suckSelector, selectorBytes, hvowWord, htabLt, htabWord,
    word_toBytesBE_toByteArray_eq_toByteArray, zeroBytes, ByteArray.append_assoc]

theorem endSnipYankEncode_eq (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    config.externalABI.encode? "yank" [.int (Int.ofNat (endSnipIdWord I).toNat)] =
      some ((endSnipYankCalldataMem σ I dogOut vatOut saleOut).readWithPadding
        endSnipYankOutPtr.toNat endSnipYankInSize.toNat) := by
  change config.externalABI.encode? "yank" [.int (Int.ofNat (endSnipIdWord I).toNat)] =
    some ((endSnipYankCalldataMem σ I dogOut vatOut saleOut).readWithPadding 128 36)
  rw [endSnipYankCalldataMem_read128_36 σ I dogOut vatOut saleOut hloDog hloVat hloSale]
  have hidLt : (endSnipIdWord I).toNat < EVM.twoPow 256 := (endSnipIdWord I).val.isLt
  have hidWord : EVM.word (endSnipIdWord I).toNat = endSnipIdWord I := by
    show UInt256.ofNat (endSnipIdWord I).toNat = endSnipIdWord I
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, uint256,
    uint256Int, yankSelector, selectorBytes, hidLt, hidWord,
    word_toBytesBE_toByteArray_eq_toByteArray]

theorem endSnipArtStoreHashMem_size (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipArtStoreHashMem σ I dogOut vatOut saleOut).size = 320 := by
  let key := endSnipIlkWord I
  let mem0 := endSnipYankPostCallMem σ I dogOut vatOut saleOut ByteArray.empty
  let mem14 := endSnipArtHashMem σ I dogOut vatOut saleOut
  have hpostSize : mem0.size = 320 := by
    simpa [mem0, endSnipYankPostCallMem_eq] using
      endSnipYankCalldataMem_size σ I dogOut vatOut saleOut hloDog hloVat hloSale
  have hmem14Size : mem14.size = mem0.size := by
    exact twoWordHashMem_size_of_ge64 key ⟨14⟩
      (by rw [hpostSize]; omega)
  have hmemStoreSize : (twoWordHashMem key ⟨14⟩ mem14).size = mem14.size := by
    exact twoWordHashMem_size_of_ge64 key ⟨14⟩
      (by rw [hmem14Size, hpostSize]; omega)
  change (twoWordHashMem key ⟨14⟩ mem14).size = 320
  rw [hmemStoreSize, hmem14Size, hpostSize]

theorem endSnipArtStoreHashMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) (hloDog : 128 ≤ dogOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloSale : 192 ≤ saleOut.size) :
    (endSnipArtStoreHashMem σ I dogOut vatOut saleOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  let key := endSnipIlkWord I
  let mem0 := endSnipYankPostCallMem σ I dogOut vatOut saleOut ByteArray.empty
  let mem14 := endSnipArtHashMem σ I dogOut vatOut saleOut
  have hpostSize : mem0.size = 320 := by
    simpa [mem0, endSnipYankPostCallMem_eq] using
      endSnipYankCalldataMem_size σ I dogOut vatOut saleOut hloDog hloVat hloSale
  have hpostRead64 :
      mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem0, endSnipYankPostCallMem_eq] using
      endSnipYankCalldataMem_read64 σ I dogOut vatOut saleOut hloDog hloVat hloSale
  have hmem14Size : mem14.size = mem0.size := by
    exact twoWordHashMem_size_of_ge64 key ⟨14⟩
      (by rw [hpostSize]; omega)
  have hmem14Read64 :
      mem14.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem14, endSnipArtHashMem, key, mem0] using
      twoWordHashMem_read64_of_ge_96 key ⟨14⟩
        (by rw [hpostSize]; omega) hpostRead64
  simpa [endSnipArtStoreHashMem, key, mem14] using
    twoWordHashMem_read64_of_ge_96 key ⟨14⟩
      (by rw [hmem14Size, hpostSize]; omega) hmem14Read64

theorem endSnipGrabMem7For_eq (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    endSnipGrabMem7For σCall σLoc I dogOut vatOut saleOut =
      endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut := by
  rfl

theorem endSnipGrabCalldataMemFor_size (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).size = 324 := by
  unfold endSnipGrabCalldataMemFor endSnipGrabWritesFor
  exact writeCascade_size_of_base (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
    [ (128, endFreeGrabSelectorShifted),
      (132, endSnipIlkWord I),
      (164, endSnipSaleUsrAddrWord saleOut),
      (196, endSnipThisWord I),
      (228, endPackVowWord σCall I),
      (260, endSnipSaleLotWord saleOut),
      (292, endSnipArtWord vatOut saleOut) ]
    (endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut hloDog hloVat hloSale)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSnipGrabCalldataMemFor_read64 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipGrabCalldataMemFor endSnipGrabWritesFor
  rw [writeCascade_read_preserved_of_base
    (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
    [ (128, endFreeGrabSelectorShifted),
      (132, endSnipIlkWord I),
      (164, endSnipSaleUsrAddrWord saleOut),
      (196, endSnipThisWord I),
      (228, endPackVowWord σCall I),
      (260, endSnipSaleLotWord saleOut),
      (292, endSnipArtWord vatOut saleOut) ]
    (endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut hloDog hloVat hloSale)
    (by simp [WindowDisjointFromWrites])]
  exact endSnipArtStoreHashMem_read64 σLoc I dogOut vatOut saleOut hloDog hloVat hloSale

theorem endSnipGrabPostCallMemFor_eq (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut ret : ByteArray) :
    endSnipGrabPostCallMemFor σCall σLoc I dogOut vatOut saleOut ret =
      endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut := by
  unfold endSnipGrabPostCallMemFor
  have hmin : (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endFreeGrabOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut)
    0 endFreeGrabOutPtr.toNat

theorem endSnipGrabCalldataMemFor_read128_4 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding 128 4 =
      grabSelector := by
  unfold endSnipGrabCalldataMemFor endSnipGrabWritesFor
  rw [writeCascade_read_window_of_head
    (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
    128 0 4 endFreeGrabSelectorShifted
    [ (132, endSnipIlkWord I),
      (164, endSnipSaleUsrAddrWord saleOut),
      (196, endSnipThisWord I),
      (228, endPackVowWord σCall I),
      (260, endSnipSaleLotWord saleOut),
      (292, endSnipArtWord vatOut saleOut) ]]
  · unfold endFreeGrabSelectorShifted grabSelector selectorBytes
    native_decide
  · rw [endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut hloDog hloVat hloSale]
    native_decide
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endSnipGrabCalldataMemFor_read132_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding 132 32 =
      (endSnipIlkWord I).toByteArray := by
  unfold endSnipGrabCalldataMemFor endSnipGrabWritesFor
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) 128
      endFreeGrabSelectorShifted)
    (word := endSnipIlkWord I)
    (rest :=
      [ (164, endSnipSaleUsrAddrWord saleOut),
        (196, endSnipThisWord I),
        (228, endPackVowWord σCall I),
        (260, endSnipSaleLotWord saleOut),
        (292, endSnipArtWord vatOut saleOut) ])
    (hbase := by
      rw [writeWord_size]
      · rw [endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut hloDog hloVat hloSale]
        native_decide)
    (hgap := by
      rw [endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut hloDog hloVat hloSale]
      native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSnipGrabCalldataMemFor_read164_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding 164 32 =
      (endSnipSaleUsrAddrWord saleOut).toByteArray := by
  unfold endSnipGrabCalldataMemFor endSnipGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) 128
        endFreeGrabSelectorShifted)
      132 (endSnipIlkWord I))
    (word := endSnipSaleUsrAddrWord saleOut)
    (rest :=
      [ (196, endSnipThisWord I),
        (228, endPackVowWord σCall I),
        (260, endSnipSaleLotWord saleOut),
        (292, endSnipArtWord vatOut saleOut) ])
    (hbase := by
      change (writeCascade (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
        [(128, endFreeGrabSelectorShifted), (132, endSnipIlkWord I)]).size = 320
      exact writeCascade_size_of_base
        (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
        [(128, endFreeGrabSelectorShifted), (132, endSnipIlkWord I)]
        (endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut hloDog hloVat hloSale)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSnipGrabCalldataMemFor_read196_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding 196 32 =
      (endSnipThisWord I).toByteArray := by
  unfold endSnipGrabCalldataMemFor endSnipGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) 128
          endFreeGrabSelectorShifted)
        132 (endSnipIlkWord I))
      164 (endSnipSaleUsrAddrWord saleOut))
    (word := endSnipThisWord I)
    (rest :=
      [ (228, endPackVowWord σCall I),
        (260, endSnipSaleLotWord saleOut),
        (292, endSnipArtWord vatOut saleOut) ])
    (hbase := by
      change (writeCascade (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
        [(128, endFreeGrabSelectorShifted), (132, endSnipIlkWord I),
          (164, endSnipSaleUsrAddrWord saleOut)]).size = 320
      exact writeCascade_size_of_base
        (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
        [(128, endFreeGrabSelectorShifted), (132, endSnipIlkWord I),
          (164, endSnipSaleUsrAddrWord saleOut)]
        (endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut hloDog hloVat hloSale)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSnipGrabCalldataMemFor_read228_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding 228 32 =
      (endPackVowWord σCall I).toByteArray := by
  unfold endSnipGrabCalldataMemFor endSnipGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) 128
            endFreeGrabSelectorShifted)
          132 (endSnipIlkWord I))
        164 (endSnipSaleUsrAddrWord saleOut))
      196 (endSnipThisWord I))
    (word := endPackVowWord σCall I)
    (rest :=
      [ (260, endSnipSaleLotWord saleOut),
        (292, endSnipArtWord vatOut saleOut) ])
    (hbase := by
      change (writeCascade (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
        [(128, endFreeGrabSelectorShifted), (132, endSnipIlkWord I),
          (164, endSnipSaleUsrAddrWord saleOut), (196, endSnipThisWord I)]).size = 320
      exact writeCascade_size_of_base
        (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
        [(128, endFreeGrabSelectorShifted), (132, endSnipIlkWord I),
          (164, endSnipSaleUsrAddrWord saleOut), (196, endSnipThisWord I)]
        (endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut hloDog hloVat hloSale)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSnipGrabCalldataMemFor_read260_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding 260 32 =
      (endSnipSaleLotWord saleOut).toByteArray := by
  unfold endSnipGrabCalldataMemFor endSnipGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord
            (writeWord (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) 128
              endFreeGrabSelectorShifted)
            132 (endSnipIlkWord I))
          164 (endSnipSaleUsrAddrWord saleOut))
        196 (endSnipThisWord I))
      228 (endPackVowWord σCall I))
    (word := endSnipSaleLotWord saleOut)
    (rest := [ (292, endSnipArtWord vatOut saleOut) ])
    (hbase := by
      change (writeCascade (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
        [(128, endFreeGrabSelectorShifted), (132, endSnipIlkWord I),
          (164, endSnipSaleUsrAddrWord saleOut), (196, endSnipThisWord I),
          (228, endPackVowWord σCall I)]).size = 320
      exact writeCascade_size_of_base
        (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
        [(128, endFreeGrabSelectorShifted), (132, endSnipIlkWord I),
          (164, endSnipSaleUsrAddrWord saleOut), (196, endSnipThisWord I),
          (228, endPackVowWord σCall I)]
        (endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut hloDog hloVat hloSale)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSnipGrabCalldataMemFor_read292_32 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding 292 32 =
      (endSnipArtWord vatOut saleOut).toByteArray := by
  unfold endSnipGrabCalldataMemFor endSnipGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord
            (writeWord
              (writeWord (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) 128
                endFreeGrabSelectorShifted)
              132 (endSnipIlkWord I))
            164 (endSnipSaleUsrAddrWord saleOut))
          196 (endSnipThisWord I))
        228 (endPackVowWord σCall I))
      260 (endSnipSaleLotWord saleOut))
    (word := endSnipArtWord vatOut saleOut)
    (rest := [])
    (hbase := by
      change (writeCascade (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
        [(128, endFreeGrabSelectorShifted), (132, endSnipIlkWord I),
          (164, endSnipSaleUsrAddrWord saleOut), (196, endSnipThisWord I),
          (228, endPackVowWord σCall I), (260, endSnipSaleLotWord saleOut)]).size = 320
      exact writeCascade_size_of_base
        (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut)
        [(128, endFreeGrabSelectorShifted), (132, endSnipIlkWord I),
          (164, endSnipSaleUsrAddrWord saleOut), (196, endSnipThisWord I),
          (228, endPackVowWord σCall I), (260, endSnipSaleLotWord saleOut)]
        (endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut hloDog hloVat hloSale)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by native_decide)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSnipGrabCalldataMemFor_read128_196 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding 128 196 =
      grabSelector ++
        (endSnipIlkWord I).toByteArray ++
        (endSnipSaleUsrAddrWord saleOut).toByteArray ++
        (endSnipThisWord I).toByteArray ++
        (endPackVowWord σCall I).toByteArray ++
        (endSnipSaleLotWord saleOut).toByteArray ++
        (endSnipArtWord vatOut saleOut).toByteArray := by
  have hsize :
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).size = 324 :=
    endSnipGrabCalldataMemFor_size σCall σLoc I dogOut vatOut saleOut
      hloDog hloVat hloSale
  rw [show 196 = 4 + 192 from rfl,
    byteArray_readWithPadding_split
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut) 128 4 192
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 192 = 32 + 160 from rfl,
    byteArray_readWithPadding_split
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut) 132 32 160
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 160 = 32 + 128 from rfl,
    byteArray_readWithPadding_split
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut) 164 32 128
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut) 196 32 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut) 228 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut) 260 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [endSnipGrabCalldataMemFor_read128_4 σCall σLoc I dogOut vatOut saleOut
      hloDog hloVat hloSale,
    endSnipGrabCalldataMemFor_read132_32 σCall σLoc I dogOut vatOut saleOut
      hloDog hloVat hloSale,
    endSnipGrabCalldataMemFor_read164_32 σCall σLoc I dogOut vatOut saleOut
      hloDog hloVat hloSale,
    endSnipGrabCalldataMemFor_read196_32 σCall σLoc I dogOut vatOut saleOut
      hloDog hloVat hloSale,
    endSnipGrabCalldataMemFor_read228_32 σCall σLoc I dogOut vatOut saleOut
      hloDog hloVat hloSale,
    endSnipGrabCalldataMemFor_read260_32 σCall σLoc I dogOut vatOut saleOut
      hloDog hloVat hloSale,
    endSnipGrabCalldataMemFor_read292_32 σCall σLoc I dogOut vatOut saleOut
      hloDog hloVat hloSale]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endSnipGrabPostCallMemFor_size (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut ret : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabPostCallMemFor σCall σLoc I dogOut vatOut saleOut ret).size = 324 := by
  rw [endSnipGrabPostCallMemFor_eq]
  exact endSnipGrabCalldataMemFor_size σCall σLoc I dogOut vatOut saleOut
    hloDog hloVat hloSale

theorem endSnipGrabPostCallMemFor_read64 (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (dogOut vatOut saleOut ret : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipGrabPostCallMemFor σCall σLoc I dogOut vatOut saleOut ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rw [endSnipGrabPostCallMemFor_eq]
  exact endSnipGrabCalldataMemFor_read64 σCall σLoc I dogOut vatOut saleOut
    hloDog hloVat hloSale

theorem endSnipLogDataMemFor_size (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipLogDataMemFor σCall σLoc I dogOut vatOut saleOut ret).size = 324 := by
  unfold endSnipLogDataMemFor
  rw [endSnipGrabPostCallMemFor_eq]
  exact toByteArray_write32_size_of_le
    (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut)
    (endSnipSaleTabWord saleOut) 128 324 324
    (endSnipGrabCalldataMemFor_size σCall σLoc I dogOut vatOut saleOut
      hloDog hloVat hloSale)
    (by rw [endSnipGrabCalldataMemFor_size σCall σLoc I dogOut vatOut saleOut
      hloDog hloVat hloSale]; omega)
    (by omega)

theorem endSnipLogDataMemFor_read64 (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipLogDataMemFor σCall σLoc I dogOut vatOut saleOut ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipLogDataMemFor
  rw [toByteArray_write_read_below_of_gap (endSnipSaleTabWord saleOut)
    (endSnipGrabPostCallMemFor σCall σLoc I dogOut vatOut saleOut ret) 128 64
    (by rw [endSnipGrabPostCallMemFor_eq,
      endSnipGrabCalldataMemFor_size σCall σLoc I dogOut vatOut saleOut
        hloDog hloVat hloSale]; omega)
    (by omega)
    (by rw [endSnipGrabPostCallMemFor_eq,
      endSnipGrabCalldataMemFor_size σCall σLoc I dogOut vatOut saleOut
        hloDog hloVat hloSale]; native_decide)]
  exact endSnipGrabPostCallMemFor_read64 σCall σLoc I dogOut vatOut saleOut ret
    hloDog hloVat hloSale

theorem endSnipLogDataMem2For_size (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipLogDataMem2For σCall σLoc I dogOut vatOut saleOut ret).size = 324 := by
  unfold endSnipLogDataMem2For
  exact toByteArray_write32_size_of_le
    (endSnipLogDataMemFor σCall σLoc I dogOut vatOut saleOut ret)
    (endSnipSaleLotWord saleOut) 160 324 324
    (endSnipLogDataMemFor_size σCall σLoc I dogOut vatOut saleOut ret
      hloDog hloVat hloSale)
    (by rw [endSnipLogDataMemFor_size σCall σLoc I dogOut vatOut saleOut ret
      hloDog hloVat hloSale]; omega)
    (by omega)

theorem endSnipLogDataMem2For_read64 (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipLogDataMem2For σCall σLoc I dogOut vatOut saleOut ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipLogDataMem2For
  rw [toByteArray_write_read_below_of_gap (endSnipSaleLotWord saleOut)
    (endSnipLogDataMemFor σCall σLoc I dogOut vatOut saleOut ret) 160 64
    (by rw [endSnipLogDataMemFor_size σCall σLoc I dogOut vatOut saleOut ret
      hloDog hloVat hloSale]; omega)
    (by omega)
    (by rw [endSnipLogDataMemFor_size σCall σLoc I dogOut vatOut saleOut ret
      hloDog hloVat hloSale]; native_decide)]
  exact endSnipLogDataMemFor_read64 σCall σLoc I dogOut vatOut saleOut ret
    hloDog hloVat hloSale

theorem endSnipLogDataMem3For_size (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipLogDataMem3For σCall σLoc I dogOut vatOut saleOut ret).size = 324 := by
  unfold endSnipLogDataMem3For
  exact toByteArray_write32_size_of_le
    (endSnipLogDataMem2For σCall σLoc I dogOut vatOut saleOut ret)
    (endSnipArtWord vatOut saleOut) 192 324 324
    (endSnipLogDataMem2For_size σCall σLoc I dogOut vatOut saleOut ret
      hloDog hloVat hloSale)
    (by rw [endSnipLogDataMem2For_size σCall σLoc I dogOut vatOut saleOut ret
      hloDog hloVat hloSale]; omega)
    (by omega)

theorem endSnipLogDataMem3For_read64 (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut ret : ByteArray)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) :
    (endSnipLogDataMem3For σCall σLoc I dogOut vatOut saleOut ret).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSnipLogDataMem3For
  rw [toByteArray_write_read_below_of_gap (endSnipArtWord vatOut saleOut)
    (endSnipLogDataMem2For σCall σLoc I dogOut vatOut saleOut ret) 192 64
    (by rw [endSnipLogDataMem2For_size σCall σLoc I dogOut vatOut saleOut ret
      hloDog hloVat hloSale]; omega)
    (by omega)
    (by rw [endSnipLogDataMem2For_size σCall σLoc I dogOut vatOut saleOut ret
      hloDog hloVat hloSale]; native_decide)]
  exact endSnipLogDataMem2For_read64 σCall σLoc I dogOut vatOut saleOut ret
    hloDog hloVat hloSale

theorem endSnipThisWordOfAddr (I : ExecutionEnv) :
    EVM.word ↑I.codeOwner = endSnipThisWord I := by
  change UInt256.ofNat I.codeOwner.val = endSnipThisWord I
  rfl

theorem endSnipSaleUsrWordOfAddr (saleOut : ByteArray) :
    EVM.word ↑(endSnipSaleUsrAddr saleOut) = endSnipSaleUsrAddrWord saleOut := by
  change UInt256.ofNat (endSnipSaleUsrAddr saleOut).val = endSnipSaleUsrAddrWord saleOut
  simpa [endSnipSaleUsrAddr, endSnipSaleUsrAddrWord] using
    (keyValueToWord_address (AccountAddress.ofNat (endSnipSaleUsrWord saleOut).toNat)).symm.trans
      (keyValueToWord_address_ofNat_mask (endSnipSaleUsrWord saleOut))

theorem endSnipGrabEncodeFor_eq (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (hlot : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hart : (endSnipArtWord vatOut saleOut).toNat < 2 ^ 255) :
    config.externalABI.encode? "grab"
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSnipSaleUsrAddr saleOut),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
          .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)] =
      some ((endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding
        endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat) := by
  change config.externalABI.encode? "grab"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address (endSnipSaleUsrAddr saleOut),
        .address I.codeOwner,
        .address (endPackVowAddr σCall I),
        .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
        .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)] =
    some ((endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding 128 196)
  rw [endSnipGrabCalldataMemFor_read128_196 σCall σLoc I dogOut vatOut saleOut
    hloDog hloVat hloSale]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endSnipIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) (by omega)
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endSnipIlkWord I := by
      simpa [endBytes32ArgBytes, endSnipIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by omega))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have husrWord : EVM.word ↑(endSnipSaleUsrAddr saleOut) =
      endSnipSaleUsrAddrWord saleOut :=
    endSnipSaleUsrWordOfAddr saleOut
  have hthisWord : EVM.word ↑I.codeOwner = endSnipThisWord I :=
    endSnipThisWordOfAddr I
  have hvowWord : EVM.word ↑(endPackVowAddr σCall I) = endPackVowWord σCall I :=
    endSnipVowWordOfAddr σCall I
  have hlotWord :
      EVM.wordOfInt (Int.ofNat (endSnipSaleLotWord saleOut).toNat) =
        endSnipSaleLotWord saleOut :=
    wordOfInt_ofNat_toNat (endSnipSaleLotWord saleOut)
  have hlotWordCast :
      EVM.wordOfInt ((endSnipSaleLotWord saleOut).toNat : Int) =
        endSnipSaleLotWord saleOut := by
    simpa using hlotWord
  have hartWord :
      EVM.wordOfInt (Int.ofNat (endSnipArtWord vatOut saleOut).toNat) =
        endSnipArtWord vatOut saleOut :=
    wordOfInt_ofNat_toNat (endSnipArtWord vatOut saleOut)
  have hartWordCast :
      EVM.wordOfInt ((endSnipArtWord vatOut saleOut).toNat : Int) =
        endSnipArtWord vatOut saleOut := by
    simpa using hartWord
  have hlotUpper : (endSnipSaleLotWord saleOut).toNat < EVM.twoPow 255 := by
    simpa [EVM.twoPow] using hlot
  have hartUpper : (endSnipArtWord vatOut saleOut).toNat < EVM.twoPow 255 := by
    simpa [EVM.twoPow] using hart
  have hbytesLen : (EVM.Word.toBytesBE (endSnipIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endSnipIlkWord I)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, int256,
    int256Int, grabSelector, selectorBytes, hbytes, hbytesLen, husrWord, hthisWord,
    hvowWord]
  rw [if_pos hlotUpper, if_pos hartUpper]
  simp [hlotWordCast, hartWordCast, word_toBytesBE_toByteArray_eq_toByteArray, zeroBytes,
    ByteArray.append_assoc]

theorem endDecode_snip_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (snipTransition.params.map Param.name)
      (transitionSignature snipTransition).paramTypes I.calldata = some (endSnipStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "id"] [bytes32, uint256]
    I.calldata = _
  simpa [config, snipTransition, bytes32, bytes32Width, uint256, uint256Int,
    endSnipStore, endSnipIlkBytes, endSnipIdWord, abiBytes32, abiBytes32Width,
    abiUInt256] using
    (decode_legacyBytes32_uint256_ok (cd := I.calldata) (x := "ilk")
      (y := "id") hsz68)

theorem endDecode_snip_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (snipTransition.params.map Param.name)
      (transitionSignature snipTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "id"] [bytes32, uint256]
    I.calldata = none
  simpa [config, snipTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    (decode_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "ilk")
      (y := "id") hsz4 hshort)

theorem endReachSnipBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endSnipConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState σ σ₀ g A I)
        endSnipEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty σ k C := by
  have hword : endSelWord I = ⟨0x38c6de40⟩ :=
    endSelWord_eq_of_beq I hsz 0x38 0xc6 0xde 0x40 ⟨0x38c6de40⟩
      (by native_decide)
      (by simpa [selIs, endSnipConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachDebtFirstArm (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDebtFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endDebtFirstArmPc 3))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endSnipEntryPc 3 hfirst
    (fun j hj => endGroup452ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem RD.endSnipDecodeToBody {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD code ee g s0 endSnipDecodedPc (de :: ⟨4⟩ :: ret :: sel :: R)
        mem aw rdata acc k C)
    (hwf : code = endBytecode)
    (hroutine : (D_J code 0).contains endSnipBodyPc = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 endSnipBodyPc
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd622 := h.jumpdest (by native_decide) (by evm_ov)
  have rd623 := rd622.pop (by native_decide) (by evm_ov)
  have rd624 := rd623.dup1 (by native_decide) (by evm_ov)
  have rd625 := rd624.calldataload (by native_decide) (by evm_ov)
  have rd626 := rd625.swap1 (by native_decide) (by evm_ov)
  have rd628 := rd626.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd629 := rd628.add (by native_decide) (by evm_ov)
  have rd630 := rd629.calldataload (by native_decide) (by evm_ov)
  have rd631 := rd630.push2 endSnipBodyPc (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [endSnipBodyPc, endSnipDecodedPc, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd631.jump (by native_decide) hroutine (by evm_ov)⟩

theorem endSnipX_decoded {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState σ σ₀ g A I) endSnipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD endBytecode I g
        (initState σ σ₀ g A I) endSnipBodyPc
        [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endSnipEntryPc) (ret := endSnipReturnPc)
    (decoded := endSnipDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.endSnipDecodeToBody
    (code := endBytecode) (ret := endSnipReturnPc) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endSnipIdWord, endSnipIlkWord] using hroutine⟩

theorem endSnipX_tagZero {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState σ σ₀ g A I) endSnipBodyPc
      [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  let key := endSnipIlkWord I
  have hslot : endSnipTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endSnipTagSlot_eq (I := I) hsz68
  have rd1654pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1655 := rd1654pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1659pre := evm_run rd1655 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1660 := rd1659pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1663pre := evm_run rd1660 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd1664pre := rd1663pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1665raw⟩ := rd1664pre.sload (by native_decide) (by evm_ov)
  have htagRaw :
      solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = ⟨0⟩ := by
    rw [← hslot]
    simpa [-Std.ExtTreeMap.get?_eq_getElem?, key, endSnipTagWord, solcSlotWordAt] using htag
  have htagRaw' :
      (σ.get? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.getD (solcMappingSlot ⟨12⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWord] using htagRaw
  have rd1665zero := rd1665raw
  rw [htagRaw'] at rd1665zero
  obtain ⟨_, _, rd1665⟩ : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨1665⟩
        (⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        σ k' C' := by
    exact ⟨_, _, by simpa [endSnipBodyPc, key] using rd1665zero⟩
  have rd1668pre := rd1665.push2 ⟨1739⟩ (by native_decide) (by evm_ov)
  have rd1669pre := rd1668pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rd1669⟩ : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨1669⟩
        [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        σ k' C' := by
    exact ⟨_, _, by simpa using rd1669pre⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1669⟩) (len := ⟨23⟩)
    (rawWord := ⟨1662547331793263672767660296024730882676930893819124057⟩)
    (shift := ⟨74⟩)
    (word := UInt256.shiftLeft
      ⟨1662547331793263672767660296024730882676930893819124057⟩ ⟨74⟩)
    (op := .PUSH23) (width := 23)
    rd1669
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    (twoWordHashMem_size_96 key ⟨12⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨12⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_tagNonzero {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState σ σ₀ g A I) endSnipBodyPc
      [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1739⟩
      [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
      (twoWordHashMem (endSnipIlkWord I) ⟨12⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  let key := endSnipIlkWord I
  have hslot : endSnipTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endSnipTagSlot_eq (I := I) hsz68
  have rd1654pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1655 := rd1654pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1659pre := evm_run rd1655 with [
    raw push1 ⟨12⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd1660 := rd1659pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1663pre := evm_run rd1660 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd1664pre := rd1663pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by native_decide) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1665raw⟩ := rd1664pre.sload (by native_decide) (by evm_ov)
  have htagRaw :
      solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = endSnipTagWord σ I := by
    rw [← hslot]
    simp [endSnipTagWord, solcSlotWordAt]
  have htagRaw' :
      (σ.get? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.getD (solcMappingSlot ⟨12⟩ key) ⟨0⟩)) =
          endSnipTagWord σ I := by
    simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWord] using htagRaw
  have rd1665nzRaw := rd1665raw
  rw [htagRaw'] at rd1665nzRaw
  obtain ⟨_, _, rd1665nz⟩ : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨1665⟩
        (endSnipTagWord σ I :: endSnipIdWord I :: endSnipIlkWord I ::
          endSnipReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        σ k' C' := by
    exact ⟨_, _, by simpa [endSnipBodyPc, key] using rd1665nzRaw⟩
  have rd1668pre := rd1665nz.push2 ⟨1739⟩ (by native_decide) (by evm_ov)
  have rd1739pre := rd1668pre.jumpiT (by native_decide) htag (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [key] using rd1739pre⟩

theorem endSnipX_dogIlksExtcodesizeGuard {σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1739⟩
      [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
      (endSnipDogIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1804⟩
      (endSnipDogWord σ I :: endSnipDogWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSnipDogIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endSnipDogWord σ I ::
        ⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipDogIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty σ k' C' := by
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSnipDogIlksBaseMem I).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipDogIlksBaseMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endSnipDogIlksBaseMem_size I]; decide)
      (endSnipDogIlksBaseMem_read64 I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSnipDogIlksCalldataMem I).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipDogIlksCalldataMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endSnipDogIlksCalldataMem_size I]; decide) (endSnipDogIlksCalldataMem_read64 I)
  have hselectorShift :
      UInt256.shiftLeft (⟨0x6cb1c69b⟩ : UInt256) ⟨225⟩ =
        endFlowVatIlksSelectorShifted := by
    native_decide
  have hdogMask :
      UInt256.land solcAddrMask (solcSlotWordAt ⟨3⟩ σ I) = endSnipDogWord σ I := by
    simpa [endSnipDogWord, solcAddrMask] using
      u256_land_comm solcAddrMask (solcSlotWordAt ⟨3⟩ σ I)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hdogMaskRight :
      (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩).land
          (solcSlotWordAt ⟨3⟩ σ I) = endSnipDogWord σ I := by
    rw [haddrMask]
    exact hdogMask
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩) = endFlowVatIlksInSize := by
    native_decide
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨36⟩) = endFlowVatIlksEndPtr := by
    native_decide
  have rd1741 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1742raw⟩ := rd1741.sload (by native_decide) (by evm_ov)
  have rd1742 : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨1743⟩
        (solcSlotWordAt ⟨3⟩ σ I :: endSnipIdWord I :: endSnipIlkWord I ::
          endSnipReturnPc :: sel :: [])
        (endSnipDogIlksBaseMem I) (UInt256.ofNat 3)
        ByteArray.empty σ k' C' := by
    exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWordAt, solcSlotWord] using rd1742raw⟩
  obtain ⟨_, _, rd1742⟩ := rd1742
  have rd1804 := evm_run rd1742 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨0x6cb1c69b⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨225⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (endFlowVatIlksSelectorMem (endSnipDogIlksBaseMem I))
      (UInt256.ofNat 5) (by native_decide) mem_cost
      (by
        simp [endFlowVatIlksSelectorMem, endFlowVatIlksOutPtr,
          endSnipDogIlksBaseMem, hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 (endSnipDogIlksCalldataMem I) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simp [endSnipDogIlksCalldataMem, endFlowVatIlksCalldataMem,
          endFlowVatIlksArg0Mem, endFlowVatIlksOutPtr, endSnipDogIlksBaseMem])
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 endFlowVatIlksSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    convert rd1804 using 1
    all_goals
      try native_decide
      try simp [endFlowVatIlksOutPtr, endFlowVatIlksInSize,
        endSnipDogIlksOutSize, endFlowVatIlksEndPtr, hdogMaskRight, hinSize, hendPtr]
      try native_decide⟩

theorem endSnipX_dogIlksNoCode {σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1739⟩
      [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
      (endSnipDogIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) = ⟨0⟩) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd1804⟩ := endSnipX_dogIlksExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1804⟩) (okPc := ⟨1816⟩) rd1804
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_dogIlksCallReady {σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1739⟩
      [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel]
      (endSnipDogIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1819⟩
      (gasWord :: endSnipDogWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSnipDogIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endSnipDogWord σ I ::
        ⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipDogIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty σ k' C' := by
  obtain ⟨_, _, rd1804⟩ := endSnipX_dogIlksExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd1819⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1804⟩) (okPc := ⟨1816⟩) rd1804
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd1819⟩

theorem endSnipX_dogIlksPostCall {σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1819⟩
      (gasWord :: endSnipDogWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSnipDogIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endSnipDogWord σ I ::
        ⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipDogIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty σ k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (σ', g'', A', z, out) = Ethereum.EVM.Θ σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endSnipDogWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (endSnipDogWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSnipDogIlksCalldataMem I).readWithPadding
            endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks I.perm)
      ∧ RD endBytecode I g (initState σ σ₀ g A I) ⟨1820⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFlowVatIlksEndPtr ::
            endFlowVatIlksSelectorWord :: endSnipDogWord σ I :: ⟨0⟩ ::
            endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
          (endSnipDogIlksPostCallMem I out) (UInt256.ofNat 8) out σ' k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨σ', z, out, Ain, callGas, k', C', hΘ, rd1820raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endSnipDogIlksWriteLen_eq (out := out) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          endFlowVatIlksOutPtr.toNat endSnipDogIlksOutSize.toNat) = UInt256.ofNat 8 := by
      unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endSnipDogIlksOutSize
      native_decide
    simpa [endSnipDogIlksPostCallMem, endFlowVatIlksOutPtr, endFlowVatIlksInSize,
      endSnipDogIlksOutSize, endFlowVatIlksEndPtr, hmin, haw] using rd1820raw

theorem endSnipX_dogIlksCallDepthLimit {σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1819⟩
      (gasWord :: endSnipDogWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSnipDogIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endSnipDogWord σ I ::
        ⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipDogIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty σ k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1820⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endSnipDogWord σ I :: ⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipDogIlksCalldataMem I) (UInt256.ofNat 8)
      ByteArray.empty σ k' C' := by
  obtain ⟨k', C', rd1820raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endSnipDogIlksOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
        endFlowVatIlksOutPtr.toNat endSnipDogIlksOutSize.toNat) = UInt256.ofNat 8 := by
    unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endSnipDogIlksOutSize
    native_decide
  simpa [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endSnipDogIlksOutSize,
    endFlowVatIlksEndPtr, hmin, byteArray_write_len_zero, haw] using rd1820raw

theorem endSnipX_dogIlksCallFailed {σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1820⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endSnipDogWord σ I :: ⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 8) rdata σ' k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1820⟩) (okPc := ⟨1836⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_dogIlksCallSucceeded {σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1820⟩
      (⟨1⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endSnipDogWord σ I :: ⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 8) rdata σ' k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1841⟩
      (⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 8) rdata σ' k' C' := by
  obtain ⟨_, _, rd1838⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨1820⟩) (okPc := ⟨1836⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  have rd1841 := evm_run rd1838 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd1841⟩

theorem endSnipX_dogIlksReturnDecodeOk {σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1841⟩
      (⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipDogIlksPostCallMem I out) (UInt256.ofNat 8) out σ' k C)
    (hlo : 128 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1861⟩
      (endSnipDogIlkClipWord out :: ⟨0⟩ :: endSnipIdWord I ::
        endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipDogIlksPostCallMem I out) (UInt256.ofNat 8) out σ' k' C' := by
  have hmload64 := endSnipDogIlksPostCallMem_mload64 I out
  have hmload128 := endSnipDogIlksPostCallMem_mload128_long I out hlo
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨128⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, ulit_toNat' out.size hout]
    exact hlo
  have rd1850 := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1858⟩ (by native_decide) (by evm_ov)]
  have rdJump := rd1850
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd1861 := evm_run rdJump with [
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw mload 0 (endSnipDogIlkClipWord out) (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload128 (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd1861⟩

theorem endSnipX_dogIlksReturnDecodeShort {σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1841⟩
      (⟨0⟩ :: endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipDogIlksPostCallMem I out) (UInt256.ofNat 8) out σ' k C)
    (hshort : out.size < 128) (hout : out.size < UInt256.size) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  have hmload64 := endSnipDogIlksPostCallMem_mload64 I out
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨128⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rd1850 := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1858⟩ (by native_decide) (by evm_ov)]
  have rdShort := rd1850
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFall
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_vatIlksExtcodesizeGuard {σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {dogOut : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1861⟩
      (endSnipDogIlkClipWord dogOut :: ⟨0⟩ :: endSnipIdWord I ::
        endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipDogIlksPostCallMem I dogOut) (UInt256.ofNat 8) dogOut σ' k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1930⟩
      (endPackVatWord σ' I :: endPackVatWord σ' I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ' I ::
        ⟨0⟩ :: endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipVatIlksCalldataMem I dogOut) (UInt256.ofNat 8)
      dogOut σ' k' C' := by
  have hmload64Base := endSnipDogIlksPostCallMem_mload64 I dogOut
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSnipVatIlksCalldataMem I dogOut).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipVatIlksCalldataMem I dogOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endSnipVatIlksCalldataMem_size_long I dogOut hloDog]; decide)
      (endSnipVatIlksCalldataMem_read64_long I dogOut hloDog)
  have hselectorShift :
      UInt256.shiftLeft (⟨0x6cb1c69b⟩ : UInt256) ⟨225⟩ =
        endFlowVatIlksSelectorShifted := by
    native_decide
  have hvatMask :
      UInt256.land solcAddrMask (solcSlotWordAt ⟨1⟩ σ' I) = endPackVatWord σ' I := by
    simpa [endPackVatWord, solcAddrMask] using
      u256_land_comm solcAddrMask (solcSlotWordAt ⟨1⟩ σ' I)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatMaskRight :
      (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩).land
          (solcSlotWordAt ⟨1⟩ σ' I) = endPackVatWord σ' I := by
    rw [haddrMask]
    exact hvatMask
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩) = endFlowVatIlksInSize := by
    native_decide
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨36⟩) = endFlowVatIlksEndPtr := by
    native_decide
  have rd1864 := evm_run h with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1864raw⟩ := rd1864.sload (by native_decide) (by evm_ov)
  have rd1864 : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨1864⟩
        (solcSlotWordAt ⟨1⟩ σ' I :: endSnipDogIlkClipWord dogOut :: ⟨0⟩ ::
          endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
        (endSnipDogIlksPostCallMem I dogOut) (UInt256.ofNat 8)
        dogOut σ' k' C' := by
    exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWordAt, solcSlotWord] using rd1864raw⟩
  obtain ⟨_, _, rd1864⟩ := rd1864
  have rd1929 := evm_run rd1864 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw push4 ⟨0x6cb1c69b⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨225⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endFlowVatIlksSelectorMem (endSnipDogIlksPostCallMem I dogOut))
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by
        simp [endFlowVatIlksSelectorMem, endFlowVatIlksOutPtr,
          hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipVatIlksCalldataMem I dogOut) (UInt256.ofNat 8)
      (by native_decide) mem_cost
      (by
        simp [endSnipVatIlksCalldataMem, endFlowVatIlksCalldataMem,
          endFlowVatIlksArg0Mem, endFlowVatIlksOutPtr])
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 endFlowVatIlksSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    convert rd1929 using 1
    all_goals
      try native_decide
      try simp [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endFlowVatIlksOutSize,
        endFlowVatIlksEndPtr, hvatMaskRight, hinSize, hendPtr]
      try native_decide⟩

theorem endSnipX_vatIlksNoCode {σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {dogOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1861⟩
      (endSnipDogIlkClipWord dogOut :: ⟨0⟩ :: endSnipIdWord I ::
        endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipDogIlksPostCallMem I dogOut) (UInt256.ofNat 8) dogOut σ' k C)
    (hloDog : 128 ≤ dogOut.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) = ⟨0⟩) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd1930⟩ := endSnipX_vatIlksExtcodesizeGuard hloDog h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1930⟩) (okPc := ⟨1942⟩) rd1930
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_vatIlksCallReady {σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {dogOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1861⟩
      (endSnipDogIlkClipWord dogOut :: ⟨0⟩ :: endSnipIdWord I ::
        endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipDogIlksPostCallMem I dogOut) (UInt256.ofNat 8) dogOut σ' k C)
    (hloDog : 128 ≤ dogOut.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1945⟩
      (gasWord :: endPackVatWord σ' I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ' I ::
        ⟨0⟩ :: endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipVatIlksCalldataMem I dogOut) (UInt256.ofNat 8)
      dogOut σ' k' C' := by
  obtain ⟨_, _, rd1930⟩ := endSnipX_vatIlksExtcodesizeGuard hloDog h
  obtain ⟨gasWord, k', C', rd1945⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1930⟩) (okPc := ⟨1942⟩) rd1930
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd1945⟩

theorem endSnipX_vatIlksPostCall {σ σcur σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {dogOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1945⟩
      (gasWord :: endPackVatWord σcur I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipVatIlksCalldataMem I dogOut) (UInt256.ofNat 8)
      dogOut σcur k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (σ', g'', A', z, out) = Ethereum.EVM.Θ σcur σ₀ Ain (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σcur I))
          (toExecute σcur (AccountAddress.ofUInt256 (endPackVatWord σcur I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSnipVatIlksCalldataMem I dogOut).readWithPadding
            endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks I.perm)
      ∧ RD endBytecode I g (initState σ σ₀ g A I) ⟨1946⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFlowVatIlksEndPtr ::
            endFlowVatIlksSelectorWord :: endPackVatWord σcur I :: ⟨0⟩ ::
            endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
            endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
          (endSnipVatIlksPostCallMem I dogOut out) (UInt256.ofNat 9) out
          σ' k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨σ', z, out, Ain, callGas, k', C', hΘ, rd1946raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endSnipVatIlksWriteLen_eq (out := out) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          endFlowVatIlksOutPtr.toNat endFlowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
      unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endFlowVatIlksOutSize
      native_decide
    simpa [endSnipVatIlksPostCallMem, endFlowVatIlksOutPtr, endFlowVatIlksInSize,
      endFlowVatIlksOutSize, endFlowVatIlksEndPtr, hmin, haw] using rd1946raw

theorem endSnipX_vatIlksCallDepthLimit {σ σcur σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {dogOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1945⟩
      (gasWord :: endPackVatWord σcur I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipVatIlksCalldataMem I dogOut) (UInt256.ofNat 8)
      dogOut σcur k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1946⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σcur I :: ⟨0⟩ :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipVatIlksCalldataMem I dogOut) (UInt256.ofNat 9) ByteArray.empty
      σcur k' C' := by
  obtain ⟨k', C', rd1946raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endFlowVatIlksOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
        endFlowVatIlksOutPtr.toNat endFlowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
    unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endFlowVatIlksOutSize
    native_decide
  simpa [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endFlowVatIlksOutSize,
    endFlowVatIlksEndPtr, hmin, byteArray_write_len_zero, haw] using rd1946raw

theorem endSnipX_vatIlksCallFailed {σ σcur σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut : ByteArray} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1946⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σcur I :: ⟨0⟩ :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata σ' k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1946⟩) (okPc := ⟨1962⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_vatIlksCallSucceeded {σ σcur σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut : ByteArray} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1946⟩
      (⟨1⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σcur I :: ⟨0⟩ :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata σ' k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1964⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata σ' k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨1946⟩) (okPc := ⟨1962⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem endSnipX_vatIlksReturnDecodeOk {σ σcur σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1964⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipVatIlksPostCallMem I dogOut vatOut) (UInt256.ofNat 9) vatOut
      σ' k C)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hout : vatOut.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨1990⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipVatIlksPostCallMem I dogOut vatOut) (UInt256.ofNat 9) vatOut
      σ' k' C' := by
  have hmload64 := endSnipVatIlksPostCallMem_mload64 I dogOut vatOut hloDog
  have hmload160 := endSnipVatIlksPostCallMem_mload160_long I dogOut vatOut hloDog hloVat
  have hlt : UInt256.lt (UInt256.ofNat vatOut.size) (⟨160⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      ulit_toNat' vatOut.size hout]
    exact hloVat
  have rd1978 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1984⟩ (by native_decide) (by evm_ov)]
  have rdJump := rd1978
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd1990 := evm_run rdJump with [
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mload 0 (endFlowVatIlkRateWord vatOut) (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload160 (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFlowVatIlksEndPtr, endFlowVatIlksSelectorWord, endFlowVatIlksOutPtr,
      endFlowVatIlksInSize, endFlowVatIlksOutSize] using rd1990⟩

theorem endSnipX_vatIlksReturnDecodeShort {σ σcur σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1964⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipVatIlksPostCallMem I dogOut vatOut) (UInt256.ofNat 9) vatOut
      σ' k C)
    (hloDog : 128 ≤ dogOut.size) (hshort : vatOut.size < 160)
    (hout : vatOut.size < UInt256.size) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  have hmload64 := endSnipVatIlksPostCallMem_mload64 I dogOut vatOut hloDog
  have hlt : UInt256.lt (UInt256.ofNat vatOut.size) (⟨160⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      ulit_toNat' vatOut.size hout]
    exact hshort
  have rd1978 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1984⟩ (by native_decide) (by evm_ov)]
  have rdShort := rd1978
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFall
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_salesExtcodesizeGuard {σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1990⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipVatIlksPostCallMem I dogOut vatOut) (UInt256.ofNat 9) vatOut
      σ' k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2058⟩
      (endSnipSalesClipWord dogOut :: endSnipSalesClipWord dogOut ::
        endFlowVatIlksOutPtr :: endFlowVatIlksInSize :: endFlowVatIlksOutPtr ::
        endSnipSalesOutSize :: endFlowVatIlksEndPtr :: endSnipSalesSelectorWord ::
        endSnipSalesClipWord dogOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipSalesCalldataMem I dogOut vatOut) (UInt256.ofNat 9) vatOut
      σ' k' C' := by
  have hmload64Base := endSnipVatIlksPostCallMem_mload64 I dogOut vatOut hloDog
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSnipSalesCalldataMem I dogOut vatOut).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipSalesCalldataMem I dogOut vatOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endSnipSalesCalldataMem_size_long I dogOut vatOut hloDog hloVat]; decide)
      (endSnipSalesCalldataMem_read64_long I dogOut vatOut hloDog hloVat)
  have hselectorShift :
      UInt256.shiftLeft endSnipSalesSelectorWord ⟨224⟩ =
        endSnipSalesSelectorShifted := by
    native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclipMaskRight :
      (endSnipDogIlkClipWord dogOut).land
          (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) =
        endSnipSalesClipWord dogOut := by
    rw [haddrMask]
    simpa [endSnipSalesClipWord] using
      u256_land_comm (endSnipDogIlkClipWord dogOut) solcAddrMask
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩) = endFlowVatIlksInSize := by
    native_decide
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨36⟩) = endFlowVatIlksEndPtr := by
    native_decide
  have rd2058 := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw push4 endSnipSalesSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipSalesSelectorMem I dogOut vatOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by
        simp [endSnipSalesSelectorMem, endFlowVatIlksOutPtr, hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipSalesCalldataMem I dogOut vatOut) (UInt256.ofNat 9)
      (by native_decide) mem_cost
      (by simp [endSnipSalesCalldataMem, endFlowVatIlksOutPtr])
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 endSnipSalesSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨192⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    convert rd2058 using 1
    all_goals
      try native_decide
      try simp [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endSnipSalesOutSize,
        endFlowVatIlksEndPtr, hclipMaskRight, hinSize, hendPtr]
      try native_decide⟩

theorem endSnipX_salesNoCode {σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1990⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipVatIlksPostCallMem I dogOut vatOut) (UInt256.ofNat 9) vatOut
      σ' k C)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endSnipSalesClipWord dogOut) = ⟨0⟩) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd2058⟩ := endSnipX_salesExtcodesizeGuard hloDog hloVat h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2058⟩) (okPc := ⟨2070⟩) rd2058
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_salesCallReady {σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨1990⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipVatIlksPostCallMem I dogOut vatOut) (UInt256.ofNat 9) vatOut
      σ' k C)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endSnipSalesClipWord dogOut) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2073⟩
      (gasWord :: endSnipSalesClipWord dogOut :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSnipSalesOutSize ::
        endFlowVatIlksEndPtr :: endSnipSalesSelectorWord ::
        endSnipSalesClipWord dogOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipSalesCalldataMem I dogOut vatOut) (UInt256.ofNat 9) vatOut
      σ' k' C' := by
  obtain ⟨_, _, rd2058⟩ := endSnipX_salesExtcodesizeGuard hloDog hloVat h
  obtain ⟨gasWord, k', C', rd2073⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2058⟩) (okPc := ⟨2070⟩) rd2058
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd2073⟩

theorem endSnipX_salesPostStaticcall {σ σcur σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {dogOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2073⟩
      (gasWord :: endSnipSalesClipWord dogOut :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSnipSalesOutSize ::
        endFlowVatIlksEndPtr :: endSnipSalesSelectorWord ::
        endSnipSalesClipWord dogOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipSalesCalldataMem I dogOut vatOut) (UInt256.ofNat 9) vatOut
      σcur k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (σ' : AccountMap)
      (z : Bool) (saleOut : ByteArray) (Ain : Substate) (callGas : UInt256)
      (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (σ', g'', A', z, saleOut) =
          Ethereum.EVM.Θ σcur σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (endSnipSalesClipWord dogOut))
            (toExecute σcur (AccountAddress.ofUInt256 (endSnipSalesClipWord dogOut)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endSnipSalesCalldataMem I dogOut vatOut).readWithPadding
              endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
            (I.depth + 1) I.header I.blobVersionedHashes I.blocks false)
      ∧ RD endBytecode I g (initState σ σ₀ g A I) ⟨2074⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFlowVatIlksEndPtr ::
            endSnipSalesSelectorWord :: endSnipSalesClipWord dogOut ::
            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut ::
            endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
            endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
          (endSnipSalesPostCallMem I dogOut vatOut saleOut) (UInt256.ofNat 10)
          saleOut σ' k' C'
      ∧ saleOut.size < UInt256.size := by
  obtain ⟨σ', z, saleOut, Ain, callGas, k', C', hΘ, rd2074raw, hout⟩ :=
    RD.solcStaticcall h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨σ', z, saleOut, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endSnipSalesWriteLen_eq (out := saleOut) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          endFlowVatIlksOutPtr.toNat endSnipSalesOutSize.toNat) = UInt256.ofNat 10 := by
      unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endSnipSalesOutSize
      native_decide
    simpa [endSnipSalesPostCallMem, endFlowVatIlksOutPtr, endFlowVatIlksInSize,
      endSnipSalesOutSize, endFlowVatIlksEndPtr, hmin, haw] using rd2074raw

theorem endSnipX_salesStaticcallDepthLimit {σ σcur σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {dogOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2073⟩
      (gasWord :: endSnipSalesClipWord dogOut :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSnipSalesOutSize ::
        endFlowVatIlksEndPtr :: endSnipSalesSelectorWord ::
        endSnipSalesClipWord dogOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipSalesCalldataMem I dogOut vatOut) (UInt256.ofNat 9) vatOut
      σcur k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2074⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endSnipSalesSelectorWord ::
        endSnipSalesClipWord dogOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipSalesCalldataMem I dogOut vatOut) (UInt256.ofNat 10) ByteArray.empty
      σcur k' C' := by
  obtain ⟨k', C', rd2074raw⟩ :=
    RD.solcStaticcallDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endSnipSalesOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
        endFlowVatIlksOutPtr.toNat endSnipSalesOutSize.toNat) = UInt256.ofNat 10 := by
    unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endSnipSalesOutSize
    native_decide
  simpa [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endSnipSalesOutSize,
    endFlowVatIlksEndPtr, hmin, byteArray_write_len_zero, haw] using rd2074raw

theorem endSnipX_salesCallFailed {σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2074⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endSnipSalesSelectorWord ::
        endSnipSalesClipWord dogOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 10) rdata σ' k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2074⟩) (okPc := ⟨2090⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_salesCallSucceeded {σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2074⟩
      (⟨1⟩ :: endFlowVatIlksEndPtr :: endSnipSalesSelectorWord ::
        endSnipSalesClipWord dogOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 10) rdata σ' k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2095⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 10) rdata σ' k' C' := by
  obtain ⟨_, _, rd2092⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2074⟩) (okPc := ⟨2090⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  have rd2095 := evm_run rd2092 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd2095⟩

theorem endSnipX_salesReturnDecodeOk {σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2095⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipSalesPostCallMem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      saleOut σ' k C)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size) (hout : saleOut.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2131⟩
      (endSnipSaleUsrWord saleOut :: ⟨64⟩ :: endSnipSaleTabWord saleOut ::
        endSnipSaleLotWord saleOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipSalesPostCallMem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      saleOut σ' k' C' := by
  have hmload64 := endSnipSalesPostCallMem_mload64 I dogOut vatOut saleOut hloDog hloVat
  have hmload160 :=
    endSnipSalesPostCallMem_mload160_long I dogOut vatOut saleOut hloDog hloVat hloSale
  have hmload192 :=
    endSnipSalesPostCallMem_mload192_long I dogOut vatOut saleOut hloDog hloVat hloSale
  have hmload224 :=
    endSnipSalesPostCallMem_mload224_long I dogOut vatOut saleOut hloDog hloVat hloSale
  have hlt : UInt256.lt (UInt256.ofNat saleOut.size) (⟨192⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide,
      ulit_toNat' saleOut.size hout]
    exact hloSale
  have rd2104 := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨192⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2112⟩ (by native_decide) (by evm_ov)]
  have rdJump := rd2104
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd2131 := evm_run rdJump with [
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mload 0 (endSnipSaleTabWord saleOut) (UInt256.ofNat 10) (by native_decide)
      mem_cost hmload160 (by decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mload 0 (endSnipSaleLotWord saleOut) (UInt256.ofNat 10) (by native_decide)
      mem_cost hmload192 (by decide) (by evm_ov),
    raw push1 ⟨96⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mload 0 (endSnipSaleUsrWord saleOut) (UInt256.ofNat 10) (by native_decide)
      mem_cost hmload224 (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd2131⟩

theorem endSnipX_salesReturnDecodeShort {σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2095⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipSalesPostCallMem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      saleOut σ' k C)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hshort : saleOut.size < 192) (hout : saleOut.size < UInt256.size) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  have hmload64 := endSnipSalesPostCallMem_mload64 I dogOut vatOut saleOut hloDog hloVat
  have hlt : UInt256.lt (UInt256.ofNat saleOut.size) (⟨192⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨192⟩ : UInt256).toNat = 192 from by decide,
      ulit_toNat' saleOut.size hout]
    exact hshort
  have rd2104 := evm_run h with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by native_decide) (by evm_ov),
    raw push1 ⟨192⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨2112⟩ (by native_decide) (by evm_ov)]
  have rdShort := rd2104
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFall
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

end Benchmarks.Dss.End

namespace Reasoning.Theory


end Reasoning.Theory

namespace Reasoning.Reach


end Reasoning.Reach

namespace Benchmarks.Dss.End


theorem endSnipX_suckExtcodesizeGuard {σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2131⟩
      (endSnipSaleUsrWord saleOut :: ⟨64⟩ :: endSnipSaleTabWord saleOut ::
        endSnipSaleLotWord saleOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipSalesPostCallMem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      saleOut σ' k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2220⟩
      (endPackVatWord σ' I :: endPackVatWord σ' I :: ⟨0⟩ ::
        endSnipSuckOutPtr :: endSnipSuckInSize :: endSnipSuckOutPtr ::
        endSnipSuckOutSize :: endSnipSuckEndPtr :: endSnipSuckSelectorWord ::
        endPackVatWord σ' I :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipSuckCalldataMem σ' I dogOut vatOut saleOut) (UInt256.ofNat 10)
      saleOut σ' k' C' := by
  have hmload64Base :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSnipSalesPostCallMem I dogOut vatOut saleOut).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipSalesPostCallMem I dogOut vatOut saleOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endSnipSalesPostCallMem_size_long I dogOut vatOut saleOut
        hloDog hloVat hloSale]; decide) (endSnipSalesPostCallMem_read64 I dogOut vatOut saleOut hloDog hloVat)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSnipSuckCalldataMem σ' I dogOut vatOut saleOut).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipSuckCalldataMem σ' I dogOut vatOut saleOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endSnipSuckCalldataMem_size σ' I dogOut vatOut saleOut
        hloDog hloVat hloSale]; decide) (endSnipSuckCalldataMem_read64 σ' I dogOut vatOut saleOut
        hloDog hloVat hloSale)
  have hselectorShift :
      UInt256.shiftLeft endSnipSuckSelectorWord ⟨224⟩ =
        endSnipSuckSelectorShifted := by
    native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hvatMask :
      UInt256.land (solcSlotWordAt ⟨1⟩ σ' I) solcAddrMask = endPackVatWord σ' I := by
    rfl
  have hvatMaskLeft :
      UInt256.land solcAddrMask (solcSlotWordAt ⟨1⟩ σ' I) = endPackVatWord σ' I := by
    simpa [endPackVatWord] using
      u256_land_comm solcAddrMask (solcSlotWordAt ⟨1⟩ σ' I)
  have hvowMask :
      UInt256.land (solcSlotWordAt ⟨4⟩ σ' I) solcAddrMask = endPackVowWord σ' I := by
    rfl
  have hvowMaskLeft :
      UInt256.land solcAddrMask (solcSlotWordAt ⟨4⟩ σ' I) = endPackVowWord σ' I := by
    simpa [endPackVowWord] using
      u256_land_comm solcAddrMask (solcSlotWordAt ⟨4⟩ σ' I)
  have rd2137 := evm_run h with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2138raw⟩ := rd2137.sload (by native_decide) (by evm_ov)
  have rd2134 : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨2134⟩
        (solcSlotWordAt ⟨1⟩ σ' I :: endSnipSaleUsrWord saleOut :: ⟨64⟩ ::
          endSnipSaleTabWord saleOut :: endSnipSaleLotWord saleOut :: ⟨0⟩ :: ⟨0⟩ ::
          ⟨0⟩ :: endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
          endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
          endSnipReturnPc :: sel :: [])
        (endSnipSalesPostCallMem I dogOut vatOut saleOut) (UInt256.ofNat 10)
        saleOut σ' k' C' := by
    exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWordAt, solcSlotWord] using rd2138raw⟩
  obtain ⟨_, _, rd2134⟩ := rd2134
  have rd2137 := evm_run rd2134 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2138raw⟩ := rd2137.sload (by native_decide) (by evm_ov)
  have rd2138 : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨2138⟩
        (solcSlotWordAt ⟨4⟩ σ' I :: ⟨4⟩ :: solcSlotWordAt ⟨1⟩ σ' I ::
          endSnipSaleUsrWord saleOut :: ⟨64⟩ :: endSnipSaleTabWord saleOut ::
          endSnipSaleLotWord saleOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
          endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
          endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
          endSnipReturnPc :: sel :: [])
        (endSnipSalesPostCallMem I dogOut vatOut saleOut) (UInt256.ofNat 10)
        saleOut σ' k' C' := by
    exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWordAt, solcSlotWord] using rd2138raw⟩
  obtain ⟨_, _, rd2138⟩ := rd2138
  have rd2220raw := evm_run rd2138 with [
    raw dup5 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw push4 endSnipSuckSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipSuckMem1 I dogOut vatOut saleOut) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by rw [hselectorShift]; rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipSuckMem2 σ' I dogOut vatOut saleOut) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 by native_decide]
        rw [haddrMask, hvowMaskLeft]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipSuckMem3 σ' I dogOut vatOut saleOut) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 by native_decide]
        rw [haddrMask, hvowMaskLeft]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipSuckCalldataMem σ' I dogOut vatOut saleOut)
      (UInt256.ofNat 10) (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 by native_decide]
        change (endSnipSaleTabWord saleOut).toByteArray.write 0
          (endSnipSuckMem3 σ' I dogOut vatOut saleOut) 196 32 =
          endSnipSuckCalldataMem σ' I dogOut vatOut saleOut
        simp [endSnipSuckCalldataMem, endSnipSuckMem1, endSnipSuckMem2,
          endSnipSuckMem3, writeCascade, Reasoning.Theory.writeWord])
      (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap9 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap7 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 endSnipSuckSelectorWord (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    convert rd2220raw using 1
    all_goals
      try native_decide
      try simp [endSnipSuckOutPtr, endSnipSuckInSize, endSnipSuckOutSize,
        endSnipSuckEndPtr, endSnipSuckSelectorWord, endPackVatWord, endPackVowWord,
        solcSlotWordAt, solcSlotWord, solcAddrMask, haddrMask, hvatMask, hvatMaskLeft,
        hvowMask, hvowMaskLeft]
      try native_decide⟩

theorem endSnipX_suckNoCode {σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2131⟩
      (endSnipSaleUsrWord saleOut :: ⟨64⟩ :: endSnipSaleTabWord saleOut ::
        endSnipSaleLotWord saleOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipSalesPostCallMem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      saleOut σ' k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) = ⟨0⟩) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd2220⟩ := endSnipX_suckExtcodesizeGuard hloDog hloVat hloSale h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2220⟩) (okPc := ⟨2232⟩) rd2220
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_suckCallReady {σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2131⟩
      (endSnipSaleUsrWord saleOut :: ⟨64⟩ :: endSnipSaleTabWord saleOut ::
        endSnipSaleLotWord saleOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipSalesPostCallMem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      saleOut σ' k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2235⟩
      (gasWord :: endPackVatWord σ' I :: ⟨0⟩ :: endSnipSuckOutPtr ::
        endSnipSuckInSize :: endSnipSuckOutPtr :: endSnipSuckOutSize ::
        endSnipSuckEndPtr :: endSnipSuckSelectorWord :: endPackVatWord σ' I ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipSuckCalldataMem σ' I dogOut vatOut saleOut) (UInt256.ofNat 10)
      saleOut σ' k' C' := by
  obtain ⟨_, _, rd2220⟩ := endSnipX_suckExtcodesizeGuard hloDog hloVat hloSale h
  obtain ⟨gasWord, k', C', rd2235⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2220⟩) (okPc := ⟨2232⟩) rd2220
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd2235⟩

theorem endSnipX_suckPostCall {σ σ' σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {dogOut vatOut saleOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2235⟩
      (gasWord :: endPackVatWord σ' I :: ⟨0⟩ :: endSnipSuckOutPtr ::
        endSnipSuckInSize :: endSnipSuckOutPtr :: endSnipSuckOutSize ::
        endSnipSuckEndPtr :: endSnipSuckSelectorWord :: endPackVatWord σ' I ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipSuckCalldataMem σ' I dogOut vatOut saleOut) (UInt256.ofNat 10)
      saleOut σ' k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (σ'' : AccountMap)
      (z : Bool) (ret : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (σ'', g'', A', z, ret) = Ethereum.EVM.Θ σ' σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (endPackVatWord σ' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSnipSuckCalldataMem σ' I dogOut vatOut saleOut).readWithPadding
            endSnipSuckOutPtr.toNat endSnipSuckInSize.toNat)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks I.perm)
      ∧ RD endBytecode I g (initState σ σ₀ g A I) ⟨2236⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endSnipSuckEndPtr ::
            endSnipSuckSelectorWord :: endPackVatWord σ' I ::
            endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
            endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
            endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
            endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
          (endSnipSuckPostCallMem σ' I dogOut vatOut saleOut ret)
          (UInt256.ofNat 10) ret σ'' k' C'
      ∧ ret.size < UInt256.size := by
  obtain ⟨σ'', z, ret, Ain, callGas, k', C', hΘ, rd2236raw, hret⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨σ'', z, ret, Ain, callGas, k', C', ?_, ?_, hret⟩
  · simpa [initState] using hΘ
  · have hmin : (min endSnipSuckOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
        show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
        exact Nat.zero_le _
      simp [endSnipSuckOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 10).toNat
          endSnipSuckOutPtr.toNat endSnipSuckInSize.toNat)
          endSnipSuckOutPtr.toNat endSnipSuckOutSize.toNat) = UInt256.ofNat 10 := by
      unfold endSnipSuckOutPtr endSnipSuckInSize endSnipSuckOutSize
      native_decide
    simpa [endSnipSuckPostCallMem, endSnipSuckOutPtr, endSnipSuckInSize,
      endSnipSuckOutSize, endSnipSuckEndPtr, hmin, byteArray_write_len_zero, haw]
      using rd2236raw

theorem endSnipX_suckCallDepthLimit {σ σ' σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {dogOut vatOut saleOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2235⟩
      (gasWord :: endPackVatWord σ' I :: ⟨0⟩ :: endSnipSuckOutPtr ::
        endSnipSuckInSize :: endSnipSuckOutPtr :: endSnipSuckOutSize ::
        endSnipSuckEndPtr :: endSnipSuckSelectorWord :: endPackVatWord σ' I ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipSuckCalldataMem σ' I dogOut vatOut saleOut) (UInt256.ofNat 10)
      saleOut σ' k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2236⟩
      (⟨0⟩ :: endSnipSuckEndPtr :: endSnipSuckSelectorWord :: endPackVatWord σ' I ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipSuckCalldataMem σ' I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ByteArray.empty σ' k' C' := by
  obtain ⟨k', C', rd2236raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endSnipSuckOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 10).toNat
        endSnipSuckOutPtr.toNat endSnipSuckInSize.toNat)
        endSnipSuckOutPtr.toNat endSnipSuckOutSize.toNat) = UInt256.ofNat 10 := by
    unfold endSnipSuckOutPtr endSnipSuckInSize endSnipSuckOutSize
    native_decide
  simpa [endSnipSuckOutPtr, endSnipSuckInSize, endSnipSuckOutSize,
    endSnipSuckEndPtr, hmin, byteArray_write_len_zero, haw] using rd2236raw

theorem endSnipX_suckCallFailed {σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2236⟩
      (⟨0⟩ :: endSnipSuckEndPtr :: endSnipSuckSelectorWord :: endPackVatWord σpre I ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 10) rdata σpost k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2236⟩) (okPc := ⟨2252⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_suckCallSucceeded {σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2236⟩
      (⟨1⟩ :: endSnipSuckEndPtr :: endSnipSuckSelectorWord :: endPackVatWord σpre I ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 10) rdata σpost k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2257⟩
      (endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 10) rdata σpost k' C' := by
  obtain ⟨_, _, rd2254⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2236⟩) (okPc := ⟨2252⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  have rd2257 := evm_run rd2254 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd2257⟩

theorem endSnipX_yankExtcodesizeGuard {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut rdata : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2257⟩
      (endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipSuckCalldataMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      rdata σpost k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2314⟩
      (endSnipSalesClipWord dogOut :: endSnipSalesClipWord dogOut :: ⟨0⟩ ::
        endSnipYankOutPtr :: endSnipYankInSize :: endSnipYankOutPtr ::
        endSnipYankOutSize :: endSnipYankEndPtr :: endSnipYankSelectorWord ::
        endSnipSalesClipWord dogOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipYankCalldataMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      rdata σpost k' C' := by
  have hmload64Base :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSnipSuckCalldataMem σmem I dogOut vatOut saleOut).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipSuckCalldataMem σmem I dogOut vatOut saleOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endSnipSuckCalldataMem_size σmem I dogOut vatOut saleOut
        hloDog hloVat hloSale]; decide) (endSnipSuckCalldataMem_read64 σmem I dogOut vatOut saleOut
        hloDog hloVat hloSale)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSnipYankCalldataMem σmem I dogOut vatOut saleOut).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipYankCalldataMem σmem I dogOut vatOut saleOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endSnipYankCalldataMem_size σmem I dogOut vatOut saleOut
        hloDog hloVat hloSale]; decide) (endSnipYankCalldataMem_read64 σmem I dogOut vatOut saleOut
        hloDog hloVat hloSale)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hclipMaskLeft :
      UInt256.land (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩)
          (endSnipDogIlkClipWord dogOut) =
        endSnipSalesClipWord dogOut := by
    rw [haddrMask]
  have hclipMaskRight :
      UInt256.land (endSnipDogIlkClipWord dogOut)
          (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) =
        endSnipSalesClipWord dogOut := by
    rw [haddrMask]
    simpa [endSnipSalesClipWord] using
      u256_land_comm (endSnipDogIlkClipWord dogOut) solcAddrMask
  have hselectorMaskShift :
      UInt256.shiftLeft (UInt256.land endSnipYankSelectorWord ⟨0xffffffff⟩) ⟨224⟩ =
        endSnipYankSelectorShifted := by
    native_decide
  have hselectorMaskShiftLeft :
      UInt256.shiftLeft (UInt256.land ⟨0xffffffff⟩ endSnipYankSelectorWord) ⟨224⟩ =
        endSnipYankSelectorShifted := by
    native_decide
  have rd2314raw := evm_run h with [
    raw dup5 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push4 endSnipYankSelectorWord (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push4 ⟨0xffffffff⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipYankMem1 σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by rw [hselectorMaskShiftLeft]; rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipYankCalldataMem σmem I dogOut vatOut saleOut)
      (UInt256.ofNat 10) (by native_decide) mem_cost
      (by
        rw [show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 by native_decide]
        change (endSnipIdWord I).toByteArray.write 0
          (endSnipYankMem1 σmem I dogOut vatOut saleOut) 132 32 =
          endSnipYankCalldataMem σmem I dogOut vatOut saleOut
        simp [endSnipYankCalldataMem, endSnipYankMem1, writeCascade,
          Reasoning.Theory.writeWord])
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endSnipYankOutPtr, endSnipYankInSize, endSnipYankOutSize,
      endSnipYankEndPtr, endSnipYankSelectorWord, haddrMask, hclipMaskLeft,
      hclipMaskRight] using rd2314raw⟩

theorem endSnipX_yankNoCode {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut rdata : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2257⟩
      (endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipSuckCalldataMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      rdata σpost k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σpost (endSnipSalesClipWord dogOut) = ⟨0⟩) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd2314⟩ := endSnipX_yankExtcodesizeGuard hloDog hloVat hloSale h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2314⟩) (okPc := ⟨2326⟩) rd2314
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_yankCallReady {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut rdata : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2257⟩
      (endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipSuckCalldataMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      rdata σpost k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σpost (endSnipSalesClipWord dogOut) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2329⟩
      (gasWord :: endSnipSalesClipWord dogOut :: ⟨0⟩ :: endSnipYankOutPtr ::
        endSnipYankInSize :: endSnipYankOutPtr :: endSnipYankOutSize ::
        endSnipYankEndPtr :: endSnipYankSelectorWord :: endSnipSalesClipWord dogOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipYankCalldataMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      rdata σpost k' C' := by
  obtain ⟨_, _, rd2314⟩ := endSnipX_yankExtcodesizeGuard hloDog hloVat hloSale h
  obtain ⟨gasWord, k', C', rd2329⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2314⟩) (okPc := ⟨2326⟩) rd2314
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd2329⟩

theorem endSnipX_yankPostCall {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {dogOut vatOut saleOut rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2329⟩
      (gasWord :: endSnipSalesClipWord dogOut :: ⟨0⟩ :: endSnipYankOutPtr ::
        endSnipYankInSize :: endSnipYankOutPtr :: endSnipYankOutSize ::
        endSnipYankEndPtr :: endSnipYankSelectorWord :: endSnipSalesClipWord dogOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipYankCalldataMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      rdata σpost k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (σ'' : AccountMap)
      (z : Bool) (ret : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (σ'', g'', A', z, ret) = Ethereum.EVM.Θ σpost σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endSnipSalesClipWord dogOut))
          (toExecute σpost (AccountAddress.ofUInt256 (endSnipSalesClipWord dogOut)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSnipYankCalldataMem σmem I dogOut vatOut saleOut).readWithPadding
            endSnipYankOutPtr.toNat endSnipYankInSize.toNat)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks I.perm)
      ∧ RD endBytecode I g (initState σ σ₀ g A I) ⟨2330⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endSnipYankEndPtr ::
            endSnipYankSelectorWord :: endSnipSalesClipWord dogOut ::
            endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
            endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
            endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
            endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
          (endSnipYankPostCallMem σmem I dogOut vatOut saleOut ret)
          (UInt256.ofNat 10) ret σ'' k' C'
      ∧ ret.size < UInt256.size := by
  obtain ⟨σ'', z, ret, Ain, callGas, k', C', hΘ, rd2330raw, hret⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨σ'', z, ret, Ain, callGas, k', C', ?_, ?_, hret⟩
  · simpa [initState] using hΘ
  · have hmin : (min endSnipYankOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
        show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
        exact Nat.zero_le _
      simp [endSnipYankOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 10).toNat
          endSnipYankOutPtr.toNat endSnipYankInSize.toNat)
          endSnipYankOutPtr.toNat endSnipYankOutSize.toNat) = UInt256.ofNat 10 := by
      unfold endSnipYankOutPtr endSnipYankInSize endSnipYankOutSize
      native_decide
    simpa [endSnipYankPostCallMem, endSnipYankOutPtr, endSnipYankInSize,
      endSnipYankOutSize, endSnipYankEndPtr, hmin, byteArray_write_len_zero, haw]
      using rd2330raw

theorem endSnipX_yankCallDepthLimit {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {dogOut vatOut saleOut rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2329⟩
      (gasWord :: endSnipSalesClipWord dogOut :: ⟨0⟩ :: endSnipYankOutPtr ::
        endSnipYankInSize :: endSnipYankOutPtr :: endSnipYankOutSize ::
        endSnipYankEndPtr :: endSnipYankSelectorWord :: endSnipSalesClipWord dogOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipYankCalldataMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      rdata σpost k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2330⟩
      (⟨0⟩ :: endSnipYankEndPtr :: endSnipYankSelectorWord :: endSnipSalesClipWord dogOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipYankCalldataMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ByteArray.empty σpost k' C' := by
  obtain ⟨k', C', rd2330raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endSnipYankOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 10).toNat
        endSnipYankOutPtr.toNat endSnipYankInSize.toNat)
        endSnipYankOutPtr.toNat endSnipYankOutSize.toNat) = UInt256.ofNat 10 := by
    unfold endSnipYankOutPtr endSnipYankInSize endSnipYankOutSize
    native_decide
  simpa [endSnipYankOutPtr, endSnipYankInSize, endSnipYankOutSize,
    endSnipYankEndPtr, hmin, byteArray_write_len_zero, haw] using rd2330raw

theorem endSnipX_yankCallFailed {σ σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2330⟩
      (⟨0⟩ :: endSnipYankEndPtr :: endSnipYankSelectorWord :: endSnipSalesClipWord dogOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 10) rdata σpost k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2330⟩) (okPc := ⟨2346⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_yankCallSucceeded {σ σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2330⟩
      (⟨1⟩ :: endSnipYankEndPtr :: endSnipYankSelectorWord :: endSnipSalesClipWord dogOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 10) rdata σpost k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2351⟩
      (endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 10) rdata σpost k' C' := by
  obtain ⟨_, _, rd2348⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨2330⟩) (okPc := ⟨2346⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      (by simp)
  have rd2351 := evm_run rd2348 with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd2351⟩

theorem endSnipX_artDivZeroInvalid {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hrate : endFlowVatIlkRateWord vatOut = ⟨0⟩)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2351⟩
      (endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipYankPostCallMem σmem I dogOut vatOut saleOut ret) (UInt256.ofNat 10)
      ret σpost k C) :
    X (g.toNat + 1) (D_J endBytecode 0)
        (initState σ σ₀ g A I) = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J endBytecode 0)
        (initState σ σ₀ g A I) = .error .InvalidInstruction := by
  have rd2359 := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨2361⟩ (by native_decide) (by evm_ov)]
  have rd2360 := rd2359.jumpiNT (by native_decide) (by simpa using hrate) (by evm_ov)
  exact RD.invalidError rd2360 (by native_decide)

theorem endSnipX_artAddEntry {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2351⟩
      (endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipYankPostCallMem σmem I dogOut vatOut saleOut ret) (UInt256.ofNat 10)
      ret σpost k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨10092⟩
      (endSnipArtWord vatOut saleOut :: endSnipArtOldWord σpost I :: ⟨2391⟩ ::
        endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k' C' := by
  let key := endSnipIlkWord I
  let mem0 := endSnipYankPostCallMem σmem I dogOut vatOut saleOut ret
  let mem14 := endSnipArtHashMem σmem I dogOut vatOut saleOut
  have hslot : endSnipArtSlot I = solcMappingSlot ⟨14⟩ key := by
    simpa [endSnipArtSlot, endSnipIlkKey, key] using
      endFlowArtSlot_eq (I := I) (by omega)
  have hmem0Size : mem0.size = 320 := by
    simpa [mem0, endSnipYankPostCallMem_eq] using
      endSnipYankCalldataMem_size σmem I dogOut vatOut saleOut hloDog hloVat hloSale
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian (KEC (mem14.readWithPadding 0 64))) =
        solcMappingSlot ⟨14⟩ key := by
    simpa [mem14, endSnipArtHashMem, key, mem0, endSnipYankPostCallMem_eq] using
      twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem0) ⟨14⟩ key
        (by rw [hmem0Size]; omega)
  have rd2359 := evm_run h with [
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨2361⟩ (by native_decide) (by evm_ov)]
  have rd2361 := rd2359.jumpiT (by native_decide) hrate (by jump_dest) (by evm_ov)
  have rd2365 := evm_run rd2361 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup12 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2366 := rd2365.mstore 0 (wordAt0Mem key mem0) (UInt256.ofNat 10)
    (by native_decide) mem_cost (by simp [wordAt0Mem, key, mem0])
    (by native_decide) (by evm_ov)
  have rd2371 := evm_run rd2366 with [
    raw push1 ⟨14⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2371' := rd2371.mstore 0 mem14 (UInt256.ofNat 10)
    (by native_decide) mem_cost
    (by
      change (⟨14⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem0) 32 32 =
        mem14
      simp [mem14, endSnipArtHashMem, twoWordHashMem, wordAt32Mem, key, mem0,
        endSnipYankPostCallMem_eq])
    (by native_decide) (by evm_ov)
  have rd2375 := evm_run rd2371' with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2376 := rd2375.keccak256 0 (endSnipArtSlot I) (UInt256.ofNat 10)
    (by native_decide) mem_cost (by simpa [key, hslot] using hhash)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2377raw⟩ := rd2376.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2377⟩ : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨2377⟩
        (endSnipArtOldWord σpost I :: endSnipSaleTabWord saleOut ::
          endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSnipSaleUsrWord saleOut ::
          endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
          endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
          endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
          endSnipReturnPc :: sel :: [])
        mem14 (UInt256.ofNat 10) ret σpost k' C' := by
    exact ⟨_, _, by
      simpa [-Std.ExtTreeMap.get?_eq_getElem?, endSnipArtOldWord, solcSlotWordAt, solcSlotWord, hslot, key, mem14]
        using rd2377raw⟩
  have rd2390 := evm_run rd2377 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push2 ⟨2391⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw push2 ⟨10092⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endSnipArtWord, mem14] using
      rd2390.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem endSnipX_artAddReturns {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hfit :
      (endSnipArtOldWord σpost I).toNat + (endSnipArtWord vatOut saleOut).toNat <
        UInt256.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨10092⟩
      (endSnipArtWord vatOut saleOut :: endSnipArtOldWord σpost I :: ⟨2391⟩ ::
        endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2391⟩
      (endSnipArtNewWord σpost I vatOut saleOut :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k' C' := by
  let old := endSnipArtOldWord σpost I
  let art := endSnipArtWord vatOut saleOut
  have hfit' : art.toNat + old.toNat < UInt256.size := by
    dsimp [old, art]
    simpa [Nat.add_comm] using hfit
  have haddNat : (art + old).toNat = art.toNat + old.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit']
  have hlt : UInt256.lt (art + old) old = ⟨0⟩ :=
    ult_zero (by rw [haddNat]; omega)
  have rd10099pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd10099 := evm_run rd10099pre with [raw lt (by native_decide) (by evm_ov)]
  have rd10099' := by
    simpa [old, art] using rd10099
  rw [hlt] at rd10099'
  have rd10100pre := evm_run rd10099' with [raw iszero (by native_decide) (by evm_ov)]
  have rd10100 := by
    simpa using rd10100pre
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd10100
  have rd10108pre := evm_run rd10100 with [
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  have rd2391 := evm_run rd10108pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  have hcomm : art + old = old + art := u256_add_comm art old
  exact ⟨_, _, by simpa [endSnipArtNewWord, old, art, hcomm] using rd2391⟩

theorem endSnipX_artAddOverflow {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hover :
      UInt256.size ≤
        (endSnipArtOldWord σpost I).toNat + (endSnipArtWord vatOut saleOut).toNat)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨10092⟩
      (endSnipArtWord vatOut saleOut :: endSnipArtOldWord σpost I :: ⟨2391⟩ ::
        endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k C) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  let old := endSnipArtOldWord σpost I
  let art := endSnipArtWord vatOut saleOut
  have hover' : UInt256.size ≤ art.toNat + old.toNat := by
    dsimp [old, art]
    simpa [Nat.add_comm] using hover
  have hsum_lt2 : art.toNat + old.toNat < 2 * UInt256.size := by
    have hart : art.toNat < UInt256.size := art.val.isLt
    have hold : old.toNat < UInt256.size := old.val.isLt
    omega
  have hmod : (art.toNat + old.toNat) % UInt256.size =
      art.toNat + old.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover']
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (art + old).toNat = art.toNat + old.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (art + old) old = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hartLt : art.toNat < UInt256.size := art.val.isLt
    omega
  have rd10099pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd10099 := evm_run rd10099pre with [raw lt (by native_decide) (by evm_ov)]
  have rd10099' := by
    simpa [old, art] using rd10099
  rw [hlt] at rd10099'
  have rd10100pre := evm_run rd10099' with [raw iszero (by native_decide) (by evm_ov)]
  have rd10100 := by
    simpa using rd10100pre
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd10100
  have rd10104pre := evm_run rd10100 with [raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have rd10104 := rd10104pre.jumpiNT (by native_decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rd10104 (by native_decide) (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_artStoreAtHashSplit {σ σmem σpost σ₀ A I} {g : Sat256}
    {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2391⟩
      (endSnipArtNewWord σpost I vatOut saleOut :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k C) :
    (I.perm = true ∧
      ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2410⟩
        (⟨0⟩ :: endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
          endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
          endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
          endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
          endSnipReturnPc :: sel :: [])
        (endSnipArtStoreHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
        ret (endSnipPostArtAccountMap σpost I
          (endSnipArtNewWord σpost I vatOut saleOut)) k' C') ∨
      (I.perm = false ∧ RDstatic endBytecode g (initState σ σ₀ g A I)) := by
  let key := endSnipIlkWord I
  let mem14 := endSnipArtHashMem σmem I dogOut vatOut saleOut
  let memStore := endSnipArtStoreHashMem σmem I dogOut vatOut saleOut
  have hslot : endSnipArtSlot I = solcMappingSlot ⟨14⟩ key := by
    simpa [endSnipArtSlot, endSnipIlkKey, key] using
      endFlowArtSlot_eq (I := I) (by omega)
  have hpostSize :
      (endSnipYankPostCallMem σmem I dogOut vatOut saleOut ByteArray.empty).size = 320 := by
    simpa [endSnipYankPostCallMem_eq] using
      endSnipYankCalldataMem_size σmem I dogOut vatOut saleOut hloDog hloVat hloSale
  have hmem14SizeEq :
      mem14.size =
        (endSnipYankPostCallMem σmem I dogOut vatOut saleOut ByteArray.empty).size := by
    simpa [mem14, endSnipArtHashMem] using
      twoWordHashMem_size_of_ge64 key ⟨14⟩ (by rw [hpostSize]; omega)
  have hmem14Size : mem14.size = 320 := by
    rw [hmem14SizeEq, hpostSize]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian (KEC (memStore.readWithPadding 0 64))) =
        solcMappingSlot ⟨14⟩ key := by
    simpa [memStore, endSnipArtStoreHashMem, key, mem14] using
      twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem14) ⟨14⟩ key
        (by rw [hmem14Size]; omega)
  have rd2396 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup11 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2396' := rd2396.mstore 0 (wordAt0Mem key mem14) (UInt256.ofNat 10)
    (by native_decide) mem_cost (by simp [wordAt0Mem, key, mem14])
    (by native_decide) (by evm_ov)
  have rd2401 := evm_run rd2396' with [
    raw push1 ⟨14⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2401' := rd2401.mstore 0 memStore (UInt256.ofNat 10)
    (by native_decide) mem_cost
    (by
      change (⟨14⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem14) 32 32 =
        memStore
      simp [memStore, endSnipArtStoreHashMem, twoWordHashMem, wordAt32Mem, key, mem14])
    (by native_decide) (by evm_ov)
  have rd2405 := evm_run rd2401' with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd2406 := rd2405.keccak256 0 (endSnipArtSlot I) (UInt256.ofNat 10)
    (by native_decide) mem_cost (by simpa [key, hslot] using hhash)
    (by native_decide) (by evm_ov)
  have rd2409 := evm_run rd2406 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have hstoreDec : decode endBytecode ⟨2409⟩ = some (.SSTORE, none) := by native_decide
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rd2409.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rd2410raw⟩ := rd2409.sstore hperm hstoreDec
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [endSnipPostArtAccountMap, memStore] using rd2410raw⟩

theorem endSnipX_artStoreIntGuardOkSplit {σ σmem σpost σ₀ A I} {g : Sat256}
    {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (hlot : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hart : (endSnipArtWord vatOut saleOut).toNat < 2 ^ 255)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2391⟩
      (endSnipArtNewWord σpost I vatOut saleOut :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k C) :
    (I.perm = true ∧
      ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2489⟩
        (endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
          endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
          endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
          endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
          endSnipReturnPc :: sel :: [])
        (endSnipArtStoreHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
        ret (endSnipPostArtAccountMap σpost I
          (endSnipArtNewWord σpost I vatOut saleOut)) k' C') ∨
      (I.perm = false ∧ RDstatic endBytecode g (initState σ σ₀ g A I)) := by
  refine permSplit_bind (endSnipX_artStoreAtHashSplit hsz68 hloDog hloVat hloSale h)
    fun _hperm hstore ↦ ?_
  obtain ⟨_, _, rd2410⟩ := hstore
  have hsltLot :
      UInt256.slt (endSnipSaleLotWord saleOut) (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa using
      (slt_lit_zero (a := endSnipSaleLotWord saleOut) (m := 0)
        (by norm_num) (by omega) hlot)
  have hsltArt :
      UInt256.slt (endSnipArtWord vatOut saleOut) (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa using
      (slt_lit_zero (a := endSnipArtWord vatOut saleOut) (m := 0)
        (by norm_num) (by omega) hart)
  have rd2418pre := evm_run rd2410 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2425⟩ (by native_decide) (by evm_ov)]
  rw [hsltLot, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2418pre
  have rd2419 := rd2418pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd2424pre := evm_run rd2419 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [hsltArt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2424pre
  have rd2489 := evm_run rd2424pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2489⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd2489⟩

theorem endSnipX_artStoreIntGuardOk {σ σmem σpost σ₀ A I} {g : Sat256}
    {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (hlot : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hart : (endSnipArtWord vatOut saleOut).toNat < 2 ^ 255)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2391⟩
      (endSnipArtNewWord σpost I vatOut saleOut :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2489⟩
      (endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipArtStoreHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret (endSnipPostArtAccountMap σpost I
        (endSnipArtNewWord σpost I vatOut saleOut)) k' C' :=
  permSplit_true hperm (endSnipX_artStoreIntGuardOkSplit
    hsz68 hloDog hloVat hloSale hlot hart h)

theorem endSnipX_artStoreIntGuardLotOverflowSplit {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (hlot : 2 ^ 255 ≤ (endSnipSaleLotWord saleOut).toNat)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2391⟩
      (endSnipArtNewWord σpost I vatOut saleOut :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k C) :
    (I.perm = true ∧
      RDrev endBytecode g (initState σ σ₀ g A I)) ∨
      (I.perm = false ∧ RDstatic endBytecode g (initState σ σ₀ g A I)) := by
  refine permSplit_bind (endSnipX_artStoreAtHashSplit hsz68 hloDog hloVat hloSale h)
    fun _hperm hstore ↦ ?_
  obtain ⟨_, _, rd2410⟩ := hstore
  have hsltLot :
      UInt256.slt (endSnipSaleLotWord saleOut) (⟨0⟩ : UInt256) = ⟨1⟩ := by
    simpa using
      (slt_lit_one_high (a := endSnipSaleLotWord saleOut) (m := 0)
        (by norm_num) hlot)
  have rd2418pre := evm_run rd2410 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2425⟩ (by native_decide) (by evm_ov)]
  rw [hsltLot, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2418pre
  have rd2425 := rd2418pre.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd2429pre := evm_run rd2425 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2489⟩ (by native_decide) (by evm_ov)]
  have rd2430 := rd2429pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact endSnip_solcErrorStringRevertTail_aw10
    (pc := ⟨2430⟩) (len := ⟨12⟩)
    (rawWord := ⟨0x456e642f6f766572666c6f77⟩) (shift := ⟨160⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f6f766572666c6f77⟩ ⟨160⟩)
    (op := .PUSH12) (width := 12)
    rd2430
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    (endSnipArtStoreHashMem_size σmem I dogOut vatOut saleOut hloDog hloVat hloSale)
    (endSnipArtStoreHashMem_read64 σmem I dogOut vatOut saleOut hloDog hloVat hloSale)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_artStoreIntGuardLotOverflow {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (hlot : 2 ^ 255 ≤ (endSnipSaleLotWord saleOut).toNat)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2391⟩
      (endSnipArtNewWord σpost I vatOut saleOut :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k C) :
    RDrev endBytecode g (initState σ σ₀ g A I) :=
  permSplit_true hperm (endSnipX_artStoreIntGuardLotOverflowSplit
    hsz68 hloDog hloVat hloSale hlot h)

theorem endSnipX_artStoreIntGuardArtOverflowSplit {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (hlot : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hart : 2 ^ 255 ≤ (endSnipArtWord vatOut saleOut).toNat)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2391⟩
      (endSnipArtNewWord σpost I vatOut saleOut :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k C) :
    (I.perm = true ∧
      RDrev endBytecode g (initState σ σ₀ g A I)) ∨
      (I.perm = false ∧ RDstatic endBytecode g (initState σ σ₀ g A I)) := by
  refine permSplit_bind (endSnipX_artStoreAtHashSplit hsz68 hloDog hloVat hloSale h)
    fun _hperm hstore ↦ ?_
  obtain ⟨_, _, rd2410⟩ := hstore
  have hsltLot :
      UInt256.slt (endSnipSaleLotWord saleOut) (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa using
      (slt_lit_zero (a := endSnipSaleLotWord saleOut) (m := 0)
        (by norm_num) (by omega) hlot)
  have hsltArt :
      UInt256.slt (endSnipArtWord vatOut saleOut) (⟨0⟩ : UInt256) = ⟨1⟩ := by
    simpa using
      (slt_lit_one_high (a := endSnipArtWord vatOut saleOut) (m := 0)
        (by norm_num) hart)
  have rd2418pre := evm_run rd2410 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨2425⟩ (by native_decide) (by evm_ov)]
  rw [hsltLot, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2418pre
  have rd2419 := rd2418pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd2424pre := evm_run rd2419 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw slt (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [hsltArt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2424pre
  have rd2429pre := evm_run rd2424pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨2489⟩ (by native_decide) (by evm_ov)]
  have rd2430 := rd2429pre.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact endSnip_solcErrorStringRevertTail_aw10
    (pc := ⟨2430⟩) (len := ⟨12⟩)
    (rawWord := ⟨0x456e642f6f766572666c6f77⟩) (shift := ⟨160⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f6f766572666c6f77⟩ ⟨160⟩)
    (op := .PUSH12) (width := 12)
    rd2430
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl
    (endSnipArtStoreHashMem_size σmem I dogOut vatOut saleOut hloDog hloVat hloSale)
    (endSnipArtStoreHashMem_read64 σmem I dogOut vatOut saleOut hloDog hloVat hloSale)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_artStoreIntGuardArtOverflow {σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut ret : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (hlot : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hart : 2 ^ 255 ≤ (endSnipArtWord vatOut saleOut).toNat)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2391⟩
      (endSnipArtNewWord σpost I vatOut saleOut :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipArtHashMem σmem I dogOut vatOut saleOut) (UInt256.ofNat 10)
      ret σpost k C) :
    RDrev endBytecode g (initState σ σ₀ g A I) :=
  permSplit_true hperm (endSnipX_artStoreIntGuardArtOverflowSplit
    hsz68 hloDog hloVat hloSale hlot hart h)

theorem endSnipX_grabExtcodesizeGuard {σ σCall σLoc σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut rdata : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2489⟩
      (endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) (UInt256.ofNat 10)
      rdata σCall k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2591⟩
      (endPackVatWord σCall I :: endPackVatWord σCall I :: ⟨0⟩ ::
        endFreeGrabOutPtr :: endFreeGrabInSize :: endFreeGrabOutPtr ::
        endFreeGrabOutSize :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σCall I :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut)
      (UInt256.ofNat 11) rdata σCall k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endSnipArtStoreHashMem_size σLoc I dogOut vatOut saleOut
        hloDog hloVat hloSale]; decide) (endSnipArtStoreHashMem_read64 σLoc I dogOut vatOut saleOut
        hloDog hloVat hloSale)
  have hmload64Grab :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSnipGrabMem7For σCall σLoc I dogOut vatOut saleOut).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipGrabMem7For σCall σLoc I dogOut vatOut saleOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    simpa [endSnipGrabMem7For_eq] using
      (mloadFreePtrValue
        (by rw [endSnipGrabCalldataMemFor_size σCall σLoc I dogOut vatOut saleOut
          hloDog hloVat hloSale]; decide) (endSnipGrabCalldataMemFor_read64 σCall σLoc I dogOut vatOut saleOut
          hloDog hloVat hloSale))
  have hselectorShift :
      UInt256.shiftLeft (⟨0x01eeacfd⟩ : UInt256) ⟨230⟩ =
        endFreeGrabSelectorShifted := by
    native_decide
  have hthisWord : EVM.word ↑I.codeOwner = endSnipThisWord I :=
    endSnipThisWordOfAddr I
  have husrMask :
      UInt256.land (endSnipSaleUsrWord saleOut) solcAddrMask =
        endSnipSaleUsrAddrWord saleOut := by
    simpa [endSnipSaleUsrAddrWord] using
      u256_land_comm (endSnipSaleUsrWord saleOut) solcAddrMask
  have husrMaskLeft :
      UInt256.land solcAddrMask (endSnipSaleUsrWord saleOut) =
        endSnipSaleUsrAddrWord saleOut := by
    rfl
  have hvowMask :
      UInt256.land (solcSlotWordAt ⟨4⟩ σCall I) solcAddrMask = endPackVowWord σCall I := by
    rfl
  have hvowMaskLeft :
      UInt256.land solcAddrMask (solcSlotWordAt ⟨4⟩ σCall I) = endPackVowWord σCall I := by
    simpa [endPackVowWord] using
      u256_land_comm solcAddrMask (solcSlotWordAt ⟨4⟩ σCall I)
  have hvatMask :
      UInt256.land (solcSlotWordAt ⟨1⟩ σCall I) solcAddrMask = endPackVatWord σCall I := by
    rfl
  have hvatMaskLeft :
      UInt256.land solcAddrMask (solcSlotWordAt ⟨1⟩ σCall I) = endPackVatWord σCall I := by
    simpa [endPackVatWord] using
      u256_land_comm solcAddrMask (solcSlotWordAt ⟨1⟩ σCall I)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd2492 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2493raw⟩ := rd2492.sload (by native_decide) (by evm_ov)
  have rd2493 : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨2493⟩
        (solcSlotWordAt ⟨1⟩ σCall I :: endSnipArtWord vatOut saleOut ::
          endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
          endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
          endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
          endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
        (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) (UInt256.ofNat 10)
        rdata σCall k' C' := by
    exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWordAt, solcSlotWord] using rd2493raw⟩
  obtain ⟨_, _, rd2493⟩ := rd2493
  have rd2496 := evm_run rd2493 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2497raw⟩ := rd2496.sload (by native_decide) (by evm_ov)
  have rd2497 : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨2497⟩
        (solcSlotWordAt ⟨4⟩ σCall I :: ⟨4⟩ :: solcSlotWordAt ⟨1⟩ σCall I ::
          endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
          endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
          endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
          endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
          endSnipReturnPc :: sel :: [])
        (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) (UInt256.ofNat 10)
        rdata σCall k' C' := by
    exact ⟨_, _, by simpa [-Std.ExtTreeMap.get?_eq_getElem?, solcSlotWordAt, solcSlotWord] using rd2497raw⟩
  obtain ⟨_, _, rd2497⟩ := rd2497
  have rd2591raw := evm_run rd2497 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 10) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 ⟨0x01eeacfd⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨230⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipGrabMem1 σLoc I dogOut vatOut saleOut) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by rw [hselectorShift]; rfl) (by decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup14 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipGrabMem2 σLoc I dogOut vatOut saleOut) (UInt256.ofNat 10)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipGrabMem3 σLoc I dogOut vatOut saleOut) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 by native_decide]
        rw [haddrMask, husrMaskLeft]
        rfl)
      (by decide) (by evm_ov),
    raw address (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipGrabMem4 σLoc I dogOut vatOut saleOut) (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 by native_decide]
        simp [endSnipGrabMem4, Reasoning.Theory.writeWord, endSnipThisWord])
      (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipGrabMem5For σCall σLoc I dogOut vatOut saleOut)
      (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨100⟩).toNat = 228 by native_decide]
        rw [haddrMask, hvowMaskLeft]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨132⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (endSnipGrabMem6For σCall σLoc I dogOut vatOut saleOut)
      (UInt256.ofNat 10)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨132⟩).toNat = 260 by native_decide]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨164⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 3 (endSnipGrabMem7For σCall σLoc I dogOut vatOut saleOut)
      (UInt256.ofNat 11)
      (by native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨164⟩).toNat = 292 by native_decide]
        rfl)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost hmload64Grab (by decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push4 ⟨0x7bab3f40⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw push1 ⟨196⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have rd2591 : ∃ k' C',
      RD endBytecode I g (initState σ σ₀ g A I) ⟨2591⟩
        (endPackVatWord σCall I :: endPackVatWord σCall I :: ⟨0⟩ ::
          endFreeGrabOutPtr :: endFreeGrabInSize :: endFreeGrabOutPtr ::
          endFreeGrabOutSize :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
          endPackVatWord σCall I :: endSnipArtWord vatOut saleOut ::
          endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
          endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
          endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
          endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
        (endSnipGrabMem7For σCall σLoc I dogOut vatOut saleOut) (UInt256.ofNat 11)
        rdata σCall k' C' := by
    exact ⟨_, _, by
      simpa [endFreeGrabOutPtr, endFreeGrabInSize, endFreeGrabOutSize,
        endFreeGrabEndPtr, endFreeGrabSelectorWord, endPackVatWord, endPackVowWord,
        solcSlotWordAt, solcSlotWord, solcAddrMask, hvatMask, hvatMaskLeft, hvowMask,
        hvowMaskLeft, husrMask, husrMaskLeft, haddrMask, hthisWord] using rd2591raw⟩
  obtain ⟨k', C', rd2591⟩ := rd2591
  exact ⟨k', C', by simpa [endSnipGrabMem7For_eq] using rd2591⟩

theorem endSnipX_grabNoCode {σ σCall σLoc σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut rdata : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2489⟩
      (endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) (UInt256.ofNat 10)
      rdata σCall k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) = ⟨0⟩) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, rd2591⟩ := endSnipX_grabExtcodesizeGuard hloDog hloVat hloSale h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨2591⟩) (okPc := ⟨2603⟩) rd2591
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_grabCallReady {σ σCall σLoc σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut rdata : ByteArray} {k C : ℕ}
    (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2489⟩
      (endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipArtStoreHashMem σLoc I dogOut vatOut saleOut) (UInt256.ofNat 10)
      rdata σCall k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2606⟩
      (gasWord :: endPackVatWord σCall I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut)
      (UInt256.ofNat 11) rdata σCall k' C' := by
  obtain ⟨_, _, rd2591⟩ := endSnipX_grabExtcodesizeGuard hloDog hloVat hloSale h
  obtain ⟨gasWord, k', C', rd2606⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨2591⟩) (okPc := ⟨2603⟩) rd2591
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd2606⟩

theorem endSnipX_grabPostCall {σ σCall σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {dogOut vatOut saleOut rdata : ByteArray} {k C : ℕ}
    {σLoc : AccountMap}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2606⟩
      (gasWord :: endPackVatWord σCall I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut)
      (UInt256.ofNat 11) rdata σCall k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (σ'' : AccountMap)
      (z : Bool) (ret : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (σ'', g'', A', z, ret) = Ethereum.EVM.Θ σCall σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σCall I))
          (toExecute σCall (AccountAddress.ofUInt256 (endPackVatWord σCall I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut).readWithPadding
            endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks I.perm)
      ∧ RD endBytecode I g (initState σ σ₀ g A I) ⟨2607⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFreeGrabEndPtr ::
            endFreeGrabSelectorWord :: endPackVatWord σCall I ::
            endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
            endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
            endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
            endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
            endSnipReturnPc :: sel :: [])
          (endSnipGrabPostCallMemFor σCall σLoc I dogOut vatOut saleOut ret)
          (UInt256.ofNat 11) ret σ'' k' C'
      ∧ ret.size < UInt256.size := by
  obtain ⟨σ'', z, ret, Ain, callGas, k', C', hΘ, rd2607raw, hret⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨σ'', z, ret, Ain, callGas, k', C', ?_, ?_, hret⟩
  · simpa [initState] using hΘ
  · have hmin : (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
        show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
        exact Nat.zero_le _
      simp [endFreeGrabOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 11).toNat
          endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
          endFreeGrabOutPtr.toNat endFreeGrabOutSize.toNat) = UInt256.ofNat 11 := by
      unfold endFreeGrabOutPtr endFreeGrabInSize endFreeGrabOutSize
      native_decide
    simpa [endSnipGrabPostCallMemFor, endFreeGrabOutPtr, endFreeGrabInSize,
      endFreeGrabOutSize, endFreeGrabEndPtr, hmin, byteArray_write_len_zero, haw]
      using rd2607raw

theorem endSnipX_grabCallDepthLimit {σ σCall σLoc σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {dogOut vatOut saleOut rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2606⟩
      (gasWord :: endPackVatWord σCall I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut)
      (UInt256.ofNat 11) rdata σCall k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2607⟩
      (⟨0⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σCall I :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipGrabCalldataMemFor σCall σLoc I dogOut vatOut saleOut)
      (UInt256.ofNat 11) ByteArray.empty σCall k' C' := by
  obtain ⟨k', C', rd2607raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endFreeGrabOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 11).toNat
        endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
        endFreeGrabOutPtr.toNat endFreeGrabOutSize.toNat) = UInt256.ofNat 11 := by
    unfold endFreeGrabOutPtr endFreeGrabInSize endFreeGrabOutSize
    native_decide
  simpa [endFreeGrabOutPtr, endFreeGrabInSize, endFreeGrabOutSize,
    endFreeGrabEndPtr, hmin, byteArray_write_len_zero, haw] using rd2607raw

theorem endSnipX_grabCallFailed {σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2607⟩
      (⟨0⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σpre I :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 11) rdata σpost k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨2607⟩) (okPc := ⟨2623⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSnipX_grabCallSucceeded {σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {dogOut vatOut saleOut mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState σ σ₀ g A I) ⟨2607⟩
      (⟨1⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σpre I :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 11) rdata σpost k C) :
    ∃ k' C', RD endBytecode I g (initState σ σ₀ g A I) ⟨2625⟩
      (endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σpre I ::
        endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      mem (UInt256.ofNat 11) rdata σpost k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨2607⟩) (okPc := ⟨2623⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp)

theorem endSnipX_grabLogReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} {σCall σLoc : AccountMap} {dogOut vatOut saleOut ret : ByteArray}
    {acc : AccountMap}
    (hperm : I.perm = true) (hloDog : 128 ≤ dogOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloSale : 192 ≤ saleOut.size)
    (h : RD endBytecode I g s0 ⟨2625⟩
      (endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSnipArtWord vatOut saleOut :: endSnipSaleUsrWord saleOut ::
        endSnipSaleLotWord saleOut :: endSnipSaleTabWord saleOut ::
        endFlowVatIlkRateWord vatOut :: endSnipDogIlkClipWord dogOut ::
        endSnipDogIlkClipWord dogOut :: endSnipIdWord I :: endSnipIlkWord I ::
        endSnipReturnPc :: sel :: [])
      (endSnipGrabPostCallMemFor σCall σLoc I dogOut vatOut saleOut ret)
      (UInt256.ofNat 11) ret acc k C) :
    RDret endBytecode g s0 acc ByteArray.empty := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSnipGrabPostCallMemFor σCall σLoc I dogOut vatOut saleOut ret).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipGrabPostCallMemFor σCall σLoc I dogOut vatOut saleOut ret).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endSnipGrabPostCallMemFor_size σCall σLoc I dogOut vatOut saleOut ret
        hloDog hloVat hloSale]; decide) (endSnipGrabPostCallMemFor_read64 σCall σLoc I dogOut vatOut saleOut
        ret hloDog hloVat hloSale)
  have hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSnipLogDataMem3For σCall σLoc I dogOut vatOut saleOut ret).size then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSnipLogDataMem3For σCall σLoc I dogOut vatOut saleOut ret).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endSnipLogDataMem3For_size σCall σLoc I dogOut vatOut saleOut ret
        hloDog hloVat hloSale]; decide) (endSnipLogDataMem3For_read64 σCall σLoc I dogOut vatOut saleOut ret
        hloDog hloVat hloSale)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have husrMaskLeft :
      UInt256.land solcAddrMask (endSnipSaleUsrWord saleOut) =
        endSnipSaleUsrAddrWord saleOut := by
    rfl
  have husrMask :
      UInt256.land (endSnipSaleUsrWord saleOut) solcAddrMask =
        endSnipSaleUsrAddrWord saleOut := by
    simpa [endSnipSaleUsrAddrWord] using
      u256_land_comm (endSnipSaleUsrWord saleOut) solcAddrMask
  let snipEvent : UInt256 :=
    ⟨0xfc67e20caaffa015d51f696df8ea5c273ba269c69bdc2ec31c1334d01286eaa4⟩
  have rd2632pre := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rdTabMem := rd2632pre.mstore 0
    (endSnipLogDataMemFor σCall σLoc I dogOut vatOut saleOut ret) (UInt256.ofNat 11)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2639pre := evm_run rdTabMem with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdLotMem := rd2639pre.mstore 0
    (endSnipLogDataMem2For σCall σLoc I dogOut vatOut saleOut ret) (UInt256.ofNat 11)
    (by native_decide) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 by native_decide]
      rfl)
    (by native_decide) (by evm_ov)
  have rd2645pre := evm_run rdLotMem with [
    raw dup1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rdArtMem := rd2645pre.mstore 0
    (endSnipLogDataMem3For σCall σLoc I dogOut vatOut saleOut ret) (UInt256.ofNat 11)
    (by native_decide) mem_cost
    (by
      rw [show ((⟨64⟩ : UInt256) + ⟨128⟩).toNat = 192 by native_decide]
      rfl)
    (by native_decide) (by evm_ov)
  have rd2665raw := evm_run rdArtMem with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 11) (by native_decide)
      mem_cost hmload64Log (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup12 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup13 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd2665 : ∃ k' C', RD endBytecode I g s0 ⟨2665⟩
      (⟨128⟩ :: ⟨128⟩ :: endSnipIlkWord I :: endSnipIdWord I ::
        endSnipSaleUsrAddrWord saleOut :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipLogDataMem3For σCall σLoc I dogOut vatOut saleOut ret)
      (UInt256.ofNat 11) ret acc k' C' := by
    exact ⟨_, _, by simpa [haddrMask, husrMask] using rd2665raw⟩
  obtain ⟨_, _, rd2665⟩ := rd2665
  have rdEvent := rd2665.pushConst snipEvent (width := 32) (op := .PUSH32)
    (by native_decide) (by native_decide) (by evm_ov)
  have rd2707raw := evm_run rdEvent with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2707 : ∃ k' C', RD endBytecode I g s0 ⟨2707⟩
      (⟨128⟩ :: ⟨96⟩ :: snipEvent :: endSnipIlkWord I :: endSnipIdWord I ::
        endSnipSaleUsrAddrWord saleOut :: endSnipArtWord vatOut saleOut ::
        endSnipSaleUsrWord saleOut :: endSnipSaleLotWord saleOut ::
        endSnipSaleTabWord saleOut :: endFlowVatIlkRateWord vatOut ::
        endSnipDogIlkClipWord dogOut :: endSnipDogIlkClipWord dogOut ::
        endSnipIdWord I :: endSnipIlkWord I :: endSnipReturnPc :: sel :: [])
      (endSnipLogDataMem3For σCall σLoc I dogOut vatOut saleOut ret)
      (UInt256.ofNat 11) ret acc k' C' := by
    exact ⟨_, _, by simpa [snipEvent] using rd2707raw⟩
  obtain ⟨_, _, rd2707⟩ := rd2707
  have rdLog := RD.log4
    (a := (⟨128⟩ : UInt256)) (b := (⟨96⟩ : UInt256))
    (c := snipEvent) (d := endSnipIlkWord I) (e := endSnipIdWord I)
    (f := endSnipSaleUsrAddrWord saleOut)
    (t := [endSnipArtWord vatOut saleOut, endSnipSaleUsrWord saleOut,
      endSnipSaleLotWord saleOut, endSnipSaleTabWord saleOut,
      endFlowVatIlkRateWord vatOut, endSnipDogIlkClipWord dogOut,
      endSnipDogIlkClipWord dogOut, endSnipIdWord I, endSnipIlkWord I,
      endSnipReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 11).toNat (⟨128⟩ : UInt256).toNat
        (⟨96⟩ : UInt256).toNat))
    rd2707 (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPopArt := RD.pop (a := endSnipArtWord vatOut saleOut)
    (t := [endSnipSaleUsrWord saleOut, endSnipSaleLotWord saleOut,
      endSnipSaleTabWord saleOut, endFlowVatIlkRateWord vatOut,
      endSnipDogIlkClipWord dogOut, endSnipDogIlkClipWord dogOut,
      endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel])
    rdLog (by native_decide) (by evm_ov)
  have rdPopUsr := RD.pop (a := endSnipSaleUsrWord saleOut)
    (t := [endSnipSaleLotWord saleOut, endSnipSaleTabWord saleOut,
      endFlowVatIlkRateWord vatOut, endSnipDogIlkClipWord dogOut,
      endSnipDogIlkClipWord dogOut, endSnipIdWord I, endSnipIlkWord I,
      endSnipReturnPc, sel])
    rdPopArt (by native_decide) (by evm_ov)
  have rdPopLot := RD.pop (a := endSnipSaleLotWord saleOut)
    (t := [endSnipSaleTabWord saleOut, endFlowVatIlkRateWord vatOut,
      endSnipDogIlkClipWord dogOut, endSnipDogIlkClipWord dogOut,
      endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel])
    rdPopUsr (by native_decide) (by evm_ov)
  have rdPopTab := RD.pop (a := endSnipSaleTabWord saleOut)
    (t := [endFlowVatIlkRateWord vatOut, endSnipDogIlkClipWord dogOut,
      endSnipDogIlkClipWord dogOut, endSnipIdWord I, endSnipIlkWord I,
      endSnipReturnPc, sel])
    rdPopLot (by native_decide) (by evm_ov)
  have rdPopRate := RD.pop (a := endFlowVatIlkRateWord vatOut)
    (t := [endSnipDogIlkClipWord dogOut, endSnipDogIlkClipWord dogOut,
      endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel])
    rdPopTab (by native_decide) (by evm_ov)
  have rdPopClipA := RD.pop (a := endSnipDogIlkClipWord dogOut)
    (t := [endSnipDogIlkClipWord dogOut, endSnipIdWord I, endSnipIlkWord I,
      endSnipReturnPc, sel])
    rdPopRate (by native_decide) (by evm_ov)
  have rdPopClipB := RD.pop (a := endSnipDogIlkClipWord dogOut)
    (t := [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, sel])
    rdPopClipA (by native_decide) (by evm_ov)
  have rdPopId := RD.pop (a := endSnipIdWord I)
    (t := [endSnipIlkWord I, endSnipReturnPc, sel])
    rdPopClipB (by native_decide) (by evm_ov)
  have rdPopIlk := RD.pop (a := endSnipIlkWord I)
    (t := [endSnipReturnPc, sel])
    rdPopId (by native_decide) (by evm_ov)
  have rd562 := RD.jump (a := endSnipReturnPc) (t := [sel]) rdPopIlk
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endSnipReturnPc) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem evalExpr_endSnip_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm (.var "ilk") =
      .ok (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endSnipStore I).get? "ilk") =
    .ok (.fixedBytes bytes32Width (endSnipIlkBytes I))
  rw [endSnipStore_get_ilk]
  rfl

theorem evalStorageRef_endSnip_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endSnipStore I } evm
      (tagRef (.var "ilk")) = .ok (endSnipTagEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endSnip_ilk evm I
  simp [endSnipTagEvaledRef, endSnipIlkKey, hilk, endSnipIlkBytes,
    endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, tagRef, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]
  rw [if_pos hargLen]

theorem evalExpr_endSnip_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
      (.storage (tagRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endSnipTagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value (hbackend := rfl)
    (cfg := config)
    (solm := { contract := contract, locals := endSnipStore I })
    (slot := tagRef (.var "ilk"))
    (er := endSnipTagEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endSnipTagSlot I))
    (hbase := by simp [endSnipStore, tagRef])
    (her := evalStorageRef_endSnip_tag evm I hsz68)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := storageLocLoad_uint256 evm (endSnipTagSlot I))

theorem evalExpr_endSnip_tag_ne_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSnipTagSlot I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm
        (.storage (tagRef (.var "ilk"))) = .ok (.int 0) := by
    simpa [htag] using evalExpr_endSnip_tag evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_ne_int_false hstorage hzero rfl

theorem evalExpr_endSnip_tag_ne_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSnipTagSlot I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSnipStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm
        (.storage (tagRef (.var "ilk"))) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endSnipTagSlot I)).toNat)) :=
    evalExpr_endSnip_tag evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_ne_int_true hstorage hzero
  intro hbad
  exact htag (uint256_toNat_eq_zero (Int.ofNat.inj hbad))

theorem endSnipDogAddr_eq_ofUInt256 (σ : AccountMap) (I : ExecutionEnv) :
    endSnipDogAddr σ I = AccountAddress.ofUInt256 (endSnipDogWord σ I) := by
  simpa [endSnipDogAddr] using
    (accountAddress_ofUInt256_eq_ofNat_toNat (endSnipDogWord σ I)).symm

theorem endSnipDogCode_zero_of_codeSize_zero {σ σ₀ A I} {g : UInt256}
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (endSnipDogAddr σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endSnipDogWord σ I) (addr := endSnipDogAddr σ I)
      (endSnipDogAddr_eq_ofUInt256 σ I) hzero

theorem endSnipDogCode_pos_of_codeSize_ne {σ σ₀ A I} {g : UInt256}
    (hne : Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (endSnipDogAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    extCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endSnipDogWord σ I) (addr := endSnipDogAddr σ I)
      (endSnipDogAddr_eq_ofUInt256 σ I) hne

theorem evalStorageRef_endSnip_dog {locals : Store} (_hbase : locals.get? "dog" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      dogRef = .ok ({ base := "dog", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, dogRef, EvalResult.bind, pure, bind]

theorem evalExpr_endSnip_dog {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "dog" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage dogRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value (hbackend := rfl)
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := dogRef)
    (er := ({ base := "dog", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨3⟩)
    (hbase := hbase)
    (her := evalStorageRef_endSnip_dog hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := storageLocLoad_address_offset0 evm ⟨3⟩)

theorem endSnipCheckedDogIlksNoCode {σ σ₀ A I} {g : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) = ⟨0⟩) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSnipStore I } evm0
      (checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
        "dogIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.storage dogRef) = .ok (.address (endSnipDogAddr σ I)) := by
    have hbase : (endSnipStore I).get? "dog" = none := by
      simp [endSnipStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSnipDogAddr, endSnipDogWord, solcSlotWordAt, solcSlotWord] using
      evalExpr_endSnip_dog (locals := endSnipStore I) evm0 hbase
  have hcodeZero :
      (UInt256.ofNat
        ((evm0.lookupAccount (endSnipDogAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [evm0] using
      endSnipDogCode_zero_of_codeSize_zero
        (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa only [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm0)
      (locals := endSnipStore I) (receiver := .storage dogRef)
      (retVar := "dogIlk") (name := "dogIlks") (sendVal := 0)
      (args := [.var "ilk"]) (perm := true) hguard

theorem endSnipCheckedDogIlksFailure {σ σ₀ A I} {g : UInt256}
    {evmDog : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSnipDogAddr σ I)) "dogIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmDog, out) true) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSnipStore I } evm0
      (checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
        "dogIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.storage dogRef) = .ok (.address (endSnipDogAddr σ I)) := by
    have hbase : (endSnipStore I).get? "dog" = none := by
      simp [endSnipStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSnipDogAddr, endSnipDogWord, solcSlotWordAt, solcSlotWord] using
      evalExpr_endSnip_dog (locals := endSnipStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endSnipDogAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endSnipDogCode_pos_of_codeSize_ne
        (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk := evalExpr_endSnip_ilk evm0 I
  have hargs :
      evalExprs? config { contract := contract, locals := endSnipStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, endSnipIlkBytes, endBytes32ArgBytes, EvalResult.bind, bind, pure]
  simpa only [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmDog)
      (locals := endSnipStore I) (receiver := .storage dogRef)
      (retVar := "dogIlk") (name := "dogIlks") (target := endSnipDogAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := out) (perm := true) hguard hreceiver hargs (by simpa [evm0] using hcall)

theorem endSnipCheckedDogIlksDecodeRevert {σ σ₀ A I} {g : UInt256}
    {evmDog : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSnipDogAddr σ I)) "dogIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmDog, out) true)
    (hshort : out.size < 128) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSnipStore I } evm0
      (checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
        "dogIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.storage dogRef) = .ok (.address (endSnipDogAddr σ I)) := by
    have hbase : (endSnipStore I).get? "dog" = none := by
      simp [endSnipStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSnipDogAddr, endSnipDogWord, solcSlotWordAt, solcSlotWord] using
      evalExpr_endSnip_dog (locals := endSnipStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endSnipDogAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endSnipDogCode_pos_of_codeSize_ne
        (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk := evalExpr_endSnip_ilk evm0 I
  have hargs :
      evalExprs? config { contract := contract, locals := endSnipStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, endSnipIlkBytes, endBytes32ArgBytes, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmDog)
      (locals := endSnipStore I) (receiver := .storage dogRef)
      (retVar := "dogIlk") (name := "dogIlks") (target := endSnipDogAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := out) (perm := true) hguard hreceiver hargs
      (by simpa [evm0] using hcall) (endSnipDogIlksDecode_none_short hshort)

theorem endSnipCheckedDogIlksSuccess {σ σ₀ A I} {g : UInt256}
    {evmDog : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSnipDogAddr σ I)) "dogIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmDog, out) true)
    (hlo : 128 ≤ out.size) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSnipStore I } evm0
      (checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
        "dogIlk")
      (.ok { contract := contract, locals := endSnipStoreDogIlk I out } evmDog) := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.storage dogRef) = .ok (.address (endSnipDogAddr σ I)) := by
    have hbase : (endSnipStore I).get? "dog" = none := by
      simp [endSnipStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSnipDogAddr, endSnipDogWord, solcSlotWordAt, solcSlotWord] using
      evalExpr_endSnip_dog (locals := endSnipStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endSnipDogAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endSnipDogCode_pos_of_codeSize_ne
        (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.binary .gt (.extCodeSize (.storage dogRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk := evalExpr_endSnip_ilk evm0 I
  have hargs :
      evalExprs? config { contract := contract, locals := endSnipStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, endSnipIlkBytes, endBytes32ArgBytes, EvalResult.bind, bind, pure]
  have hvalue := endSnipDogIlksDecode_ok (out := out) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm0) (evm' := evmDog)
    (locals := endSnipStore I) (receiver := .storage dogRef)
    (retVar := "dogIlk") (name := "dogIlks") (target := endSnipDogAddr σ I)
    (sendVal := 0) (args := [.var "ilk"])
    (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
    (out := out) (perm := true)
    (value :=
      [.address (endSnipDogIlkClipAddr out),
        .int (Int.ofNat (endSnipDogIlkChopWord out).toNat),
        .int (Int.ofNat (endSnipDogIlkHoleWord out).toNat),
        .int (Int.ofNat (endSnipDogIlkDirtWord out).toNat)])
    hguard hreceiver hargs (by simpa [evm0] using hcall) hvalue
  simpa [checkedExternalCallStmts, endSnipStoreDogIlk, collapseReturns] using hblock

theorem evalExpr_endSnip_dogIlk_clip (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreDogIlk I out } evm
      (.tupleGet (.var "dogIlk") 0) =
        .ok (.address (endSnipDogIlkClipAddr out)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSnipStoreDogIlk I out } evm
        (.var "dogIlk") =
          .ok (.tuple [.address (endSnipDogIlkClipAddr out),
            .int (Int.ofNat (endSnipDogIlkChopWord out).toNat),
            .int (Int.ofNat (endSnipDogIlkHoleWord out).toNat),
            .int (Int.ofNat (endSnipDogIlkDirtWord out).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSnipStoreDogIlk I out).get? "dogIlk") =
        .ok (.tuple [.address (endSnipDogIlkClipAddr out),
          .int (Int.ofNat (endSnipDogIlkChopWord out).toNat),
          .int (Int.ofNat (endSnipDogIlkHoleWord out).toNat),
          .int (Int.ofNat (endSnipDogIlkDirtWord out).toNat)])
    rw [endSnipStoreDogIlk, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem endSnipStmtClip (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    ExecStmt config { contract := contract, locals := endSnipStoreDogIlk I out } evm
      (.letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0))
      (.ok { contract := contract, locals := endSnipStoreClip I out } evm) := by
  simpa [endSnipStoreClip] using
    ExecStmt.letDecl (evalExpr_endSnip_dogIlk_clip evm I out)

theorem endSnipBodyReverts_dogIlksBlock {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord σ I ≠ ⟨0⟩)
    (hdogBlock :
      let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
          "dogIlk") .reverted) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body .reverted := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSnipTagSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply htag
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSnipTagWord, solcSlotWordAt, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endSnip_tag_ne_true evm0 I hsz68 htagLoad
  have hdog :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
          "dogIlk") .reverted := by
    simpa [evm0] using hdogBlock
  have hdogWithTail :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
          "dogIlk" ++
        [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"] "clipSale"
          (perm := false) ++
        [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
          .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
          .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ] ++
        checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
            asInt256 (.var "art")] "_grab")
        .reverted := by
    exact execBlock_append_term
      (s2 :=
        [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"] "clipSale"
          (perm := false) ++
        [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
          .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
          .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ] ++
        checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
            asInt256 (.var "art")] "_grab")
      hdog (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        snipTransition.body .reverted := by
    simp only [snipTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [checkedExternalCallStmts, List.append_assoc] using hdogWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endSnipBodyReverts_dogIlksNoCode {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) = ⟨0⟩) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body .reverted := by
  intro evm0
  exact endSnipBodyReverts_dogIlksBlock
    (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz68 htag
    (by
      simpa using
        (endSnipCheckedDogIlksNoCode
          (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcodeSize))

theorem endSnipBodyReverts_dogIlksCallFailed {σ σ₀ A I} {g : UInt256}
    {evmDog : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSnipDogAddr σ I)) "dogIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmDog, out) true) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body .reverted := by
  intro evm0
  exact endSnipBodyReverts_dogIlksBlock
    (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz68 htag
    (by
      simpa using
        (endSnipCheckedDogIlksFailure
          (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (evmDog := evmDog) (out := out)
          hcodeSize hcall))

theorem endSnipBodyReverts_dogIlksDecodeShort {σ σ₀ A I} {g : UInt256}
    {evmDog : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSnipDogAddr σ I)) "dogIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmDog, out) true)
    (hshort : out.size < 128) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body .reverted := by
  intro evm0
  exact endSnipBodyReverts_dogIlksBlock
    (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz68 htag
    (by
      simpa using
        (endSnipCheckedDogIlksDecodeRevert
          (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (evmDog := evmDog) (out := out)
          hcodeSize hcall hshort))

theorem endSnipPrefixClipSuccess {σ σ₀ A I} {g : UInt256}
    {evmDog : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSnipDogAddr σ I)) "dogIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmDog, out) true)
    (hlo : 128 ≤ out.size) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSnipStore I } evm0
      (nonpayable ++
        [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
          "dogIlk" ++
        [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ])
      (.ok { contract := contract, locals := endSnipStoreClip I out } evmDog) := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSnipTagSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply htag
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSnipTagWord, solcSlotWordAt, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endSnip_tag_ne_true evm0 I hsz68 htagLoad
  have hdog :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
          "dogIlk")
        (.ok { contract := contract, locals := endSnipStoreDogIlk I out } evmDog) := by
    simpa [evm0] using
      endSnipCheckedDogIlksSuccess
        (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmDog := evmDog) (out := out)
        hcodeSize hcall hlo
  have hclip :
      ExecBlock config { contract := contract, locals := endSnipStoreDogIlk I out } evmDog
        [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ]
        (.ok { contract := contract, locals := endSnipStoreClip I out } evmDog) := by
    exact ExecBlock.consNormal (endSnipStmtClip evmDog I out) ExecBlock.nil
  have hdogClip :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
          "dogIlk" ++
        [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ])
        (.ok { contract := contract, locals := endSnipStoreClip I out } evmDog) := by
    exact execBlock_append hdog hclip
  simp only [nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  simpa [List.append_assoc] using hdogClip

theorem endSnipVatReceiver_afterClip {σ I dogOut evm}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSnipStoreClip I dogOut } evm
      (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
  have hbase : (endSnipStoreClip I dogOut).get? "vat" = none := by
    simp [endSnipStoreClip, endSnipStoreDogIlk, endSnipStore]
  simpa [hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVatAddr, endPackVatWord, solcSlotWordAt, solcSlotWord] using
    evalExpr_endPack_vat (locals := endSnipStoreClip I dogOut) evm hbase

theorem endSnipVatCode_zero_afterClip {σ I} {dogOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
  simpa [State.lookupAccount, hmap] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endPackVatWord σ I) (addr := endPackVatAddr σ I)
      (endPackVatAddr_eq_ofUInt256 σ I) hzero

theorem endSnipVatCode_pos_afterClip {σ I} {dogOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hne : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount, hmap] using
    extCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endPackVatWord σ I) (addr := endPackVatAddr σ I)
      (endPackVatAddr_eq_ofUInt256 σ I) hne

theorem evalExprs_endSnip_vatIlksArgs_afterClip (evm : EVM.State)
    (I : ExecutionEnv) (dogOut : ByteArray) :
    evalExprs? config { contract := contract, locals := endSnipStoreClip I dogOut } evm
      [.var "ilk"] = .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
  have hilk :
      evalExpr? config { contract := contract, locals := endSnipStoreClip I dogOut } evm
        (.var "ilk") = .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSnipStoreClip I dogOut).get? "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endSnipStoreClip, store_get_ne _ _ (by native_decide),
      endSnipStoreDogIlk, store_get_ne _ _ (by native_decide), endSnipStore_get_ilk]
    rfl
  simp [evalExprs?, hilk, endSnipIlkBytes, endBytes32ArgBytes, EvalResult.bind, bind, pure]

theorem endSnipCheckedVatIlksNoCode {σ I} {dogOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSnipStoreClip I dogOut } evm
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  have hreceiver := endSnipVatReceiver_afterClip (σ := σ) (I := I) (dogOut := dogOut)
    (evm := evm) hmap howner
  have hcodeZero := endSnipVatCode_zero_afterClip (σ := σ) (I := I) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreClip I dogOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSnipStoreClip I dogOut) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (sendVal := 0)
      (args := [.var "ilk"]) (perm := true) hguard

theorem endSnipCheckedVatIlksFailure {σ I} {dogOut vatOut : ByteArray}
    {evm evmVat : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmVat, vatOut) true) :
    ExecBlock config { contract := contract, locals := endSnipStoreClip I dogOut } evm
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  have hreceiver := endSnipVatReceiver_afterClip (σ := σ) (I := I) (dogOut := dogOut)
    (evm := evm) hmap howner
  have hcodePos := endSnipVatCode_pos_afterClip (σ := σ) (I := I) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreClip I dogOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSnip_vatIlksArgs_afterClip evm I dogOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmVat)
      (locals := endSnipStoreClip I dogOut) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := vatOut) (perm := true) hguard hreceiver hargs hcall

theorem endSnipCheckedVatIlksDecodeRevert {σ I} {dogOut vatOut : ByteArray}
    {evm evmVat : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, vatOut) true)
    (hshort : vatOut.size < 160) :
    ExecBlock config { contract := contract, locals := endSnipStoreClip I dogOut } evm
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  have hreceiver := endSnipVatReceiver_afterClip (σ := σ) (I := I) (dogOut := dogOut)
    (evm := evm) hmap howner
  have hcodePos := endSnipVatCode_pos_afterClip (σ := σ) (I := I) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreClip I dogOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSnip_vatIlksArgs_afterClip evm I dogOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evmVat)
      (locals := endSnipStoreClip I dogOut) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := vatOut) (perm := true) hguard hreceiver hargs hcall
      (endFlowVatIlksDecode_none_short hshort)

theorem endSnipCheckedVatIlksSuccess {σ I} {dogOut vatOut : ByteArray}
    {evm evmVat : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, vatOut) true)
    (hlo : 160 ≤ vatOut.size) :
    ExecBlock config { contract := contract, locals := endSnipStoreClip I dogOut } evm
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk")
      (.ok { contract := contract, locals := endSnipStoreVatIlk I dogOut vatOut }
        evmVat) := by
  have hreceiver := endSnipVatReceiver_afterClip (σ := σ) (I := I) (dogOut := dogOut)
    (evm := evm) hmap howner
  have hcodePos := endSnipVatCode_pos_afterClip (σ := σ) (I := I) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreClip I dogOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSnip_vatIlksArgs_afterClip evm I dogOut
  have hvalue := endFlowVatIlksDecode_ok (out := vatOut) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmVat)
    (locals := endSnipStoreClip I dogOut) (receiver := .storage vatRef)
    (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
    (sendVal := 0) (args := [.var "ilk"])
    (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
    (out := vatOut) (perm := true)
    (value :=
      [.int (Int.ofNat (endFlowVatIlkArtWord vatOut).toNat),
        .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat),
        .int (Int.ofNat (endFlowVatIlkSpotWord vatOut).toNat),
        .int (Int.ofNat (endFlowVatIlkLineWord vatOut).toNat),
        .int (Int.ofNat (endFlowVatIlkDustWord vatOut).toNat)])
    hguard hreceiver hargs hcall hvalue
  simpa [checkedExternalCallStmts, endSnipStoreVatIlk, collapseReturns] using hblock

theorem evalExpr_endSnip_vatIlk_rate (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreVatIlk I dogOut vatOut } evm
      (.tupleGet (.var "vatIlk") 1) =
        .ok (.int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSnipStoreVatIlk I dogOut vatOut } evm
        (.var "vatIlk") =
          .ok (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord vatOut).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat),
            .int (Int.ofNat (endFlowVatIlkSpotWord vatOut).toNat),
            .int (Int.ofNat (endFlowVatIlkLineWord vatOut).toNat),
            .int (Int.ofNat (endFlowVatIlkDustWord vatOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSnipStoreVatIlk I dogOut vatOut).get? "vatIlk") =
        .ok (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord vatOut).toNat),
          .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat),
          .int (Int.ofNat (endFlowVatIlkSpotWord vatOut).toNat),
          .int (Int.ofNat (endFlowVatIlkLineWord vatOut).toNat),
          .int (Int.ofNat (endFlowVatIlkDustWord vatOut).toNat)])
    rw [endSnipStoreVatIlk, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem endSnipStmtRate (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSnipStoreVatIlk I dogOut vatOut } evm
      (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
      (.ok { contract := contract, locals := endSnipStoreRate I dogOut vatOut } evm) := by
  simpa [endSnipStoreRate] using
    ExecStmt.letDecl (evalExpr_endSnip_vatIlk_rate evm I dogOut vatOut)

theorem endSnipPrefixRateSuccess {I} {dogOut vatOut : ByteArray}
    {evm0 evmDog evmVat : EVM.State}
    (hprefix :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
            "dogIlk" ++
          [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ])
        (.ok { contract := contract, locals := endSnipStoreClip I dogOut } evmDog))
    (hvat :
      ExecBlock config { contract := contract, locals := endSnipStoreClip I dogOut } evmDog
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk")
        (.ok { contract := contract, locals := endSnipStoreVatIlk I dogOut vatOut }
          evmVat)) :
    ExecBlock config { contract := contract, locals := endSnipStore I } evm0
      (nonpayable ++
        [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
          "dogIlk" ++
        [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
      (.ok { contract := contract, locals := endSnipStoreRate I dogOut vatOut } evmVat) := by
  have hrate :
      ExecBlock config { contract := contract, locals := endSnipStoreVatIlk I dogOut vatOut }
        evmVat
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ]
        (.ok { contract := contract, locals := endSnipStoreRate I dogOut vatOut } evmVat) := by
    exact ExecBlock.consNormal (endSnipStmtRate evmVat I dogOut vatOut) ExecBlock.nil
  have hvatRate :
      ExecBlock config { contract := contract, locals := endSnipStoreClip I dogOut } evmDog
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
        (.ok { contract := contract, locals := endSnipStoreRate I dogOut vatOut } evmVat) := by
    exact execBlock_append hvat hrate
  have hseq := execBlock_append hprefix hvatRate
  simpa [List.append_assoc] using hseq

theorem endSnipBodyReverts_afterClipVatIlksBlock {I} {dogOut : ByteArray}
    {evm0 evmDog : EVM.State}
    (hprefix :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
            "dogIlk" ++
          [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ])
        (.ok { contract := contract, locals := endSnipStoreClip I dogOut } evmDog))
    (hvat :
      ExecBlock config { contract := contract, locals := endSnipStoreClip I dogOut } evmDog
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk") .reverted) :
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body .reverted := by
  let afterVat : List Stmt :=
    [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
    checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"] "clipSale"
      (perm := false) ++
    [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
      .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
      .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
    checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
      [vowAddr, vowAddr, .var "tab"] "_suck" ++
    checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
    [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
      .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
      .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
      .require
        (.binary .and
          (.binary .lt (.var "lot") (.intLit int256Limit))
          (.binary .lt (.var "art") (.intLit int256Limit))) ] ++
    checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
      [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
        asInt256 (.var "art")] "_grab"
  have hvatWithTail :
      ExecBlock config { contract := contract, locals := endSnipStoreClip I dogOut } evmDog
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++ afterVat) .reverted := by
    exact execBlock_append_term
      (s2 := afterVat) hvat (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        snipTransition.body .reverted := by
    have hseq := execBlock_append hprefix hvatWithTail
    simpa [snipTransition, afterVat, List.append_assoc] using hseq
  exact ExecFuncBody.execBlockRevert hblock

theorem endSnipSalesReceiver_afterRate {I dogOut vatOut evm} :
    evalExpr? config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
      evm (.var "clip") = .ok (.address (endSnipDogIlkClipAddr dogOut)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((endSnipStoreRate I dogOut vatOut).get? "clip") =
    .ok (.address (endSnipDogIlkClipAddr dogOut))
  rw [endSnipStoreRate, store_get_ne _ _ (by native_decide),
    endSnipStoreVatIlk, store_get_ne _ _ (by native_decide),
    endSnipStoreClip, store_get_self]
  rfl

theorem endSnipSalesCode_zero_afterRate {σ : AccountMap} {dogOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (endSnipSalesClipWord dogOut) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (endSnipDogIlkClipAddr dogOut)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount, hmap] using
    extCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endSnipSalesClipWord dogOut)
      (addr := endSnipDogIlkClipAddr dogOut)
      (endSnipSalesClipAddr_eq_ofUInt256 dogOut) hzero

theorem endSnipSalesCode_pos_afterRate {σ : AccountMap} {dogOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (endSnipSalesClipWord dogOut) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (endSnipDogIlkClipAddr dogOut)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount, hmap] using
    extCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endSnipSalesClipWord dogOut)
      (addr := endSnipDogIlkClipAddr dogOut)
      (endSnipSalesClipAddr_eq_ofUInt256 dogOut) hne

theorem evalExprs_endSnip_salesArgs_afterRate (evm : EVM.State)
    (I : ExecutionEnv) (dogOut vatOut : ByteArray) :
    evalExprs? config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
      evm [.var "id"] = .ok [.int (Int.ofNat (endSnipIdWord I).toNat)] := by
  have hid :
      evalExpr? config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
        evm (.var "id") = .ok (.int (Int.ofNat (endSnipIdWord I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endSnipStoreRate I dogOut vatOut).get? "id") =
      .ok (.int (Int.ofNat (endSnipIdWord I).toNat))
    rw [endSnipStoreRate, store_get_ne _ _ (by native_decide),
      endSnipStoreVatIlk, store_get_ne _ _ (by native_decide),
      endSnipStoreClip, store_get_ne _ _ (by native_decide),
      endSnipStoreDogIlk, store_get_ne _ _ (by native_decide),
      endSnipStore, store_get_self]
    rfl
  simp [evalExprs?, hid, EvalResult.bind, bind, pure]

theorem endSnipCheckedSalesNoCode {σ I} {dogOut vatOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipSalesClipWord dogOut) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSnipStoreRate I dogOut vatOut } evm
      (checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
        "clipSale" (perm := false)) .reverted := by
  have hreceiver := endSnipSalesReceiver_afterRate (I := I) (dogOut := dogOut)
    (vatOut := vatOut) (evm := evm)
  have hcodeZero := endSnipSalesCode_zero_afterRate (σ := σ) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
        evm (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSnipStoreRate I dogOut vatOut) (receiver := .var "clip")
      (retVar := "clipSale") (name := "sales") (sendVal := 0)
      (args := [.var "id"]) (perm := false) hguard

theorem endSnipCheckedSalesFailure {σ I} {dogOut vatOut saleOut : ByteArray}
    {evm evmSales : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipSalesClipWord dogOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endSnipDogIlkClipAddr dogOut))
        "sales" 0 [.int (Int.ofNat (endSnipIdWord I).toNat)]
        (false, evmSales, saleOut) false) :
    ExecBlock config { contract := contract, locals := endSnipStoreRate I dogOut vatOut } evm
      (checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
        "clipSale" (perm := false)) .reverted := by
  have hreceiver := endSnipSalesReceiver_afterRate (I := I) (dogOut := dogOut)
    (vatOut := vatOut) (evm := evm)
  have hcodePos := endSnipSalesCode_pos_afterRate (σ := σ) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
        evm (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSnip_salesArgs_afterRate evm I dogOut vatOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmSales)
      (locals := endSnipStoreRate I dogOut vatOut) (receiver := .var "clip")
      (retVar := "clipSale") (name := "sales")
      (target := endSnipDogIlkClipAddr dogOut)
      (sendVal := 0) (args := [.var "id"])
      (argVals := [.int (Int.ofNat (endSnipIdWord I).toNat)])
      (out := saleOut) (perm := false) hguard hreceiver hargs hcall

theorem endSnipCheckedSalesDecodeRevert {σ I} {dogOut vatOut saleOut : ByteArray}
    {evm evmSales : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipSalesClipWord dogOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endSnipDogIlkClipAddr dogOut))
        "sales" 0 [.int (Int.ofNat (endSnipIdWord I).toNat)]
        (true, evmSales, saleOut) false)
    (hshort : saleOut.size < 192) :
    ExecBlock config { contract := contract, locals := endSnipStoreRate I dogOut vatOut } evm
      (checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
        "clipSale" (perm := false)) .reverted := by
  have hreceiver := endSnipSalesReceiver_afterRate (I := I) (dogOut := dogOut)
    (vatOut := vatOut) (evm := evm)
  have hcodePos := endSnipSalesCode_pos_afterRate (σ := σ) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
        evm (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSnip_salesArgs_afterRate evm I dogOut vatOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evmSales)
      (locals := endSnipStoreRate I dogOut vatOut) (receiver := .var "clip")
      (retVar := "clipSale") (name := "sales")
      (target := endSnipDogIlkClipAddr dogOut)
      (sendVal := 0) (args := [.var "id"])
      (argVals := [.int (Int.ofNat (endSnipIdWord I).toNat)])
      (out := saleOut) (perm := false) hguard hreceiver hargs hcall
      (endSnipSalesDecode_none_short hshort)

theorem endSnipCheckedSalesSuccess {σ I} {dogOut vatOut saleOut : ByteArray}
    {evm evmSales : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipSalesClipWord dogOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endSnipDogIlkClipAddr dogOut))
        "sales" 0 [.int (Int.ofNat (endSnipIdWord I).toNat)]
        (true, evmSales, saleOut) false)
    (hlo : 192 ≤ saleOut.size) :
    ExecBlock config { contract := contract, locals := endSnipStoreRate I dogOut vatOut } evm
      (checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
        "clipSale" (perm := false))
      (.ok { contract := contract, locals := endSnipStoreClipSale I dogOut vatOut saleOut }
        evmSales) := by
  have hreceiver := endSnipSalesReceiver_afterRate (I := I) (dogOut := dogOut)
    (vatOut := vatOut) (evm := evm)
  have hcodePos := endSnipSalesCode_pos_afterRate (σ := σ) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
        evm (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSnip_salesArgs_afterRate evm I dogOut vatOut
  have hvalue := endSnipSalesDecode_ok (out := saleOut) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmSales)
    (locals := endSnipStoreRate I dogOut vatOut) (receiver := .var "clip")
    (retVar := "clipSale") (name := "sales")
    (target := endSnipDogIlkClipAddr dogOut)
    (sendVal := 0) (args := [.var "id"])
    (argVals := [.int (Int.ofNat (endSnipIdWord I).toNat)])
    (out := saleOut) (perm := false)
    (value := [.int (Int.ofNat (endSnipSalePosWord saleOut).toNat),
      .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat),
      .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
      .address (endSnipSaleUsrAddr saleOut),
      .int (Int.ofNat ((endSnipSaleTicWord saleOut).toNat % EVM.twoPow 96)),
      .int (Int.ofNat (endSnipSaleTopWord saleOut).toNat)])
    hguard hreceiver hargs hcall hvalue
  simpa [checkedExternalCallStmts, endSnipStoreClipSale, collapseReturns] using hblock

theorem evalExpr_endSnip_clipSale_tab (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreClipSale I dogOut vatOut saleOut }
      evm (.tupleGet (.var "clipSale") 1) =
        .ok (.int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSnipStoreClipSale I dogOut vatOut saleOut }
        evm (.var "clipSale") =
          .ok (.tuple [.int (Int.ofNat (endSnipSalePosWord saleOut).toNat),
            .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat),
            .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
            .address (endSnipSaleUsrAddr saleOut),
            .int (Int.ofNat ((endSnipSaleTicWord saleOut).toNat % EVM.twoPow 96)),
            .int (Int.ofNat (endSnipSaleTopWord saleOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSnipStoreClipSale I dogOut vatOut saleOut).get? "clipSale") =
        .ok (.tuple [.int (Int.ofNat (endSnipSalePosWord saleOut).toNat),
          .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat),
          .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
          .address (endSnipSaleUsrAddr saleOut),
          .int (Int.ofNat ((endSnipSaleTicWord saleOut).toNat % EVM.twoPow 96)),
          .int (Int.ofNat (endSnipSaleTopWord saleOut).toNat)])
    rw [endSnipStoreClipSale, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalExpr_endSnip_clipSale_lot (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreTab I dogOut vatOut saleOut }
      evm (.tupleGet (.var "clipSale") 2) =
        .ok (.int (Int.ofNat (endSnipSaleLotWord saleOut).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSnipStoreTab I dogOut vatOut saleOut }
        evm (.var "clipSale") =
          .ok (.tuple [.int (Int.ofNat (endSnipSalePosWord saleOut).toNat),
            .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat),
            .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
            .address (endSnipSaleUsrAddr saleOut),
            .int (Int.ofNat ((endSnipSaleTicWord saleOut).toNat % EVM.twoPow 96)),
            .int (Int.ofNat (endSnipSaleTopWord saleOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSnipStoreTab I dogOut vatOut saleOut).get? "clipSale") =
        .ok (.tuple [.int (Int.ofNat (endSnipSalePosWord saleOut).toNat),
          .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat),
          .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
          .address (endSnipSaleUsrAddr saleOut),
          .int (Int.ofNat ((endSnipSaleTicWord saleOut).toNat % EVM.twoPow 96)),
          .int (Int.ofNat (endSnipSaleTopWord saleOut).toNat)])
    rw [endSnipStoreTab, store_get_ne _ _ (by native_decide),
      endSnipStoreClipSale, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalExpr_endSnip_clipSale_usr (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreLot I dogOut vatOut saleOut }
      evm (.tupleGet (.var "clipSale") 3) =
        .ok (.address (endSnipSaleUsrAddr saleOut)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSnipStoreLot I dogOut vatOut saleOut }
        evm (.var "clipSale") =
          .ok (.tuple [.int (Int.ofNat (endSnipSalePosWord saleOut).toNat),
            .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat),
            .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
            .address (endSnipSaleUsrAddr saleOut),
            .int (Int.ofNat ((endSnipSaleTicWord saleOut).toNat % EVM.twoPow 96)),
            .int (Int.ofNat (endSnipSaleTopWord saleOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSnipStoreLot I dogOut vatOut saleOut).get? "clipSale") =
        .ok (.tuple [.int (Int.ofNat (endSnipSalePosWord saleOut).toNat),
          .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat),
          .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
          .address (endSnipSaleUsrAddr saleOut),
          .int (Int.ofNat ((endSnipSaleTicWord saleOut).toNat % EVM.twoPow 96)),
          .int (Int.ofNat (endSnipSaleTopWord saleOut).toNat)])
    rw [endSnipStoreLot, store_get_ne _ _ (by native_decide),
      endSnipStoreTab, store_get_ne _ _ (by native_decide),
      endSnipStoreClipSale, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem endSnipStmtTab (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSnipStoreClipSale I dogOut vatOut saleOut }
      evm (.letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1))
      (.ok { contract := contract, locals := endSnipStoreTab I dogOut vatOut saleOut } evm) := by
  simpa [endSnipStoreTab] using
    ExecStmt.letDecl (evalExpr_endSnip_clipSale_tab evm I dogOut vatOut saleOut)

theorem endSnipStmtLot (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSnipStoreTab I dogOut vatOut saleOut }
      evm (.letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2))
      (.ok { contract := contract, locals := endSnipStoreLot I dogOut vatOut saleOut } evm) := by
  simpa [endSnipStoreLot] using
    ExecStmt.letDecl (evalExpr_endSnip_clipSale_lot evm I dogOut vatOut saleOut)

theorem endSnipStmtUsr (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSnipStoreLot I dogOut vatOut saleOut }
      evm (.letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3))
      (.ok { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut } evm) := by
  simpa [endSnipStoreUsr] using
    ExecStmt.letDecl (evalExpr_endSnip_clipSale_usr evm I dogOut vatOut saleOut)

theorem endSnipPrefixUsrSuccess {I} {dogOut vatOut saleOut : ByteArray}
    {evm0 evmVat evmSales : EVM.State}
    (hprefix :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
            "dogIlk" ++
          [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
        (.ok { contract := contract, locals := endSnipStoreRate I dogOut vatOut } evmVat))
    (hsales :
      ExecBlock config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
        evmVat
        (checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
          "clipSale" (perm := false))
        (.ok { contract := contract, locals := endSnipStoreClipSale I dogOut vatOut saleOut }
          evmSales)) :
    ExecBlock config { contract := contract, locals := endSnipStore I } evm0
      (nonpayable ++
        [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
          "dogIlk" ++
        [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
          "clipSale" (perm := false) ++
        [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
          .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
          .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ])
      (.ok { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmSales) := by
  have htab :
      ExecBlock config
        { contract := contract, locals := endSnipStoreClipSale I dogOut vatOut saleOut }
        evmSales [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1) ]
        (.ok { contract := contract, locals := endSnipStoreTab I dogOut vatOut saleOut }
          evmSales) := by
    exact ExecBlock.consNormal (endSnipStmtTab evmSales I dogOut vatOut saleOut) ExecBlock.nil
  have hlot :
      ExecBlock config { contract := contract, locals := endSnipStoreTab I dogOut vatOut saleOut }
        evmSales [ .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2) ]
        (.ok { contract := contract, locals := endSnipStoreLot I dogOut vatOut saleOut }
          evmSales) := by
    exact ExecBlock.consNormal (endSnipStmtLot evmSales I dogOut vatOut saleOut) ExecBlock.nil
  have husr :
      ExecBlock config { contract := contract, locals := endSnipStoreLot I dogOut vatOut saleOut }
        evmSales [ .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ]
        (.ok { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
          evmSales) := by
    exact ExecBlock.consNormal (endSnipStmtUsr evmSales I dogOut vatOut saleOut) ExecBlock.nil
  have htail :
      ExecBlock config
        { contract := contract, locals := endSnipStoreClipSale I dogOut vatOut saleOut }
        evmSales
        [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
          .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
          .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ]
        (.ok { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
          evmSales) := by
    exact execBlock_append htab
      (Reasoning.Theory.execBlock_append hlot husr)
  have hsalesTail :
      ExecBlock config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
        evmVat
        (checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
          "clipSale" (perm := false) ++
        [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
          .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
          .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ])
        (.ok { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
          evmSales) := by
    exact execBlock_append hsales htail
  have hseq := execBlock_append hprefix hsalesTail
  simpa [List.append_assoc] using hseq

theorem endSnipVatReceiver_afterUsr {σ I dogOut vatOut saleOut evm}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evm (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
  have hbase : (endSnipStoreUsr I dogOut vatOut saleOut).get? "vat" = none := by
    rw [endSnipStoreUsr, store_get_ne _ _ (by native_decide),
      endSnipStoreLot, store_get_ne _ _ (by native_decide),
      endSnipStoreTab, store_get_ne _ _ (by native_decide),
      endSnipStoreClipSale, store_get_ne _ _ (by native_decide),
      endSnipStoreRate, store_get_ne _ _ (by native_decide),
      endSnipStoreVatIlk, store_get_ne _ _ (by native_decide),
      endSnipStoreClip, store_get_ne _ _ (by native_decide),
      endSnipStoreDogIlk, store_get_ne _ _ (by native_decide),
      endSnipStore, store_get_ne _ _ (by native_decide),
      store_get_ne _ _ (by native_decide)]
    simp
  simpa [hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVatAddr, endPackVatWord, solcSlotWordAt, solcSlotWord] using
    evalExpr_endPack_vat (locals := endSnipStoreUsr I dogOut vatOut saleOut) evm hbase

theorem evalExprs_endSnip_suckArgs_afterUsr (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExprs? config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evm [vowAddr, vowAddr, .var "tab"] =
        .ok [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)] := by
  have hvow :
      evalExpr? config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evm vowAddr = .ok (.address (endPackVowAddr σ I)) := by
    have hbase : (endSnipStoreUsr I dogOut vatOut saleOut).get? "vow" = none := by
      rw [endSnipStoreUsr, store_get_ne _ _ (by native_decide),
        endSnipStoreLot, store_get_ne _ _ (by native_decide),
        endSnipStoreTab, store_get_ne _ _ (by native_decide),
        endSnipStoreClipSale, store_get_ne _ _ (by native_decide),
        endSnipStoreRate, store_get_ne _ _ (by native_decide),
        endSnipStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSnipStoreClip, store_get_ne _ _ (by native_decide),
        endSnipStoreDogIlk, store_get_ne _ _ (by native_decide),
        endSnipStore, store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp
    simpa [vowAddr, hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVowAddr, endPackVowWord, solcSlotWordAt, solcSlotWord] using
      evalExpr_endPack_vow (locals := endSnipStoreUsr I dogOut vatOut saleOut) evm hbase
  have htab :
      evalExpr? config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evm (.var "tab") = .ok (.int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)) := by
    simpa [endSnipStoreUsr, endSnipStoreLot, endSnipStoreTab] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSnipStoreUsr I dogOut vatOut saleOut)
        (name := "tab") (value := endSnipSaleTabWord saleOut)
        (by
          rw [endSnipStoreUsr, store_get_ne _ _ (by native_decide),
            endSnipStoreLot, store_get_ne _ _ (by native_decide),
            endSnipStoreTab, store_get_self])
  simp [evalExprs?, hvow, htab, EvalResult.bind, bind, pure]

theorem endSnipCheckedSuckNoCode {σ I} {dogOut vatOut saleOut : ByteArray}
    {evm : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, vowAddr, .var "tab"] "_suck") .reverted := by
  have hreceiver := endSnipVatReceiver_afterUsr
    (σ := σ) (I := I) (dogOut := dogOut) (vatOut := vatOut) (saleOut := saleOut)
    (evm := evm) hmap howner
  have hcodeZero := endSnipVatCode_zero_afterClip
    (σ := σ) (I := I) (dogOut := dogOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSnipStoreUsr I dogOut vatOut saleOut) (receiver := .storage vatRef)
      (retVar := "_suck") (name := "suck") (sendVal := 0)
      (args := [vowAddr, vowAddr, .var "tab"]) (perm := true) hguard

theorem endSnipCheckedSuckFailure {σ I} {dogOut vatOut saleOut suckOut : ByteArray}
    {evm evmSuck : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "suck" 0
        [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)]
        (false, evmSuck, suckOut) true) :
    ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, vowAddr, .var "tab"] "_suck") .reverted := by
  have hreceiver := endSnipVatReceiver_afterUsr
    (σ := σ) (I := I) (dogOut := dogOut) (vatOut := vatOut) (saleOut := saleOut)
    (evm := evm) hmap howner
  have hcodePos := endSnipVatCode_pos_afterClip
    (σ := σ) (I := I) (dogOut := dogOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSnip_suckArgs_afterUsr evm I σ dogOut vatOut saleOut
    hmap howner
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmSuck)
      (locals := endSnipStoreUsr I dogOut vatOut saleOut) (receiver := .storage vatRef)
      (retVar := "_suck") (name := "suck") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [vowAddr, vowAddr, .var "tab"])
      (argVals :=
        [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)])
      (out := suckOut) (perm := true) hguard hreceiver hargs hcall

theorem endSnipCheckedSuckSuccess {σ I} {dogOut vatOut saleOut suckOut : ByteArray}
    {evm evmSuck : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "suck" 0
        [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)]
        (true, evmSuck, suckOut) true) :
    ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, vowAddr, .var "tab"] "_suck")
      (.ok { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evmSuck) := by
  have hreceiver := endSnipVatReceiver_afterUsr
    (σ := σ) (I := I) (dogOut := dogOut) (vatOut := vatOut) (saleOut := saleOut)
    (evm := evm) hmap howner
  have hcodePos := endSnipVatCode_pos_afterClip
    (σ := σ) (I := I) (dogOut := dogOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSnip_suckArgs_afterUsr evm I σ dogOut vatOut saleOut
    hmap howner
  have hdec : config.externalABI.decode? "suck" suckOut = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmSuck)
    (locals := endSnipStoreUsr I dogOut vatOut saleOut) (receiver := .storage vatRef)
    (retVar := "_suck") (name := "suck") (target := endPackVatAddr σ I)
    (sendVal := 0) (args := [vowAddr, vowAddr, .var "tab"])
    (argVals :=
      [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
        .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)])
    (out := suckOut) (perm := true) (value := [])
    hguard hreceiver hargs hcall hdec
  simpa only [checkedExternalCallStmts, endSnipStoreSuck, collapseReturns] using hblock

theorem endSnipClipReceiver_afterSuck {I dogOut vatOut saleOut evm} :
    evalExpr? config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
      evm (.var "clip") = .ok (.address (endSnipDogIlkClipAddr dogOut)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((endSnipStoreSuck I dogOut vatOut saleOut).get? "clip") =
    .ok (.address (endSnipDogIlkClipAddr dogOut))
  rw [endSnipStoreSuck, store_get_ne _ _ (by native_decide),
    endSnipStoreUsr, store_get_ne _ _ (by native_decide),
    endSnipStoreLot, store_get_ne _ _ (by native_decide),
    endSnipStoreTab, store_get_ne _ _ (by native_decide),
    endSnipStoreClipSale, store_get_ne _ _ (by native_decide),
    endSnipStoreRate, store_get_ne _ _ (by native_decide),
    endSnipStoreVatIlk, store_get_ne _ _ (by native_decide),
    endSnipStoreClip, store_get_self]
  rfl

theorem evalExprs_endSnip_yankArgs_afterSuck (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    evalExprs? config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
      evm [.var "id"] = .ok [.int (Int.ofNat (endSnipIdWord I).toNat)] := by
  have hid :
      evalExpr? config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evm (.var "id") = .ok (.int (Int.ofNat (endSnipIdWord I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endSnipStoreSuck I dogOut vatOut saleOut).get? "id") =
      .ok (.int (Int.ofNat (endSnipIdWord I).toNat))
    rw [endSnipStoreSuck, store_get_ne _ _ (by native_decide),
      endSnipStoreUsr, store_get_ne _ _ (by native_decide),
      endSnipStoreLot, store_get_ne _ _ (by native_decide),
      endSnipStoreTab, store_get_ne _ _ (by native_decide),
      endSnipStoreClipSale, store_get_ne _ _ (by native_decide),
      endSnipStoreRate, store_get_ne _ _ (by native_decide),
      endSnipStoreVatIlk, store_get_ne _ _ (by native_decide),
      endSnipStoreClip, store_get_ne _ _ (by native_decide),
      endSnipStoreDogIlk, store_get_ne _ _ (by native_decide),
      endSnipStore, store_get_self]
    rfl
  simp only [evalExprs?, hid, EvalResult.bind, bind, pure]

theorem endSnipCheckedYankNoCode {σ I} {dogOut vatOut saleOut : ByteArray}
    {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipSalesClipWord dogOut) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
      evm
      (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
      .reverted := by
  have hreceiver := endSnipClipReceiver_afterSuck
    (I := I) (dogOut := dogOut) (vatOut := vatOut) (saleOut := saleOut) (evm := evm)
  have hcodeZero := endSnipSalesCode_zero_afterRate (σ := σ) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evm (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa only [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSnipStoreSuck I dogOut vatOut saleOut) (receiver := .var "clip")
      (retVar := "_yank") (name := "yank") (sendVal := 0)
      (args := [.var "id"]) (perm := true) hguard

theorem endSnipCheckedYankFailure {σ I} {dogOut vatOut saleOut yankOut : ByteArray}
    {evm evmYank : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipSalesClipWord dogOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endSnipDogIlkClipAddr dogOut))
        "yank" 0 [.int (Int.ofNat (endSnipIdWord I).toNat)]
        (false, evmYank, yankOut) true) :
    ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
      evm
      (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
      .reverted := by
  have hreceiver := endSnipClipReceiver_afterSuck
    (I := I) (dogOut := dogOut) (vatOut := vatOut) (saleOut := saleOut) (evm := evm)
  have hcodePos := endSnipSalesCode_pos_afterRate (σ := σ) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evm (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSnip_yankArgs_afterSuck evm I dogOut vatOut saleOut
  simpa only [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmYank)
      (locals := endSnipStoreSuck I dogOut vatOut saleOut) (receiver := .var "clip")
      (retVar := "_yank") (name := "yank") (target := endSnipDogIlkClipAddr dogOut)
      (sendVal := 0) (args := [.var "id"])
      (argVals := [.int (Int.ofNat (endSnipIdWord I).toNat)])
      (out := yankOut) (perm := true) hguard hreceiver hargs hcall

theorem endSnipCheckedYankSuccess {σ I} {dogOut vatOut saleOut yankOut : ByteArray}
    {evm evmYank : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSnipSalesClipWord dogOut) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endSnipDogIlkClipAddr dogOut))
        "yank" 0 [.int (Int.ofNat (endSnipIdWord I).toNat)]
        (true, evmYank, yankOut) true) :
    ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
      evm
      (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
      (.ok { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
        evmYank) := by
  have hreceiver := endSnipClipReceiver_afterSuck
    (I := I) (dogOut := dogOut) (vatOut := vatOut) (saleOut := saleOut) (evm := evm)
  have hcodePos := endSnipSalesCode_pos_afterRate (σ := σ) (dogOut := dogOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evm (.binary .gt (.extCodeSize (.var "clip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSnip_yankArgs_afterSuck evm I dogOut vatOut saleOut
  have hdec : config.externalABI.decode? "yank" yankOut = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmYank)
    (locals := endSnipStoreSuck I dogOut vatOut saleOut) (receiver := .var "clip")
    (retVar := "_yank") (name := "yank") (target := endSnipDogIlkClipAddr dogOut)
    (sendVal := 0) (args := [.var "id"])
    (argVals := [.int (Int.ofNat (endSnipIdWord I).toNat)])
    (out := yankOut) (perm := true) (value := [])
    hguard hreceiver hargs hcall hdec
  simpa only [checkedExternalCallStmts, endSnipStoreYank, collapseReturns] using hblock

theorem evalExpr_endSnip_tab_afterYank (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
      evm (.var "tab") = .ok (.int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)) := by
  simpa [endSnipStoreYank, endSnipStoreSuck, endSnipStoreUsr, endSnipStoreLot,
    endSnipStoreTab] using
    endEvalExpr_varUInt256 (evm := evm)
      (locals := endSnipStoreYank I dogOut vatOut saleOut)
      (name := "tab") (value := endSnipSaleTabWord saleOut)
      (by
        rw [endSnipStoreYank, store_get_ne _ _ (by native_decide),
          endSnipStoreSuck, store_get_ne _ _ (by native_decide),
          endSnipStoreUsr, store_get_ne _ _ (by native_decide),
          endSnipStoreLot, store_get_ne _ _ (by native_decide),
          endSnipStoreTab, store_get_self])

theorem evalExpr_endSnip_rate_afterYank (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
      evm (.var "rate") = .ok (.int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)) := by
  simpa [endSnipStoreYank, endSnipStoreSuck, endSnipStoreUsr, endSnipStoreLot,
    endSnipStoreTab, endSnipStoreClipSale, endSnipStoreRate] using
    endEvalExpr_varUInt256 (evm := evm)
      (locals := endSnipStoreYank I dogOut vatOut saleOut)
      (name := "rate") (value := endFlowVatIlkRateWord vatOut)
      (by
        rw [endSnipStoreYank, store_get_ne _ _ (by native_decide),
          endSnipStoreSuck, store_get_ne _ _ (by native_decide),
          endSnipStoreUsr, store_get_ne _ _ (by native_decide),
          endSnipStoreLot, store_get_ne _ _ (by native_decide),
          endSnipStoreTab, store_get_ne _ _ (by native_decide),
          endSnipStoreClipSale, store_get_ne _ _ (by native_decide),
          endSnipStoreRate, store_get_self])

theorem endSnipStmtArt (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩) :
    ExecStmt config { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
      evm (.letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")))
      (.ok { contract := contract, locals := endSnipStoreArt I dogOut vatOut saleOut } evm) := by
  have htab := evalExpr_endSnip_tab_afterYank evm I dogOut vatOut saleOut
  have hrateExpr := evalExpr_endSnip_rate_afterYank evm I dogOut vatOut saleOut
  have hdiv :
      evalExpr? config { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
        evm (.binary .div (.var "tab") (.var "rate")) =
          .ok (.int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)) :=
    endEvalExpr_div_uint256_ok htab hrateExpr hrate rfl
  simpa [endSnipStoreArt] using ExecStmt.letDecl hdiv

theorem endSnipStmtArtReverts (evm : EVM.State) (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray)
    (hrate : endFlowVatIlkRateWord vatOut = ⟨0⟩) :
    ExecStmt config { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
      evm (.letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")))
      .reverted := by
  have htab := evalExpr_endSnip_tab_afterYank evm I dogOut vatOut saleOut
  have hrateExpr := evalExpr_endSnip_rate_afterYank evm I dogOut vatOut saleOut
  exact ExecStmt.letDeclRevert (endEvalExpr_div_uint256_revert_zero htab hrateExpr hrate)

theorem endSnipStoreDogIlk_get_ilk (I : ExecutionEnv) (dogOut : ByteArray) :
    (endSnipStoreDogIlk I dogOut).get? "ilk" =
      some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStoreDogIlk, store_get_ne _ _ (by native_decide)]
  exact endSnipStore_get_ilk I

theorem endSnipStoreClip_get_ilk (I : ExecutionEnv) (dogOut : ByteArray) :
    (endSnipStoreClip I dogOut).get? "ilk" =
      some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStoreClip, store_get_ne _ _ (by native_decide)]
  exact endSnipStoreDogIlk_get_ilk I dogOut

theorem endSnipStoreVatIlk_get_ilk (I : ExecutionEnv) (dogOut vatOut : ByteArray) :
    (endSnipStoreVatIlk I dogOut vatOut).get? "ilk" =
      some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStoreVatIlk, store_get_ne _ _ (by native_decide)]
  exact endSnipStoreClip_get_ilk I dogOut

theorem endSnipStoreRate_get_ilk (I : ExecutionEnv) (dogOut vatOut : ByteArray) :
    (endSnipStoreRate I dogOut vatOut).get? "ilk" =
      some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStoreRate, store_get_ne _ _ (by native_decide)]
  exact endSnipStoreVatIlk_get_ilk I dogOut vatOut

theorem endSnipStoreClipSale_get_ilk (I : ExecutionEnv)
    (dogOut vatOut saleOut : ByteArray) :
    (endSnipStoreClipSale I dogOut vatOut saleOut).get? "ilk" =
      some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStoreClipSale, store_get_ne _ _ (by native_decide)]
  exact endSnipStoreRate_get_ilk I dogOut vatOut

theorem endSnipStoreTab_get_ilk (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) :
    (endSnipStoreTab I dogOut vatOut saleOut).get? "ilk" =
      some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStoreTab, store_get_ne _ _ (by native_decide)]
  exact endSnipStoreClipSale_get_ilk I dogOut vatOut saleOut

theorem endSnipStoreLot_get_ilk (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) :
    (endSnipStoreLot I dogOut vatOut saleOut).get? "ilk" =
      some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStoreLot, store_get_ne _ _ (by native_decide)]
  exact endSnipStoreTab_get_ilk I dogOut vatOut saleOut

theorem endSnipStoreUsr_get_ilk (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) :
    (endSnipStoreUsr I dogOut vatOut saleOut).get? "ilk" =
      some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStoreUsr, store_get_ne _ _ (by native_decide)]
  exact endSnipStoreLot_get_ilk I dogOut vatOut saleOut

theorem endSnipStoreSuck_get_ilk (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) :
    (endSnipStoreSuck I dogOut vatOut saleOut).get? "ilk" =
      some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStoreSuck, store_get_ne _ _ (by native_decide)]
  exact endSnipStoreUsr_get_ilk I dogOut vatOut saleOut

theorem endSnipStoreYank_get_ilk (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) :
    (endSnipStoreYank I dogOut vatOut saleOut).get? "ilk" =
      some (.fixedBytes bytes32Width (endSnipIlkBytes I)) := by
  rw [endSnipStoreYank, store_get_ne _ _ (by native_decide)]
  exact endSnipStoreSuck_get_ilk I dogOut vatOut saleOut

theorem endSnipStoreArt_get_ilk (I : ExecutionEnv) (dogOut vatOut saleOut : ByteArray) :
    (endSnipStoreArt I dogOut vatOut saleOut).get? "ilk" = some (endFlowIlkValue I) := by
  rw [endSnipStoreArt, store_get_ne _ _ (by native_decide)]
  simpa [endFlowIlkValue, endBytes32ArgValue, endBytes32ArgBytes, endSnipIlkBytes]
    using endSnipStoreYank_get_ilk I dogOut vatOut saleOut

theorem endSnipStmtArtNewAddReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSnipArtSlot I) =
        endSnipArtOldWord σ I)
    (hfit :
      (endSnipArtOldWord σ I).toNat + (endSnipArtWord vatOut saleOut).toNat <
        UInt256.size) :
    ExecStmt config { contract := contract, locals := endSnipStoreArt I dogOut vatOut saleOut }
      evm (.internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew")
      (.ok { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
        evm) := by
  have hArt :
      evalExpr? config { contract := contract, locals := endSnipStoreArt I dogOut vatOut saleOut }
        evm (.storage (ArtRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endSnipArtOldWord σ I).toNat)) := by
    have hbase : (endSnipStoreArt I dogOut vatOut saleOut).get? "Art" = none := by
      rw [endSnipStoreArt, store_get_ne _ _ (by native_decide),
        endSnipStoreYank, store_get_ne _ _ (by native_decide),
        endSnipStoreSuck, store_get_ne _ _ (by native_decide),
        endSnipStoreUsr, store_get_ne _ _ (by native_decide),
        endSnipStoreLot, store_get_ne _ _ (by native_decide),
        endSnipStoreTab, store_get_ne _ _ (by native_decide),
        endSnipStoreClipSale, store_get_ne _ _ (by native_decide),
        endSnipStoreRate, store_get_ne _ _ (by native_decide),
        endSnipStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSnipStoreClip, store_get_ne _ _ (by native_decide),
        endSnipStoreDogIlk, store_get_ne _ _ (by native_decide),
        endSnipStore, store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp
    have hget := endSnipStoreArt_get_ilk I dogOut vatOut saleOut
    have hstorage := evalExpr_endFlow_Art_of_get evm I hbase hget (by omega)
    simpa [hArtLoad, endSnipArtWord, endSnipArtOldWord, endSnipArtSlot,
      endFlowArtSlot, endSnipIlkKey, endFlowIlkKey] using hstorage
  have hart :
      evalExpr? config { contract := contract, locals := endSnipStoreArt I dogOut vatOut saleOut }
        evm (.var "art") = .ok (.int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)) := by
    simpa [endSnipStoreArt] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSnipStoreArt I dogOut vatOut saleOut)
        (name := "art") (value := endSnipArtWord vatOut saleOut)
        (by rw [endSnipStoreArt, store_get_self])
  have hargs :
      evalExprs? config { contract := contract, locals := endSnipStoreArt I dogOut vatOut saleOut }
        evm [.storage (ArtRef (.var "ilk")), .var "art"] =
          .ok [.int (Int.ofNat (endSnipArtOldWord σ I).toNat),
            .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)] := by
    simp only [evalExprs?, hArt, hart, EvalResult.bind, bind, pure]
  have hstmt := endInternalAddFunctionReturn
    (evm := evm) (locals := endSnipStoreArt I dogOut vatOut saleOut)
    (args := [.storage (ArtRef (.var "ilk")), .var "art"])
    (retVar := "ArtNew") (x := endSnipArtOldWord σ I)
    (y := endSnipArtWord vatOut saleOut)
    (sum := endSnipArtNewWord σ I vatOut saleOut) hargs rfl hfit
  simpa only [endSnipStoreArtNew, resumeAfterInternalCall, collapseReturns,
    endSnipArtNewWord] using hstmt

theorem endSnipStmtArtNewAddReverts (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSnipArtSlot I) =
        endSnipArtOldWord σ I)
    (hover :
      UInt256.size ≤
        (endSnipArtOldWord σ I).toNat + (endSnipArtWord vatOut saleOut).toNat) :
    ExecStmt config { contract := contract, locals := endSnipStoreArt I dogOut vatOut saleOut }
      evm (.internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew")
      .reverted := by
  have hArt :
      evalExpr? config { contract := contract, locals := endSnipStoreArt I dogOut vatOut saleOut }
        evm (.storage (ArtRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endSnipArtOldWord σ I).toNat)) := by
    have hbase : (endSnipStoreArt I dogOut vatOut saleOut).get? "Art" = none := by
      rw [endSnipStoreArt, store_get_ne _ _ (by native_decide),
        endSnipStoreYank, store_get_ne _ _ (by native_decide),
        endSnipStoreSuck, store_get_ne _ _ (by native_decide),
        endSnipStoreUsr, store_get_ne _ _ (by native_decide),
        endSnipStoreLot, store_get_ne _ _ (by native_decide),
        endSnipStoreTab, store_get_ne _ _ (by native_decide),
        endSnipStoreClipSale, store_get_ne _ _ (by native_decide),
        endSnipStoreRate, store_get_ne _ _ (by native_decide),
        endSnipStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSnipStoreClip, store_get_ne _ _ (by native_decide),
        endSnipStoreDogIlk, store_get_ne _ _ (by native_decide),
        endSnipStore, store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp
    have hget := endSnipStoreArt_get_ilk I dogOut vatOut saleOut
    have hstorage := evalExpr_endFlow_Art_of_get evm I hbase hget (by omega)
    simpa [hArtLoad, endSnipArtWord, endSnipArtOldWord, endSnipArtSlot,
      endFlowArtSlot, endSnipIlkKey, endFlowIlkKey] using hstorage
  have hart :
      evalExpr? config { contract := contract, locals := endSnipStoreArt I dogOut vatOut saleOut }
        evm (.var "art") = .ok (.int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)) := by
    simpa [endSnipStoreArt] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSnipStoreArt I dogOut vatOut saleOut)
        (name := "art") (value := endSnipArtWord vatOut saleOut)
        (by rw [endSnipStoreArt, store_get_self])
  have hargs :
      evalExprs? config { contract := contract, locals := endSnipStoreArt I dogOut vatOut saleOut }
        evm [.storage (ArtRef (.var "ilk")), .var "art"] =
          .ok [.int (Int.ofNat (endSnipArtOldWord σ I).toNat),
            .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)] := by
    simp only [evalExprs?, hArt, hart, EvalResult.bind, bind, pure]
  exact endInternalAddFunctionRevert
    (evm := evm) (locals := endSnipStoreArt I dogOut vatOut saleOut)
    (args := [.storage (ArtRef (.var "ilk")), .var "art"])
    (retVar := "ArtNew") (x := endSnipArtOldWord σ I)
    (y := endSnipArtWord vatOut saleOut) hargs hover

theorem endSnipAssignArt {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (artNew : UInt256)
    (hbase : locals.get? "Art" = none)
    (hget : locals.get? "ilk" = some (endFlowIlkValue I))
    (hsz68 : 68 ≤ I.calldata.size) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (ArtRef (.var "ilk")) (.int (Int.ofNat artNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, endSnipPostArtState evm I artNew) := by
  simpa only [endSnipPostArtState, endSnipArtSlot, endSnipIlkKey, endFlowArtSlot,
    endFlowIlkKey] using
    endFlowAssignArtOfGet evm I artNew hbase hget (by omega)

theorem endSnipStmtArtAssignSplit (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size) :
    (ExecStmt config
      { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
      evm (.assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"))
      (.ok { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
        (endSnipPostArtState evm I (endSnipArtNewWord σ I vatOut saleOut)))) ∧
      (evm.executionEnv.perm = false →
        ExecStmt config
          { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
        evm (.assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"))
        .staticViolation) := by
  have hArtNew :
      evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
        evm (.var "ArtNew") =
        .ok (.int (Int.ofNat (endSnipArtNewWord σ I vatOut saleOut).toNat)) := by
    simpa [endSnipStoreArtNew] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSnipStoreArtNew σ I dogOut vatOut saleOut)
        (name := "ArtNew") (value := endSnipArtNewWord σ I vatOut saleOut)
        (by rw [endSnipStoreArtNew, store_get_self])
  have hassign :
      assignStorageRef? config
        { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
        evm .storage (ArtRef (.var "ilk"))
        (.int (Int.ofNat (endSnipArtNewWord σ I vatOut saleOut).toNat)) =
          .ok ({ contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut },
            endSnipPostArtState evm I (endSnipArtNewWord σ I vatOut saleOut)) := by
    have hbase : (endSnipStoreArtNew σ I dogOut vatOut saleOut).get? "Art" = none := by
      rw [endSnipStoreArtNew, store_get_ne _ _ (by native_decide),
        endSnipStoreArt, store_get_ne _ _ (by native_decide),
        endSnipStoreYank, store_get_ne _ _ (by native_decide),
        endSnipStoreSuck, store_get_ne _ _ (by native_decide),
        endSnipStoreUsr, store_get_ne _ _ (by native_decide),
        endSnipStoreLot, store_get_ne _ _ (by native_decide),
        endSnipStoreTab, store_get_ne _ _ (by native_decide),
        endSnipStoreClipSale, store_get_ne _ _ (by native_decide),
        endSnipStoreRate, store_get_ne _ _ (by native_decide),
        endSnipStoreVatIlk, store_get_ne _ _ (by native_decide),
        endSnipStoreClip, store_get_ne _ _ (by native_decide),
        endSnipStoreDogIlk, store_get_ne _ _ (by native_decide),
        endSnipStore, store_get_ne _ _ (by native_decide),
        store_get_ne _ _ (by native_decide)]
      simp
    have hget :
        (endSnipStoreArtNew σ I dogOut vatOut saleOut).get? "ilk" =
          some (endFlowIlkValue I) := by
      rw [endSnipStoreArtNew, store_get_ne _ _ (by native_decide)]
      exact endSnipStoreArt_get_ilk I dogOut vatOut saleOut
    exact endSnipAssignArt evm I (endSnipArtNewWord σ I vatOut saleOut) hbase hget hsz68
  exact ⟨ExecStmt.assign hArtNew hassign,
    fun hperm ↦ ExecStmt.assignStatic hArtNew hassign hperm⟩

theorem endSnipStmtArtAssign (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size) :
    ExecStmt config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
      evm (.assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"))
      (.ok { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
        (endSnipPostArtState evm I (endSnipArtNewWord σ I vatOut saleOut))) :=
  (endSnipStmtArtAssignSplit evm I σ dogOut vatOut saleOut hsz68).1

theorem endSnipEvalExpr_intLimit (evm : EVM.State) {locals : Store} :
    evalExpr? config { contract := contract, locals := locals } evm (.intLit int256Limit) =
      .ok (.int int256Limit) := by
  simp [evalExpr?, pure]

theorem endSnipEvalExpr_lt_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hlt : a < b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .lt lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, hlt]

theorem endSnipEvalExpr_lt_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (hle : b ≤ a) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .lt lhs rhs) =
      .ok (.bool false) := by
  have hnot : ¬ a < b := by omega
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, hnot]

theorem evalExpr_endSnip_lot_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
      evm (.var "lot") =
      .ok (.int (Int.ofNat (endSnipSaleLotWord saleOut).toNat)) := by
  simpa [endSnipStoreArtNew, endSnipStoreArt, endSnipStoreYank, endSnipStoreSuck,
    endSnipStoreUsr, endSnipStoreLot] using
    endEvalExpr_varUInt256 (evm := evm)
      (locals := endSnipStoreArtNew σ I dogOut vatOut saleOut)
      (name := "lot") (value := endSnipSaleLotWord saleOut)
      (by
        rw [endSnipStoreArtNew, store_get_ne _ _ (by native_decide),
          endSnipStoreArt, store_get_ne _ _ (by native_decide),
          endSnipStoreYank, store_get_ne _ _ (by native_decide),
          endSnipStoreSuck, store_get_ne _ _ (by native_decide),
          endSnipStoreUsr, store_get_ne _ _ (by native_decide),
          endSnipStoreLot, store_get_self])

theorem evalExpr_endSnip_art_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
      evm (.var "art") =
      .ok (.int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)) := by
  simpa [endSnipStoreArtNew, endSnipStoreArt] using
    endEvalExpr_varUInt256 (evm := evm)
      (locals := endSnipStoreArtNew σ I dogOut vatOut saleOut)
      (name := "art") (value := endSnipArtWord vatOut saleOut)
      (by
        rw [endSnipStoreArtNew, store_get_ne _ _ (by native_decide),
          endSnipStoreArt, store_get_self])

theorem endSnipEvalExpr_intGuard_true (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (hlot : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hart : (endSnipArtWord vatOut saleOut).toNat < 2 ^ 255) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) = .ok (.bool true) := by
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by native_decide
  have hlotExpr := evalExpr_endSnip_lot_afterArtNew evm I σ dogOut vatOut saleOut
  have hartExpr := evalExpr_endSnip_art_afterArtNew evm I σ dogOut vatOut saleOut
  have hlimitExpr :
      evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
        (.intLit int256Limit) = .ok (.int int256Limit) :=
    endSnipEvalExpr_intLimit evm
  have hlotLt :
      evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
        (.binary .lt (.var "lot") (.intLit int256Limit)) = .ok (.bool true) :=
    endSnipEvalExpr_lt_int_true hlotExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_lt.mpr hlot)
  have hartLt :
      evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
        (.binary .lt (.var "art") (.intLit int256Limit)) = .ok (.bool true) :=
    endSnipEvalExpr_lt_int_true hartExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_lt.mpr hart)
  simp [evalExpr?, EvalResult.bind, bind, hlotLt, hartLt, pure]

theorem endSnipEvalExpr_intGuard_false_lot (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (hlot : 2 ^ 255 ≤ (endSnipSaleLotWord saleOut).toNat) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) = .ok (.bool false) := by
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by native_decide
  have hlotExpr := evalExpr_endSnip_lot_afterArtNew evm I σ dogOut vatOut saleOut
  have hlimitExpr :
      evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
        (.intLit int256Limit) = .ok (.int int256Limit) :=
    endSnipEvalExpr_intLimit evm
  have hlotLt :
      evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
        (.binary .lt (.var "lot") (.intLit int256Limit)) = .ok (.bool false) :=
    endSnipEvalExpr_lt_int_false hlotExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_le.mpr hlot)
  simp [evalExpr?, EvalResult.bind, bind, hlotLt, pure]

theorem endSnipEvalExpr_intGuard_false_art (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (hlot : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hart : 2 ^ 255 ≤ (endSnipArtWord vatOut saleOut).toNat) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) = .ok (.bool false) := by
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by native_decide
  have hlotExpr := evalExpr_endSnip_lot_afterArtNew evm I σ dogOut vatOut saleOut
  have hartExpr := evalExpr_endSnip_art_afterArtNew evm I σ dogOut vatOut saleOut
  have hlimitExpr :
      evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
        (.intLit int256Limit) = .ok (.int int256Limit) :=
    endSnipEvalExpr_intLimit evm
  have hlotLt :
      evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
        (.binary .lt (.var "lot") (.intLit int256Limit)) = .ok (.bool true) :=
    endSnipEvalExpr_lt_int_true hlotExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_lt.mpr hlot)
  have hartLt :
      evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut } evm
        (.binary .lt (.var "art") (.intLit int256Limit)) = .ok (.bool false) :=
    endSnipEvalExpr_lt_int_false hartExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_le.mpr hart)
  simp [evalExpr?, EvalResult.bind, bind, hlotLt, hartLt, pure]

theorem endSnipVatReceiver_afterArtNewFor {σCall σLoc I dogOut vatOut saleOut evm}
    (hmap : evm.accountMap = σCall)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut } evm
      (.storage vatRef) = .ok (.address (endPackVatAddr σCall I)) := by
  simpa only [hmap] using
    evalExpr_endPack_vat_addr
      (locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut) evm I
      (endSnipStoreArtNew_get_vat_none σLoc I dogOut vatOut saleOut) howner

theorem evalExpr_endSnip_ilk_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
      evm (.var "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
  apply endEvalExpr_varFixedBytes
  rw [endSnipStoreArtNew, store_get_ne _ _ (by native_decide)]
  simpa [endFlowIlkValue, endBytes32ArgValue] using
    endSnipStoreArt_get_ilk I dogOut vatOut saleOut

theorem evalExpr_endSnip_usr_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
      evm (.var "usr") = .ok (.address (endSnipSaleUsrAddr saleOut)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
    ((endSnipStoreArtNew σ I dogOut vatOut saleOut).get? "usr") =
      .ok (.address (endSnipSaleUsrAddr saleOut))
  rw [endSnipStoreArtNew, store_get_ne _ _ (by native_decide),
    endSnipStoreArt, store_get_ne _ _ (by native_decide),
    endSnipStoreYank, store_get_ne _ _ (by native_decide),
    endSnipStoreSuck, store_get_ne _ _ (by native_decide),
    endSnipStoreUsr, store_get_self]
  rfl

theorem evalExpr_endSnip_this_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
      evm thisAddr = .ok (.address I.codeOwner) := by
  simp [thisAddr, evalExpr?, envValue, howner, pure]

theorem evalExpr_endSnip_vow_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
      evm vowAddr = .ok (.address (endPackVowAddr evm.accountMap I)) := by
  exact evalExpr_endPack_vow_addr
    (locals := endSnipStoreArtNew σ I dogOut vatOut saleOut) evm I
    (endSnipStoreArtNew_get_vow_none σ I dogOut vatOut saleOut) howner

theorem evalExpr_endSnip_lot_asInt_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (hlotBound : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
      evm (asInt256 (.var "lot")) =
      .ok (.int (Int.ofNat (endSnipSaleLotWord saleOut).toNat)) := by
  have hlot := evalExpr_endSnip_lot_afterArtNew evm I σ dogOut vatOut saleOut
  have hcast := evalExpr_cast_int (intType := int256Int) hlot
  have hbound : (endSnipSaleLotWord saleOut).toNat < EVM.twoPow 255 := by
    simpa [EVM.twoPow] using hlotBound
  have hnormalize :
      normalizeInt int256Int (Int.ofNat (endSnipSaleLotWord saleOut).toNat) =
        Int.ofNat (endSnipSaleLotWord saleOut).toNat := by
    simpa [int256Int] using
      normalizeInt_sint256_word_of_lt (endSnipSaleLotWord saleOut) hbound
  calc
    evalExpr? config
        { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
        evm (asInt256 (.var "lot")) =
        .ok (.int (normalizeInt int256Int
          (Int.ofNat (endSnipSaleLotWord saleOut).toNat))) := by
      simpa only [asInt256, int256St] using hcast
    _ = .ok (.int (Int.ofNat (endSnipSaleLotWord saleOut).toNat)) := by
      rw [hnormalize]

theorem evalExpr_endSnip_art_asInt_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (hartBound : (endSnipArtWord vatOut saleOut).toNat < 2 ^ 255) :
    evalExpr? config { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
      evm (asInt256 (.var "art")) =
      .ok (.int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)) := by
  have hart := evalExpr_endSnip_art_afterArtNew evm I σ dogOut vatOut saleOut
  have hcast := evalExpr_cast_int (intType := int256Int) hart
  have hbound : (endSnipArtWord vatOut saleOut).toNat < EVM.twoPow 255 := by
    simpa [EVM.twoPow] using hartBound
  have hnormalize :
      normalizeInt int256Int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat) =
        Int.ofNat (endSnipArtWord vatOut saleOut).toNat := by
    simpa [int256Int] using
      normalizeInt_sint256_word_of_lt (endSnipArtWord vatOut saleOut) hbound
  calc
    evalExpr? config
        { contract := contract, locals := endSnipStoreArtNew σ I dogOut vatOut saleOut }
        evm (asInt256 (.var "art")) =
        .ok (.int (normalizeInt int256Int
          (Int.ofNat (endSnipArtWord vatOut saleOut).toNat))) := by
      simpa only [asInt256, int256St] using hcast
    _ = .ok (.int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)) := by
      rw [hnormalize]

theorem evalExprs_endSnip_grabArgs (evm : EVM.State) (I : ExecutionEnv)
    (σCall σLoc : AccountMap) (dogOut vatOut saleOut : ByteArray)
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hlotBound : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hartBound : (endSnipArtWord vatOut saleOut).toNat < 2 ^ 255) :
    evalExprs? config { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut } evm
      [.var "ilk", .var "usr", thisAddr, vowAddr,
        asInt256 (.var "lot"), asInt256 (.var "art")] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSnipSaleUsrAddr saleOut),
          .address I.codeOwner,
          .address (endPackVowAddr evm.accountMap I),
          .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
          .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)] := by
  have hilk := evalExpr_endSnip_ilk_afterArtNew evm I σLoc dogOut vatOut saleOut
  have husr := evalExpr_endSnip_usr_afterArtNew evm I σLoc dogOut vatOut saleOut
  have hthis := evalExpr_endSnip_this_afterArtNew evm I σLoc dogOut vatOut saleOut howner
  have hvow := evalExpr_endSnip_vow_afterArtNew evm I σLoc dogOut vatOut saleOut howner
  have hlot :=
    evalExpr_endSnip_lot_asInt_afterArtNew evm I σLoc dogOut vatOut saleOut hlotBound
  have hart :=
    evalExpr_endSnip_art_asInt_afterArtNew evm I σLoc dogOut vatOut saleOut hartBound
  rw [evalExprs?]
  simp only [hilk, EvalResult.bind, bind]
  rw [evalExprs?]
  simp only [husr, EvalResult.bind, bind]
  rw [evalExprs?]
  simp only [hthis, EvalResult.bind, bind]
  rw [evalExprs?]
  simp only [hvow, EvalResult.bind, bind]
  rw [evalExprs?]
  simp only [hlot, EvalResult.bind, bind]
  rw [evalExprs?]
  simp only [hart, EvalResult.bind, bind]
  rw [evalExprs?]
  simp only [pure]

theorem endSnipGrabTailReverts_noCodeFor {σCall σLoc I}
    {dogOut vatOut saleOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σCall) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) = ⟨0⟩) :
    ExecBlock config
      { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")] "_grab")
      .reverted := by
  have hreceiver := endSnipVatReceiver_afterArtNewFor
    (σCall := σCall) (σLoc := σLoc) (I := I) (dogOut := dogOut)
    (vatOut := vatOut) (saleOut := saleOut) (evm := evm) hmap howner
  have hcodeZero := endSnipVatCode_zero_afterClip
    (σ := σCall) (I := I) (dogOut := dogOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut)
      (receiver := .storage vatRef) (retVar := "_grab") (name := "grab")
      (sendVal := 0)
      (args := [.var "ilk", .var "usr", thisAddr, vowAddr,
        asInt256 (.var "lot"), asInt256 (.var "art")])
      (perm := true) hguard

theorem endSnipGrabTailReverts_callFailedFor {σCall σLoc I}
    {dogOut vatOut saleOut grabOut : ByteArray} {evm evmGrab : EVM.State}
    (hmap : evm.accountMap = σCall) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) ≠ ⟨0⟩)
    (hlotBound : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hartBound : (endSnipArtWord vatOut saleOut).toNat < 2 ^ 255)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σCall I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSnipSaleUsrAddr saleOut),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
          .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)]
        (false, evmGrab, grabOut) true) :
    ExecBlock config
      { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")] "_grab")
      .reverted := by
  have hreceiver := endSnipVatReceiver_afterArtNewFor
    (σCall := σCall) (σLoc := σLoc) (I := I) (dogOut := dogOut)
    (vatOut := vatOut) (saleOut := saleOut) (evm := evm) hmap howner
  have hcodePos := endSnipVatCode_pos_afterClip
    (σ := σCall) (I := I) (dogOut := dogOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargsRaw :=
    evalExprs_endSnip_grabArgs evm I σCall σLoc dogOut vatOut saleOut howner
      hlotBound hartBound
  have hargs :
      evalExprs? config
        { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
        evm [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
            .address (endSnipSaleUsrAddr saleOut),
            .address I.codeOwner,
            .address (endPackVowAddr σCall I),
            .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
            .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)] := by
    simpa [hmap] using hargsRaw
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmGrab)
      (locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut)
      (receiver := .storage vatRef) (retVar := "_grab") (name := "grab")
      (target := endPackVatAddr σCall I) (sendVal := 0)
      (args := [.var "ilk", .var "usr", thisAddr, vowAddr,
        asInt256 (.var "lot"), asInt256 (.var "art")])
      (argVals :=
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSnipSaleUsrAddr saleOut),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
          .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)])
      (out := grabOut) (perm := true) hguard hreceiver hargs hcall

theorem endSnipGrabTailReturns_successFor {σCall σLoc I}
    {dogOut vatOut saleOut grabOut : ByteArray} {evm evmGrab : EVM.State}
    (hmap : evm.accountMap = σCall) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) ≠ ⟨0⟩)
    (hlotBound : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hartBound : (endSnipArtWord vatOut saleOut).toNat < 2 ^ 255)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σCall I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSnipSaleUsrAddr saleOut),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
          .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)]
        (true, evmGrab, grabOut) true) :
    ExecBlock config
      { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")] "_grab")
      (.ok { contract := contract, locals := endSnipStoreGrab σLoc I dogOut vatOut saleOut }
        evmGrab) := by
  have hreceiver := endSnipVatReceiver_afterArtNewFor
    (σCall := σCall) (σLoc := σLoc) (I := I) (dogOut := dogOut)
    (vatOut := vatOut) (saleOut := saleOut) (evm := evm) hmap howner
  have hcodePos := endSnipVatCode_pos_afterClip
    (σ := σCall) (I := I) (dogOut := dogOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargsRaw :=
    evalExprs_endSnip_grabArgs evm I σCall σLoc dogOut vatOut saleOut howner
      hlotBound hartBound
  have hargs :
      evalExprs? config
        { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
        evm [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
            .address (endSnipSaleUsrAddr saleOut),
            .address I.codeOwner,
            .address (endPackVowAddr σCall I),
            .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
            .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)] := by
    simpa [hmap] using hargsRaw
  have hdec : config.externalABI.decode? "grab" grabOut = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmGrab)
    (locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut)
    (receiver := .storage vatRef) (retVar := "_grab") (name := "grab")
    (target := endPackVatAddr σCall I) (sendVal := 0)
    (args := [.var "ilk", .var "usr", thisAddr, vowAddr,
      asInt256 (.var "lot"), asInt256 (.var "art")])
    (argVals :=
      [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address (endSnipSaleUsrAddr saleOut),
        .address I.codeOwner,
        .address (endPackVowAddr σCall I),
        .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
        .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)])
    (out := grabOut) (perm := true) (value := [])
    hguard hreceiver hargs hcall hdec
  simpa [checkedExternalCallStmts, endSnipStoreGrab, collapseReturns] using hblock

theorem endSnipTailAfterUsrReturnsSplit {I σLoc}
    {dogOut vatOut saleOut : ByteArray} {evmUsr evmSuck evmYank : EVM.State}
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evmYank evmYank.executionEnv.codeOwner (endSnipArtSlot I) =
        endSnipArtOldWord σLoc I)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (hfit :
      (endSnipArtOldWord σLoc I).toNat + (endSnipArtWord vatOut saleOut).toNat <
        UInt256.size)
    (hsuck :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck")
        (.ok { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
          evmSuck))
    (hyank :
      ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evmSuck
        (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
        (.ok { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
          evmYank)) :
    (((endSnipSaleLotWord saleOut).toNat < 2 ^ 255) →
      ((endSnipArtWord vatOut saleOut).toNat < 2 ^ 255) →
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evmUsr
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ])
      (.ok { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
        (endSnipPostArtState evmYank I (endSnipArtNewWord σLoc I vatOut saleOut)))) ∧
      (evmYank.executionEnv.perm = false →
        ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck" ++
          checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
          [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
            .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
            .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
            .require
              (.binary .and
                (.binary .lt (.var "lot") (.intLit int256Limit))
                (.binary .lt (.var "art") (.intLit int256Limit))) ])
        .staticViolation) := by
  have hprefix {result : ExecResult}
      (hwrite : ExecBlock config
        { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
        evmYank [.assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require (.binary .and
            (.binary .lt (.var "lot") (.intLit int256Limit))
            (.binary .lt (.var "art") (.intLit int256Limit)))] result) :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck" ++
          checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
          [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
            .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
            .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
            .require
              (.binary .and
                (.binary .lt (.var "lot") (.intLit int256Limit))
                (.binary .lt (.var "art") (.intLit int256Limit))) ])
        result := by
    have hartBlock :
        ExecBlock config
          { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
          evmYank
          [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
            .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
            .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
            .require
              (.binary .and
                (.binary .lt (.var "lot") (.intLit int256Limit))
                (.binary .lt (.var "art") (.intLit int256Limit))) ]
          result := by
      refine ExecBlock.consNormal (endSnipStmtArt evmYank I dogOut vatOut saleOut hrate) ?_
      refine ExecBlock.consNormal
        (endSnipStmtArtNewAddReturns evmYank I σLoc dogOut vatOut saleOut hsz68 hArtLoad hfit) ?_
      exact hwrite
    simpa [List.append_assoc] using
     execBlock_append hsuck
        (Reasoning.Theory.execBlock_append hyank hartBlock)
  have hassign := endSnipStmtArtAssignSplit evmYank I σLoc
    dogOut vatOut saleOut hsz68
  constructor
  · intro hlot hart
    apply hprefix
    refine ExecBlock.consNormal
      (hassign.1) ?_
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue
        (endSnipEvalExpr_intGuard_true
          (endSnipPostArtState evmYank I (endSnipArtNewWord σLoc I vatOut saleOut))
          I σLoc dogOut vatOut saleOut hlot hart))
      ExecBlock.nil
  · intro hperm
    exact hprefix (ExecBlock.consStatic (hassign.2 hperm))

theorem endSnipTailAfterUsrReturns {I σLoc}
    {dogOut vatOut saleOut : ByteArray} {evmUsr evmSuck evmYank : EVM.State}
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evmYank evmYank.executionEnv.codeOwner (endSnipArtSlot I) =
        endSnipArtOldWord σLoc I)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (hfit :
      (endSnipArtOldWord σLoc I).toNat + (endSnipArtWord vatOut saleOut).toNat <
        UInt256.size)
    (hlot : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hart : (endSnipArtWord vatOut saleOut).toNat < 2 ^ 255)
    (hsuck :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck")
        (.ok { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
          evmSuck))
    (hyank :
      ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evmSuck
        (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
        (.ok { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
          evmYank)) :
    ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evmUsr
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ])
      (.ok { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
        (endSnipPostArtState evmYank I (endSnipArtNewWord σLoc I vatOut saleOut))) :=
  (endSnipTailAfterUsrReturnsSplit hsz68 hArtLoad hrate hfit
    hsuck hyank).1 hlot hart

theorem endSnipTailReverts_suck {I} {dogOut vatOut saleOut : ByteArray}
    {evmUsr : EVM.State}
    (hsuck :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck")
        .reverted) :
    ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evmUsr
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ])
      .reverted := by
  simpa [List.append_assoc] using
   execBlock_append_term hsuck (by intro f' e' h; cases h)

theorem endSnipTailReverts_yank {I} {dogOut vatOut saleOut : ByteArray}
    {evmUsr evmSuck : EVM.State}
    (hsuck :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck")
        (.ok { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
          evmSuck))
    (hyank :
      ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evmSuck
        (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
        .reverted) :
    ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evmUsr
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ])
      .reverted := by
  have hyankTail :
      ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evmSuck
        (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ])
        .reverted := by
    exact execBlock_append_term hyank (by intro f' e' h; cases h)
  simpa [List.append_assoc] using
   execBlock_append hsuck hyankTail

theorem endSnipTailReverts_artDivZero {I} {dogOut vatOut saleOut : ByteArray}
    {evmUsr evmSuck evmYank : EVM.State}
    (hrate : endFlowVatIlkRateWord vatOut = ⟨0⟩)
    (hsuck :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck")
        (.ok { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
          evmSuck))
    (hyank :
      ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evmSuck
        (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
        (.ok { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
          evmYank)) :
    ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evmUsr
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ])
      .reverted := by
  have hartRevert :
      ExecBlock config { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
        evmYank
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ]
        .reverted :=
    ExecBlock.consRevert (endSnipStmtArtReverts evmYank I dogOut vatOut saleOut hrate)
  simpa [List.append_assoc] using
   execBlock_append hsuck
      (Reasoning.Theory.execBlock_append hyank hartRevert)

theorem endSnipTailReverts_artAddOverflow {I σLoc}
    {dogOut vatOut saleOut : ByteArray} {evmUsr evmSuck evmYank : EVM.State}
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evmYank evmYank.executionEnv.codeOwner (endSnipArtSlot I) =
        endSnipArtOldWord σLoc I)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤
        (endSnipArtOldWord σLoc I).toNat + (endSnipArtWord vatOut saleOut).toNat)
    (hsuck :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck")
        (.ok { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
          evmSuck))
    (hyank :
      ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evmSuck
        (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
        (.ok { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
          evmYank)) :
    ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evmUsr
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ])
      .reverted := by
  have hartBlock :
      ExecBlock config { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
        evmYank
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ]
        .reverted := by
    refine ExecBlock.consNormal (endSnipStmtArt evmYank I dogOut vatOut saleOut hrate) ?_
    exact ExecBlock.consRevert
      (endSnipStmtArtNewAddReverts evmYank I σLoc dogOut vatOut saleOut hsz68 hArtLoad hover)
  simpa [List.append_assoc] using
   execBlock_append hsuck
      (Reasoning.Theory.execBlock_append hyank hartBlock)

theorem endSnipTailReverts_intGuardLot {I σLoc}
    {dogOut vatOut saleOut : ByteArray} {evmUsr evmSuck evmYank : EVM.State}
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evmYank evmYank.executionEnv.codeOwner (endSnipArtSlot I) =
        endSnipArtOldWord σLoc I)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (hfit :
      (endSnipArtOldWord σLoc I).toNat + (endSnipArtWord vatOut saleOut).toNat <
        UInt256.size)
    (hlot : 2 ^ 255 ≤ (endSnipSaleLotWord saleOut).toNat)
    (hsuck :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck")
        (.ok { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
          evmSuck))
    (hyank :
      ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evmSuck
        (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
        (.ok { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
          evmYank)) :
    ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evmUsr
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ])
      .reverted := by
  have hartBlock :
      ExecBlock config { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
        evmYank
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ]
        .reverted := by
    refine ExecBlock.consNormal (endSnipStmtArt evmYank I dogOut vatOut saleOut hrate) ?_
    refine ExecBlock.consNormal
      (endSnipStmtArtNewAddReturns evmYank I σLoc dogOut vatOut saleOut hsz68 hArtLoad hfit) ?_
    refine ExecBlock.consNormal
      (endSnipStmtArtAssign evmYank I σLoc dogOut vatOut saleOut hsz68) ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endSnipEvalExpr_intGuard_false_lot
          (endSnipPostArtState evmYank I (endSnipArtNewWord σLoc I vatOut saleOut))
          I σLoc dogOut vatOut saleOut hlot))
  simpa [List.append_assoc] using
   execBlock_append hsuck
      (Reasoning.Theory.execBlock_append hyank hartBlock)

theorem endSnipTailReverts_intGuardArt {I σLoc}
    {dogOut vatOut saleOut : ByteArray} {evmUsr evmSuck evmYank : EVM.State}
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evmYank evmYank.executionEnv.codeOwner (endSnipArtSlot I) =
        endSnipArtOldWord σLoc I)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (hfit :
      (endSnipArtOldWord σLoc I).toNat + (endSnipArtWord vatOut saleOut).toNat <
        UInt256.size)
    (hlot : (endSnipSaleLotWord saleOut).toNat < 2 ^ 255)
    (hart : 2 ^ 255 ≤ (endSnipArtWord vatOut saleOut).toNat)
    (hsuck :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck")
        (.ok { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
          evmSuck))
    (hyank :
      ExecBlock config { contract := contract, locals := endSnipStoreSuck I dogOut vatOut saleOut }
        evmSuck
        (checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank")
        (.ok { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
          evmYank)) :
    ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
      evmUsr
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ])
      .reverted := by
  have hartBlock :
      ExecBlock config { contract := contract, locals := endSnipStoreYank I dogOut vatOut saleOut }
        evmYank
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ]
        .reverted := by
    refine ExecBlock.consNormal (endSnipStmtArt evmYank I dogOut vatOut saleOut hrate) ?_
    refine ExecBlock.consNormal
      (endSnipStmtArtNewAddReturns evmYank I σLoc dogOut vatOut saleOut hsz68 hArtLoad hfit) ?_
    refine ExecBlock.consNormal
      (endSnipStmtArtAssign evmYank I σLoc dogOut vatOut saleOut hsz68) ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endSnipEvalExpr_intGuard_false_art
          (endSnipPostArtState evmYank I (endSnipArtNewWord σLoc I vatOut saleOut))
          I σLoc dogOut vatOut saleOut hlot hart))
  simpa [List.append_assoc] using
   execBlock_append hsuck
      (Reasoning.Theory.execBlock_append hyank hartBlock)

theorem endSnipBodyBlock_afterUsrTailTerm {I} {dogOut vatOut saleOut : ByteArray} {result :
  ExecResult}
    {evm0 evmUsr : EVM.State}
    (hprefixUsr :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
            "dogIlk" ++
          [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
            "clipSale" (perm := false) ++
          [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
            .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
            .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ])
        (.ok { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
          evmUsr))
    (htail :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck" ++
          checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
          [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
            .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
            .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
            .require
              (.binary .and
                (.binary .lt (.var "lot") (.intLit int256Limit))
                (.binary .lt (.var "art") (.intLit int256Limit))) ])
        result)
    (hterm : ∀ f e, result ≠ .ok f e) :
    ExecBlock config { contract := contract, locals := endSnipStore I } evm0
      snipTransition.body result := by
  let grabTail :=
    checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
      [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
        asInt256 (.var "art")] "_grab"
  have htailWithGrab :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck" ++
          checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
          [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
            .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
            .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
            .require
              (.binary .and
                (.binary .lt (.var "lot") (.intLit int256Limit))
                (.binary .lt (.var "art") (.intLit int256Limit))) ] ++ grabTail)
        result := by
    exact execBlock_append_term htail hterm
  have hblock :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        snipTransition.body result := by
    have hseq := execBlock_append hprefixUsr htailWithGrab
    simpa [snipTransition, grabTail, List.append_assoc] using hseq
  exact hblock

theorem endSnipBodyReverts_afterUsrTailReverted {I} {dogOut vatOut saleOut : ByteArray}
    {evm0 evmUsr : EVM.State}
    (hprefixUsr :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
            "dogIlk" ++
          [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
            "clipSale" (perm := false) ++
          [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
            .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
            .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ])
        (.ok { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
          evmUsr))
    (htail :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck" ++
          checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
          [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
            .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
            .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
            .require
              (.binary .and
                (.binary .lt (.var "lot") (.intLit int256Limit))
                (.binary .lt (.var "art") (.intLit int256Limit))) ])
        .reverted) :
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body .reverted :=
  ExecFuncBody.execBlockRevert
    (endSnipBodyBlock_afterUsrTailTerm hprefixUsr htail (by intro _ _ h; cases h))

theorem endSnipBodyReverts_afterUsrTailGrabReverted {I σLoc}
    {dogOut vatOut saleOut : ByteArray} {evm0 evmUsr evmPost : EVM.State}
    (hprefixUsr :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
            "dogIlk" ++
          [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
            "clipSale" (perm := false) ++
          [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
            .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
            .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ])
        (.ok { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
          evmUsr))
    (htail :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck" ++
          checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
          [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
            .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
            .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
            .require
              (.binary .and
                (.binary .lt (.var "lot") (.intLit int256Limit))
                (.binary .lt (.var "art") (.intLit int256Limit))) ])
        (.ok { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
          evmPost))
    (hgrab :
      ExecBlock config
        { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
        evmPost
        (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
            asInt256 (.var "art")] "_grab")
        .reverted) :
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body .reverted := by
  let grabTail :=
    checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
      [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
        asInt256 (.var "art")] "_grab"
  have htailWithGrab :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck" ++
          checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
          [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
            .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
            .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
            .require
              (.binary .and
                (.binary .lt (.var "lot") (.intLit int256Limit))
                (.binary .lt (.var "art") (.intLit int256Limit))) ] ++ grabTail)
        .reverted := by
    exact execBlock_append htail hgrab
  have hblock :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        snipTransition.body .reverted := by
    have hseq := execBlock_append hprefixUsr htailWithGrab
    simpa [snipTransition, grabTail, List.append_assoc] using hseq
  exact ExecFuncBody.execBlockRevert hblock

theorem endSnipBodyReturns_afterUsrTailGrabSuccess {I σLoc}
    {dogOut vatOut saleOut : ByteArray} {evm0 evmUsr evmPost evmGrab : EVM.State}
    (hprefixUsr :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
            "dogIlk" ++
          [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
            "clipSale" (perm := false) ++
          [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
            .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
            .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ])
        (.ok { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
          evmUsr))
    (htail :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck" ++
          checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
          [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
            .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
            .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
            .require
              (.binary .and
                (.binary .lt (.var "lot") (.intLit int256Limit))
                (.binary .lt (.var "art") (.intLit int256Limit))) ])
        (.ok { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
          evmPost))
    (hgrab :
      ExecBlock config
        { contract := contract, locals := endSnipStoreArtNew σLoc I dogOut vatOut saleOut }
        evmPost
        (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
            asInt256 (.var "art")] "_grab")
        (.ok { contract := contract, locals := endSnipStoreGrab σLoc I dogOut vatOut saleOut }
          evmGrab)) :
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body
      (.returned { contract := contract, locals := endSnipStoreGrab σLoc I dogOut vatOut saleOut }
        evmGrab none) := by
  let grabTail :=
    checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
      [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
        asInt256 (.var "art")] "_grab"
  have htailWithGrab :
      ExecBlock config { contract := contract, locals := endSnipStoreUsr I dogOut vatOut saleOut }
        evmUsr
        (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
            [vowAddr, vowAddr, .var "tab"] "_suck" ++
          checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
          [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
            .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
            .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
            .require
              (.binary .and
                (.binary .lt (.var "lot") (.intLit int256Limit))
                (.binary .lt (.var "art") (.intLit int256Limit))) ] ++ grabTail)
        (.ok { contract := contract, locals := endSnipStoreGrab σLoc I dogOut vatOut saleOut }
          evmGrab) := by
    exact execBlock_append htail hgrab
  have hblock :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        snipTransition.body
        (.ok { contract := contract, locals := endSnipStoreGrab σLoc I dogOut vatOut saleOut }
          evmGrab) := by
    have hseq := execBlock_append hprefixUsr htailWithGrab
    simpa [snipTransition, grabTail, List.append_assoc] using hseq
  exact ExecFuncBody.execBlockOK hblock

theorem endSnipBodyReverts_afterRateSalesBlock {I} {dogOut vatOut : ByteArray}
    {evm0 evmVat : EVM.State}
    (hprefix :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
            "dogIlk" ++
          [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
        (.ok { contract := contract, locals := endSnipStoreRate I dogOut vatOut } evmVat))
    (hsales :
      ExecBlock config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
        evmVat
        (checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
          "clipSale" (perm := false)) .reverted) :
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body .reverted := by
  let afterSales : List Stmt :=
    [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
      .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
      .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
    checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
      [vowAddr, vowAddr, .var "tab"] "_suck" ++
    checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
    [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
      .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
      .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
      .require
        (.binary .and
          (.binary .lt (.var "lot") (.intLit int256Limit))
          (.binary .lt (.var "art") (.intLit int256Limit))) ] ++
    checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
      [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
        asInt256 (.var "art")] "_grab"
  have hsalesWithTail :
      ExecBlock config { contract := contract, locals := endSnipStoreRate I dogOut vatOut }
        evmVat
        (checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"]
          "clipSale" (perm := false) ++ afterSales) .reverted := by
    exact execBlock_append_term
      (s2 := afterSales) hsales (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endSnipStore I } evm0
        snipTransition.body .reverted := by
    have hseq := execBlock_append hprefix hsalesWithTail
    simpa [snipTransition, afterSales, List.append_assoc] using hseq
  exact ExecFuncBody.execBlockRevert hblock

theorem endSnipBodyReverts_tagZero {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSnipTagWord σ I = ⟨0⟩) :
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSnipStore I) snipTransition.body .reverted := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSnipTagSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSnipTagWord, solcSlotWordAt, solcSlotWord] using htag
  have hguard :
      evalExpr? config { contract := contract, locals := endSnipStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endSnip_tag_ne_false evm0 I hsz68 htagLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [snipTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endSnipStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0))
      (rest :=
        checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0) [.var "ilk"]
          "dogIlk" ++
        [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "clip") "sales" (.intLit 0) [.var "id"] "clipSale"
          (perm := false) ++
        [ .letDecl "tab" (some uint256) (.tupleGet (.var "clipSale") 1),
          .letDecl "lot" (some uint256) (.tupleGet (.var "clipSale") 2),
          .letDecl "usr" (some addr) (.tupleGet (.var "clipSale") 3) ] ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck" ++
        checkedExternalCallStmts (.var "clip") "yank" (.intLit 0) [.var "id"] "_yank" ++
        [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
          .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
          .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
          .require
            (.binary .and
              (.binary .lt (.var "lot") (.intLit int256Limit))
              (.binary .lt (.var "art") (.intLit int256Limit))) ] ++
        checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
          [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
            asInt256 (.var "art")] "_grab")
      (by simp only [evm0, initState]; exact hwv)
      hguard

theorem endSnipX_shortarg {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState σ σ₀ g A I) endSnipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev endBytecode g (initState σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := endSnipEntryPc) (ret := endSnipReturnPc)
    (decoded := endSnipDecodedPc) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endSnipBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some snipTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) endSnipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact (endSnipX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_snip_none_short hsz4 hshort)

theorem endSnipBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf snipTransition)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsel' : selIs I endSnipConcreteSelector := by
    simpa [endSnipSelectorBytes, endSnipConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endSnipConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some snipTransition :=
    endDispatchSnip hsel
  have hreach := endReachSnipBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_snip_ok (I := I) hsz68
    obtain ⟨_, _, hbodyReach⟩ :=
      endSnipX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have htagCouple : endSnipTagWord σ I = endSnipTagWord σ I := rfl
    by_cases htag : endSnipTagWord σ I = ⟨0⟩
    · have htagSolm : endSnipTagWord σ I = ⟨0⟩ := by
        rw [← htagCouple]
        exact htag
      have hbody :
          ExecTransitionBody config contract evmSolm (endSnipStore I)
            snipTransition.body .reverted := by
        simpa [evmSolm] using
          endSnipBodyReverts_tagZero
            (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hsz68 htagSolm
      exact (endSnipX_tagZero (g := Sat256.ofUInt256 g) hsz68 htag hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have htagNE : endSnipTagWord σ I ≠ ⟨0⟩ := htag
      have htagSolmNE : endSnipTagWord σ I ≠ ⟨0⟩ := by
        intro hbad
        exact htagNE (by rw [htagCouple, hbad])
      obtain ⟨kTag, CTag, htagPcRaw⟩ :=
        endSnipX_tagNonzero (g := Sat256.ofUInt256 g) hsz68 htagNE hbodyReach
      have htagPc :
          RD endBytecode I (Sat256.ofUInt256 g)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1739⟩
            [endSnipIdWord I, endSnipIlkWord I, endSnipReturnPc, endSelWord I]
            (endSnipDogIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty
            σ kTag CTag := by
        simpa [endSnipDogIlksBaseMem] using htagPcRaw
      have hAddressId (a : AccountAddress) : EVM.address a = a := by
        apply Fin.ext
        show ↑a % EVM.twoPow 160 = ↑a
        rw [Nat.mod_eq_of_lt]
        exact a.isLt
      by_cases hdogCode :
          Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) =
            ⟨0⟩
      · have hdogCodeSolm :
            Reasoning.Theory.extCodeSizeWord σ
              (endSnipDogWord σ I) = ⟨0⟩ :=
          hdogCode
        have hbody :
            ExecTransitionBody config contract evmSolm (endSnipStore I)
              snipTransition.body .reverted := by
          simpa [evmSolm] using
            endSnipBodyReverts_dogIlksNoCode
              (σ := σ) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hsz68 htagSolmNE hdogCodeSolm
        exact (endSnipX_dogIlksNoCode (g := Sat256.ofUInt256 g) htagPc hdogCode)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hdogCodeNE :
            Reasoning.Theory.extCodeSizeWord σ (endSnipDogWord σ I) ≠
              ⟨0⟩ := hdogCode
        have hdogCodeSolmNE :
            Reasoning.Theory.extCodeSizeWord σ
              (endSnipDogWord σ I) ≠ ⟨0⟩ :=
          hdogCodeNE
        obtain ⟨dogGasWord, _, _, hcallReady⟩ :=
          endSnipX_dogIlksCallReady
            (g := Sat256.ofUInt256 g) htagPc hdogCodeNE
        by_cases hdepthLt : I.depth.val < 1024
        · obtain ⟨σ_dog, zDog, dogOut, AinDog, callGasDog, _, _, hΘDog,
              rd1820, hdogOutSize⟩ :=
            endSnipX_dogIlksPostCall hcallReady hdepthLt
          rcases hΘDog with ⟨gDog'', ADog, hΘDogEq⟩
          have hdepthNe :
              (initState σ σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth ≠
              1024 := by
            intro hbad
            have hbadI : I.depth = 1024 := by
              simpa [initState] using hbad
            have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
            omega
          have htgtDog :
              EVM.address (endSnipDogAddr σ I) =
              AccountAddress.ofUInt256 (endSnipDogWord σ I) := by
            calc
              EVM.address (endSnipDogAddr σ I)
                  = EVM.address
                      (AccountAddress.ofUInt256 (endSnipDogWord σ I)) := by
                    rw [endSnipDogAddr_eq_ofUInt256]
              _ = AccountAddress.ofUInt256 (endSnipDogWord σ I) :=
                    hAddressId (AccountAddress.ofUInt256 (endSnipDogWord σ I))
          let σ_dog_solm : AccountMap := σ_dog
          let A_dog_solm : Substate := ADog
          have hAccountsDog : σ_dog = σ_dog_solm := rfl
          have hSubstateDog : ADog = A_dog_solm := rfl
          have hcallSolmRaw := callCoincides (cfg := config) (evm := evmSolm)
              (name := "dogIlks")
              (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
              (tgt := EVM.address (endSnipDogAddr σ I))
              (targetWord := endSnipDogWord σ I)
              (σ' := σ_dog) (A' := ADog) (A_in := AinDog)
              (z := zDog) (o := dogOut) (g'' := gDog'')
              (callGas := callGasDog) (mem := endSnipDogIlksCalldataMem I)
              (inOff := endFlowVatIlksOutPtr) (inSize := endFlowVatIlksInSize)
              (callPerm := true) hdepthNe htgtDog
              (endSnipDogIlksEncode_eq I hsz68 (endSnipDogIlksBaseMem_size I))
              (by simpa [evmSolm, initState] using hΘDogEq)
          have hDogAddr : endSnipDogAddr σ I = endSnipDogAddr σ I := rfl
          have hcallSolm :
              typedCallViaEVM config evmSolm
              (EVM.address (endSnipDogAddr σ I)) "dogIlks" 0
              [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
              (zDog,
                { evmSolm with
                  accountMap := σ_dog_solm
                  substate := A_dog_solm
 },
                dogOut) true := by
            simpa [evmSolm, hDogAddr] using hcallSolmRaw
          cases zDog
          · have hbody :
              ExecTransitionBody config contract evmSolm (endSnipStore I)
                snipTransition.body .reverted := by
              simpa [evmSolm] using
                endSnipBodyReverts_dogIlksCallFailed
                  (σ := σ) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                  (evmDog :=
                    { evmSolm with
                      accountMap := σ_dog_solm
                      substate := A_dog_solm
 })
                  (out := dogOut)
                  hwv hsz68 htagSolmNE hdogCodeSolmNE
                  (by simpa [evmSolm] using hcallSolm)
            exact (endSnipX_dogIlksCallFailed rd1820 hdogOutSize)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · let evmDogEvm :=
              { initState σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_dog
              substate := ADog
 }
            let evmDogSolm :=
              { evmSolm with
              accountMap := σ_dog_solm
              substate := A_dog_solm
 }
            have hStateDog : EVMStateEquiv evmDogEvm evmDogSolm := by
              refine ⟨rfl, ?_⟩
              simpa [evmDogEvm, evmDogSolm] using hAccountsDog
            obtain ⟨_, _, rd1841⟩ :=
              endSnipX_dogIlksCallSucceeded (g := Sat256.ofUInt256 g) rd1820
            by_cases hshortDog : dogOut.size < 128
            · have hbody :
                ExecTransitionBody config contract evmSolm (endSnipStore I)
                  snipTransition.body .reverted := by
                simpa [evmDogSolm, evmSolm] using
                  endSnipBodyReverts_dogIlksDecodeShort
                    (σ := σ) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    (evmDog := evmDogSolm) (out := dogOut)
                    hwv hsz68 htagSolmNE hdogCodeSolmNE
                    (by simpa [evmDogSolm, evmSolm] using hcallSolm)
                    hshortDog
              exact (endSnipX_dogIlksReturnDecodeShort rd1841 hshortDog hdogOutSize)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hloDog : 128 ≤ dogOut.size := Nat.le_of_not_gt hshortDog
              obtain ⟨_, _, rd1861⟩ :=
                endSnipX_dogIlksReturnDecodeOk rd1841 hloDog hdogOutSize
              have hprefix :
                ExecBlock config { contract := contract, locals := endSnipStore I }
                  evmSolm
                  (nonpayable ++
                    [ .require
                        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
                    checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0)
                      [.var "ilk"] "dogIlk" ++
                    [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ])
                  (.ok { contract := contract, locals := endSnipStoreClip I dogOut }
                    evmDogSolm) := by
                simpa [evmDogSolm, evmSolm] using
                  endSnipPrefixClipSuccess
                    (σ := σ) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    (evmDog := evmDogSolm) (out := dogOut)
                    hwv hsz68 htagSolmNE hdogCodeSolmNE
                    (by simpa [evmDogSolm, evmSolm] using hcallSolm)
                    hloDog
              by_cases hvatCode :
                  Reasoning.Theory.extCodeSizeWord σ_dog
                    (endPackVatWord σ_dog I) = ⟨0⟩
              · have hvatCodeSolm :
                    Reasoning.Theory.extCodeSizeWord σ_dog_solm
                      (endPackVatWord σ_dog_solm I) = ⟨0⟩ :=
                  (by simpa only [hAccountsDog] using hvatCode)
                have hvatBlock :
                    ExecBlock config
                      { contract := contract, locals := endSnipStoreClip I dogOut }
                      evmDogSolm
                      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk") .reverted := by
                  exact endSnipCheckedVatIlksNoCode
                    (σ := σ_dog_solm) (I := I) (dogOut := dogOut) (evm := evmDogSolm)
                    (by simp [evmDogSolm])
                    (by simp [evmDogSolm, evmSolm, initState])
                    hvatCodeSolm
                have hbody :
                    ExecTransitionBody config contract evmSolm (endSnipStore I)
                      snipTransition.body .reverted := by
                  exact endSnipBodyReverts_afterClipVatIlksBlock hprefix hvatBlock
                exact (endSnipX_vatIlksNoCode rd1861 hloDog hvatCode)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hvatCodeNE :
                    Reasoning.Theory.extCodeSizeWord σ_dog
                      (endPackVatWord σ_dog I) ≠ ⟨0⟩ := hvatCode
                have hvatCodeSolmNE :
                    Reasoning.Theory.extCodeSizeWord σ_dog_solm
                      (endPackVatWord σ_dog_solm I) ≠ ⟨0⟩ :=
                  (by simpa only [hAccountsDog] using hvatCodeNE)
                obtain ⟨gasWordVat, _, _, hvatReady⟩ :=
                  endSnipX_vatIlksCallReady rd1861 hloDog hvatCodeNE
                obtain ⟨σ_vat, zVat, vatOut, AinVat, callGasVat, _, _,
                    hΘVat, rd1946, hvatOutSize⟩ :=
                  endSnipX_vatIlksPostCall hvatReady hdepthLt
                rcases hΘVat with ⟨gVat'', AVat, hΘVatEq⟩
                have htgtVat :
                    EVM.address (endPackVatAddr σ_dog I) =
                      AccountAddress.ofUInt256 (endPackVatWord σ_dog I) := by
                  calc
                    EVM.address (endPackVatAddr σ_dog I)
                        = EVM.address
                            (AccountAddress.ofUInt256 (endPackVatWord σ_dog I)) := by
                          rw [endPackVatAddr_eq_ofUInt256]
                    _ = AccountAddress.ofUInt256 (endPackVatWord σ_dog I) :=
                          hAddressId (AccountAddress.ofUInt256 (endPackVatWord σ_dog I))
                let σ_vat_solm : AccountMap := σ_vat
                let A_vat_solm : Substate := AVat
                have hAccountsVat : σ_vat = σ_vat_solm := rfl
                have hSubstateVat : AVat = A_vat_solm := rfl
                have hcallVatSolmRaw := callCoincides (cfg := config) (evm := evmDogSolm)
                  (name := "vatIlks")
                  (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
                  (tgt := EVM.address (endPackVatAddr σ_dog I))
                  (targetWord := endPackVatWord σ_dog I)
                  (σ' := σ_vat) (A' := AVat) (A_in := AinVat)
                  (z := zVat) (o := vatOut) (g'' := gVat'')
                  (callGas := callGasVat) (mem := endSnipVatIlksCalldataMem I dogOut)
                  (inOff := endFlowVatIlksOutPtr) (inSize := endFlowVatIlksInSize)
                  (callPerm := true)
                  (by simpa [evmDogSolm, evmDogEvm, initState] using hdepthNe)
                  htgtVat (endSnipVatIlksEncode_eq I dogOut hsz68 hloDog)
                  (by simpa [evmDogSolm, evmSolm, initState] using hΘVatEq)
                have hVatAddr : endPackVatAddr σ_dog I = endPackVatAddr σ_dog_solm I := by
                  simp [endPackVatAddr, hAccountsDog]
                have hcallVatSolm :
                    typedCallViaEVM config evmDogSolm
                    (EVM.address (endPackVatAddr σ_dog_solm I)) "vatIlks" 0
                    [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
                    (zVat,
                      { evmDogSolm with
                        accountMap := σ_vat_solm
                        substate := A_vat_solm
 },
                      vatOut) true := by
                  simpa [evmDogSolm, hVatAddr] using hcallVatSolmRaw
                cases zVat
                · have hvatBlock :
                    ExecBlock config
                      { contract := contract, locals := endSnipStoreClip I dogOut }
                      evmDogSolm
                      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk") .reverted := by
                    exact endSnipCheckedVatIlksFailure
                      (σ := σ_dog_solm) (I := I) (dogOut := dogOut) (vatOut := vatOut)
                      (evm := evmDogSolm)
                      (evmVat :=
                        { evmDogSolm with
                          accountMap := σ_vat_solm
                          substate := A_vat_solm
 })
                      (by simp [evmDogSolm])
                      (by simp [evmDogSolm, evmSolm, initState])
                      hvatCodeSolmNE
                      (by simpa [evmDogSolm] using hcallVatSolm)
                  have hbody :
                      ExecTransitionBody config contract evmSolm (endSnipStore I)
                        snipTransition.body .reverted := by
                    exact endSnipBodyReverts_afterClipVatIlksBlock hprefix hvatBlock
                  exact (endSnipX_vatIlksCallFailed rd1946 hvatOutSize)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · let evmVatEvm :=
                    { evmDogEvm with
                    accountMap := σ_vat
                    substate := AVat
 }
                  let evmVatSolm :=
                    { evmDogSolm with
                    accountMap := σ_vat_solm
                    substate := A_vat_solm
 }
                  have hStateVat : EVMStateEquiv evmVatEvm evmVatSolm := by
                    refine ⟨rfl, ?_⟩
                    simpa [evmVatEvm, evmVatSolm] using hAccountsVat
                  obtain ⟨_, _, rd1964⟩ :=
                    endSnipX_vatIlksCallSucceeded (g := Sat256.ofUInt256 g) rd1946
                  by_cases hshortVat : vatOut.size < 160
                  · have hvatBlock :
                      ExecBlock config
                        { contract := contract, locals := endSnipStoreClip I dogOut }
                        evmDogSolm
                        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                          [.var "ilk"] "vatIlk") .reverted := by
                      exact endSnipCheckedVatIlksDecodeRevert
                        (σ := σ_dog_solm) (I := I) (dogOut := dogOut) (vatOut := vatOut)
                        (evm := evmDogSolm) (evmVat := evmVatSolm)
                        (by simp [evmDogSolm])
                        (by simp [evmDogSolm, evmSolm, initState])
                        hvatCodeSolmNE
                        (by simpa [evmVatSolm, evmDogSolm] using hcallVatSolm)
                        hshortVat
                    have hbody :
                        ExecTransitionBody config contract evmSolm (endSnipStore I)
                          snipTransition.body .reverted := by
                      exact endSnipBodyReverts_afterClipVatIlksBlock hprefix hvatBlock
                    exact (endSnipX_vatIlksReturnDecodeShort rd1964 hloDog hshortVat hvatOutSize)
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hloVat : 160 ≤ vatOut.size := Nat.le_of_not_gt hshortVat
                    obtain ⟨_, _, rd1990⟩ :=
                      endSnipX_vatIlksReturnDecodeOk rd1964 hloDog hloVat hvatOutSize
                    have hvatBlock :
                        ExecBlock config
                          { contract := contract, locals := endSnipStoreClip I dogOut }
                          evmDogSolm
                          (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                            [.var "ilk"] "vatIlk")
                          (.ok
                            { contract := contract,
                              locals := endSnipStoreVatIlk I dogOut vatOut }
                            evmVatSolm) := by
                      exact endSnipCheckedVatIlksSuccess
                        (σ := σ_dog_solm) (I := I) (dogOut := dogOut) (vatOut := vatOut)
                        (evm := evmDogSolm) (evmVat := evmVatSolm)
                        (by simp [evmDogSolm])
                        (by simp [evmDogSolm, evmSolm, initState])
                        hvatCodeSolmNE
                        (by simpa [evmVatSolm, evmDogSolm] using hcallVatSolm)
                        hloVat
                    have hprefixRate :
                        ExecBlock config { contract := contract, locals := endSnipStore I }
                          evmSolm
                          (nonpayable ++
                          [ .require
                              (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
                          checkedExternalCallStmts (.storage dogRef) "dogIlks" (.intLit 0)
                            [.var "ilk"] "dogIlk" ++
                          [ .letDecl "clip" (some addr) (.tupleGet (.var "dogIlk") 0) ] ++
                          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                            [.var "ilk"] "vatIlk" ++
                          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
                        (.ok
                          { contract := contract,
                              locals := endSnipStoreRate I dogOut vatOut }
                            evmVatSolm) := by
                      exact endSnipPrefixRateSuccess hprefix hvatBlock
                    by_cases hsalesCode :
                        Reasoning.Theory.extCodeSizeWord σ_vat
                          (endSnipSalesClipWord dogOut) = ⟨0⟩
                    · have hsalesCodeSolm :
                          Reasoning.Theory.extCodeSizeWord σ_vat_solm
                            (endSnipSalesClipWord dogOut) = ⟨0⟩ := by
                        simpa only [hAccountsVat] using hsalesCode
                      have hsalesBlock :
                          ExecBlock config
                            { contract := contract,
                              locals := endSnipStoreRate I dogOut vatOut }
                            evmVatSolm
                            (checkedExternalCallStmts (.var "clip") "sales"
                              (.intLit 0) [.var "id"] "clipSale" (perm := false))
                            .reverted := by
                        exact endSnipCheckedSalesNoCode
                          (σ := σ_vat_solm) (I := I) (dogOut := dogOut)
                          (vatOut := vatOut) (evm := evmVatSolm)
                          (by rfl)
                          hsalesCodeSolm
                      have hbody :
                          ExecTransitionBody config contract evmSolm (endSnipStore I)
                            snipTransition.body .reverted := by
                        exact endSnipBodyReverts_afterRateSalesBlock
                          hprefixRate hsalesBlock
                      exact (endSnipX_salesNoCode rd1990 hloDog hloVat hsalesCode)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hsalesCodeNE :
                          Reasoning.Theory.extCodeSizeWord σ_vat
                            (endSnipSalesClipWord dogOut) ≠ ⟨0⟩ := hsalesCode
                      have hsalesCodeSolmNE :
                          Reasoning.Theory.extCodeSizeWord σ_vat_solm
                            (endSnipSalesClipWord dogOut) ≠ ⟨0⟩ := by
                        simpa only [hAccountsVat] using hsalesCodeNE
                      obtain ⟨gasWordSales, _, _, hsalesReady⟩ :=
                        endSnipX_salesCallReady rd1990 hloDog hloVat hsalesCodeNE
                      obtain ⟨σ_sales, zSales, saleOut, AinSales,
                          callGasSales, _, _, hΘSales, rd2074, hsaleOutSize⟩ :=
                        endSnipX_salesPostStaticcall hsalesReady hdepthLt
                      rcases hΘSales with ⟨gSales'', ASales, hΘSalesEq⟩
                      have htgtSales :
                          EVM.address (endSnipDogIlkClipAddr dogOut) =
                            AccountAddress.ofUInt256 (endSnipSalesClipWord dogOut) := by
                        calc
                          EVM.address (endSnipDogIlkClipAddr dogOut)
                              = EVM.address
                                  (AccountAddress.ofUInt256
                                    (endSnipSalesClipWord dogOut)) := by
                                rw [endSnipSalesClipAddr_eq_ofUInt256]
                          _ = AccountAddress.ofUInt256 (endSnipSalesClipWord dogOut) :=
                                hAddressId
                                  (AccountAddress.ofUInt256
                                    (endSnipSalesClipWord dogOut))
                      let σ_sales_solm : AccountMap := σ_sales
                      let A_sales_solm : Substate := ASales
                      have hAccountsSales : σ_sales = σ_sales_solm := rfl
                      have hSubstateSales : ASales = A_sales_solm := rfl
                      have hcallSalesSolmRaw := callCoincides (cfg := config) (evm := evmVatSolm)
                        (name := "sales")
                        (args := [.int (Int.ofNat (endSnipIdWord I).toNat)])
                        (tgt := EVM.address (endSnipDogIlkClipAddr dogOut))
                        (targetWord := endSnipSalesClipWord dogOut)
                        (σ' := σ_sales) (A' := ASales) (A_in := AinSales)
                        (z := zSales) (o := saleOut) (g'' := gSales'')
                        (callGas := callGasSales)
                        (mem := endSnipSalesCalldataMem I dogOut vatOut)
                        (inOff := endFlowVatIlksOutPtr) (inSize := endFlowVatIlksInSize)
                        (callPerm := false)
                        (by simpa [evmVatSolm, evmVatEvm, evmDogEvm, initState] using hdepthNe)
                        htgtSales (endSnipSalesEncode_eq I dogOut vatOut hloDog hloVat)
                        (by simpa [evmVatSolm, evmVatEvm, evmDogEvm, initState] using hΘSalesEq)
                      let evmSalesSolm :=
                        { evmVatSolm with
                          accountMap := σ_sales_solm
                          substate := A_sales_solm
 }
                      have hcallSalesSolm :
                          typedCallViaEVM config evmVatSolm
                          (EVM.address (endSnipDogIlkClipAddr dogOut)) "sales" 0
                          [.int (Int.ofNat (endSnipIdWord I).toNat)]
                          (zSales, evmSalesSolm, saleOut) false := by
                        change typedCallViaEVM config evmVatSolm
                          (EVM.address (endSnipDogIlkClipAddr dogOut)) "sales" 0
                          [.int (Int.ofNat (endSnipIdWord I).toNat)]
                          (zSales,
                            { evmVatSolm with
                              accountMap := σ_sales_solm
                              substate := A_sales_solm
 },
                            saleOut) false
                        exact hcallSalesSolmRaw
                      cases zSales
                      · have rd2074Failed := by
                          simpa only [if_false] using rd2074
                        have hsalesBlock :
                            ExecBlock config
                              { contract := contract,
                                locals := endSnipStoreRate I dogOut vatOut }
                              evmVatSolm
                              (checkedExternalCallStmts (.var "clip") "sales"
                                (.intLit 0) [.var "id"] "clipSale" (perm := false))
                              .reverted := by
                          exact endSnipCheckedSalesFailure
                            (σ := σ_vat_solm) (I := I) (dogOut := dogOut)
                            (vatOut := vatOut) (saleOut := saleOut)
                            (evm := evmVatSolm)
                            (evmSales := evmSalesSolm)
                            (by rfl)
                            hsalesCodeSolmNE
                            hcallSalesSolm
                        have hbody :
                            ExecTransitionBody config contract evmSolm (endSnipStore I)
                              snipTransition.body .reverted := by
                          exact endSnipBodyReverts_afterRateSalesBlock
                            hprefixRate hsalesBlock
                        exact (endSnipX_salesCallFailed rd2074Failed hsaleOutSize)
                          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · let evmSalesEvm :=
                          { evmVatEvm with
                          accountMap := σ_sales
                          substate := ASales
 }
                        have hStateSales : EVMStateEquiv evmSalesEvm evmSalesSolm := by
                          refine ⟨rfl, ?_⟩
                          simpa [evmSalesEvm, evmSalesSolm] using hAccountsSales
                        have rd2074Success := by
                          simpa only [if_true] using rd2074
                        obtain ⟨_, _, rd2095⟩ :=
                          endSnipX_salesCallSucceeded
                            (g := Sat256.ofUInt256 g) rd2074Success
                        by_cases hshortSale : saleOut.size < 192
                        · have hsalesBlock :
                              ExecBlock config
                                { contract := contract,
                                  locals := endSnipStoreRate I dogOut vatOut }
                                evmVatSolm
                                (checkedExternalCallStmts (.var "clip") "sales"
                                  (.intLit 0) [.var "id"] "clipSale" (perm := false))
                                .reverted := by
                            exact endSnipCheckedSalesDecodeRevert
                              (σ := σ_vat_solm) (I := I) (dogOut := dogOut)
                              (vatOut := vatOut) (saleOut := saleOut)
                              (evm := evmVatSolm) (evmSales := evmSalesSolm)
                              (by rfl)
                              hsalesCodeSolmNE
                              hcallSalesSolm
                              hshortSale
                          have hbody :
                              ExecTransitionBody config contract evmSolm
                                (endSnipStore I) snipTransition.body .reverted := by
                            exact endSnipBodyReverts_afterRateSalesBlock
                              hprefixRate hsalesBlock
                          exact (endSnipX_salesReturnDecodeShort rd2095 hloDog hloVat
                              hshortSale hsaleOutSize)
                            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · have hloSale : 192 ≤ saleOut.size := Nat.le_of_not_gt hshortSale
                          have hsalesBlock :
                              ExecBlock config
                                { contract := contract,
                                  locals := endSnipStoreRate I dogOut vatOut }
                                evmVatSolm
                                (checkedExternalCallStmts (.var "clip") "sales"
                                  (.intLit 0) [.var "id"] "clipSale" (perm := false))
                                (.ok
                                  { contract := contract,
                                    locals :=
                                      endSnipStoreClipSale I dogOut vatOut saleOut }
                                  evmSalesSolm) := by
                            exact endSnipCheckedSalesSuccess
                              (σ := σ_vat_solm) (I := I) (dogOut := dogOut)
                              (vatOut := vatOut) (saleOut := saleOut)
                              (evm := evmVatSolm) (evmSales := evmSalesSolm)
                              (by rfl)
                              hsalesCodeSolmNE
                              hcallSalesSolm
                              hloSale
                          have hprefixUsr :=
                            endSnipPrefixUsrSuccess hprefixRate hsalesBlock
                          obtain ⟨_, _, rd2131⟩ :=
                            endSnipX_salesReturnDecodeOk rd2095 hloDog hloVat hloSale
                              hsaleOutSize
                          have hmapSalesSolm : evmSalesSolm.accountMap = σ_sales_solm := by
                            rfl
                          have hownerSalesSolm :
                              evmSalesSolm.executionEnv.codeOwner = I.codeOwner := by
                            rfl
                          by_cases hsuckCode :
                              Reasoning.Theory.extCodeSizeWord σ_sales
                                (endPackVatWord σ_sales I) = ⟨0⟩
                          · have hsuckCodeSolm :
                                Reasoning.Theory.extCodeSizeWord σ_sales_solm
                                  (endPackVatWord σ_sales_solm I) = ⟨0⟩ :=
                              (by simpa only [hAccountsSales] using hsuckCode)
                            have hsuckBlock :=
                              endSnipCheckedSuckNoCode
                                (σ := σ_sales_solm) (I := I) (dogOut := dogOut)
                                (vatOut := vatOut) (saleOut := saleOut)
                                (evm := evmSalesSolm) hmapSalesSolm hownerSalesSolm
                                hsuckCodeSolm
                            have htail := endSnipTailReverts_suck hsuckBlock
                            have hbody :
                                ExecTransitionBody config contract evmSolm
                                  (endSnipStore I) snipTransition.body .reverted := by
                              exact endSnipBodyReverts_afterUsrTailReverted
                                hprefixUsr htail
                            exact
                              (endSnipX_suckNoCode
                                (g := Sat256.ofUInt256 g) hloDog hloVat hloSale
                                rd2131 hsuckCode)
                                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                          · have hsuckCodeNE :
                                Reasoning.Theory.extCodeSizeWord σ_sales
                                  (endPackVatWord σ_sales I) ≠ ⟨0⟩ := hsuckCode
                            have hsuckCodeSolmNE :
                                Reasoning.Theory.extCodeSizeWord σ_sales_solm
                                  (endPackVatWord σ_sales_solm I) ≠ ⟨0⟩ :=
                              (by simpa only [hAccountsSales] using hsuckCodeNE)
                            obtain ⟨suckGasWord, _, _, rdSuckReady⟩ :=
                              endSnipX_suckCallReady
                                (g := Sat256.ofUInt256 g) hloDog hloVat hloSale
                                rd2131 hsuckCodeNE
                            obtain ⟨σ_suck, zSuck, suckOut, AinSuck,
                                callGasSuck, _, _, hΘSuck, rd2236, hsuckOutSize⟩ :=
                              endSnipX_suckPostCall rdSuckReady hdepthLt
                            rcases hΘSuck with ⟨gSuck'', ASuck, hΘSuckEq⟩
                            have hdepthNeSuck :
                                evmSalesEvm.executionEnv.depth ≠ 1024 := by
                              intro hbad
                              have hbadI : I.depth = 1024 := by
                                simpa [evmSalesEvm, evmVatEvm, evmDogEvm, initState]
                                  using hbad
                              have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
                              omega
                            have htgtSuck :
                                EVM.address (endPackVatAddr σ_sales I) =
                                  AccountAddress.ofUInt256 (endPackVatWord σ_sales I) := by
                              calc
                                EVM.address (endPackVatAddr σ_sales I)
                                    = EVM.address
                                        (AccountAddress.ofUInt256
                                          (endPackVatWord σ_sales I)) := by
                                      rw [endPackVatAddr_eq_ofUInt256]
                                _ = AccountAddress.ofUInt256 (endPackVatWord σ_sales I) :=
                                      hAddressId
                                        (AccountAddress.ofUInt256 (endPackVatWord σ_sales I))
                            let σ_suck_solm : AccountMap := σ_suck
                            let A_suck_solm : Substate := ASuck
                            have hAccountsSuck : σ_suck = σ_suck_solm := rfl
                            have hSubstateSuck : ASuck = A_suck_solm := rfl
                            have hcallSuckSolmRaw := callCoincides (cfg := config) (evm := evmSalesSolm)
                              (name := "suck")
                              (args :=
                                [.address (endPackVowAddr σ_sales I),
                                  .address (endPackVowAddr σ_sales I),
                                  .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)])
                              (tgt := EVM.address (endPackVatAddr σ_sales I))
                              (targetWord := endPackVatWord σ_sales I)
                              (σ' := σ_suck) (A' := ASuck) (A_in := AinSuck)
                              (z := zSuck) (o := suckOut) (g'' := gSuck'')
                              (callGas := callGasSuck)
                              (mem := endSnipSuckCalldataMem σ_sales I dogOut vatOut saleOut)
                              (inOff := endSnipSuckOutPtr) (inSize := endSnipSuckInSize)
                              (callPerm := true) hdepthNeSuck htgtSuck
                              (endSnipSuckEncode_eq σ_sales I dogOut vatOut saleOut
                                hloDog hloVat hloSale)
                              (by simpa [evmSalesSolm, evmVatSolm, evmDogSolm,
                                evmSolm, initState] using hΘSuckEq)
                            have hVatWordSuck :
                                endPackVatWord σ_sales I =
                                  endPackVatWord σ_sales_solm I :=
                              congrArg (fun m => endPackVatWord m I) hAccountsSales
                            have hVatAddrSuck :
                                endPackVatAddr σ_sales I =
                                  endPackVatAddr σ_sales_solm I := by
                              simp [endPackVatAddr, hVatWordSuck]
                            have hVowWordSuck :
                                endPackVowWord σ_sales I =
                                  endPackVowWord σ_sales_solm I :=
                              (congrArg (fun m => endPackVowWord m I) hAccountsSales)
                            have hVowAddrSuck :
                                endPackVowAddr σ_sales I =
                                  endPackVowAddr σ_sales_solm I := by
                              simp [endPackVowAddr, hVowWordSuck]
                            let evmSuckSolm :=
                              { evmSalesSolm with
                                accountMap := σ_suck_solm
                                substate := A_suck_solm
 }
                            have hcallSuckSolm :
                                typedCallViaEVM config evmSalesSolm
                                  (EVM.address (endPackVatAddr σ_sales_solm I)) "suck" 0
                                  [.address (endPackVowAddr σ_sales_solm I),
                                    .address (endPackVowAddr σ_sales_solm I),
                                    .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)]
                                  (zSuck, evmSuckSolm, suckOut) true := by
                              change typedCallViaEVM config evmSalesSolm
                                (EVM.address (endPackVatAddr σ_sales_solm I)) "suck" 0
                                [.address (endPackVowAddr σ_sales_solm I),
                                  .address (endPackVowAddr σ_sales_solm I),
                                  .int (Int.ofNat (endSnipSaleTabWord saleOut).toNat)]
                                (zSuck,
                                  { evmSalesSolm with
                                    accountMap := σ_suck_solm
                                    substate := A_suck_solm
 },
                                  suckOut) true
                              rw [← hVatAddrSuck, ← hVowAddrSuck]
                              exact hcallSuckSolmRaw
                            cases zSuck
                            · have hsuckBlock :=
                                endSnipCheckedSuckFailure
                                  (σ := σ_sales_solm) (I := I) (dogOut := dogOut)
                                  (vatOut := vatOut) (saleOut := saleOut)
                                  (suckOut := suckOut) (evm := evmSalesSolm)
                                  (evmSuck := evmSuckSolm)
                                  hmapSalesSolm hownerSalesSolm hsuckCodeSolmNE
                                  hcallSuckSolm
                              have htail := endSnipTailReverts_suck hsuckBlock
                              have hbody :
                                  ExecTransitionBody config contract evmSolm
                                    (endSnipStore I) snipTransition.body .reverted := by
                                exact endSnipBodyReverts_afterUsrTailReverted
                                  hprefixUsr htail
                              have rd2236Fail := by
                                simpa only [if_false] using rd2236
                              exact (endSnipX_suckCallFailed rd2236Fail hsuckOutSize)
                                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                            · let evmSuckEvm :=
                                { evmSalesEvm with
                                  accountMap := σ_suck
                                  substate := ASuck
 }
                              have hStateSuck : EVMStateEquiv evmSuckEvm evmSuckSolm := by
                                refine ⟨rfl, ?_⟩
                                simpa [evmSuckEvm, evmSuckSolm] using hAccountsSuck
                              have hmapSuckSolm :
                                  evmSuckSolm.accountMap = σ_suck_solm := by
                                rfl
                              have hownerSuckSolm :
                                  evmSuckSolm.executionEnv.codeOwner = I.codeOwner := by
                                rfl
                              have hsuckBlock :=
                                endSnipCheckedSuckSuccess
                                  (σ := σ_sales_solm) (I := I) (dogOut := dogOut)
                                  (vatOut := vatOut) (saleOut := saleOut)
                                  (suckOut := suckOut) (evm := evmSalesSolm)
                                  (evmSuck := evmSuckSolm)
                                  hmapSalesSolm hownerSalesSolm hsuckCodeSolmNE
                                  hcallSuckSolm
                              have rd2236Succ := by
                                simpa only [if_true] using rd2236
                              obtain ⟨_, _, rd2257⟩ :=
                                endSnipX_suckCallSucceeded rd2236Succ
                              by_cases hyankCode :
                                  Reasoning.Theory.extCodeSizeWord σ_suck
                                    (endSnipSalesClipWord dogOut) = ⟨0⟩
                              · have hyankCodeSolm :
                                    Reasoning.Theory.extCodeSizeWord σ_suck_solm
                                    (endSnipSalesClipWord dogOut) = ⟨0⟩ := by
                                  simpa only [hAccountsSuck] using hyankCode
                                have hyankBlock :=
                                  endSnipCheckedYankNoCode
                                    (σ := σ_suck_solm) (I := I) (dogOut := dogOut)
                                    (vatOut := vatOut) (saleOut := saleOut)
                                    (evm := evmSuckSolm) hmapSuckSolm hyankCodeSolm
                                have htail := endSnipTailReverts_yank hsuckBlock hyankBlock
                                have hbody :
                                    ExecTransitionBody config contract evmSolm
                                      (endSnipStore I) snipTransition.body .reverted := by
                                  exact endSnipBodyReverts_afterUsrTailReverted
                                    hprefixUsr htail
                                exact
                                  (endSnipX_yankNoCode
                                    (g := Sat256.ofUInt256 g) (σmem := σ_sales)
                                    (σpost := σ_suck) hloDog hloVat hloSale rd2257
                                    hyankCode)
                                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                              · have hyankCodeNE :
                                    Reasoning.Theory.extCodeSizeWord σ_suck
                                      (endSnipSalesClipWord dogOut) ≠ ⟨0⟩ := hyankCode
                                have hyankCodeSolmNE :
                                    Reasoning.Theory.extCodeSizeWord σ_suck_solm
                                    (endSnipSalesClipWord dogOut) ≠ ⟨0⟩ := by
                                  simpa only [hAccountsSuck] using hyankCodeNE
                                obtain ⟨yankGasWord, _, _, rdYankReady⟩ :=
                                  endSnipX_yankCallReady
                                    (g := Sat256.ofUInt256 g) (σmem := σ_sales)
                                    (σpost := σ_suck) hloDog hloVat hloSale rd2257
                                    hyankCodeNE
                                obtain ⟨σ_yank, zYank, yankOut, AinYank,
                                    callGasYank, _, _, hΘYank, rd2330, hyankOutSize⟩ :=
                                  endSnipX_yankPostCall
                                    (σmem := σ_sales) (σpost := σ_suck)
                                    rdYankReady hdepthLt
                                rcases hΘYank with ⟨gYank'', AYank, hΘYankEq⟩
                                have hdepthNeYank :
                                    evmSuckEvm.executionEnv.depth ≠ 1024 := by
                                  intro hbad
                                  have hbadI : I.depth = 1024 := by
                                    simpa [evmSuckEvm, evmSalesEvm, evmVatEvm,
                                      evmDogEvm, initState] using hbad
                                  have hbadVal : I.depth.val = 1024 :=
                                    congrArg Fin.val hbadI
                                  omega
                                let σ_yank_solm : AccountMap := σ_yank
                                let A_yank_solm : Substate := AYank
                                have hAccountsYank : σ_yank = σ_yank_solm := rfl
                                have hSubstateYank : AYank = A_yank_solm := rfl
                                have hcallYankSolmRaw := callCoincides (cfg := config) (evm := evmSuckSolm)
                                  (name := "yank")
                                  (args := [.int (Int.ofNat (endSnipIdWord I).toNat)])
                                  (tgt := EVM.address (endSnipDogIlkClipAddr dogOut))
                                  (targetWord := endSnipSalesClipWord dogOut)
                                  (σ' := σ_yank) (A' := AYank) (A_in := AinYank)
                                  (z := zYank) (o := yankOut) (g'' := gYank'')
                                  (callGas := callGasYank)
                                  (mem := endSnipYankCalldataMem σ_sales I dogOut vatOut saleOut)
                                  (inOff := endSnipYankOutPtr) (inSize := endSnipYankInSize)
                                  (callPerm := true) hdepthNeYank htgtSales
                                  (endSnipYankEncode_eq σ_sales I dogOut vatOut saleOut
                                    hloDog hloVat hloSale)
                                  (by simpa [evmSuckSolm, evmSalesSolm, evmVatSolm,
                                    evmDogSolm, evmSolm, initState] using hΘYankEq)
                                let evmYankSolm :=
                                  { evmSuckSolm with
                                    accountMap := σ_yank_solm
                                    substate := A_yank_solm
 }
                                have hcallYankSolm :
                                    typedCallViaEVM config evmSuckSolm
                                      (EVM.address (endSnipDogIlkClipAddr dogOut))
                                      "yank" 0
                                      [.int (Int.ofNat (endSnipIdWord I).toNat)]
                                      (zYank, evmYankSolm, yankOut) true := by
                                  change typedCallViaEVM config evmSuckSolm
                                    (EVM.address (endSnipDogIlkClipAddr dogOut)) "yank" 0
                                    [.int (Int.ofNat (endSnipIdWord I).toNat)]
                                    (zYank,
                                      { evmSuckSolm with
                                        accountMap := σ_yank_solm
                                        substate := A_yank_solm
 },
                                      yankOut) true
                                  exact hcallYankSolmRaw
                                cases zYank
                                · have hyankBlock :=
                                    endSnipCheckedYankFailure
                                      (σ := σ_suck_solm) (I := I) (dogOut := dogOut)
                                      (vatOut := vatOut) (saleOut := saleOut)
                                      (yankOut := yankOut) (evm := evmSuckSolm)
                                      (evmYank := evmYankSolm)
                                      hmapSuckSolm hyankCodeSolmNE
                                      hcallYankSolm
                                  have htail :=
                                    endSnipTailReverts_yank hsuckBlock hyankBlock
                                  have hbody :
                                      ExecTransitionBody config contract evmSolm
                                        (endSnipStore I) snipTransition.body .reverted := by
                                    exact endSnipBodyReverts_afterUsrTailReverted
                                      hprefixUsr htail
                                  have rd2330Fail := by
                                    simpa only [if_false] using rd2330
                                  exact
                                    (endSnipX_yankCallFailed
                                      (σpost := σ_yank) rd2330Fail hyankOutSize)
                                      |>.reEquivExecutionRevert hcode hdispatch hdecode
                                        hbody
                                · let evmYankEvm :=
                                    { evmSuckEvm with
                                      accountMap := σ_yank
                                      substate := AYank
 }
                                  have hyankBlock :=
                                    endSnipCheckedYankSuccess
                                      (σ := σ_suck_solm) (I := I) (dogOut := dogOut)
                                      (vatOut := vatOut) (saleOut := saleOut)
                                      (yankOut := yankOut) (evm := evmSuckSolm)
                                      (evmYank := evmYankSolm)
                                      hmapSuckSolm hyankCodeSolmNE
                                      hcallYankSolm
                                  have rd2330Succ := by
                                    simpa only [if_true] using rd2330
                                  obtain ⟨_, _, rd2351⟩ :=
                                    endSnipX_yankCallSucceeded
                                      (σpost := σ_yank) rd2330Succ
                                  have hArtCoupleYank :
                                      endSnipArtOldWord σ_yank I =
                                        endSnipArtOldWord σ_yank_solm I := by
                                    exact congrArg (fun m => endSnipArtOldWord m I) hAccountsYank
                                  have hArtLoadSolm :
                                      Solm.EVM.storageLoad evmYankSolm
                                        evmYankSolm.executionEnv.codeOwner
                                        (endSnipArtSlot I) =
                                          endSnipArtOldWord σ_yank_solm I := by
                                    simp [evmYankSolm, Solm.EVM.storageLoad,
                                      State.lookupAccount, evmSuckSolm, evmSalesSolm,
                                      evmVatSolm, evmDogSolm, evmSolm, initState,
                                      endSnipArtOldWord, solcSlotWordAt, solcSlotWord,
                                      Account.lookupStorage]
                                  by_cases hrate :
                                      endFlowVatIlkRateWord vatOut = ⟨0⟩
                                  · have htail :=
                                      endSnipTailReverts_artDivZero hrate hsuckBlock
                                        hyankBlock
                                    have hbody :
                                        ExecTransitionBody config contract evmSolm
                                          (endSnipStore I) snipTransition.body
                                          .reverted := by
                                      exact endSnipBodyReverts_afterUsrTailReverted
                                        hprefixUsr htail
                                    have hinvalidOr :=
                                      endSnipX_artDivZeroInvalid
                                        (g := Sat256.ofUInt256 g) (σmem := σ_sales)
                                        (σpost := σ_yank) hrate rd2351
                                    rcases hinvalidOr with hoog | hinvalid
                                    · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
                                        rw [← hcode] at hoog
                                        simpa [initState, Sat256.ofUInt256] using hoog))
                                    · have hxi :
                                          Ξ σ σ₀ g A I =
                                            .error .InvalidInstruction :=
                                        Xi_error_of_X (g := g) (by
                                          rw [← hcode] at hinvalid
                                          simpa [initState, Sat256.ofUInt256] using
                                            hinvalid)
                                      exact reEquiv_execution hdispatch hdecode hbody
                                        (execResultsEquiv.invalidHalt hxi rfl)
                                  · have hrateNE :
                                      endFlowVatIlkRateWord vatOut ≠ ⟨0⟩ := hrate
                                    obtain ⟨_, _, rd10092⟩ :=
                                      endSnipX_artAddEntry
                                        (g := Sat256.ofUInt256 g) (σmem := σ_sales)
                                        (σpost := σ_yank) hsz68 hloDog hloVat hloSale
                                        hrateNE rd2351
                                    by_cases hover :
                                        UInt256.size ≤
                                          (endSnipArtOldWord σ_yank I).toNat +
                                            (endSnipArtWord vatOut saleOut).toNat
                                    · have hoverSolm :
                                          UInt256.size ≤
                                            (endSnipArtOldWord σ_yank_solm I).toNat +
                                              (endSnipArtWord vatOut saleOut).toNat := by
                                        simpa [← hArtCoupleYank] using hover
                                      have htail :=
                                        endSnipTailReverts_artAddOverflow
                                          hsz68 hArtLoadSolm hrateNE hoverSolm
                                          hsuckBlock hyankBlock
                                      have hbody :
                                          ExecTransitionBody config contract evmSolm
                                            (endSnipStore I) snipTransition.body
                                            .reverted := by
                                        exact endSnipBodyReverts_afterUsrTailReverted
                                          hprefixUsr htail
                                      exact
                                        (endSnipX_artAddOverflow
                                          (g := Sat256.ofUInt256 g) (σmem := σ_sales)
                                          (σpost := σ_yank) hover rd10092)
                                          |>.reEquivExecutionRevert hcode hdispatch
                                            hdecode hbody
                                    · have hfit :
                                          (endSnipArtOldWord σ_yank I).toNat +
                                            (endSnipArtWord vatOut saleOut).toNat <
                                              UInt256.size :=
                                        Nat.lt_of_not_ge hover
                                      have hfitSolm :
                                          (endSnipArtOldWord σ_yank_solm I).toNat +
                                            (endSnipArtWord vatOut saleOut).toNat <
                                              UInt256.size := by
                                        simpa [← hArtCoupleYank] using hfit
                                      obtain ⟨_, _, rd2391⟩ :=
                                        endSnipX_artAddReturns
                                          (g := Sat256.ofUInt256 g) (σmem := σ_sales)
                                          (σpost := σ_yank) hfit rd10092
                                      by_cases hperm : I.perm = true
                                      swap
                                      · have hp : I.perm = false := by simpa using hperm
                                        have hstatic := permSplit_false hp
                                          (endSnipX_artStoreAtHashSplit hsz68 hloDog hloVat
                                            hloSale rd2391)
                                        have htail := (endSnipTailAfterUsrReturnsSplit hsz68
                                          hArtLoadSolm hrateNE hfitSolm hsuckBlock hyankBlock).2
                                          (by simpa [evmYankSolm, evmSuckSolm, evmSalesSolm,
                                            evmVatSolm, evmDogSolm,
                                            evmSolm, initState] using hp)
                                        have hbody := ExecFuncBody.execBlockStatic
                                          (endSnipBodyBlock_afterUsrTailTerm hprefixUsr htail
                                            (by intro _ _ h; cases h))
                                        exact hstatic.reEquivStaticHalt hcode hdispatch hdecode
                                          hbody
                                      let int256Bound : Nat :=
                                        57896044618658097711785492504343953926634992332820282019728792003956564819968
                                      have hint256Bound : int256Bound = 2 ^ 255 := by
                                        native_decide
                                      by_cases hlotBound :
                                          (endSnipSaleLotWord saleOut).toNat < int256Bound
                                      · have hlot :
                                            (endSnipSaleLotWord saleOut).toNat < 2 ^ 255 := by
                                          simpa [hint256Bound] using hlotBound
                                        by_cases hartBound :
                                            (endSnipArtWord vatOut saleOut).toNat <
                                              int256Bound
                                        · have hart :
                                              (endSnipArtWord vatOut saleOut).toNat <
                                                2 ^ 255 := by
                                            simpa [hint256Bound] using hartBound
                                          obtain ⟨_, _, rd2489⟩ :=
                                            endSnipX_artStoreIntGuardOk
                                              (g := Sat256.ofUInt256 g)
                                              (σmem := σ_sales) (σpost := σ_yank)
                                              hperm hsz68 hloDog hloVat hloSale hlot
                                              hart rd2391
                                          have htailOk :=
                                            endSnipTailAfterUsrReturns hsz68
                                              hArtLoadSolm hrateNE hfitSolm hlot hart
                                              hsuckBlock hyankBlock
                                          let σ_post :=
                                            endSnipPostArtAccountMap σ_yank I
                                              (endSnipArtNewWord σ_yank I vatOut saleOut)
                                          let σ_post_solm :=
                                            endSnipPostArtAccountMap σ_yank_solm I
                                              (endSnipArtNewWord σ_yank_solm I vatOut
                                                saleOut)
                                          let evmPostEvm :=
                                            endSnipPostArtState evmYankEvm I
                                              (endSnipArtNewWord σ_yank I vatOut saleOut)
                                          let evmPostSolm :=
                                            endSnipPostArtState evmYankSolm I
                                              (endSnipArtNewWord σ_yank_solm I vatOut
                                                saleOut)
                                          have hStateYank :
                                              EVMStateEquiv evmYankEvm evmYankSolm := by
                                            refine ⟨?_, ?_⟩
                                            · simpa [evmYankEvm, evmYankSolm] using
                                                hStateSuck.executionEnv
                                            · simpa [evmYankEvm, evmYankSolm] using
                                                hAccountsYank
                                          have hArtNewCouple :
                                              endSnipArtNewWord σ_yank I vatOut saleOut =
                                                endSnipArtNewWord σ_yank_solm I vatOut
                                                  saleOut := by
                                            simp [endSnipArtNewWord, hArtCoupleYank]
                                          have hStatePost :
                                              EVMStateEquiv evmPostEvm evmPostSolm := by
                                            simpa [evmPostEvm, evmPostSolm,
                                              endSnipPostArtState] using
                                              hStateYank.storageStore_codeOwner
                                                (endSnipArtSlot I) hArtNewCouple
                                          have hAccountsPost :
                                              Eq σ_post σ_post_solm := by
                                            simpa [evmPostEvm, evmPostSolm, σ_post,
                                              σ_post_solm, endSnipPostArtState,
                                              endSnipPostArtAccountMap,
                                              storageStore_accountMap] using
                                              hStatePost.accountMap
                                          have hmapPostSolm : evmPostSolm.accountMap = σ_post_solm := by
                                            calc
                                              evmPostSolm.accountMap = evmPostEvm.accountMap :=
                                                hStatePost.accountMap.symm
                                              _ = σ_post := by
                                                simp [evmPostEvm, endSnipPostArtState,
                                                  endSnipPostArtAccountMap, σ_post,
                                                  evmYankEvm, evmSuckEvm, evmSalesEvm,
                                                  evmVatEvm, evmDogEvm, evmSolm, initState,
                                                  storageStore_accountMap]
                                              _ = σ_post_solm := hAccountsPost
                                          have hownerPostSolm : evmPostSolm.executionEnv.codeOwner = I.codeOwner := by
                                            calc
                                              evmPostSolm.executionEnv.codeOwner =
                                                  evmPostEvm.executionEnv.codeOwner := by
                                                rw [← hStatePost.executionEnv]
                                              _ = I.codeOwner := by
                                                simp [evmPostEvm, endSnipPostArtState,
                                                  evmYankEvm, evmSuckEvm, evmSalesEvm,
                                                  evmVatEvm, evmDogEvm, evmSolm, initState,
                                                  storageStore_executionEnv]
                                          have hgrabCode :
                                              Reasoning.Theory.extCodeSizeWord σ_post
                                                (endPackVatWord σ_post I) = ⟨0⟩ ∨
                                              Reasoning.Theory.extCodeSizeWord σ_post
                                                (endPackVatWord σ_post I) ≠ ⟨0⟩ :=
                                            eq_or_ne _ _
                                          cases hgrabCode with
                                          | inl hgrabCodeZero =>
                                            have hgrabCodeSolm :
                                                Reasoning.Theory.extCodeSizeWord σ_post_solm
                                                  (endPackVatWord σ_post_solm I) = ⟨0⟩ := by
                                              simpa only [hAccountsPost] using hgrabCodeZero
                                            have htail := endSnipGrabTailReverts_noCodeFor
                                              (σCall := σ_post_solm) (σLoc := σ_yank_solm)
                                              (I := I) (dogOut := dogOut) (vatOut := vatOut)
                                              (saleOut := saleOut) (evm := evmPostSolm)
                                              hmapPostSolm hownerPostSolm hgrabCodeSolm
                                            have hbody :
                                              ExecTransitionBody config contract evmSolm
                                                  (endSnipStore I) snipTransition.body
                                                  .reverted := by
                                              exact
                                                endSnipBodyReverts_afterUsrTailGrabReverted
                                                  (I := I) (σLoc := σ_yank_solm)
                                                  (dogOut := dogOut) (vatOut := vatOut)
                                                  (saleOut := saleOut) (evm0 := evmSolm)
                                                  (evmUsr := evmSalesSolm)
                                                  (evmPost := evmPostSolm)
                                                  hprefixUsr htailOk htail
                                            exact (endSnipX_grabNoCode hloDog hloVat hloSale
                                              rd2489 hgrabCodeZero).reEquivExecutionRevert
                                                hcode hdispatch hdecode hbody
                                          | inr hgrabCodeNE =>
                                            have hgrabCodeSolmNE :
                                                Reasoning.Theory.extCodeSizeWord σ_post_solm
                                                  (endPackVatWord σ_post_solm I) ≠ ⟨0⟩ := by
                                              simpa only [hAccountsPost] using hgrabCodeNE
                                            obtain ⟨gasWordGrab, _, _, rd2606⟩ :=
                                              endSnipX_grabCallReady hloDog hloVat hloSale
                                                rd2489 hgrabCodeNE
                                            obtain ⟨σ_grab, zGrab, ret, AinGrab, callGasGrab,
                                                _, _, hΘGrab, rd2607, hretSize⟩ :=
                                              endSnipX_grabPostCall rd2606 hdepthLt
                                            rcases hΘGrab with ⟨gGrab'', AGrab, hΘGrabEq⟩
                                            have hVatWordGrab :
                                                endPackVatWord σ_post I =
                                                  endPackVatWord σ_post_solm I :=
                                              congrArg (fun m => endPackVatWord m I) hAccountsPost
                                            have hVatAddrGrab :
                                                endPackVatAddr σ_post I =
                                                  endPackVatAddr σ_post_solm I := by
                                              simp [endPackVatAddr, hVatWordGrab]
                                            have hVowWordGrab :
                                                endPackVowWord σ_post I =
                                                  endPackVowWord σ_post_solm I := by
                                              exact congrArg (fun m => endPackVowWord m I)
                                                hAccountsPost
                                            have hVowAddrGrab :
                                                endPackVowAddr σ_post I =
                                                  endPackVowAddr σ_post_solm I := by
                                              simp [endPackVowAddr, hVowWordGrab]
                                            have htgtGrab :
                                                EVM.address (endPackVatAddr σ_post I) =
                                                  AccountAddress.ofUInt256 (endPackVatWord σ_post I) := by
                                              calc
                                                EVM.address (endPackVatAddr σ_post I) =
                                                    EVM.address (AccountAddress.ofUInt256
                                                      (endPackVatWord σ_post I)) := by
                                                  rw [endPackVatAddr_eq_ofUInt256]
                                                _ = AccountAddress.ofUInt256 (endPackVatWord σ_post I) :=
                                                  hAddressId _
                                            have htgtGrabSolm :
                                                EVM.address (endPackVatAddr σ_post_solm I) =
                                                  AccountAddress.ofUInt256 (endPackVatWord σ_post_solm I) := by
                                              simpa [hVatAddrGrab, hVatWordGrab] using htgtGrab
                                            let σ_grab_solm : AccountMap := σ_grab
                                            let A_grab_solm : Substate := AGrab
                                            have hAccountsGrab : σ_grab = σ_grab_solm := rfl
                                            have hSubstateGrab : AGrab = A_grab_solm := rfl
                                            have hΘGrabEqPost :
                                                (σ_grab, gGrab'', AGrab, zGrab, ret) =
                                                  Θ σ_post σ₀ AinGrab
                                                    (AccountAddress.ofUInt256
                                                      (UInt256.ofNat ↑I.codeOwner))
                                                    I.sender
                                                    (AccountAddress.ofUInt256
                                                      (endPackVatWord σ_post I))
                                                    (toExecute σ_post
                                                      (AccountAddress.ofUInt256
                                                        (endPackVatWord σ_post I)))
                                                    callGasGrab (UInt256.ofNat I.gasPrice)
                                                    ⟨0⟩ ⟨0⟩
                                                    ((endSnipGrabCalldataMemFor σ_post σ_sales I
                                                      dogOut vatOut saleOut).readWithPadding
                                                      endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
                                                    (I.depth + 1) I.header I.blobVersionedHashes
                                                    I.blocks I.perm := by
                                              simpa only [σ_post] using hΘGrabEq
                                            have hdepthGrabSolm :
                                                evmPostSolm.executionEnv.depth ≠ 1024 := by
                                              rw [← hStatePost.executionEnv]
                                              simpa [evmPostEvm, endSnipPostArtState,
                                                evmYankEvm, evmSuckEvm, evmSalesEvm,
                                                evmVatEvm, evmDogEvm, evmSolm, initState,
                                                storageStore_executionEnv] using hdepthNe
                                            have hEnvPostSolm : evmPostSolm.executionEnv = I := by
                                              calc
                                                evmPostSolm.executionEnv = evmPostEvm.executionEnv :=
                                                  hStatePost.executionEnv.symm
                                                _ = I := by
                                                  simp [evmPostEvm, endSnipPostArtState,
                                                    evmYankEvm, evmSuckEvm, evmSalesEvm,
                                                    evmVatEvm, evmDogEvm, evmSolm, initState,
                                                    storageStore_executionEnv]
                                            have hEnvCodeOwnerPost :=
                                              congrArg (fun env : ExecutionEnv => env.codeOwner)
                                                hEnvPostSolm
                                            have hEnvSenderPost :=
                                              congrArg (fun env : ExecutionEnv => env.sender)
                                                hEnvPostSolm
                                            have hEnvGasPricePost :=
                                              congrArg (fun env : ExecutionEnv => env.gasPrice)
                                                hEnvPostSolm
                                            have hEnvDepthPost :=
                                              congrArg (fun env : ExecutionEnv => env.depth)
                                                hEnvPostSolm
                                            have hEnvHeaderPost :=
                                              congrArg (fun env : ExecutionEnv => env.header)
                                                hEnvPostSolm
                                            have hEnvBlobHashesPost :=
                                              congrArg (fun env : ExecutionEnv => env.blobVersionedHashes)
                                                hEnvPostSolm
                                            have hEnvBlocksPost :=
                                              congrArg (fun env : ExecutionEnv => env.blocks)
                                                hEnvPostSolm
                                            have hEnvPermPost :
                                                evmPostSolm.executionEnv.perm = I.perm := by
                                              rw [hEnvPostSolm]
                                            have hpermGrab :
                                                evmPostSolm.executionEnv.perm = true := by
                                              rw [hEnvPostSolm]
                                              exact hperm
                                            have hSigma0PostSolm : evmPostSolm.σ₀ = σ₀ := by
                                              change (Solm.EVM.storageStore evmYankSolm
                                                I.codeOwner (endSnipArtSlot I)
                                                (endSnipArtNewWord σ_yank_solm I vatOut saleOut)).σ₀ = σ₀
                                              rw [storageStore_σ₀]
                                              simp [evmYankSolm, evmSuckSolm, evmSalesSolm,
                                                evmVatSolm, evmDogSolm, evmSolm, initState]
                                            have hgrabCallSolmRaw := callCoincides (cfg := config)
                                              (evm := evmPostSolm) (name := "grab")
                                              (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I),
                                                .address (endSnipSaleUsrAddr saleOut),
                                                .address I.codeOwner,
                                                .address (endPackVowAddr σ_post_solm I),
                                                .int (Int.ofNat (endSnipSaleLotWord saleOut).toNat),
                                                .int (Int.ofNat (endSnipArtWord vatOut saleOut).toNat)])
                                              (tgt := EVM.address (endPackVatAddr σ_post_solm I))
                                              (targetWord := endPackVatWord σ_post_solm I)
                                              (σ' := σ_grab) (A' := AGrab) (A_in := AinGrab)
                                              (z := zGrab) (o := ret) (g'' := gGrab'')
                                              (callGas := callGasGrab)
                                              (mem := endSnipGrabCalldataMemFor σ_post_solm σ_sales I dogOut vatOut saleOut)
                                              (inOff := endFreeGrabOutPtr) (inSize := endFreeGrabInSize)
                                              (callPerm := true)
                                              hdepthGrabSolm
                                              htgtGrabSolm
                                              (endSnipGrabEncodeFor_eq σ_post_solm σ_sales I dogOut vatOut saleOut
                                                hsz68 hloDog hloVat hloSale hlot hart)
                                              (by
                                                calc
                                                  (σ_grab, gGrab'', AGrab, zGrab, ret) =
                                                      Θ σ_post σ₀ AinGrab
                                                        (AccountAddress.ofUInt256
                                                          (UInt256.ofNat ↑I.codeOwner))
                                                        I.sender
                                                        (AccountAddress.ofUInt256
                                                          (endPackVatWord σ_post I))
                                                        (toExecute σ_post
                                                          (AccountAddress.ofUInt256
                                                            (endPackVatWord σ_post I)))
                                                        callGasGrab (UInt256.ofNat I.gasPrice)
                                                        ⟨0⟩ ⟨0⟩
                                                        ((endSnipGrabCalldataMemFor σ_post σ_sales I
                                                          dogOut vatOut saleOut).readWithPadding
                                                          endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
                                                        (I.depth + 1) I.header I.blobVersionedHashes
                                                        I.blocks I.perm := hΘGrabEqPost
                                                  _ = Θ evmPostSolm.accountMap evmPostSolm.σ₀ AinGrab
                                                        (AccountAddress.ofUInt256
                                                          (UInt256.ofNat evmPostSolm.executionEnv.codeOwner))
                                                        evmPostSolm.executionEnv.sender
                                                        (AccountAddress.ofUInt256
                                                          (endPackVatWord σ_post_solm I))
                                                        (toExecute evmPostSolm.accountMap
                                                          (AccountAddress.ofUInt256
                                                            (endPackVatWord σ_post_solm I)))
                                                        callGasGrab
                                                        (UInt256.ofNat evmPostSolm.executionEnv.gasPrice)
                                                        ⟨0⟩ ⟨0⟩
                                                        ((endSnipGrabCalldataMemFor σ_post_solm σ_sales I
                                                          dogOut vatOut saleOut).readWithPadding
                                                          endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
                                                        (evmPostSolm.executionEnv.depth + 1)
                                                        evmPostSolm.executionEnv.header
                                                        evmPostSolm.executionEnv.blobVersionedHashes
                                                        evmPostSolm.executionEnv.blocks
                                                        evmPostSolm.executionEnv.perm := by
                                                    change Θ σ_post σ₀ AinGrab
                                                      (AccountAddress.ofUInt256
                                                        (UInt256.ofNat I.codeOwner)) I.sender
                                                      (AccountAddress.ofUInt256
                                                        (endPackVatWord σ_post I))
                                                      (toExecute σ_post
                                                        (AccountAddress.ofUInt256
                                                          (endPackVatWord σ_post I)))
                                                      callGasGrab (UInt256.ofNat I.gasPrice)
                                                      ⟨0⟩ ⟨0⟩
                                                      ((endSnipGrabCalldataMemFor σ_post σ_sales I
                                                        dogOut vatOut saleOut).readWithPadding
                                                        endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
                                                      (I.depth + 1) I.header I.blobVersionedHashes
                                                      I.blocks I.perm =
                                                      Θ evmPostSolm.accountMap evmPostSolm.σ₀ AinGrab
                                                        (AccountAddress.ofUInt256
                                                          (UInt256.ofNat evmPostSolm.executionEnv.codeOwner))
                                                        evmPostSolm.executionEnv.sender
                                                        (AccountAddress.ofUInt256
                                                          (endPackVatWord σ_post_solm I))
                                                        (toExecute evmPostSolm.accountMap
                                                          (AccountAddress.ofUInt256
                                                            (endPackVatWord σ_post_solm I)))
                                                        callGasGrab
                                                        (UInt256.ofNat evmPostSolm.executionEnv.gasPrice)
                                                        ⟨0⟩ ⟨0⟩
                                                        ((endSnipGrabCalldataMemFor σ_post_solm σ_sales I
                                                          dogOut vatOut saleOut).readWithPadding
                                                          endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
                                                        (evmPostSolm.executionEnv.depth + 1)
                                                        evmPostSolm.executionEnv.header
                                                        evmPostSolm.executionEnv.blobVersionedHashes
                                                        evmPostSolm.executionEnv.blocks
                                                        evmPostSolm.executionEnv.perm
                                                    simp only [hAccountsPost,
                                                      hmapPostSolm,
                                                      hSigma0PostSolm, hEnvCodeOwnerPost,
                                                      hEnvSenderPost, hEnvGasPricePost,
                                                      hEnvDepthPost, hEnvHeaderPost,
                                                      hEnvBlobHashesPost, hEnvBlocksPost,
                                                      hEnvPermPost])
                                            have hgrabCallSolm :
                                                typedCallViaEVM config evmPostSolm
                                                  (EVM.address
                                                    (endPackVatAddr σ_post_solm I))
                                                  "grab" 0
                                                  [.fixedBytes bytes32Width
                                                      (endBytes32ArgBytes I),
                                                    .address
                                                      (endSnipSaleUsrAddr saleOut),
                                                    .address I.codeOwner,
                                                    .address
                                                      (endPackVowAddr σ_post_solm I),
                                                    .int (Int.ofNat
                                                      (endSnipSaleLotWord saleOut).toNat),
                                                    .int (Int.ofNat
                                                      (endSnipArtWord vatOut saleOut).toNat)]
                                                  (zGrab,
                                                    { evmPostSolm with
                                                      accountMap := σ_grab_solm
                                                      substate := A_grab_solm
   },
                                                    ret) true := by
                                              simpa [hVatAddrGrab, hVowAddrGrab] using
                                                hgrabCallSolmRaw
                                            cases zGrab
                                            · have hgrab :=
                                                endSnipGrabTailReverts_callFailedFor
                                                  (σCall := σ_post_solm)
                                                  (σLoc := σ_yank_solm) (I := I)
                                                  (dogOut := dogOut) (vatOut := vatOut)
                                                  (saleOut := saleOut) (grabOut := ret)
                                                  (evm := evmPostSolm)
                                                  (evmGrab :=
                                                    { evmPostSolm with
                                                      accountMap := σ_grab_solm
                                                      substate := A_grab_solm
   })
                                                  hmapPostSolm hownerPostSolm
                                                  hgrabCodeSolmNE
                                                  hlot hart
                                                  (by simpa using hgrabCallSolm)
                                              have hbody :
                                                  ExecTransitionBody config contract evmSolm
                                                    (endSnipStore I) snipTransition.body
                                                    .reverted := by
                                                exact
                                                  endSnipBodyReverts_afterUsrTailGrabReverted
                                                    hprefixUsr htailOk hgrab
                                              have rd2607Fail := by
                                                simpa only [if_false] using rd2607
                                              exact
                                                (endSnipX_grabCallFailed rd2607Fail
                                                  hretSize)
                                                  |>.reEquivExecutionRevert hcode
                                                    hdispatch hdecode hbody
                                            · let evmGrabEvm :=
                                                { evmPostEvm with
                                                  accountMap := σ_grab
                                                  substate := AGrab
   }
                                              let evmGrabSolm :=
                                                { evmPostSolm with
                                                  accountMap := σ_grab_solm
                                                  substate := A_grab_solm
   }
                                              have hStateGrab :
                                                  EVMStateEquiv evmGrabEvm evmGrabSolm := by
                                                refine ⟨?_, ?_⟩
                                                · simpa [evmGrabEvm, evmGrabSolm] using
                                                    hStatePost.executionEnv
                                                · simpa [evmGrabEvm, evmGrabSolm] using
                                                    hAccountsGrab
                                              have rd2607Succ := by
                                                simpa only [if_true] using rd2607
                                              obtain ⟨_, _, rd2625⟩ :=
                                                endSnipX_grabCallSucceeded rd2607Succ
                                              have hretEvm :=
                                                endSnipX_grabLogReturn
                                                  (σCall := σ_post) (σLoc := σ_sales)
                                                  (dogOut := dogOut) (vatOut := vatOut)
                                                  (saleOut := saleOut) (ret := ret)
                                                  hperm hloDog hloVat hloSale rd2625
                                              have hgrab :=
                                                endSnipGrabTailReturns_successFor
                                                  (σCall := σ_post_solm)
                                                  (σLoc := σ_yank_solm) (I := I)
                                                  (dogOut := dogOut) (vatOut := vatOut)
                                                  (saleOut := saleOut) (grabOut := ret)
                                                  (evm := evmPostSolm)
                                                  (evmGrab := evmGrabSolm)
                                                  hmapPostSolm hownerPostSolm
                                                  hgrabCodeSolmNE
                                                  hlot hart
                                                  (by simpa [evmGrabSolm] using
                                                    hgrabCallSolm)
                                              have hbody :
                                                  ExecTransitionBody config contract evmSolm
                                                    (endSnipStore I) snipTransition.body
                                                    (.returned
                                                      { contract := contract,
                                                        locals :=
                                                          endSnipStoreGrab σ_yank_solm
                                                            I dogOut vatOut saleOut }
                                                      evmGrabSolm none) := by
                                                exact
                                                  endSnipBodyReturns_afterUsrTailGrabSuccess
                                                    hprefixUsr htailOk hgrab
                                              exact hretEvm.reEquivExecutionGen
                                                hcode hdispatch hdecode hbody
                                                (by
                                                  calc
                                                    _ = evmGrabEvm.accountMap := by
                                                      simp [evmGrabEvm]
                                                    _ = evmGrabSolm.accountMap :=
                                                      hStateGrab.accountMap)
                                                (by
                                                  simpa [snipTransition] using
                                                    (returnEquiv.fallthrough
                                                      (o := ByteArray.empty) (r := none)
                                                      (t := []) (dvs := []) rfl
                                                      (by native_decide)
                                                      (by native_decide)))
                                        · have hartOverflowBound :
                                            int256Bound ≤
                                              (endSnipArtWord vatOut saleOut).toNat :=
                                            Nat.le_of_not_gt hartBound
                                          have hartOverflow :
                                              2 ^ 255 ≤
                                                (endSnipArtWord vatOut saleOut).toNat := by
                                            simpa [hint256Bound] using hartOverflowBound
                                          have htail :=
                                            endSnipTailReverts_intGuardArt hsz68
                                              hArtLoadSolm hrateNE hfitSolm hlot
                                              hartOverflow hsuckBlock hyankBlock
                                          have hbody :
                                              ExecTransitionBody config contract evmSolm
                                                (endSnipStore I) snipTransition.body
                                                .reverted := by
                                            exact endSnipBodyReverts_afterUsrTailReverted
                                              hprefixUsr htail
                                          exact
                                            (endSnipX_artStoreIntGuardArtOverflow
                                              (g := Sat256.ofUInt256 g)
                                              (σmem := σ_sales) (σpost := σ_yank)
                                              hperm hsz68 hloDog hloVat hloSale hlot
                                              hartOverflow rd2391)
                                              |>.reEquivExecutionRevert hcode hdispatch
                                                hdecode hbody
                                      · have hlotOverflowBound :
                                            int256Bound ≤
                                              (endSnipSaleLotWord saleOut).toNat :=
                                          Nat.le_of_not_gt hlotBound
                                        have hlotOverflow :
                                            2 ^ 255 ≤
                                              (endSnipSaleLotWord saleOut).toNat := by
                                          simpa [hint256Bound] using hlotOverflowBound
                                        have htail :=
                                          endSnipTailReverts_intGuardLot hsz68
                                            hArtLoadSolm hrateNE hfitSolm hlotOverflow
                                            hsuckBlock hyankBlock
                                        have hbody :
                                            ExecTransitionBody config contract evmSolm
                                              (endSnipStore I) snipTransition.body
                                              .reverted := by
                                          exact endSnipBodyReverts_afterUsrTailReverted
                                            hprefixUsr htail
                                        exact
                                          (endSnipX_artStoreIntGuardLotOverflow
                                            (g := Sat256.ofUInt256 g)
                                            (σmem := σ_sales) (σpost := σ_yank)
                                            hperm hsz68 hloDog hloVat hloSale
                                            hlotOverflow rd2391)
                                            |>.reEquivExecutionRevert hcode hdispatch
                                              hdecode hbody
        · rw [not_lt] at hdepthLt
          have hdepthEq : I.depth = 1024 :=
            Fin.ext (by have := I.depth.isLt; omega)
          obtain ⟨_, _, rd1820⟩ :=
            endSnipX_dogIlksCallDepthLimit
              (g := Sat256.ofUInt256 g) hcallReady hdepthEq
          let A_dog :=
            (evmSolm.addAccessedAccount
              (EVM.address (endSnipDogAddr σ I))).substate
          have hcallSolm :
              typedCallViaEVM config evmSolm
                (EVM.address (endSnipDogAddr σ I)) "dogIlks" 0
                [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
                (false, { evmSolm with substate := A_dog }, ByteArray.empty) true := by
            simpa [A_dog] using
              (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
                (tgt := EVM.address (endSnipDogAddr σ I))
                (name := "dogIlks")
                (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
                (callPerm := true)
                (endSnipDogIlksEncode_eq I hsz68 (endSnipDogIlksBaseMem_size I))
                (by simpa [evmSolm, initState] using hdepthEq))
          have hbody :
              ExecTransitionBody config contract evmSolm (endSnipStore I)
                snipTransition.body .reverted := by
            simpa [evmSolm] using
              endSnipBodyReverts_dogIlksCallFailed
                (σ := σ) (σ₀ := σ₀)
                (A := A) (I := I) (g := g)
                (evmDog := { evmSolm with substate := A_dog })
                (out := ByteArray.empty)
                hwv hsz68 htagSolmNE hdogCodeSolmNE
                (by simpa using hcallSolm)
          exact (endSnipX_dogIlksCallFailed rd1820 (by native_decide))
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact endSnipBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
