import Benchmarks.Dss.End.Dispatch
import Benchmarks.Dss.End.Flow
import Benchmarks.Dss.End.Free
import Benchmarks.Dss.End.Snip

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `skip(bytes32,uint256)` transition -/

abbrev endSkipConcreteSelector : ByteArray := selectorBytes 0x50 0x3e 0xcf 0x06

abbrev endSkipIlkWord (I : ExecutionEnv) : UInt256 := endBytes32ArgWord I

abbrev endSkipIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endSkipIdWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36

abbrev endSkipStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (endSkipIlkBytes I))).insert
    "id" (.int (Int.ofNat (endSkipIdWord I).toNat))

theorem endSkipStore_get_ilk (I : ExecutionEnv) :
    (endSkipStore I).get? "ilk" = some (.fixedBytes bytes32Width (endSkipIlkBytes I)) := by
  rw [endSkipStore, store_get_ne _ _ (by decide +native), store_get_self]

abbrev endSkipIlkKey (I : ExecutionEnv) : KeyValue := endBytes32ArgKey I

abbrev endSkipTagEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "tag", steps := [.mindex (endSkipIlkKey I)] }

abbrev endSkipTagSlot (I : ExecutionEnv) : UInt256 := tagSlot (endSkipIlkKey I)

abbrev endSkipTagWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endSkipTagSlot I) σ I

abbrev endSkipEntryPc : UInt256 := ⟨672⟩
abbrev endSkipReturnPc : UInt256 := ⟨562⟩
abbrev endSkipDecodedPc : UInt256 := ⟨694⟩
abbrev endSkipBodyPc : UInt256 := ⟨3224⟩

abbrev endSkipCatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (endSlotWord ⟨2⟩ σ I) solcAddrMask

abbrev endSkipCatAddr (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (endSkipCatWord σ I).toNat

abbrev endSkipCatIlkFlipWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev endSkipCatIlkFlipTargetWord (out : ByteArray) : UInt256 :=
  UInt256.land solcAddrMask (endSkipCatIlkFlipWord out)

abbrev endSkipCatIlkFlipAddr (out : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (endSkipCatIlkFlipWord out).toNat

abbrev endSkipCatIlkChopWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev endSkipCatIlkLumpWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 64 96))

abbrev endSkipStoreCatIlk (I : ExecutionEnv) (catOut : ByteArray) : Store :=
  (endSkipStore I).insert "catIlk"
    (.tuple [.address (endSkipCatIlkFlipAddr catOut),
      .int (Int.ofNat (endSkipCatIlkChopWord catOut).toNat),
      .int (Int.ofNat (endSkipCatIlkLumpWord catOut).toNat)])

abbrev endSkipStoreFlip (I : ExecutionEnv) (catOut : ByteArray) : Store :=
  (endSkipStoreCatIlk I catOut).insert "flip" (.address (endSkipCatIlkFlipAddr catOut))

noncomputable def endSkipCatIlksBaseMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (endSkipIlkWord I) ⟨12⟩ solcFreePtrMem

noncomputable def endSkipCatIlksCalldataMem (I : ExecutionEnv) : ByteArray :=
  endFlowVatIlksCalldataMem I (endSkipCatIlksBaseMem I)

abbrev endSkipCatIlksOutSize : UInt256 := ⟨96⟩

noncomputable def endSkipCatIlksPostCallMem (I : ExecutionEnv) (catOut : ByteArray) :
    ByteArray :=
  catOut.write 0 (endSkipCatIlksCalldataMem I) endFlowVatIlksOutPtr.toNat
    (min endSkipCatIlksOutSize.toNat catOut.size)

abbrev endSkipStoreVatIlk (I : ExecutionEnv) (catOut vatOut : ByteArray) : Store :=
  (endSkipStoreFlip I catOut).insert "vatIlk"
    (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord vatOut).toNat),
      .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat),
      .int (Int.ofNat (endFlowVatIlkSpotWord vatOut).toNat),
      .int (Int.ofNat (endFlowVatIlkLineWord vatOut).toNat),
      .int (Int.ofNat (endFlowVatIlkDustWord vatOut).toNat)])

abbrev endSkipStoreRate (I : ExecutionEnv) (catOut vatOut : ByteArray) : Store :=
  (endSkipStoreVatIlk I catOut vatOut).insert "rate"
    (.int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat))

noncomputable def endSkipVatIlksCalldataMem (I : ExecutionEnv) (catOut : ByteArray) :
    ByteArray :=
  endFlowVatIlksCalldataMem I (endSkipCatIlksPostCallMem I catOut)

noncomputable def endSkipVatIlksPostCallMem (I : ExecutionEnv)
    (catOut vatOut : ByteArray) : ByteArray :=
  vatOut.write 0 (endSkipVatIlksCalldataMem I catOut) endFlowVatIlksOutPtr.toNat
    (min endFlowVatIlksOutSize.toNat vatOut.size)

abbrev endSkipBidsSelectorWord : UInt256 := ⟨0x4423c5f1⟩
abbrev endSkipBidsSelectorShifted : UInt256 :=
  ⟨0x4423c5f100000000000000000000000000000000000000000000000000000000⟩
abbrev endSkipBidsOutSize : UInt256 := ⟨256⟩

noncomputable def endSkipBidsSelectorMem (I : ExecutionEnv)
    (catOut vatOut : ByteArray) : ByteArray :=
  endSkipBidsSelectorShifted.toByteArray.write 0
    (endSkipVatIlksPostCallMem I catOut vatOut) endFlowVatIlksOutPtr.toNat 32

noncomputable def endSkipBidsCalldataMem (I : ExecutionEnv)
    (catOut vatOut : ByteArray) : ByteArray :=
  (endSkipIdWord I).toByteArray.write 0 (endSkipBidsSelectorMem I catOut vatOut)
    (endFlowVatIlksOutPtr + ⟨4⟩).toNat 32

noncomputable def endSkipBidsPostCallMem (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  bidOut.write 0 (endSkipBidsCalldataMem I catOut vatOut) endFlowVatIlksOutPtr.toNat
    (min endSkipBidsOutSize.toNat bidOut.size)

abbrev endSkipBidWord (bidOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (bidOut.extract 0 32))

abbrev endSkipLotWord (bidOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (bidOut.extract 32 64))

abbrev endSkipBidGuyWord (bidOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (bidOut.extract 64 96))

abbrev endSkipBidTicWord (bidOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (bidOut.extract 96 128))

abbrev endSkipBidEndWord (bidOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (bidOut.extract 128 160))

abbrev endSkipUsrWord (bidOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (bidOut.extract 160 192))

abbrev endSkipUsrAddr (bidOut : ByteArray) : AccountAddress :=
  AccountAddress.ofNat (endSkipUsrWord bidOut).toNat

abbrev endSkipUsrAddrWord (bidOut : ByteArray) : UInt256 :=
  UInt256.land solcAddrMask (endSkipUsrWord bidOut)

abbrev endSkipBidGalWord (bidOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (bidOut.extract 192 224))

abbrev endSkipTabWord (bidOut : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (bidOut.extract 224 256))

abbrev endSkipStoreFlipBid (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : Store :=
  (endSkipStoreRate I catOut vatOut).insert "flipBid"
    (.tuple [.int (Int.ofNat (endSkipBidWord bidOut).toNat),
      .int (Int.ofNat (endSkipLotWord bidOut).toNat),
      .address (AccountAddress.ofNat (endSkipBidGuyWord bidOut).toNat),
      .int (Int.ofNat ((endSkipBidTicWord bidOut).toNat % EVM.twoPow 48)),
      .int (Int.ofNat ((endSkipBidEndWord bidOut).toNat % EVM.twoPow 48)),
      .address (endSkipUsrAddr bidOut),
      .address (AccountAddress.ofNat (endSkipBidGalWord bidOut).toNat),
      .int (Int.ofNat (endSkipTabWord bidOut).toNat)])

abbrev endSkipStoreBid (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) : Store :=
  (endSkipStoreFlipBid I catOut vatOut bidOut).insert "bid"
    (.int (Int.ofNat (endSkipBidWord bidOut).toNat))

abbrev endSkipStoreLot (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) : Store :=
  (endSkipStoreBid I catOut vatOut bidOut).insert "lot"
    (.int (Int.ofNat (endSkipLotWord bidOut).toNat))

abbrev endSkipStoreUsr (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) : Store :=
  (endSkipStoreLot I catOut vatOut bidOut).insert "usr" (.address (endSkipUsrAddr bidOut))

abbrev endSkipStoreTab (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) : Store :=
  (endSkipStoreUsr I catOut vatOut bidOut).insert "tab"
    (.int (Int.ofNat (endSkipTabWord bidOut).toNat))

abbrev endSkipSuckSelectorWord : UInt256 := ⟨0xf24e23eb⟩
abbrev endSkipSuckSelectorShifted : UInt256 :=
  ⟨0xf24e23eb00000000000000000000000000000000000000000000000000000000⟩
abbrev endSkipSuckOutPtr : UInt256 := ⟨128⟩
abbrev endSkipSuckInSize : UInt256 := ⟨100⟩
abbrev endSkipSuckOutSize : UInt256 := ⟨0⟩
abbrev endSkipSuckEndPtr : UInt256 := ⟨228⟩

abbrev endSkipHopeSelectorWord : UInt256 := ⟨0xa3b22fc4⟩
abbrev endSkipHopeSelectorShifted : UInt256 :=
  ⟨0xa3b22fc400000000000000000000000000000000000000000000000000000000⟩
abbrev endSkipHopeOutPtr : UInt256 := ⟨128⟩
abbrev endSkipHopeInSize : UInt256 := ⟨36⟩
abbrev endSkipHopeOutSize : UInt256 := ⟨0⟩
abbrev endSkipHopeEndPtr : UInt256 := ⟨164⟩

abbrev endSkipYankSelectorWord : UInt256 := ⟨0x26e027f1⟩
abbrev endSkipYankSelectorShifted : UInt256 :=
  ⟨0x26e027f100000000000000000000000000000000000000000000000000000000⟩
abbrev endSkipYankOutPtr : UInt256 := ⟨128⟩
abbrev endSkipYankInSize : UInt256 := ⟨36⟩
abbrev endSkipYankOutSize : UInt256 := ⟨0⟩
abbrev endSkipYankEndPtr : UInt256 := ⟨164⟩

abbrev endSkipThisWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.codeOwner.val

abbrev endSkipStoreSuck1 (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) :
    Store :=
  (endSkipStoreTab I catOut vatOut bidOut).insert "_suck1" (collapseReturns [])

abbrev endSkipStoreSuck2 (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) :
    Store :=
  (endSkipStoreSuck1 I catOut vatOut bidOut).insert "_suck2" (collapseReturns [])

abbrev endSkipStoreHope (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) :
    Store :=
  (endSkipStoreSuck2 I catOut vatOut bidOut).insert "_hope" (collapseReturns [])

abbrev endSkipStoreYank (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) :
    Store :=
  (endSkipStoreHope I catOut vatOut bidOut).insert "_yank" (collapseReturns [])

abbrev endSkipArtWord (vatOut bidOut : ByteArray) : UInt256 :=
  UInt256.div (endSkipTabWord bidOut) (endFlowVatIlkRateWord vatOut)

abbrev endSkipStoreArt (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) :
    Store :=
  (endSkipStoreYank I catOut vatOut bidOut).insert "art"
    (.int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat))

abbrev endSkipArtSlot (I : ExecutionEnv) : UInt256 := ArtSlot (endSkipIlkKey I)

abbrev endSkipArtOldWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord (endSkipArtSlot I) σ I

abbrev endSkipArtNewWord (σ : AccountMap) (I : ExecutionEnv)
    (vatOut bidOut : ByteArray) : UInt256 :=
  endSkipArtOldWord σ I + endSkipArtWord vatOut bidOut

abbrev endSkipStoreArtNew (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : Store :=
  (endSkipStoreArt I catOut vatOut bidOut).insert "ArtNew"
    (.int (Int.ofNat (endSkipArtNewWord σ I vatOut bidOut).toNat))

abbrev endSkipPostArtState (evm : EVM.State) (I : ExecutionEnv)
    (artNew : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (endSkipArtSlot I) artNew

def endSkipPostArtAccountMap (σ : AccountMap) (I : ExecutionEnv) (artNew : UInt256) :
    AccountMap :=
  sstoreAccountMap I.codeOwner σ (endSkipArtSlot I) artNew

theorem endSkip_storageStore_blocks (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount,
    Account.updateStorage]

theorem endSkip_storageStore_genesisBlockHeader (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader =
      evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount,
    Account.updateStorage]

theorem endSkip_storageStore_σ₀ (evm : EVM.State) (addr : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount,
    Account.updateStorage]

abbrev endSkipStoreGrab (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : Store :=
  (endSkipStoreArtNew σ I catOut vatOut bidOut).insert "_grab" (collapseReturns [])

noncomputable def endSkipSuck1CalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeCascade (endSkipBidsPostCallMem I catOut vatOut bidOut)
    [ (128, endSkipSuckSelectorShifted),
      (132, endPackVowWord σ I),
      (164, endPackVowWord σ I),
      (196, endSkipTabWord bidOut) ]

noncomputable def endSkipSuck1PostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkipSuck1CalldataMem σ I catOut vatOut bidOut)
    endSkipSuckOutPtr.toNat (min endSkipSuckOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkipSuck2CalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeCascade (endSkipSuck1PostCallMem σ I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipSuckSelectorShifted),
      (132, endPackVowWord σ I),
      (164, endSkipThisWord I),
      (196, endSkipBidWord bidOut) ]

noncomputable def endSkipSuck2PostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkipSuck2CalldataMem σ I catOut vatOut bidOut)
    endSkipSuckOutPtr.toNat (min endSkipSuckOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkipSuck2CalldataMemFor (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeCascade (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipSuckSelectorShifted),
      (132, endPackVowWord σcall I),
      (164, endSkipThisWord I),
      (196, endSkipBidWord bidOut) ]

noncomputable def endSkipSuck2PostCallMemFor (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut)
    endSkipSuckOutPtr.toNat (min endSkipSuckOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkipHopeCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeCascade (endSkipSuck2PostCallMem σ I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipHopeSelectorShifted),
      (132, endSkipCatIlkFlipTargetWord catOut) ]

noncomputable def endSkipHopePostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkipHopeCalldataMem σ I catOut vatOut bidOut)
    endSkipHopeOutPtr.toNat (min endSkipHopeOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkipHopeCalldataMemFor (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeCascade (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipHopeSelectorShifted),
      (132, endSkipCatIlkFlipTargetWord catOut) ]

noncomputable def endSkipHopePostCallMemFor (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut)
    endSkipHopeOutPtr.toNat (min endSkipHopeOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkipYankCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeCascade (endSkipHopePostCallMem σ I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipYankSelectorShifted), (132, endSkipIdWord I) ]

noncomputable def endSkipYankPostCallMem (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkipYankCalldataMem σ I catOut vatOut bidOut)
    endSkipYankOutPtr.toNat (min endSkipYankOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkipYankCalldataMemFor (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeCascade (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipYankSelectorShifted), (132, endSkipIdWord I) ]

noncomputable def endSkipYankPostCallMemFor (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut)
    endSkipYankOutPtr.toNat (min endSkipYankOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkipArtHashMem (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  twoWordHashMem (endSkipIlkWord I) ⟨14⟩
    (endSkipYankPostCallMem σ I catOut vatOut bidOut ByteArray.empty)

noncomputable def endSkipArtStoreHashMem (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  twoWordHashMem (endSkipIlkWord I) ⟨14⟩
    (endSkipArtHashMem σ I catOut vatOut bidOut)

noncomputable def endSkipArtHashMemFor (σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  twoWordHashMem (endSkipIlkWord I) ⟨14⟩
    (endSkipYankPostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)

noncomputable def endSkipArtStoreHashMemFor (σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  twoWordHashMem (endSkipIlkWord I) ⟨14⟩
    (endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut)

def endSkipGrabWritesFor (σCall σLoc : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : List (Nat × UInt256) :=
  [ (128, endFreeGrabSelectorShifted),
    (132, endSkipIlkWord I),
    (164, endSkipUsrAddrWord bidOut),
    (196, endSkipThisWord I),
    (228, endPackVowWord σCall I),
    (260, endSkipLotWord bidOut),
    (292, endSkipArtWord vatOut bidOut) ]

noncomputable def endSkipGrabCalldataMemFor (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeCascade (endSkipArtStoreHashMem σLoc I catOut vatOut bidOut)
    (endSkipGrabWritesFor σCall σLoc I catOut vatOut bidOut)

noncomputable def endSkipGrabPostCallMemFor (σCall σLoc : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkipGrabCalldataMemFor σCall σLoc I catOut vatOut bidOut)
    endFreeGrabOutPtr.toNat (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkipGrabCalldataMemForTrace
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeCascade (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
    (endSkipGrabWritesFor σCall σmem I catOut vatOut bidOut)

noncomputable def endSkipGrabMem1Trace (σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeWord (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) 128
    endFreeGrabSelectorShifted

noncomputable def endSkipGrabMem2Trace (σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeWord (endSkipGrabMem1Trace σmem σcall I catOut vatOut bidOut) 132
    (endSkipIlkWord I)

noncomputable def endSkipGrabMem3Trace (σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeWord (endSkipGrabMem2Trace σmem σcall I catOut vatOut bidOut) 164
    (endSkipUsrAddrWord bidOut)

noncomputable def endSkipGrabMem4Trace (σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeWord (endSkipGrabMem3Trace σmem σcall I catOut vatOut bidOut) 196
    (endSkipThisWord I)

noncomputable def endSkipGrabMem5Trace
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeWord (endSkipGrabMem4Trace σmem σcall I catOut vatOut bidOut) 228
    (endPackVowWord σCall I)

noncomputable def endSkipGrabMem6Trace
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeWord (endSkipGrabMem5Trace σCall σmem σcall I catOut vatOut bidOut) 260
    (endSkipLotWord bidOut)

noncomputable def endSkipGrabMem7Trace
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) : ByteArray :=
  writeWord (endSkipGrabMem6Trace σCall σmem σcall I catOut vatOut bidOut) 292
    (endSkipArtWord vatOut bidOut)

noncomputable def endSkipGrabPostCallMemForTrace
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  ret.write 0 (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
    endFreeGrabOutPtr.toNat (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat

noncomputable def endSkipLogDataMemForTrace
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  (endSkipTabWord bidOut).toByteArray.write 0
    (endSkipGrabPostCallMemForTrace σCall σmem σcall I catOut vatOut bidOut ret) 128 32

noncomputable def endSkipLogDataMem2ForTrace
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  (endSkipLotWord bidOut).toByteArray.write 0
    (endSkipLogDataMemForTrace σCall σmem σcall I catOut vatOut bidOut ret) 160 32

noncomputable def endSkipLogDataMem3ForTrace
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) : ByteArray :=
  (endSkipArtWord vatOut bidOut).toByteArray.write 0
    (endSkipLogDataMem2ForTrace σCall σmem σcall I catOut vatOut bidOut ret) 192 32

theorem endSkipTagSlot_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    endSkipTagSlot I = solcMappingSlot ⟨12⟩ (endSkipIlkWord I) := by
  unfold endSkipTagSlot endSkipIlkKey tagSlot mapSlot solcMappingSlot
  rw [endKeyValueToWord_bytes32ArgKey (by omega)]

theorem endSkipCatIlksEncode_eq (I : ExecutionEnv) {mem : ByteArray}
    (hsz68 : 68 ≤ I.calldata.size) (hmem : mem.size = 96) :
    config.externalABI.encode? "catIlks" [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
      some ((endFlowVatIlksCalldataMem I mem).readWithPadding
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat) := by
  change config.externalABI.encode? "catIlks"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
    some ((endFlowVatIlksCalldataMem I mem).readWithPadding 128 36)
  rw [endFlowVatIlksCalldataMem_read128_36 I hmem]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endSkipIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) (by omega)
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endSkipIlkWord I := by
      simpa [endBytes32ArgBytes, endSkipIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by omega))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hlen : (EVM.Word.toBytesBE (endSkipIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endSkipIlkWord I)
  simp [config, externalABI, ilksEncode?, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, ilksSelector,
    selectorBytes, hbytes, hlen, ABI.zeroBytes, word_toBytesBE_toByteArray_eq_toByteArray]

theorem endSkipCatIlksBaseMem_size (I : ExecutionEnv) :
    (endSkipCatIlksBaseMem I).size = 96 := by
  rw [endSkipCatIlksBaseMem]
  exact twoWordHashMem_size_96 (endSkipIlkWord I) ⟨12⟩ solcFreePtrMem_size

theorem endSkipCatIlksBaseMem_read64 (I : ExecutionEnv) :
    (endSkipCatIlksBaseMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endSkipCatIlksBaseMem]
  exact twoWordHashMem_read64 (endSkipIlkWord I) ⟨12⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

theorem endSkipCatIlksCalldataMem_size (I : ExecutionEnv) :
    (endSkipCatIlksCalldataMem I).size = 164 := by
  rw [endSkipCatIlksCalldataMem]
  exact endFlowVatIlksCalldataMem_size I (endSkipCatIlksBaseMem_size I)

theorem endSkipCatIlksCalldataMem_read64 (I : ExecutionEnv) :
    (endSkipCatIlksCalldataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endSkipCatIlksCalldataMem]
  exact endFlowVatIlksCalldataMem_read64 I (endSkipCatIlksBaseMem_size I)
    (endSkipCatIlksBaseMem_read64 I)

theorem endSkipCatIlksWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endSkipCatIlksOutSize (UInt256.ofNat out.size)).toNat = min 96 out.size := by
  change (min (UInt256.ofNat 96) (UInt256.ofNat out.size)).toNat = min 96 out.size
  by_cases hle : 96 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 96) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 96 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 96)]
    exact umin_ofNat_right_toNat_of_lt (c := 96) (n := out.size) (by decide) hlt hout

theorem endSkipCatIlksPostCallMem_size_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 96 ≤ out.size) :
    (endSkipCatIlksPostCallMem I out).size = 224 := by
  unfold endSkipCatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endSkipCatIlksOutSize.toNat = 96 by decide +native]
  rw [Nat.min_eq_left hlo]
  change (out.write 0 (endSkipCatIlksCalldataMem I) 128 96).size = 224
  rw [write_eq_gen_extend out (endSkipCatIlksCalldataMem I) 128 96
    (by omega) (by omega)
    (by rw [endSkipCatIlksCalldataMem_size I]; omega)
    (by rw [endSkipCatIlksCalldataMem_size I]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    endSkipCatIlksCalldataMem_size I]
  omega

theorem endSkipCatIlksPostCallMem_read64 (I : ExecutionEnv) (out : ByteArray) :
    (endSkipCatIlksPostCallMem I out).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipCatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endSkipCatIlksOutSize.toNat = 96 by decide +native]
  by_cases hlen0 : min 96 out.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endSkipCatIlksCalldataMem_read64 I
  · rw [write_read_below_gen_extend out (endSkipCatIlksCalldataMem I)
      128 (min 96 out.size) 64 hlen0
      (Nat.min_le_right _ _)
      (by
        rw [endSkipCatIlksCalldataMem_size I]
        omega)
      (by decide +native)]
    exact endSkipCatIlksCalldataMem_read64 I

theorem endSkipCatIlksPostCallMem_mload64 (I : ExecutionEnv) (out : ByteArray) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSkipCatIlksPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipCatIlksPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      unfold endSkipCatIlksPostCallMem
      rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
        show endSkipCatIlksOutSize.toNat = 96 by decide +native]
      by_cases hlen0 : min 96 out.size = 0
      · rw [hlen0, byteArray_write_len_zero, endSkipCatIlksCalldataMem_size I]
        decide
      · by_cases hin : 128 + min 96 out.size ≤ (endSkipCatIlksCalldataMem I).size
        · rw [write_eq_gen out (endSkipCatIlksCalldataMem I) 128 (min 96 out.size)
            hlen0 (Nat.min_le_right _ _) hin]
          rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
            ByteArray.size_extract, ByteArray.size_extract, endSkipCatIlksCalldataMem_size I]
          have hle96 : min 96 out.size ≤ 96 := Nat.min_le_left _ _
          omega
        · rw [write_eq_gen_extend out (endSkipCatIlksCalldataMem I) 128
            (min 96 out.size) hlen0 (Nat.min_le_right _ _)
            (by rw [endSkipCatIlksCalldataMem_size I]; omega) (Nat.lt_of_not_ge hin)]
          rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
            endSkipCatIlksCalldataMem_size I]
          have hle96 : min 96 out.size ≤ 96 := Nat.min_le_left _ _
          have hpos : 0 < min 96 out.size := Nat.pos_of_ne_zero hlen0
          omega)
    (by decide)
    (endSkipCatIlksPostCallMem_read64 I out)

theorem endSkipCatIlksPostCallMem_read128_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 96 ≤ out.size) :
    (endSkipCatIlksPostCallMem I out).readWithPadding 128 32 = out.extract 0 32 := by
  unfold endSkipCatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endSkipCatIlksOutSize.toNat = 96 by decide +native,
    Nat.min_eq_left hlo]
  rw [write_eq_gen_extend out (endSkipCatIlksCalldataMem I) 128 96
    (by omega) (by omega)
    (by rw [endSkipCatIlksCalldataMem_size I]; omega)
    (by rw [endSkipCatIlksCalldataMem_size I]; omega)]
  have hprefix : ((endSkipCatIlksCalldataMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSkipCatIlksCalldataMem_size I]
    omega
  rw [readWithPadding_eq_extract' _ 128 32 (by omega) (by omega)
    (by
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        endSkipCatIlksCalldataMem_size I]
      omega)]
  rw [extract_append_right_window _ _ 128 160 (by rw [hprefix])]
  rw [hprefix]
  rw [extract_extract_BA, show (128 - 128 : ℕ) = 0 from rfl,
    show min (0 + (160 - 128)) 96 = 32 from by omega]

theorem endSkipCatIlksPostCallMem_mload128_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 96 ≤ out.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (endSkipCatIlksPostCallMem I out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipCatIlksPostCallMem I out).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      endSkipCatIlkFlipWord out := by
  rw [if_neg]
  · change UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipCatIlksPostCallMem I out).readWithPadding 128 32)) =
        endSkipCatIlkFlipWord out
    rw [endSkipCatIlksPostCallMem_read128_long I out hlo]
  · rw [endSkipCatIlksPostCallMem_size_long I out hlo]
    decide +native

theorem endSkipCatIlksDecode_ok {out : ByteArray} (hlo : 96 ≤ out.size) :
    config.externalABI.decode? "catIlks" out =
      some [.address (endSkipCatIlkFlipAddr out),
        .int (Int.ofNat (endSkipCatIlkChopWord out).toNat),
        .int (Int.ofNat (endSkipCatIlkLumpWord out).toNat)] := by
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
  have hword0 := endFlow_bytesToWord_drop_take32_eq_extract out 0
  have hword32 := endFlow_bytesToWord_drop_take32_eq_extract out 32
  have hword64 := endFlow_bytesToWord_drop_take32_eq_extract out 64
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
      [addr, uint256, uint256] out =
    some [.address (endSkipCatIlkFlipAddr out),
      .int (Int.ofNat (endSkipCatIlkChopWord out).toNat),
      .int (Int.ofNat (endSkipCatIlkLumpWord out).toNat)]
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [addr, uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256, uint256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [addr, uint256, uint256].length) (by decide) (by simp)]
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
  rw [hword0, hword32, hword64]

theorem endSkipCatIlksDecode_none_short {out : ByteArray} (hshort : out.size < 96) :
    config.externalABI.decode? "catIlks" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
      [addr, uint256, uint256] out = none
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [addr, uint256, uint256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [addr, uint256, uint256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [addr, uint256, uint256].length) (by decide) (by simp)]
  cases hdec :
      decodeScalarWordsWithMode? DecodeMode.legacySolc05 [addr, uint256, uint256]
        out.toList 0 with
  | none =>
      simp [hdec]
  | some values =>
      have hlenDec := decodeScalarWordsWithMode?_some_length
        (mode := DecodeMode.legacySolc05)
        (types := [addr, uint256, uint256])
        (bytes := out.toList) (cursor := 0) (values := values) (by omega) hdec
      rw [hlen] at hlenDec
      norm_num at hlenDec
      omega

theorem endSkipVatIlksBaseMem_size_long (I : ExecutionEnv) (catOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) :
    (endSkipCatIlksPostCallMem I catOut).size = 224 :=
  endSkipCatIlksPostCallMem_size_long I catOut hloCat

theorem endSkipVatIlksSelectorMem_size_long (I : ExecutionEnv) (catOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) :
    (endFlowVatIlksSelectorMem (endSkipCatIlksPostCallMem I catOut)).size = 224 := by
  unfold endFlowVatIlksSelectorMem
  exact toByteArray_write32_size_of_le (endSkipCatIlksPostCallMem I catOut)
    endFlowVatIlksSelectorShifted 128 224 224
    (endSkipVatIlksBaseMem_size_long I catOut hloCat)
    (by rw [endSkipVatIlksBaseMem_size_long I catOut hloCat]; omega)
    (by decide +native)

theorem endSkipVatIlksCalldataMem_size_long (I : ExecutionEnv) (catOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) :
    (endSkipVatIlksCalldataMem I catOut).size = 224 := by
  unfold endSkipVatIlksCalldataMem endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by decide +native]
  exact toByteArray_write32_size_of_le
    (endFlowVatIlksSelectorMem (endSkipCatIlksPostCallMem I catOut))
    (endFlowIlkWord I) 132 224 224
    (endSkipVatIlksSelectorMem_size_long I catOut hloCat)
    (by rw [endSkipVatIlksSelectorMem_size_long I catOut hloCat]; omega)
    (by decide +native)

theorem endSkipVatIlksSelectorMem_read64_long (I : ExecutionEnv) (catOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) :
    (endFlowVatIlksSelectorMem (endSkipCatIlksPostCallMem I catOut)).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endFlowVatIlksSelectorMem
  change (endFlowVatIlksSelectorShifted.toByteArray.write 0
      (endSkipCatIlksPostCallMem I catOut) 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap endFlowVatIlksSelectorShifted
    (endSkipCatIlksPostCallMem I catOut) 128 64
    (by rw [endSkipVatIlksBaseMem_size_long I catOut hloCat]; omega)
    (by omega)
    (by rw [endSkipVatIlksBaseMem_size_long I catOut hloCat]; decide +native)]
  exact endSkipCatIlksPostCallMem_read64 I catOut

theorem endSkipVatIlksCalldataMem_read64_long (I : ExecutionEnv) (catOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) :
    (endSkipVatIlksCalldataMem I catOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipVatIlksCalldataMem endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by decide +native]
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [endSkipVatIlksSelectorMem_size_long I catOut hloCat]; omega) (by omega)]
  exact endSkipVatIlksSelectorMem_read64_long I catOut hloCat

theorem endSkipVatIlksSelectorMem_extract128_132_long (I : ExecutionEnv)
    (catOut : ByteArray) (hloCat : 96 ≤ catOut.size) :
    (endFlowVatIlksSelectorMem (endSkipCatIlksPostCallMem I catOut)).extract 128 132 =
      ilksSelector := by
  have hread :
      (endFlowVatIlksSelectorMem (endSkipCatIlksPostCallMem I catOut)).readWithPadding
        128 4 = ilksSelector := by
    unfold endFlowVatIlksSelectorMem
    change (endFlowVatIlksSelectorShifted.toByteArray.write 0
        (endSkipCatIlksPostCallMem I catOut) 128 32).readWithPadding (128 + 0) 4 =
      ilksSelector
    rw [toByteArray_write_read_window_of_gap endFlowVatIlksSelectorShifted
      (endSkipCatIlksPostCallMem I catOut) 128 0 4
      (by omega) (by omega) (by decide +native)
      (by rw [endSkipVatIlksBaseMem_size_long I catOut hloCat]; decide +native)]
    decide +native
  rw [← hread]
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
    (by rw [endSkipVatIlksSelectorMem_size_long I catOut hloCat]; omega)]

theorem endSkipVatIlksCalldataMem_read128_36_long (I : ExecutionEnv)
    (catOut : ByteArray) (hloCat : 96 ≤ catOut.size) :
    (endSkipVatIlksCalldataMem I catOut).readWithPadding 128 36 =
      ilksSelector ++ (endFlowIlkWord I).toByteArray := by
  unfold endSkipVatIlksCalldataMem endFlowVatIlksCalldataMem endFlowVatIlksArg0Mem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by decide +native]
  let selMem := endFlowVatIlksSelectorMem (endSkipCatIlksPostCallMem I catOut)
  have hselSize : selMem.size = 224 := by
    simpa [selMem] using endSkipVatIlksSelectorMem_size_long I catOut hloCat
  have hfinalSize : ((endFlowIlkWord I).toByteArray.write 0 selMem 132 32).size = 224 := by
    exact toByteArray_write32_size_of_le selMem (endFlowIlkWord I) 132 224 224
      hselSize (by rw [hselSize]; omega) (by decide +native)
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
    (by rw [hfinalSize]; omega)]
  rw [write32_eq _ _ 132 (by rw [toByteArray_size]) (by rw [hselSize]; omega)]
  change ((selMem.extract 0 132 ++ (endFlowIlkWord I).toByteArray.extract 0 32 ++
      selMem.extract (132 + 32) selMem.size).extract 128 (128 + 36)) =
    ilksSelector ++ (endFlowIlkWord I).toByteArray
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
      endSkipVatIlksSelectorMem_extract128_132_long I catOut hloCat
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

theorem endSkipVatIlksEncode_eq (I : ExecutionEnv) (catOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size) (hloCat : 96 ≤ catOut.size) :
    config.externalABI.encode? "vatIlks" [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
      some ((endSkipVatIlksCalldataMem I catOut).readWithPadding
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat) := by
  change config.externalABI.encode? "vatIlks"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I)] =
    some ((endSkipVatIlksCalldataMem I catOut).readWithPadding 128 36)
  rw [endSkipVatIlksCalldataMem_read128_36_long I catOut hloCat]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endFlowIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) (by omega)
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endFlowIlkWord I := by
      simpa [endBytes32ArgBytes, endFlowIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by omega))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have hlen : (EVM.Word.toBytesBE (endFlowIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endFlowIlkWord I)
  simp [config, externalABI, ilksEncode?, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, ilksSelector,
    selectorBytes, hbytes, hlen, ABI.zeroBytes, word_toBytesBE_toByteArray_eq_toByteArray]

theorem endSkipVatIlksWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endFlowVatIlksOutSize (UInt256.ofNat out.size)).toNat = min 160 out.size := by
  simpa [endFlowVatIlksOutSize] using endFlowVatIlksWriteLen_eq (out := out) hout

theorem endSkipVatIlksPostCallMem_size_long (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkipVatIlksPostCallMem I catOut vatOut).size = 288 := by
  unfold endSkipVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endFlowVatIlksOutSize.toNat = 160 by decide +native]
  rw [Nat.min_eq_left hloVat]
  rw [write_eq_gen_extend vatOut (endSkipVatIlksCalldataMem I catOut) 128 160
    (by omega) (by omega)
    (by rw [endSkipVatIlksCalldataMem_size_long I catOut hloCat]; omega)
    (by rw [endSkipVatIlksCalldataMem_size_long I catOut hloCat]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
  rw [endSkipVatIlksCalldataMem_size_long I catOut hloCat]
  omega

theorem endSkipVatIlksPostCallMem_read64 (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size) :
    (endSkipVatIlksPostCallMem I catOut vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endFlowVatIlksOutSize.toNat = 160 by decide +native]
  by_cases hlen0 : min 160 vatOut.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endSkipVatIlksCalldataMem_read64_long I catOut hloCat
  · rw [write_read_below_gen_extend vatOut (endSkipVatIlksCalldataMem I catOut)
      128 (min 160 vatOut.size) 64 hlen0 (Nat.min_le_right _ _)
      (by rw [endSkipVatIlksCalldataMem_size_long I catOut hloCat]; omega)
      (by decide +native)]
    exact endSkipVatIlksCalldataMem_read64_long I catOut hloCat

theorem endSkipVatIlksPostCallMem_size_gt64 (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size) :
    64 < (endSkipVatIlksPostCallMem I catOut vatOut).size := by
  unfold endSkipVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endFlowVatIlksOutSize.toNat = 160 by decide +native]
  by_cases hlen0 : min 160 vatOut.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    rw [endSkipVatIlksCalldataMem_size_long I catOut hloCat]
    omega
  · by_cases hext :
        (endSkipVatIlksCalldataMem I catOut).size < 128 + min 160 vatOut.size
    · rw [write_eq_gen_extend vatOut (endSkipVatIlksCalldataMem I catOut)
        128 (min 160 vatOut.size) hlen0 (Nat.min_le_right _ _)
        (by rw [endSkipVatIlksCalldataMem_size_long I catOut hloCat]; omega) hext]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        endSkipVatIlksCalldataMem_size_long I catOut hloCat]
      omega
    · have hin : 128 + min 160 vatOut.size ≤
          (endSkipVatIlksCalldataMem I catOut).size := by omega
      rw [write_eq_gen vatOut (endSkipVatIlksCalldataMem I catOut)
        128 (min 160 vatOut.size) hlen0 (Nat.min_le_right _ _) hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract,
        endSkipVatIlksCalldataMem_size_long I catOut hloCat]
      omega

theorem endSkipVatIlksPostCallMem_mload64 (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSkipVatIlksPostCallMem I catOut vatOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSkipVatIlksPostCallMem I catOut vatOut).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (endSkipVatIlksPostCallMem_size_gt64 I catOut vatOut hloCat)
    (by decide)
    (endSkipVatIlksPostCallMem_read64 I catOut vatOut hloCat)

theorem endSkipVatIlksPostCallMem_read160_long (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkipVatIlksPostCallMem I catOut vatOut).readWithPadding 160 32 =
      vatOut.extract 32 64 := by
  unfold endSkipVatIlksPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endFlowVatIlksOutSize.toNat = 160 by decide +native]
  rw [Nat.min_eq_left hloVat]
  rw [write_eq_gen_extend vatOut (endSkipVatIlksCalldataMem I catOut) 128 160
    (by omega) (by omega)
    (by rw [endSkipVatIlksCalldataMem_size_long I catOut hloCat]; omega)
    (by rw [endSkipVatIlksCalldataMem_size_long I catOut hloCat]; omega)]
  have hprefix : ((endSkipVatIlksCalldataMem I catOut).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSkipVatIlksCalldataMem_size_long I catOut hloCat]
    omega
  have hsrc : (vatOut.extract 0 160).size = 160 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((endSkipVatIlksCalldataMem I catOut).extract 0 128 ++
        vatOut.extract 0 160).size = 288 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      160 + 32 ≤ ((endSkipVatIlksCalldataMem I catOut).extract 0 128 ++
        vatOut.extract 0 160).size := by
    rw [hmemSize]
    norm_num
  rw [readWithPadding_eq_extract _ 160 hreadIn]
  rw [show 160 + 32 = 192 by omega]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem endSkipVatIlksPostCallMem_mload160_long (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (endSkipVatIlksPostCallMem I catOut vatOut).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((endSkipVatIlksPostCallMem I catOut vatOut).readWithPadding
          (⟨160⟩ : UInt256).toNat 32))) =
      endFlowVatIlkRateWord vatOut := by
  unfold endFlowVatIlkRateWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSkipVatIlksPostCallMem I catOut vatOut).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (vatOut.extract 32 64))
    rw [endSkipVatIlksPostCallMem_read160_long I catOut vatOut hloCat hloVat]
  · exact not_or.mpr
      ⟨by rw [endSkipVatIlksPostCallMem_size_long I catOut vatOut hloCat hloVat];
          decide,
        by decide +native⟩

theorem endSkipBidsSelectorMem_size_long (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkipBidsSelectorMem I catOut vatOut).size = 288 := by
  unfold endSkipBidsSelectorMem
  exact toByteArray_write32_size_of_le
    (endSkipVatIlksPostCallMem I catOut vatOut) endSkipBidsSelectorShifted 128 288 288
    (endSkipVatIlksPostCallMem_size_long I catOut vatOut hloCat hloVat)
    (by rw [endSkipVatIlksPostCallMem_size_long I catOut vatOut hloCat hloVat]; omega)
    (by decide +native)

theorem endSkipBidsCalldataMem_size_long (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkipBidsCalldataMem I catOut vatOut).size = 288 := by
  unfold endSkipBidsCalldataMem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by decide +native]
  exact toByteArray_write32_size_of_le
    (endSkipBidsSelectorMem I catOut vatOut) (endSkipIdWord I) 132 288 288
    (endSkipBidsSelectorMem_size_long I catOut vatOut hloCat hloVat)
    (by rw [endSkipBidsSelectorMem_size_long I catOut vatOut hloCat hloVat]; omega)
    (by decide +native)

theorem endSkipBidsSelectorMem_read64_long (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkipBidsSelectorMem I catOut vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipBidsSelectorMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native]
  rw [toByteArray_write_read_below_of_gap endSkipBidsSelectorShifted
    (endSkipVatIlksPostCallMem I catOut vatOut) 128 64
    (by rw [endSkipVatIlksPostCallMem_size_long I catOut vatOut hloCat hloVat]; omega)
    (by omega)
    (by
      rw [endSkipVatIlksPostCallMem_size_long I catOut vatOut hloCat hloVat]
      decide +native)]
  exact endSkipVatIlksPostCallMem_read64 I catOut vatOut hloCat

theorem endSkipBidsCalldataMem_read64_long (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkipBidsCalldataMem I catOut vatOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipBidsCalldataMem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by decide +native]
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [endSkipBidsSelectorMem_size_long I catOut vatOut hloCat hloVat]; omega)
    (by omega)]
  exact endSkipBidsSelectorMem_read64_long I catOut vatOut hloCat hloVat

theorem endSkipBidsSelectorMem_extract128_132_long (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkipBidsSelectorMem I catOut vatOut).extract 128 132 = bidsSelector := by
  have hread :
      (endSkipBidsSelectorMem I catOut vatOut).readWithPadding 128 4 =
        bidsSelector := by
    unfold endSkipBidsSelectorMem
    change (endSkipBidsSelectorShifted.toByteArray.write 0
        (endSkipVatIlksPostCallMem I catOut vatOut) 128 32).readWithPadding 128 4 =
      bidsSelector
    rw [write32_read_prefix_len _ _ 128 4 (by rw [toByteArray_size])
      (by rw [endSkipVatIlksPostCallMem_size_long I catOut vatOut hloCat hloVat]; omega)
      (by omega) (by omega) (by omega)]
    decide +native
  rw [← hread]
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
    (by rw [endSkipBidsSelectorMem_size_long I catOut vatOut hloCat hloVat]; omega)]

theorem endSkipBidsCalldataMem_read128_36_long (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkipBidsCalldataMem I catOut vatOut).readWithPadding 128 36 =
      bidsSelector ++ (endSkipIdWord I).toByteArray := by
  unfold endSkipBidsCalldataMem
  rw [show (endFlowVatIlksOutPtr + ⟨4⟩).toNat = 132 by decide +native]
  let selMem := endSkipBidsSelectorMem I catOut vatOut
  have hselSize : selMem.size = 288 := by
    simpa [selMem] using endSkipBidsSelectorMem_size_long I catOut vatOut hloCat hloVat
  have hfinalSize : ((endSkipIdWord I).toByteArray.write 0 selMem 132 32).size = 288 := by
    exact toByteArray_write32_size_of_le selMem (endSkipIdWord I) 132 288 288
      hselSize (by rw [hselSize]; omega) (by decide +native)
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
    (by rw [hfinalSize]; omega)]
  rw [write32_eq _ _ 132 (by rw [toByteArray_size]) (by rw [hselSize]; omega)]
  change ((selMem.extract 0 132 ++ (endSkipIdWord I).toByteArray.extract 0 32 ++
      selMem.extract (132 + 32) selMem.size).extract 128 (128 + 36)) =
    bidsSelector ++ (endSkipIdWord I).toByteArray
  rw [show 132 + 32 = 164 by omega]
  rw [ByteArray.append_assoc]
  have hA : (selMem.extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, hselSize]
    omega
  rw [extract_append_span (selMem.extract 0 132)
    ((endSkipIdWord I).toByteArray.extract 0 32 ++ selMem.extract 164 selMem.size)
    128 164 (by rw [hA]; omega) (by rw [hA]; omega)]
  rw [hA]
  rw [extract_extract_BA]
  rw [show (0 : ℕ) + 128 = 128 by omega,
    show min (0 + 132) 132 = 132 by omega]
  have hselExtract :
      selMem.extract 128 132 = bidsSelector := by
    simpa [selMem] using
      endSkipBidsSelectorMem_extract128_132_long I catOut vatOut hloCat hloVat
  rw [hselExtract]
  rw [show 164 - 132 = 32 by omega]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_extract, toByteArray_size]
    omega)]
  rw [extract_extract_BA]
  rw [show (0 : ℕ) + 0 = 0 by omega,
    show min (0 + 32) 32 = 32 by omega]
  have hWfull :
      (endSkipIdWord I).toByteArray.extract 0 32 = (endSkipIdWord I).toByteArray := by
    have h := @ByteArray.extract_zero_size (endSkipIdWord I).toByteArray
    rwa [toByteArray_size] at h
  rw [hWfull]

theorem endSkipBidsEncode_eq (I : ExecutionEnv) (catOut vatOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size) :
    config.externalABI.encode? "bids" [.int (Int.ofNat (endSkipIdWord I).toNat)] =
      some ((endSkipBidsCalldataMem I catOut vatOut).readWithPadding
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat) := by
  change config.externalABI.encode? "bids" [.int (Int.ofNat (endSkipIdWord I).toNat)] =
    some ((endSkipBidsCalldataMem I catOut vatOut).readWithPadding 128 36)
  rw [endSkipBidsCalldataMem_read128_36_long I catOut vatOut hloCat hloVat]
  have hidLt : (endSkipIdWord I).toNat < EVM.twoPow 256 := (endSkipIdWord I).val.isLt
  have hidWord : EVM.word (endSkipIdWord I).toNat = endSkipIdWord I := by
    show UInt256.ofNat (endSkipIdWord I).toNat = endSkipIdWord I
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, uint256, uint256Int, bidsSelector,
    selectorBytes, hidLt, hidWord, word_toBytesBE_toByteArray_eq_toByteArray]

theorem endSkipBidsCalldataMem_mload64_long (I : ExecutionEnv)
    (catOut vatOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSkipBidsCalldataMem I catOut vatOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipBidsCalldataMem I catOut vatOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]; decide)
    (by decide)
    (endSkipBidsCalldataMem_read64_long I catOut vatOut hloCat hloVat)

theorem endSkipBidsWriteLen_eq {out : ByteArray} (hout : out.size < UInt256.size) :
    (min endSkipBidsOutSize (UInt256.ofNat out.size)).toNat = min 256 out.size := by
  change (min (UInt256.ofNat 256) (UInt256.ofNat out.size)).toNat = min 256 out.size
  by_cases hle : 256 ≤ out.size
  · rw [Nat.min_eq_left hle]
    exact umin_ofNat_right_toNat_of_ge (c := 256) (n := out.size) (by decide) hle hout
  · have hlt : out.size < 256 := by omega
    rw [Nat.min_eq_right (by omega : out.size ≤ 256)]
    exact umin_ofNat_right_toNat_of_lt (c := 256) (n := out.size) (by decide) hlt hout

theorem endSkipBidsPostCallMem_size_long (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (endSkipBidsPostCallMem I catOut vatOut bidOut).size = 384 := by
  unfold endSkipBidsPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endSkipBidsOutSize.toNat = 256 by decide +native]
  rw [Nat.min_eq_left hloBid]
  rw [write_eq_gen_extend bidOut (endSkipBidsCalldataMem I catOut vatOut) 128 256
    (by omega) (by omega)
    (by rw [endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]; omega)
    (by rw [endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
  rw [endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]
  omega

theorem endSkipBidsPostCallMem_read64 (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipBidsPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endSkipBidsOutSize.toNat = 256 by decide +native]
  by_cases hlen0 : min 256 bidOut.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    exact endSkipBidsCalldataMem_read64_long I catOut vatOut hloCat hloVat
  · rw [write_read_below_gen_extend bidOut (endSkipBidsCalldataMem I catOut vatOut)
      128 (min 256 bidOut.size) 64 hlen0 (Nat.min_le_right _ _)
      (by rw [endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]; omega)
      (by decide +native)]
    exact endSkipBidsCalldataMem_read64_long I catOut vatOut hloCat hloVat

theorem endSkipBidsPostCallMem_size_gt64 (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    64 < (endSkipBidsPostCallMem I catOut vatOut bidOut).size := by
  unfold endSkipBidsPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endSkipBidsOutSize.toNat = 256 by decide +native]
  by_cases hlen0 : min 256 bidOut.size = 0
  · rw [hlen0, byteArray_write_len_zero]
    rw [endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]
    omega
  · by_cases hext :
        (endSkipBidsCalldataMem I catOut vatOut).size < 128 + min 256 bidOut.size
    · rw [write_eq_gen_extend bidOut (endSkipBidsCalldataMem I catOut vatOut)
        128 (min 256 bidOut.size) hlen0 (Nat.min_le_right _ _)
        (by rw [endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]; omega)
        hext]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
        endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]
      omega
    · have hin : 128 + min 256 bidOut.size ≤
          (endSkipBidsCalldataMem I catOut vatOut).size := by omega
      rw [write_eq_gen bidOut (endSkipBidsCalldataMem I catOut vatOut)
        128 (min 256 bidOut.size) hlen0 (Nat.min_le_right _ _) hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract,
        endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]
      omega

theorem endSkipBidsPostCallMem_mload64 (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (endSkipBidsPostCallMem I catOut vatOut bidOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (endSkipBidsPostCallMem_size_gt64 I catOut vatOut bidOut hloCat hloVat)
    (by decide)
    (endSkipBidsPostCallMem_read64 I catOut vatOut bidOut hloCat hloVat)

theorem endSkipBidsPostCallMem_read_long (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size)
    (off : ℕ) (hoff : off + 32 ≤ 256) :
    (endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding (128 + off) 32 =
      bidOut.extract off (off + 32) := by
  unfold endSkipBidsPostCallMem
  rw [show endFlowVatIlksOutPtr.toNat = 128 by decide +native,
    show endSkipBidsOutSize.toNat = 256 by decide +native]
  rw [Nat.min_eq_left hloBid]
  rw [write_eq_gen_extend bidOut (endSkipBidsCalldataMem I catOut vatOut) 128 256
    (by omega) (by omega)
    (by rw [endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]; omega)
    (by rw [endSkipBidsCalldataMem_size_long I catOut vatOut hloCat hloVat]; omega)]
  have hprefix :
      ((endSkipBidsCalldataMem I catOut vatOut).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, endSkipBidsCalldataMem_size_long I catOut vatOut
      hloCat hloVat]
    omega
  have hsrc : (bidOut.extract 0 256).size = 256 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((endSkipBidsCalldataMem I catOut vatOut).extract 0 128 ++
        bidOut.extract 0 256).size = 384 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      128 + off + 32 ≤ ((endSkipBidsCalldataMem I catOut vatOut).extract 0 128 ++
        bidOut.extract 0 256).size := by
    rw [hmemSize]
    omega
  rw [readWithPadding_eq_extract _ (128 + off) hreadIn]
  rw [show 128 + off + 32 = 128 + (off + 32) by omega]
  rw [extract_append_right_window _ _ (128 + off) (128 + (off + 32))
    (by rw [hprefix]; omega), hprefix]
  rw [show 128 + off - 128 = off by omega,
    show 128 + (off + 32) - 128 = off + 32 by omega]
  rw [extract_extract_BA]
  rw [show (0 : ℕ) + off = off by omega,
    show min (0 + (off + 32)) 256 = off + 32 by omega]

theorem endSkipBidsPostCallMem_mload128_long (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (endSkipBidsPostCallMem I catOut vatOut bidOut).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
      endSkipBidWord bidOut := by
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding 128 32)) =
        endSkipBidWord bidOut
    rw [endSkipBidsPostCallMem_read_long I catOut vatOut bidOut hloCat hloVat
      hloBid 0 (by omega)]
  · exact not_or.mpr
      ⟨by rw [endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat
          hloBid]; decide,
        by decide +native⟩

theorem endSkipBidsPostCallMem_mload160_long (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (endSkipBidsPostCallMem I catOut vatOut bidOut).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding
            (⟨160⟩ : UInt256).toNat 32))) =
      endSkipLotWord bidOut := by
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding 160 32)) =
        endSkipLotWord bidOut
    rw [endSkipBidsPostCallMem_read_long I catOut vatOut bidOut hloCat hloVat
      hloBid 32 (by omega)]
  · exact not_or.mpr
      ⟨by rw [endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat
          hloBid]; decide,
        by decide +native⟩

theorem endSkipBidsPostCallMem_mload288_long (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (if (⟨288⟩ : UInt256).toNat ≥ (endSkipBidsPostCallMem I catOut vatOut bidOut).size
        ∨ (⟨288⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding
            (⟨288⟩ : UInt256).toNat 32))) =
      endSkipUsrWord bidOut := by
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding 288 32)) =
        endSkipUsrWord bidOut
    rw [endSkipBidsPostCallMem_read_long I catOut vatOut bidOut hloCat hloVat
      hloBid 160 (by omega)]
  · exact not_or.mpr
      ⟨by rw [endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat
          hloBid]; decide,
        by decide +native⟩

theorem endSkipBidsPostCallMem_mload352_long (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (if (⟨352⟩ : UInt256).toNat ≥ (endSkipBidsPostCallMem I catOut vatOut bidOut).size
        ∨ (⟨352⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding
            (⟨352⟩ : UInt256).toNat 32))) =
      endSkipTabWord bidOut := by
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian
        ((endSkipBidsPostCallMem I catOut vatOut bidOut).readWithPadding 352 32)) =
        endSkipTabWord bidOut
    rw [endSkipBidsPostCallMem_read_long I catOut vatOut bidOut hloCat hloVat
      hloBid 224 (by omega)]
  · exact not_or.mpr
      ⟨by rw [endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat
          hloBid]; decide,
        by decide +native⟩

theorem decodeScalarWordWithMode_legacy_uint48_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWordWithMode? DecodeMode.legacySolc05 uint48 bytes start =
      some (.int (Int.ofNat ((ABI.bytesToWord ((bytes.drop start).take 32)).toNat %
        EVM.twoPow 48)), start + 32) := by
  simp only [uint48, uint48Int, decodeScalarWordWithMode?, readWord?, readBytes?, bind,
    Option.bind]
  rw [if_pos hlen]
  simp [decodeABIWord?, UInt256.toNat]

theorem endSkipBidsDecode_ok {out : ByteArray} (hlo : 256 ≤ out.size) :
    config.externalABI.decode? "bids" out =
      some [.int (Int.ofNat (endSkipBidWord out).toNat),
        .int (Int.ofNat (endSkipLotWord out).toNat),
        .address (AccountAddress.ofNat (endSkipBidGuyWord out).toNat),
        .int (Int.ofNat ((endSkipBidTicWord out).toNat % EVM.twoPow 48)),
        .int (Int.ofNat ((endSkipBidEndWord out).toNat % EVM.twoPow 48)),
        .address (endSkipUsrAddr out),
        .address (AccountAddress.ofNat (endSkipBidGalWord out).toNat),
        .int (Int.ofNat (endSkipTabWord out).toNat)] := by
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
  have htake192 : ((out.toList.drop 192).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have htake224 : ((out.toList.drop 224).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword0 := endFlow_bytesToWord_drop_take32_eq_extract out 0
  have hword32 := endFlow_bytesToWord_drop_take32_eq_extract out 32
  have hword64 := endFlow_bytesToWord_drop_take32_eq_extract out 64
  have hword96 := endFlow_bytesToWord_drop_take32_eq_extract out 96
  have hword128 := endFlow_bytesToWord_drop_take32_eq_extract out 128
  have hword160 := endFlow_bytesToWord_drop_take32_eq_extract out 160
  have hword192 := endFlow_bytesToWord_drop_take32_eq_extract out 192
  have hword224 := endFlow_bytesToWord_drop_take32_eq_extract out 224
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
      [uint256, uint256, addr, uint48, uint48, addr, addr, uint256] out = _
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [uint256, uint256, addr, uint48, uint48, addr, addr, uint256])
    (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, addr, uint48, uint48, addr, addr, uint256])
    (bytes := out.toList) (cursor := 0)
    (total := 32 * [uint256, uint256, addr, uint48, uint48, addr, addr, uint256].length)
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
  have haddr64 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList (0 + 32 + 32) =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((out.toList.drop 64).take 32)).toNat), 64 + 32) := by
    simpa [addr, abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 64) htake64
  rw [haddr64]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_legacy_uint48_ok (bytes := out.toList) (start := 96)
    htake96]
  simp only [Option.bind_some]
  rw [decodeScalarWordWithMode_legacy_uint48_ok (bytes := out.toList) (start := 128)
    htake128]
  simp only [Option.bind_some]
  have haddr160 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList
          (0 + 32 + 32 + 32 + 32 + 32) =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((out.toList.drop 160).take 32)).toNat), 160 + 32) := by
    simpa [addr, abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 160) htake160
  rw [haddr160]
  simp only [Option.bind_some]
  have haddr192 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 addr out.toList
          (0 + 32 + 32 + 32 + 32 + 32 + 32) =
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((out.toList.drop 192).take 32)).toNat), 192 + 32) := by
    simpa [addr, abiAddress] using
      decodeScalarWord_legacyAddress_ok (bytes := out.toList) (start := 192) htake192
  rw [haddr192]
  simp only [Option.bind_some]
  have huint224 :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 uint256 out.toList
          (0 + 32 + 32 + 32 + 32 + 32 + 32 + 32) =
        some (.int (Int.ofNat
          (ABI.bytesToWord ((out.toList.drop 224).take 32)).toNat), 224 + 32) := by
    simpa [uint256, abiUInt256] using
      decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
        (bytes := out.toList) (start := 224) htake224
  rw [huint224]
  simp only [Option.bind_some]
  rw [hword0, hword32, hword64, hword96, hword128, hword160, hword192, hword224]

theorem endSkipBidsDecode_none_short {out : ByteArray} (hshort : out.size < 256) :
    config.externalABI.decode? "bids" out = none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  change ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05
      [uint256, uint256, addr, uint48, uint48, addr, addr, uint256] out = none
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq
    (types := [uint256, uint256, addr, uint48, uint48, addr, addr, uint256])
    (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [uint256, uint256, addr, uint48, uint48, addr, addr, uint256])
    (bytes := out.toList) (cursor := 0)
    (total := 32 * [uint256, uint256, addr, uint48, uint48, addr, addr, uint256].length)
    (by decide) (by simp)]
  cases hdec : decodeScalarWordsWithMode? DecodeMode.legacySolc05
      [uint256, uint256, addr, uint48, uint48, addr, addr, uint256] out.toList 0 with
  | none =>
      simp [hdec]
  | some values =>
      have hlenDec := decodeScalarWordsWithMode?_some_length
        (mode := DecodeMode.legacySolc05)
        (types := [uint256, uint256, addr, uint48, uint48, addr, addr, uint256])
        (bytes := out.toList) (cursor := 0) (values := values) (by omega) hdec
      rw [hlen] at hlenDec
      norm_num at hlenDec
      omega

theorem endSkipSuck1CalldataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck1CalldataMem σ I catOut vatOut bidOut).size = 384 := by
  unfold endSkipSuck1CalldataMem
  exact writeCascade_size_of_base (endSkipBidsPostCallMem I catOut vatOut bidOut)
    [ (128, endSkipSuckSelectorShifted),
      (132, endPackVowWord σ I),
      (164, endPackVowWord σ I),
      (196, endSkipTabWord bidOut) ]
    (endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat hloBid)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSkipSuck1CalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck1CalldataMem σ I catOut vatOut bidOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipSuck1CalldataMem
  rw [writeCascade_read_preserved_of_base
    (endSkipBidsPostCallMem I catOut vatOut bidOut)
    [ (128, endSkipSuckSelectorShifted),
      (132, endPackVowWord σ I),
      (164, endPackVowWord σ I),
      (196, endSkipTabWord bidOut) ]
    (endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat hloBid)
    (by simp [WindowDisjointFromWrites])]
  exact endSkipBidsPostCallMem_read64 I catOut vatOut bidOut hloCat hloVat

theorem endSkipSuck1CalldataMem_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (endSkipSuck1CalldataMem σ I catOut vatOut bidOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipSuck1CalldataMem σ I catOut vatOut bidOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [endSkipSuck1CalldataMem_size σ I catOut vatOut bidOut hloCat hloVat hloBid]
      decide)
    (by decide)
    (endSkipSuck1CalldataMem_read64 σ I catOut vatOut bidOut hloCat hloVat hloBid)

theorem endSkipSuck1PostCallMem_eq (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) :
    endSkipSuck1PostCallMem σ I catOut vatOut bidOut ret =
      endSkipSuck1CalldataMem σ I catOut vatOut bidOut := by
  unfold endSkipSuck1PostCallMem
  have hmin : (min endSkipSuckOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endSkipSuckOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret
    (endSkipSuck1CalldataMem σ I catOut vatOut bidOut) 0 endSkipSuckOutPtr.toNat

theorem endSkipSuck1CalldataMem_read128_4 (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck1CalldataMem σ I catOut vatOut bidOut).readWithPadding 128 4 =
      suckSelector := by
  unfold endSkipSuck1CalldataMem
  rw [writeCascade_read_window_of_head (endSkipBidsPostCallMem I catOut vatOut bidOut)
    128 0 4 endSkipSuckSelectorShifted
    [ (132, endPackVowWord σ I),
      (164, endPackVowWord σ I),
      (196, endSkipTabWord bidOut) ]]
  · unfold endSkipSuckSelectorShifted suckSelector selectorBytes
    decide +native
  · rw [endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat hloBid]
    decide +native
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endSkipSuck1CalldataMem_read132_32 (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck1CalldataMem σ I catOut vatOut bidOut).readWithPadding 132 32 =
      (endPackVowWord σ I).toByteArray := by
  unfold endSkipSuck1CalldataMem
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (endSkipBidsPostCallMem I catOut vatOut bidOut) 128
      endSkipSuckSelectorShifted)
    (word := endPackVowWord σ I)
    (rest := [ (164, endPackVowWord σ I), (196, endSkipTabWord bidOut) ])
    (hbase := by
      rw [writeWord_size]
      · rw [endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat
          hloBid]
        decide +native)
    (hgap := by
      rw [endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat hloBid]
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipSuck1CalldataMem_read164_32 (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck1CalldataMem σ I catOut vatOut bidOut).readWithPadding 164 32 =
      (endPackVowWord σ I).toByteArray := by
  unfold endSkipSuck1CalldataMem
  rw [writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (endSkipBidsPostCallMem I catOut vatOut bidOut) 128
        endSkipSuckSelectorShifted)
      132 (endPackVowWord σ I))
    (word := endPackVowWord σ I)
    (rest := [ (196, endSkipTabWord bidOut) ])
    (hbase := by
      change (writeCascade (endSkipBidsPostCallMem I catOut vatOut bidOut)
        [(128, endSkipSuckSelectorShifted), (132, endPackVowWord σ I)]).size = 384
      exact writeCascade_size_of_base (endSkipBidsPostCallMem I catOut vatOut bidOut)
        [(128, endSkipSuckSelectorShifted), (132, endPackVowWord σ I)]
        (endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat hloBid)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipSuck1CalldataMem_read196_32 (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck1CalldataMem σ I catOut vatOut bidOut).readWithPadding 196 32 =
      (endSkipTabWord bidOut).toByteArray := by
  unfold endSkipSuck1CalldataMem
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord (endSkipBidsPostCallMem I catOut vatOut bidOut) 128
          endSkipSuckSelectorShifted)
        132 (endPackVowWord σ I))
      164 (endPackVowWord σ I))
    (word := endSkipTabWord bidOut)
    (rest := [])
    (hbase := by
      change (writeCascade (endSkipBidsPostCallMem I catOut vatOut bidOut)
        [(128, endSkipSuckSelectorShifted), (132, endPackVowWord σ I),
          (164, endPackVowWord σ I)]).size = 384
      exact writeCascade_size_of_base (endSkipBidsPostCallMem I catOut vatOut bidOut)
        [(128, endSkipSuckSelectorShifted), (132, endPackVowWord σ I),
          (164, endPackVowWord σ I)]
        (endSkipBidsPostCallMem_size_long I catOut vatOut bidOut hloCat hloVat hloBid)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipSuck1CalldataMem_read128_100 (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck1CalldataMem σ I catOut vatOut bidOut).readWithPadding 128 100 =
      suckSelector ++ (endPackVowWord σ I).toByteArray ++
        (endPackVowWord σ I).toByteArray ++
        (endSkipTabWord bidOut).toByteArray := by
  have hsize :
      (endSkipSuck1CalldataMem σ I catOut vatOut bidOut).size = 384 :=
    endSkipSuck1CalldataMem_size σ I catOut vatOut bidOut hloCat hloVat hloBid
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (endSkipSuck1CalldataMem σ I catOut vatOut bidOut)
      128 4 96 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (endSkipSuck1CalldataMem σ I catOut vatOut bidOut)
      132 32 64 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (endSkipSuck1CalldataMem σ I catOut vatOut bidOut)
      164 32 32 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [endSkipSuck1CalldataMem_read128_4 σ I catOut vatOut bidOut hloCat hloVat hloBid,
    endSkipSuck1CalldataMem_read132_32 σ I catOut vatOut bidOut hloCat hloVat hloBid,
    endSkipSuck1CalldataMem_read164_32 σ I catOut vatOut bidOut hloCat hloVat hloBid,
    endSkipSuck1CalldataMem_read196_32 σ I catOut vatOut bidOut hloCat hloVat hloBid]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endSkipThisWordOfAddr (I : ExecutionEnv) :
    EVM.word ↑I.codeOwner = endSkipThisWord I := by
  change UInt256.ofNat I.codeOwner.val = endSkipThisWord I
  rfl

theorem endSkipUsrWordOfAddr (bidOut : ByteArray) :
    EVM.word ↑(endSkipUsrAddr bidOut) = endSkipUsrAddrWord bidOut := by
  change UInt256.ofNat (endSkipUsrAddr bidOut).val = endSkipUsrAddrWord bidOut
  simpa [endSkipUsrAddr, endSkipUsrAddrWord] using
    (keyValueToWord_address (AccountAddress.ofNat (endSkipUsrWord bidOut).toNat)).symm.trans
      (keyValueToWord_address_ofNat_mask (endSkipUsrWord bidOut))

theorem endSkipVowWordOfAddr (σ : AccountMap) (I : ExecutionEnv) :
    EVM.word ↑(endPackVowAddr σ I) = endPackVowWord σ I := by
  have hvowCanon : (endPackVowWord σ I).toNat < EVM.addressModulus := by
    simpa [endPackVowWord] using
      solcAddrMask_result_canonical (endSlotWord ⟨4⟩ σ I)
  have hvowVal :
      (endPackVowAddr σ I).val = (endPackVowWord σ I).toNat := by
    unfold endPackVowAddr AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hvowCanon
  change UInt256.ofNat (endPackVowAddr σ I).val = endPackVowWord σ I
  rw [hvowVal]
  exact u256_ofNat_toNat _

theorem endSkipCatIlkFlipWordOfAddr (catOut : ByteArray) :
    EVM.word ↑(endSkipCatIlkFlipAddr catOut) = endSkipCatIlkFlipTargetWord catOut := by
  change UInt256.ofNat (endSkipCatIlkFlipAddr catOut).val =
    endSkipCatIlkFlipTargetWord catOut
  simpa [endSkipCatIlkFlipAddr, endSkipCatIlkFlipTargetWord] using
    (keyValueToWord_address
      (AccountAddress.ofNat (endSkipCatIlkFlipWord catOut).toNat)).symm.trans
      (keyValueToWord_address_ofNat_mask (endSkipCatIlkFlipWord catOut))

theorem endSkipSuck1Encode_eq (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    config.externalABI.encode? "suck"
        [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSkipTabWord bidOut).toNat)] =
      some ((endSkipSuck1CalldataMem σ I catOut vatOut bidOut).readWithPadding
        endSkipSuckOutPtr.toNat endSkipSuckInSize.toNat) := by
  change config.externalABI.encode? "suck"
        [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSkipTabWord bidOut).toNat)] =
      some ((endSkipSuck1CalldataMem σ I catOut vatOut bidOut).readWithPadding
        128 100)
  rw [endSkipSuck1CalldataMem_read128_100 σ I catOut vatOut bidOut hloCat hloVat hloBid]
  have hvowWord : EVM.word ↑(endPackVowAddr σ I) = endPackVowWord σ I :=
    endSkipVowWordOfAddr σ I
  have htabLt : (endSkipTabWord bidOut).toNat < EVM.twoPow 256 :=
    (endSkipTabWord bidOut).val.isLt
  have htabWord : EVM.word (endSkipTabWord bidOut).toNat = endSkipTabWord bidOut := by
    show UInt256.ofNat (endSkipTabWord bidOut).toNat = endSkipTabWord bidOut
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, abiAddress, uint256,
    uint256Int, suckSelector, selectorBytes, hvowWord, htabLt, htabWord,
    word_toBytesBE_toByteArray_eq_toByteArray, zeroBytes, ByteArray.append_assoc]

theorem endSkipSuck2CalldataMem_size (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck2CalldataMem σ I catOut vatOut bidOut).size = 384 := by
  unfold endSkipSuck2CalldataMem
  exact writeCascade_size_of_base
    (endSkipSuck1PostCallMem σ I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipSuckSelectorShifted),
      (132, endPackVowWord σ I),
      (164, endSkipThisWord I),
      (196, endSkipBidWord bidOut) ]
    (base := 384) (out := 384)
    (by
      simpa [endSkipSuck1PostCallMem_eq] using
        endSkipSuck1CalldataMem_size σ I catOut vatOut bidOut hloCat hloVat hloBid)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSkipSuck2CalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck2CalldataMem σ I catOut vatOut bidOut).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipSuck2CalldataMem
  rw [writeCascade_read_preserved_of_base
    (endSkipSuck1PostCallMem σ I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipSuckSelectorShifted),
      (132, endPackVowWord σ I),
      (164, endSkipThisWord I),
      (196, endSkipBidWord bidOut) ]
    (base := 384)
    (by
      simpa [endSkipSuck1PostCallMem_eq] using
        endSkipSuck1CalldataMem_size σ I catOut vatOut bidOut hloCat hloVat hloBid)
    (by simp [WindowDisjointFromWrites])]
  rw [endSkipSuck1PostCallMem_eq]
  exact endSkipSuck1CalldataMem_read64 σ I catOut vatOut bidOut hloCat hloVat hloBid

theorem endSkipSuck2CalldataMem_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (endSkipSuck2CalldataMem σ I catOut vatOut bidOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipSuck2CalldataMem σ I catOut vatOut bidOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [endSkipSuck2CalldataMem_size σ I catOut vatOut bidOut hloCat hloVat hloBid]
      decide)
    (by decide)
    (endSkipSuck2CalldataMem_read64 σ I catOut vatOut bidOut hloCat hloVat hloBid)

theorem endSkipSuck2PostCallMem_eq (σ : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) :
    endSkipSuck2PostCallMem σ I catOut vatOut bidOut ret =
      endSkipSuck2CalldataMem σ I catOut vatOut bidOut := by
  unfold endSkipSuck2PostCallMem
  have hmin : (min endSkipSuckOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endSkipSuckOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret
    (endSkipSuck2CalldataMem σ I catOut vatOut bidOut) 0 endSkipSuckOutPtr.toNat

theorem endSkipSuck2CalldataMemFor_size (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).size = 384 := by
  unfold endSkipSuck2CalldataMemFor
  exact writeCascade_size_of_base
    (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipSuckSelectorShifted),
      (132, endPackVowWord σcall I),
      (164, endSkipThisWord I),
      (196, endSkipBidWord bidOut) ]
    (base := 384) (out := 384)
    (by
      simpa [endSkipSuck1PostCallMem_eq] using
        endSkipSuck1CalldataMem_size σmem I catOut vatOut bidOut hloCat hloVat hloBid)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSkipSuck2CalldataMemFor_read64 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipSuck2CalldataMemFor
  rw [writeCascade_read_preserved_of_base
    (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipSuckSelectorShifted),
      (132, endPackVowWord σcall I),
      (164, endSkipThisWord I),
      (196, endSkipBidWord bidOut) ]
    (base := 384)
    (by
      simpa [endSkipSuck1PostCallMem_eq] using
        endSkipSuck1CalldataMem_size σmem I catOut vatOut bidOut hloCat hloVat hloBid)
    (by simp [WindowDisjointFromWrites])]
  rw [endSkipSuck1PostCallMem_eq]
  exact endSkipSuck1CalldataMem_read64 σmem I catOut vatOut bidOut hloCat hloVat hloBid

theorem endSkipSuck2CalldataMemFor_mload64 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [endSkipSuck2CalldataMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid]
      decide)
    (by decide)
    (endSkipSuck2CalldataMemFor_read64 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid)

theorem endSkipSuck2PostCallMemFor_eq (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut ret : ByteArray) :
    endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut ret =
      endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut := by
  unfold endSkipSuck2PostCallMemFor
  have hmin : (min endSkipSuckOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endSkipSuckOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret
    (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut)
    0 endSkipSuckOutPtr.toNat

theorem endSkipSuck2CalldataMemFor_read128_4 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      128 4 = suckSelector := by
  unfold endSkipSuck2CalldataMemFor
  rw [writeCascade_read_window_of_head
    (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
    128 0 4 endSkipSuckSelectorShifted
    [ (132, endPackVowWord σcall I),
      (164, endSkipThisWord I),
      (196, endSkipBidWord bidOut) ]]
  · unfold endSkipSuckSelectorShifted suckSelector selectorBytes
    decide +native
  · rw [endSkipSuck1PostCallMem_eq]
    rw [endSkipSuck1CalldataMem_size σmem I catOut vatOut bidOut hloCat hloVat hloBid]
    decide +native
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endSkipSuck2CalldataMemFor_read132_32 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      132 32 = (endPackVowWord σcall I).toByteArray := by
  unfold endSkipSuck2CalldataMemFor
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
      128 endSkipSuckSelectorShifted)
    (word := endPackVowWord σcall I)
    (rest := [ (164, endSkipThisWord I), (196, endSkipBidWord bidOut) ])
    (hbase := by
      rw [writeWord_size]
      · rw [endSkipSuck1PostCallMem_eq]
        rw [endSkipSuck1CalldataMem_size σmem I catOut vatOut bidOut hloCat hloVat
          hloBid]
        decide +native)
    (hgap := by
      rw [endSkipSuck1PostCallMem_eq]
      rw [endSkipSuck1CalldataMem_size σmem I catOut vatOut bidOut hloCat hloVat hloBid]
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipSuck2CalldataMemFor_read164_32 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      164 32 = (endSkipThisWord I).toByteArray := by
  unfold endSkipSuck2CalldataMemFor
  rw [writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
        128 endSkipSuckSelectorShifted)
      132 (endPackVowWord σcall I))
    (word := endSkipThisWord I)
    (rest := [ (196, endSkipBidWord bidOut) ])
    (hbase := by
      change (writeCascade
        (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
        [(128, endSkipSuckSelectorShifted), (132, endPackVowWord σcall I)]).size = 384
      exact writeCascade_size_of_base
        (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
        [(128, endSkipSuckSelectorShifted), (132, endPackVowWord σcall I)]
        (by
          simpa [endSkipSuck1PostCallMem_eq] using
            endSkipSuck1CalldataMem_size σmem I catOut vatOut bidOut hloCat hloVat
              hloBid)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipSuck2CalldataMemFor_read196_32 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      196 32 = (endSkipBidWord bidOut).toByteArray := by
  unfold endSkipSuck2CalldataMemFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
          128 endSkipSuckSelectorShifted)
        132 (endPackVowWord σcall I))
      164 (endSkipThisWord I))
    (word := endSkipBidWord bidOut)
    (rest := [])
    (hbase := by
      change (writeCascade
        (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
        [(128, endSkipSuckSelectorShifted), (132, endPackVowWord σcall I),
          (164, endSkipThisWord I)]).size = 384
      exact writeCascade_size_of_base
        (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut ByteArray.empty)
        [(128, endSkipSuckSelectorShifted), (132, endPackVowWord σcall I),
          (164, endSkipThisWord I)]
        (by
          simpa [endSkipSuck1PostCallMem_eq] using
            endSkipSuck1CalldataMem_size σmem I catOut vatOut bidOut hloCat hloVat
              hloBid)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipSuck2CalldataMemFor_read128_100 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      128 100 =
      suckSelector ++ (endPackVowWord σcall I).toByteArray ++
        (endSkipThisWord I).toByteArray ++
        (endSkipBidWord bidOut).toByteArray := by
  have hsize :
      (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).size = 384 :=
    endSkipSuck2CalldataMemFor_size σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split
      (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut)
      128 4 96 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split
      (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut)
      132 32 64 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split
      (endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut)
      164 32 32 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [endSkipSuck2CalldataMemFor_read128_4 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipSuck2CalldataMemFor_read132_32 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipSuck2CalldataMemFor_read164_32 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipSuck2CalldataMemFor_read196_32 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endSkipSuck2EncodeFor_eq (σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    config.externalABI.encode? "suck"
        [.address (endPackVowAddr σcall I), .address I.codeOwner,
          .int (Int.ofNat (endSkipBidWord bidOut).toNat)] =
      some ((endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
        endSkipSuckOutPtr.toNat endSkipSuckInSize.toNat) := by
  change config.externalABI.encode? "suck"
        [.address (endPackVowAddr σcall I), .address I.codeOwner,
          .int (Int.ofNat (endSkipBidWord bidOut).toNat)] =
      some ((endSkipSuck2CalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
        128 100)
  rw [endSkipSuck2CalldataMemFor_read128_100 σmem σcall I catOut vatOut bidOut
    hloCat hloVat hloBid]
  have hvowWord : EVM.word ↑(endPackVowAddr σcall I) = endPackVowWord σcall I :=
    endSkipVowWordOfAddr σcall I
  have hthisWord : EVM.word ↑I.codeOwner = endSkipThisWord I := endSkipThisWordOfAddr I
  have hbidLt : (endSkipBidWord bidOut).toNat < EVM.twoPow 256 :=
    (endSkipBidWord bidOut).val.isLt
  have hbidWord : EVM.word (endSkipBidWord bidOut).toNat = endSkipBidWord bidOut := by
    show UInt256.ofNat (endSkipBidWord bidOut).toNat = endSkipBidWord bidOut
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, abiAddress, uint256,
    uint256Int, suckSelector, selectorBytes, hvowWord, hthisWord, hbidLt, hbidWord,
    word_toBytesBE_toByteArray_eq_toByteArray, zeroBytes, ByteArray.append_assoc]

theorem endSkipHopeCalldataMemFor_size (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).size = 384 := by
  unfold endSkipHopeCalldataMemFor
  exact writeCascade_size_of_base
    (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipHopeSelectorShifted),
      (132, endSkipCatIlkFlipTargetWord catOut) ]
    (base := 384) (out := 384)
    (by
      simpa [endSkipSuck2PostCallMemFor_eq] using
        endSkipSuck2CalldataMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSkipHopeCalldataMemFor_read64 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipHopeCalldataMemFor
  rw [writeCascade_read_preserved_of_base
    (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipHopeSelectorShifted),
      (132, endSkipCatIlkFlipTargetWord catOut) ]
    (base := 384)
    (by
      simpa [endSkipSuck2PostCallMemFor_eq] using
        endSkipSuck2CalldataMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid)
    (by simp [WindowDisjointFromWrites])]
  rw [endSkipSuck2PostCallMemFor_eq]
  exact endSkipSuck2CalldataMemFor_read64 σmem σcall I catOut vatOut bidOut
    hloCat hloVat hloBid

theorem endSkipHopeCalldataMemFor_mload64 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [endSkipHopeCalldataMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid]
      decide)
    (by decide)
    (endSkipHopeCalldataMemFor_read64 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid)

theorem endSkipHopePostCallMemFor_eq (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut ret : ByteArray) :
    endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut ret =
      endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut := by
  unfold endSkipHopePostCallMemFor
  have hmin : (min endSkipHopeOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endSkipHopeOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret
    (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut)
    0 endSkipHopeOutPtr.toNat

theorem endSkipHopeCalldataMemFor_read128_4 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      128 4 = hopeSelector := by
  unfold endSkipHopeCalldataMemFor
  rw [writeCascade_read_window_of_head
    (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)
    128 0 4 endSkipHopeSelectorShifted
    [ (132, endSkipCatIlkFlipTargetWord catOut) ]]
  · unfold endSkipHopeSelectorShifted hopeSelector selectorBytes
    decide +native
  · rw [endSkipSuck2PostCallMemFor_eq]
    rw [endSkipSuck2CalldataMemFor_size σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid]
    decide +native
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endSkipHopeCalldataMemFor_read132_32 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      132 32 = (endSkipCatIlkFlipTargetWord catOut).toByteArray := by
  unfold endSkipHopeCalldataMemFor
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)
      128 endSkipHopeSelectorShifted)
    (word := endSkipCatIlkFlipTargetWord catOut)
    (rest := [])
    (hbase := by
      rw [writeWord_size]
      · rw [endSkipSuck2PostCallMemFor_eq]
        rw [endSkipSuck2CalldataMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid]
        decide +native)
    (hgap := by
      rw [endSkipSuck2PostCallMemFor_eq]
      rw [endSkipSuck2CalldataMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid]
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipHopeCalldataMemFor_read128_36 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      128 36 =
      hopeSelector ++ (endSkipCatIlkFlipTargetWord catOut).toByteArray := by
  have hsize :
      (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).size = 384 :=
    endSkipHopeCalldataMemFor_size σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split
      (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut)
      128 4 32 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [endSkipHopeCalldataMemFor_read128_4 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipHopeCalldataMemFor_read132_32 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid]

theorem endSkipHopeEncodeFor_eq (σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    config.externalABI.encode? "hope" [.address (endSkipCatIlkFlipAddr catOut)] =
      some ((endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
        endSkipHopeOutPtr.toNat endSkipHopeInSize.toNat) := by
  change config.externalABI.encode? "hope" [.address (endSkipCatIlkFlipAddr catOut)] =
      some ((endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
        128 36)
  rw [endSkipHopeCalldataMemFor_read128_36 σmem σcall I catOut vatOut bidOut
    hloCat hloVat hloBid]
  have hflipWord :
      EVM.word ↑(endSkipCatIlkFlipAddr catOut) = endSkipCatIlkFlipTargetWord catOut :=
    endSkipCatIlkFlipWordOfAddr catOut
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, abiAddress, hopeSelector,
    selectorBytes, hflipWord, word_toBytesBE_toByteArray_eq_toByteArray, zeroBytes,
    ByteArray.append_assoc]

theorem endSkipYankCalldataMemFor_size (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).size = 384 := by
  unfold endSkipYankCalldataMemFor
  exact writeCascade_size_of_base
    (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipYankSelectorShifted), (132, endSkipIdWord I) ]
    (base := 384) (out := 384)
    (by
      simpa [endSkipHopePostCallMemFor_eq] using
        endSkipHopeCalldataMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSkipYankCalldataMemFor_read64 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipYankCalldataMemFor
  rw [writeCascade_read_preserved_of_base
    (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)
    [ (128, endSkipYankSelectorShifted), (132, endSkipIdWord I) ]
    (base := 384)
    (by
      simpa [endSkipHopePostCallMemFor_eq] using
        endSkipHopeCalldataMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid)
    (by simp [WindowDisjointFromWrites])]
  rw [endSkipHopePostCallMemFor_eq]
  exact endSkipHopeCalldataMemFor_read64 σmem σcall I catOut vatOut bidOut
    hloCat hloVat hloBid

theorem endSkipYankCalldataMemFor_mload64 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [endSkipYankCalldataMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid]
      decide)
    (by decide)
    (endSkipYankCalldataMemFor_read64 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid)

theorem endSkipYankPostCallMemFor_eq (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut ret : ByteArray) :
    endSkipYankPostCallMemFor σmem σcall I catOut vatOut bidOut ret =
      endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut := by
  unfold endSkipYankPostCallMemFor
  have hmin : (min endSkipYankOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endSkipYankOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret
    (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut)
    0 endSkipYankOutPtr.toNat

theorem endSkipYankCalldataMemFor_read128_4 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      128 4 = yankSelector := by
  unfold endSkipYankCalldataMemFor
  rw [writeCascade_read_window_of_head
    (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)
    128 0 4 endSkipYankSelectorShifted
    [ (132, endSkipIdWord I) ]]
  · unfold endSkipYankSelectorShifted yankSelector selectorBytes
    decide +native
  · rw [endSkipHopePostCallMemFor_eq]
    rw [endSkipHopeCalldataMemFor_size σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid]
    decide +native
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endSkipYankCalldataMemFor_read132_32 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      132 32 = (endSkipIdWord I).toByteArray := by
  unfold endSkipYankCalldataMemFor
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty)
      128 endSkipYankSelectorShifted)
    (word := endSkipIdWord I)
    (rest := [])
    (hbase := by
      rw [writeWord_size]
      · rw [endSkipHopePostCallMemFor_eq]
        rw [endSkipHopeCalldataMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid]
        decide +native)
    (hgap := by
      rw [endSkipHopePostCallMemFor_eq]
      rw [endSkipHopeCalldataMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid]
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipYankCalldataMemFor_read128_36 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      128 36 =
      yankSelector ++ (endSkipIdWord I).toByteArray := by
  have hsize :
      (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).size = 384 :=
    endSkipYankCalldataMemFor_size σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split
      (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut)
      128 4 32 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [endSkipYankCalldataMemFor_read128_4 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipYankCalldataMemFor_read132_32 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid]

theorem endSkipYankEncodeFor_eq (σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size) :
    config.externalABI.encode? "yank" [.int (Int.ofNat (endSkipIdWord I).toNat)] =
      some ((endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
        endSkipYankOutPtr.toNat endSkipYankInSize.toNat) := by
  change config.externalABI.encode? "yank" [.int (Int.ofNat (endSkipIdWord I).toNat)] =
    some ((endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      128 36)
  rw [endSkipYankCalldataMemFor_read128_36 σmem σcall I catOut vatOut bidOut
    hloCat hloVat hloBid]
  have hidLt : (endSkipIdWord I).toNat < EVM.twoPow 256 := (endSkipIdWord I).val.isLt
  have hidWord : EVM.word (endSkipIdWord I).toNat = endSkipIdWord I := by
    show UInt256.ofNat (endSkipIdWord I).toNat = endSkipIdWord I
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, uint256, uint256Int, yankSelector,
    selectorBytes, hidLt, hidWord, word_toBytesBE_toByteArray_eq_toByteArray,
    zeroBytes, ByteArray.append_assoc]

theorem endSkipArtStoreHashMemFor_size (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut).size = 384 := by
  let key := endSkipIlkWord I
  let mem0 := endSkipYankPostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty
  let mem14 := endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut
  have hpostSize : mem0.size = 384 := by
    simpa [mem0, endSkipYankPostCallMemFor_eq] using
      endSkipYankCalldataMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid
  have hmem14Size : mem14.size = mem0.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨14⟩
      (by rw [hpostSize]; omega)
  have hmemStoreSize : (twoWordHashMem key ⟨14⟩ mem14).size = mem14.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨14⟩
      (by rw [hmem14Size, hpostSize]; omega)
  change (twoWordHashMem key ⟨14⟩ mem14).size = 384
  rw [hmemStoreSize, hmem14Size, hpostSize]

theorem endSkipArtStoreHashMemFor_read64 (σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩ := by
  let key := endSkipIlkWord I
  let mem0 := endSkipYankPostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty
  let mem14 := endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut
  have hpostSize : mem0.size = 384 := by
    simpa [mem0, endSkipYankPostCallMemFor_eq] using
      endSkipYankCalldataMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid
  have hpostRead64 :
      mem0.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem0, endSkipYankPostCallMemFor_eq] using
      endSkipYankCalldataMemFor_read64 σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid
  have hmem14Size : mem14.size = mem0.size := by
    exact endFlow_twoWordHashMem_size_of_ge64 key ⟨14⟩
      (by rw [hpostSize]; omega)
  have hmem14Read64 :
      mem14.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mem14, endSkipArtHashMemFor, key, mem0] using
      endFlow_twoWordHashMem_read64_of_ge96 key ⟨14⟩
        (by rw [hpostSize]; omega) hpostRead64
  simpa [endSkipArtStoreHashMemFor, key, mem14] using
    endFlow_twoWordHashMem_read64_of_ge96 key ⟨14⟩
      (by rw [hmem14Size, hpostSize]; omega) hmem14Read64

theorem endSkipGrabMem7Trace_eq (σCall σmem σcall : AccountMap)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) :
    endSkipGrabMem7Trace σCall σmem σcall I catOut vatOut bidOut =
      endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut := by
  rfl

theorem endSkipGrabCalldataMemForTrace_size
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).size =
      384 := by
  unfold endSkipGrabCalldataMemForTrace endSkipGrabWritesFor
  exact writeCascade_size_of_base
    (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
    [ (128, endFreeGrabSelectorShifted),
      (132, endSkipIlkWord I),
      (164, endSkipUsrAddrWord bidOut),
      (196, endSkipThisWord I),
      (228, endPackVowWord σCall I),
      (260, endSkipLotWord bidOut),
      (292, endSkipArtWord vatOut bidOut) ]
    (base := 384) (out := 384)
    (endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid)
    (by simp [WriteGapsOk]) (by simp [writeCascadeSize])

theorem endSkipGrabCalldataMemForTrace_read64
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endSkipGrabCalldataMemForTrace endSkipGrabWritesFor
  rw [writeCascade_read_preserved_of_base
    (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
    [ (128, endFreeGrabSelectorShifted),
      (132, endSkipIlkWord I),
      (164, endSkipUsrAddrWord bidOut),
      (196, endSkipThisWord I),
      (228, endPackVowWord σCall I),
      (260, endSkipLotWord bidOut),
      (292, endSkipArtWord vatOut bidOut) ]
    (base := 384)
    (endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid)
    (by simp [WindowDisjointFromWrites])]
  exact endSkipArtStoreHashMemFor_read64 σmem σcall I catOut vatOut bidOut
    hloCat hloVat hloBid

theorem endSkipGrabCalldataMemForTrace_mload64
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
            |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [endSkipGrabCalldataMemForTrace_size σCall σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid]
      decide)
    (by decide)
    (endSkipGrabCalldataMemForTrace_read64 σCall σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid)

theorem endSkipGrabCalldataMemForTrace_read128_4
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).readWithPadding
      128 4 =
      grabSelector := by
  unfold endSkipGrabCalldataMemForTrace endSkipGrabWritesFor
  rw [writeCascade_read_window_of_head
    (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
    128 0 4 endFreeGrabSelectorShifted
    [ (132, endSkipIlkWord I),
      (164, endSkipUsrAddrWord bidOut),
      (196, endSkipThisWord I),
      (228, endPackVowWord σCall I),
      (260, endSkipLotWord bidOut),
      (292, endSkipArtWord vatOut bidOut) ]]
  · unfold endFreeGrabSelectorShifted grabSelector selectorBytes
    decide +native
  · rw [endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid]
    decide +native
  · simp [WindowDisjointFromWrites]
  · norm_num
  · norm_num
  · norm_num

theorem endSkipGrabCalldataMemForTrace_read132_32
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).readWithPadding
      132 32 =
      (endSkipIlkWord I).toByteArray := by
  unfold endSkipGrabCalldataMemForTrace endSkipGrabWritesFor
  rw [writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) 128
      endFreeGrabSelectorShifted)
    (word := endSkipIlkWord I)
    (rest :=
      [ (164, endSkipUsrAddrWord bidOut),
        (196, endSkipThisWord I),
        (228, endPackVowWord σCall I),
        (260, endSkipLotWord bidOut),
        (292, endSkipArtWord vatOut bidOut) ])
    (hbase := by
      rw [writeWord_size]
      · rw [endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid]
        decide +native)
    (hgap := by
      rw [endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid]
      decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipGrabCalldataMemForTrace_read164_32
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).readWithPadding
      164 32 =
      (endSkipUsrAddrWord bidOut).toByteArray := by
  unfold endSkipGrabCalldataMemForTrace endSkipGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) 128
        endFreeGrabSelectorShifted)
      132 (endSkipIlkWord I))
    (word := endSkipUsrAddrWord bidOut)
    (rest :=
      [ (196, endSkipThisWord I),
        (228, endPackVowWord σCall I),
        (260, endSkipLotWord bidOut),
        (292, endSkipArtWord vatOut bidOut) ])
    (hbase := by
      change (writeCascade (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkipIlkWord I)]).size = 384
      exact writeCascade_size_of_base
        (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkipIlkWord I)]
        (base := 384) (out := 384)
        (endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipGrabCalldataMemForTrace_read196_32
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).readWithPadding
      196 32 =
      (endSkipThisWord I).toByteArray := by
  unfold endSkipGrabCalldataMemForTrace endSkipGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) 128
          endFreeGrabSelectorShifted)
        132 (endSkipIlkWord I))
      164 (endSkipUsrAddrWord bidOut))
    (word := endSkipThisWord I)
    (rest :=
      [ (228, endPackVowWord σCall I),
        (260, endSkipLotWord bidOut),
        (292, endSkipArtWord vatOut bidOut) ])
    (hbase := by
      change (writeCascade (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkipIlkWord I),
          (164, endSkipUsrAddrWord bidOut)]).size = 384
      exact writeCascade_size_of_base
        (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkipIlkWord I),
          (164, endSkipUsrAddrWord bidOut)]
        (base := 384) (out := 384)
        (endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipGrabCalldataMemForTrace_read228_32
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).readWithPadding
      228 32 =
      (endPackVowWord σCall I).toByteArray := by
  unfold endSkipGrabCalldataMemForTrace endSkipGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) 128
            endFreeGrabSelectorShifted)
          132 (endSkipIlkWord I))
        164 (endSkipUsrAddrWord bidOut))
      196 (endSkipThisWord I))
    (word := endPackVowWord σCall I)
    (rest := [ (260, endSkipLotWord bidOut), (292, endSkipArtWord vatOut bidOut) ])
    (hbase := by
      change (writeCascade (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkipIlkWord I),
          (164, endSkipUsrAddrWord bidOut), (196, endSkipThisWord I)]).size = 384
      exact writeCascade_size_of_base
        (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkipIlkWord I),
          (164, endSkipUsrAddrWord bidOut), (196, endSkipThisWord I)]
        (base := 384) (out := 384)
        (endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipGrabCalldataMemForTrace_read260_32
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).readWithPadding
      260 32 =
      (endSkipLotWord bidOut).toByteArray := by
  unfold endSkipGrabCalldataMemForTrace endSkipGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord
            (writeWord (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) 128
              endFreeGrabSelectorShifted)
            132 (endSkipIlkWord I))
          164 (endSkipUsrAddrWord bidOut))
        196 (endSkipThisWord I))
      228 (endPackVowWord σCall I))
    (word := endSkipLotWord bidOut)
    (rest := [ (292, endSkipArtWord vatOut bidOut) ])
    (hbase := by
      change (writeCascade (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkipIlkWord I),
          (164, endSkipUsrAddrWord bidOut), (196, endSkipThisWord I),
          (228, endPackVowWord σCall I)]).size = 384
      exact writeCascade_size_of_base
        (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkipIlkWord I),
          (164, endSkipUsrAddrWord bidOut), (196, endSkipThisWord I),
          (228, endPackVowWord σCall I)]
        (base := 384) (out := 384)
        (endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipGrabCalldataMemForTrace_read292_32
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).readWithPadding
      292 32 =
      (endSkipArtWord vatOut bidOut).toByteArray := by
  unfold endSkipGrabCalldataMemForTrace endSkipGrabWritesFor
  rw [writeCascade_cons, writeCascade_cons, writeCascade_cons, writeCascade_cons,
    writeCascade_cons, writeCascade_cons]
  exact writeCascade_read_word_of_head_of_base
    (writeWord
      (writeWord
        (writeWord
          (writeWord
            (writeWord
              (writeWord (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
                128 endFreeGrabSelectorShifted)
              132 (endSkipIlkWord I))
            164 (endSkipUsrAddrWord bidOut))
          196 (endSkipThisWord I))
        228 (endPackVowWord σCall I))
      260 (endSkipLotWord bidOut))
    (word := endSkipArtWord vatOut bidOut)
    (rest := [])
    (hbase := by
      change (writeCascade (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkipIlkWord I),
          (164, endSkipUsrAddrWord bidOut), (196, endSkipThisWord I),
          (228, endPackVowWord σCall I), (260, endSkipLotWord bidOut)]).size = 384
      exact writeCascade_size_of_base
        (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        [(128, endFreeGrabSelectorShifted), (132, endSkipIlkWord I),
          (164, endSkipUsrAddrWord bidOut), (196, endSkipThisWord I),
          (228, endPackVowWord σCall I), (260, endSkipLotWord bidOut)]
        (base := 384) (out := 384)
        (endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
          hloCat hloVat hloBid)
        (by simp [WriteGapsOk]) (by simp [writeCascadeSize]))
    (hgap := by decide +native)
    (hlater := by simp [WindowDisjointFromWrites])

theorem endSkipGrabCalldataMemForTrace_read128_196
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).readWithPadding
      128 196 =
      grabSelector ++
        (endSkipIlkWord I).toByteArray ++
        (endSkipUsrAddrWord bidOut).toByteArray ++
        (endSkipThisWord I).toByteArray ++
        (endPackVowWord σCall I).toByteArray ++
        (endSkipLotWord bidOut).toByteArray ++
        (endSkipArtWord vatOut bidOut).toByteArray := by
  have hsize :
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut).size =
        384 :=
    endSkipGrabCalldataMemForTrace_size σCall σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid
  rw [show 196 = 4 + 192 from rfl,
    byteArray_readWithPadding_split
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      128 4 192 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 192 = 32 + 160 from rfl,
    byteArray_readWithPadding_split
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      132 32 160 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 160 = 32 + 128 from rfl,
    byteArray_readWithPadding_split
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      164 32 128 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 128 = 32 + 96 from rfl,
    byteArray_readWithPadding_split
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      196 32 96 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      228 32 64 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      260 32 32 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [hsize]; omega)]
  rw [endSkipGrabCalldataMemForTrace_read128_4 σCall σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipGrabCalldataMemForTrace_read132_32 σCall σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipGrabCalldataMemForTrace_read164_32 σCall σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipGrabCalldataMemForTrace_read196_32 σCall σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipGrabCalldataMemForTrace_read228_32 σCall σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipGrabCalldataMemForTrace_read260_32 σCall σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid,
    endSkipGrabCalldataMemForTrace_read292_32 σCall σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem endSkipGrabEncodeForTrace_eq
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (hlot : (endSkipLotWord bidOut).toNat < 2 ^ 255)
    (hart : (endSkipArtWord vatOut bidOut).toNat < 2 ^ 255) :
    config.externalABI.encode? "grab"
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkipUsrAddr bidOut),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (Int.ofNat (endSkipLotWord bidOut).toNat),
          .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)] =
      some ((endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
        |>.readWithPadding endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat) := by
  change config.externalABI.encode? "grab"
      [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address (endSkipUsrAddr bidOut),
        .address I.codeOwner,
        .address (endPackVowAddr σCall I),
        .int (Int.ofNat (endSkipLotWord bidOut).toNat),
        .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)] =
    some ((endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      |>.readWithPadding 128 196)
  rw [endSkipGrabCalldataMemForTrace_read128_196 σCall σmem σcall I catOut vatOut bidOut
    hloCat hloVat hloBid]
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endSkipIlkWord I) := by
    have hlen32 : (endBytes32ArgBytes I).length = 32 :=
      endBytes32ArgBytes_len32 (I := I) (by omega)
    have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endSkipIlkWord I := by
      simpa [endBytes32ArgBytes, endSkipIlkWord, endBytes32ArgWord] using
        (decode_word_at_eq_any I.calldata 4 (by omega))
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  have husrWord : EVM.word ↑(endSkipUsrAddr bidOut) = endSkipUsrAddrWord bidOut :=
    endSkipUsrWordOfAddr bidOut
  have hthisWord : EVM.word ↑I.codeOwner = endSkipThisWord I :=
    endSkipThisWordOfAddr I
  have hvowWord : EVM.word ↑(endPackVowAddr σCall I) = endPackVowWord σCall I :=
    endSkipVowWordOfAddr σCall I
  have hlotWord :
      EVM.wordOfInt (Int.ofNat (endSkipLotWord bidOut).toNat) =
        endSkipLotWord bidOut :=
    wordOfInt_ofNat_toNat (endSkipLotWord bidOut)
  have hlotWordCast :
      EVM.wordOfInt ((endSkipLotWord bidOut).toNat : Int) =
        endSkipLotWord bidOut := by
    simpa using hlotWord
  have hartWord :
      EVM.wordOfInt (Int.ofNat (endSkipArtWord vatOut bidOut).toNat) =
        endSkipArtWord vatOut bidOut :=
    wordOfInt_ofNat_toNat (endSkipArtWord vatOut bidOut)
  have hartWordCast :
      EVM.wordOfInt ((endSkipArtWord vatOut bidOut).toNat : Int) =
        endSkipArtWord vatOut bidOut := by
    simpa using hartWord
  have hlotUpper : (endSkipLotWord bidOut).toNat < EVM.twoPow 255 := by
    simpa [EVM.twoPow] using hlot
  have hartUpper : (endSkipArtWord vatOut bidOut).toNat < EVM.twoPow 255 := by
    simpa [EVM.twoPow] using hart
  have hbytesLen : (EVM.Word.toBytesBE (endSkipIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (endSkipIlkWord I)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, int256,
    int256Int, grabSelector, selectorBytes, hbytes, hbytesLen, husrWord, hthisWord,
    hvowWord]
  rw [if_pos hlotUpper, if_pos hartUpper]
  simp [hlotWordCast, hartWordCast, word_toBytesBE_toByteArray_eq_toByteArray, zeroBytes,
    ByteArray.append_assoc]

theorem endSkip_solcErrorStringMem0_size_of_size384 {mem : ByteArray}
    (hmem : mem.size = 384) :
    (solcErrorStringMem0 mem).size = 384 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, hmem]

theorem endSkip_solcErrorStringMem1_size_of_size384 {mem : ByteArray}
    (hmem : mem.size = 384) :
    (solcErrorStringMem1 mem).size = 384 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endSkip_solcErrorStringMem0_size_of_size384 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    endSkip_solcErrorStringMem0_size_of_size384 hmem]

theorem endSkip_solcErrorStringMem2_size_of_size384 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 384) :
    (solcErrorStringMem2 len mem).size = 384 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endSkip_solcErrorStringMem1_size_of_size384 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    endSkip_solcErrorStringMem1_size_of_size384 hmem]

theorem endSkip_solcErrorStringMem3_size_of_size384 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 384) :
    (solcErrorStringMem3 len word mem).size = 384 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [endSkip_solcErrorStringMem2_size_of_size384 len hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract,
    endSkip_solcErrorStringMem2_size_of_size384 len hmem]

theorem endSkip_solcErrorStringMem3_read64_of_size384 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 384)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [endSkip_solcErrorStringMem2_size_of_size384 len hmem]; omega) (by omega)
      (by
        rw [endSkip_solcErrorStringMem2_size_of_size384 len hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [endSkip_solcErrorStringMem1_size_of_size384 hmem]; omega) (by omega)
      (by
        rw [endSkip_solcErrorStringMem1_size_of_size384 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [endSkip_solcErrorStringMem0_size_of_size384 hmem]; omega) (by omega)
      (by
        rw [endSkip_solcErrorStringMem0_size_of_size384 hmem]
        exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem endSkip_solcErrorStringMem3_mload64_of_size384 (len word : UInt256)
    {mem : ByteArray} (hmem : mem.size = 384)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [endSkip_solcErrorStringMem3_size_of_size384 len word hmem]; decide)
    (by decide) (endSkip_solcErrorStringMem3_read64_of_size384 len word hmem hread64)

set_option maxHeartbeats 1000000 in
theorem endSkip_solcErrorStringRevertTail_aw12 {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {pc len rawWord shift word : UInt256}
    {op : Operation.POp} {width : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 12) rdata acc k C)
    (hwf : solcErrorStringRevertTailWf code pc len rawWord shift op width)
    (hpush : op ≠ .PUSH0)
    (hword : UInt256.shiftLeft rawWord shift = word)
    (hmem : mem.size = 384)
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
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 12)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 12)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 12) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
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
      (UInt256.ofNat 12) hdMstore3 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hdSwap (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) hdMload
      mem_cost
      (endSkip_solcErrorStringMem3_mload64_of_size384 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hdSwap2 (by evm_ov),
    raw dup2 hdDup2 (by evm_ov),
    raw swap1 hdSwap3 (by evm_ov),
    raw sub hdSub (by evm_ov),
    raw push1 ⟨100⟩ hd100 (by evm_ov),
    raw add hdAdd2 (by evm_ov),
    raw swap1 hdSwap4 (by evm_ov),
    raw rev 0 hdRev mem_cost (by evm_ov)]

theorem endSkipGrabPostCallMemForTrace_eq
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray) :
    endSkipGrabPostCallMemForTrace σCall σmem σcall I catOut vatOut bidOut ret =
      endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut := by
  unfold endSkipGrabPostCallMemForTrace
  have hmin : (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
      show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
      exact Nat.zero_le _
    simp [endFreeGrabOutSize, min, hle]
  rw [hmin]
  exact byteArray_write_len_zero ret
    (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
    0 endFreeGrabOutPtr.toNat

theorem endSkipGrabPostCallMemForTrace_size
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabPostCallMemForTrace σCall σmem σcall I catOut vatOut bidOut ret).size =
      384 := by
  rw [endSkipGrabPostCallMemForTrace_eq]
  exact endSkipGrabCalldataMemForTrace_size σCall σmem σcall I catOut vatOut bidOut
    hloCat hloVat hloBid

theorem endSkipGrabPostCallMemForTrace_read64
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipGrabPostCallMemForTrace σCall σmem σcall I catOut vatOut bidOut ret).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [endSkipGrabPostCallMemForTrace_eq]
  exact endSkipGrabCalldataMemForTrace_read64 σCall σmem σcall I catOut vatOut bidOut
    hloCat hloVat hloBid

theorem endSkipLogDataMem3ForTrace_size
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipLogDataMem3ForTrace σCall σmem σcall I catOut vatOut bidOut ret).size =
      384 := by
  let mem0 := endSkipGrabPostCallMemForTrace σCall σmem σcall I catOut vatOut bidOut ret
  let mem1 := endSkipLogDataMemForTrace σCall σmem σcall I catOut vatOut bidOut ret
  let mem2 := endSkipLogDataMem2ForTrace σCall σmem σcall I catOut vatOut bidOut ret
  have h0 : mem0.size = 384 :=
    endSkipGrabPostCallMemForTrace_size σCall σmem σcall I catOut vatOut bidOut ret
      hloCat hloVat hloBid
  have h1 : mem1.size = 384 := by
    unfold mem1 endSkipLogDataMemForTrace
    exact toByteArray_write32_size_of_le mem0 (endSkipTabWord bidOut) 128 384 384 h0
      (by rw [h0]; omega) (by decide +native)
  have h2 : mem2.size = 384 := by
    unfold mem2 endSkipLogDataMem2ForTrace
    exact toByteArray_write32_size_of_le mem1 (endSkipLotWord bidOut) 160 384 384 h1
      (by rw [h1]; omega) (by decide +native)
  unfold endSkipLogDataMem3ForTrace
  exact toByteArray_write32_size_of_le mem2 (endSkipArtWord vatOut bidOut) 192 384 384 h2
    (by rw [h2]; omega) (by decide +native)

theorem endSkipLogDataMem3ForTrace_read64
    (σCall σmem σcall : AccountMap) (I : ExecutionEnv)
    (catOut vatOut bidOut ret : ByteArray)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) :
    (endSkipLogDataMem3ForTrace σCall σmem σcall I catOut vatOut bidOut ret).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩ := by
  let mem0 := endSkipGrabPostCallMemForTrace σCall σmem σcall I catOut vatOut bidOut ret
  let mem1 := endSkipLogDataMemForTrace σCall σmem σcall I catOut vatOut bidOut ret
  let mem2 := endSkipLogDataMem2ForTrace σCall σmem σcall I catOut vatOut bidOut ret
  have h0 : mem0.size = 384 :=
    endSkipGrabPostCallMemForTrace_size σCall σmem σcall I catOut vatOut bidOut ret
      hloCat hloVat hloBid
  have h1 : mem1.size = 384 := by
    unfold mem1 endSkipLogDataMemForTrace
    exact toByteArray_write32_size_of_le mem0 (endSkipTabWord bidOut) 128 384 384 h0
      (by rw [h0]; omega) (by decide +native)
  have h2 : mem2.size = 384 := by
    unfold mem2 endSkipLogDataMem2ForTrace
    exact toByteArray_write32_size_of_le mem1 (endSkipLotWord bidOut) 160 384 384 h1
      (by rw [h1]; omega) (by decide +native)
  unfold endSkipLogDataMem3ForTrace endSkipLogDataMem2ForTrace endSkipLogDataMemForTrace
  rw [toByteArray_write_read_below_of_gap _ _ 192 64
      (by change 64 + 32 ≤ mem2.size; rw [h2]; omega)
      (by omega)
      (by change 192 - mem2.size < USize.size; rw [h2]; exact lt_usize _ (by norm_num))]
  rw [toByteArray_write_read_below_of_gap _ _ 160 64
      (by change 64 + 32 ≤ mem1.size; rw [h1]; omega)
      (by omega)
      (by change 160 - mem1.size < USize.size; rw [h1]; exact lt_usize _ (by norm_num))]
  rw [toByteArray_write_read_below_of_gap _ _ 128 64
      (by change 64 + 32 ≤ mem0.size; rw [h0]; omega)
      (by omega)
      (by change 128 - mem0.size < USize.size; rw [h0]; exact lt_usize _ (by norm_num))]
  exact endSkipGrabPostCallMemForTrace_read64 σCall σmem σcall I catOut vatOut bidOut ret
    hloCat hloVat hloBid

theorem endDecode_skip_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (skipTransition.params.map Param.name)
      (transitionSignature skipTransition).paramTypes I.calldata = some (endSkipStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "id"] [bytes32, uint256]
    I.calldata = _
  simpa [config, skipTransition, bytes32, bytes32Width, uint256, uint256Int,
    endSkipStore, endSkipIlkBytes, endSkipIdWord, abiBytes32, abiBytes32Width,
    abiUInt256] using
    (endDecode_legacyBytes32_uint256_ok (cd := I.calldata) (x := "ilk")
      (y := "id") hsz68)

theorem endDecode_skip_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (skipTransition.params.map Param.name)
      (transitionSignature skipTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["ilk", "id"] [bytes32, uint256]
    I.calldata = none
  simpa [config, skipTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    (endDecode_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "ilk")
      (y := "id") hsz4 hshort)

theorem endReachSkipBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endSkipConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endSkipEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x503ecf06⟩ :=
    endSelWord_eq_of_beq I hsz 0x50 0x3e 0xcf 0x06 ⟨0x503ecf06⟩
      (by decide +native)
      (by simpa [selIs, endSkipConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup403FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; decide +native)
      (by rw [hword]; decide +native)
      (by rw [hword]; decide +native)
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endGroup403FirstArmPc 2))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact RD.dispatchTo endSkipEntryPc 2 hfirst
    (fun j hj => endGroup403ArmsWellFormed j (by omega))
    heq0 htake (by jump_dest) (by decide +native) (by simp)

theorem RD.endSkipDecodeToBody {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 endSkipDecodedPc (de :: ⟨4⟩ :: ret :: sel :: R)
        mem aw rdata acc k C)
    (hwf : code = endBytecode)
    (hroutine : (D_J code 0).contains endSkipBodyPc = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 endSkipBodyPc
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd694 := h.jumpdest (by decide +native) (by evm_ov)
  have rd695 := rd694.pop (by decide +native) (by evm_ov)
  have rd696 := rd695.dup1 (by decide +native) (by evm_ov)
  have rd697 := rd696.calldataload (by decide +native) (by evm_ov)
  have rd698 := rd697.swap1 (by decide +native) (by evm_ov)
  have rd700 := rd698.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd701 := rd700.add (by decide +native) (by evm_ov)
  have rd702 := rd701.calldataload (by decide +native) (by evm_ov)
  have rd703 := rd702.push2 endSkipBodyPc (by decide +native) (by evm_ov)
  exact ⟨_, _, by
    simpa [endSkipBodyPc, endSkipDecodedPc, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd703.jump (by decide +native) hroutine (by evm_ov)⟩

theorem endSkipX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endSkipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
        (initState cA gh bl σ σ₀ g A I) endSkipBodyPc
        [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endSkipEntryPc) (ret := endSkipReturnPc)
    (decoded := endSkipDecodedPc) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.endSkipDecodeToBody
    (code := endBytecode) (ret := endSkipReturnPc) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endSkipIdWord, endSkipIlkWord] using hroutine⟩

theorem endSkipX_tagZero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord σ I = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endSkipBodyPc
      [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let key := endSkipIlkWord I
  have hslot : endSkipTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endSkipTagSlot_eq (I := I) hsz68
  have rd3229pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd3230 := rd3229pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd3234pre := evm_run rd3230 with [
    raw push1 ⟨12⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd3235 := rd3234pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd3238pre := evm_run rd3235 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd3239pre := rd3238pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by decide +native) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd3240raw⟩ := rd3239pre.sload (by decide +native) (by evm_ov)
  have htagRaw :
      solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = ⟨0⟩ := by
    rw [← hslot]
    simpa [key, endSkipTagWord, endSlotWord] using htag
  have htagRaw' :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.findD (solcMappingSlot ⟨12⟩ key) ⟨0⟩)) = ⟨0⟩ := by
    simpa [solcSlotWord] using htagRaw
  have rd3240zero := rd3240raw
  rw [htagRaw'] at rd3240zero
  obtain ⟨_, _, rd3240⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3240⟩
        (⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSkipBodyPc, key] using rd3240zero⟩
  have rd3243pre := rd3240.push2 ⟨3314⟩ (by decide +native) (by evm_ov)
  have rd3244pre := rd3243pre.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  obtain ⟨_, _, rd3244⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3244⟩
        [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa using rd3244pre⟩
  exact RD.solcErrorStringRevertTail
    (pc := ⟨3244⟩) (len := ⟨23⟩)
    (rawWord := ⟨1662547331793263672767660296024730882676930893819124057⟩)
    (shift := ⟨74⟩)
    (word := UInt256.shiftLeft
      ⟨1662547331793263672767660296024730882676930893819124057⟩ ⟨74⟩)
    (op := .PUSH23) (width := 23)
    rd3244
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) rfl
    (twoWordHashMem_size_96 key ⟨12⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 key ⟨12⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_tagNonzero {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord σ I ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) endSkipBodyPc
      [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3314⟩
      [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
      (twoWordHashMem (endSkipIlkWord I) ⟨12⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let key := endSkipIlkWord I
  have hslot : endSkipTagSlot I = solcMappingSlot ⟨12⟩ key := by
    simpa [key] using endSkipTagSlot_eq (I := I) hsz68
  have rd3229pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd3230 := rd3229pre.mstore 0 (wordAt0Mem key solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd3234pre := evm_run rd3230 with [
    raw push1 ⟨12⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd3235 := rd3234pre.mstore 0 (twoWordHashMem key ⟨12⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have rd3238pre := evm_run rd3235 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨12⟩ solcFreePtrMem).readWithPadding 0 64))) =
          solcMappingSlot ⟨12⟩ key :=
    twoWordHashMem_solcMappingSlot ⟨12⟩ key solcFreePtrMem_size
  have rd3239pre := rd3238pre.keccak256 0 (solcMappingSlot ⟨12⟩ key)
    (UInt256.ofNat 3) (by decide +native) mem_cost
    (by
      simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
        show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hhash)
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd3240raw⟩ := rd3239pre.sload (by decide +native) (by evm_ov)
  have htagRaw :
      solcSlotWord σ I (solcMappingSlot ⟨12⟩ key) = endSkipTagWord σ I := by
    rw [← hslot]
    simp [endSkipTagWord, endSlotWord]
  have htagRaw' :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun ac => ac.storage.findD (solcMappingSlot ⟨12⟩ key) ⟨0⟩)) =
          endSkipTagWord σ I := by
    simpa [solcSlotWord] using htagRaw
  have rd3240nzRaw := rd3240raw
  rw [htagRaw'] at rd3240nzRaw
  obtain ⟨_, _, rd3240nz⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3240⟩
        (endSkipTagWord σ I :: endSkipIdWord I :: endSkipIlkWord I ::
          endSkipReturnPc :: sel :: [])
        (twoWordHashMem key ⟨12⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSkipBodyPc, key] using rd3240nzRaw⟩
  have rd3243pre := rd3240nz.push2 ⟨3314⟩ (by decide +native) (by evm_ov)
  have rd3314pre := rd3243pre.jumpiT (by decide +native) htag (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [key] using rd3314pre⟩

theorem endSkipX_catIlksExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3314⟩
      [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
      (endSkipCatIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3379⟩
      (endSkipCatWord σ I :: endSkipCatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSkipCatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endSkipCatWord σ I ::
        ⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipCatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  have hmload64Hash :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSkipCatIlksBaseMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkipCatIlksBaseMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endSkipCatIlksBaseMem_size I]; decide)
      (by decide)
      (endSkipCatIlksBaseMem_read64 I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSkipCatIlksCalldataMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkipCatIlksCalldataMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endSkipCatIlksCalldataMem_size I]; decide)
      (by decide) (endSkipCatIlksCalldataMem_read64 I)
  have hselectorShift :
      UInt256.shiftLeft (⟨0x6cb1c69b⟩ : UInt256) ⟨225⟩ =
        endFlowVatIlksSelectorShifted := by
    decide +native
  have hcatMask :
      UInt256.land solcAddrMask (endSlotWord ⟨2⟩ σ I) = endSkipCatWord σ I := by
    simpa [endSkipCatWord, solcAddrMask] using
      u256_land_comm solcAddrMask (endSlotWord ⟨2⟩ σ I)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hcatMaskRight :
      (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩).land
          (endSlotWord ⟨2⟩ σ I) = endSkipCatWord σ I := by
    rw [haddrMask]
    exact hcatMask
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩) = endFlowVatIlksInSize := by
    decide +native
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨36⟩) = endFlowVatIlksEndPtr := by
    decide +native
  have rd3317 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨2⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd3318raw⟩ := rd3317.sload (by decide +native) (by evm_ov)
  have rd3318 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3318⟩
        (endSlotWord ⟨2⟩ σ I :: endSkipIdWord I :: endSkipIlkWord I ::
          endSkipReturnPc :: sel :: [])
        (endSkipCatIlksBaseMem I) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd3318raw⟩
  obtain ⟨_, _, rd3318⟩ := rd3318
  have rd3379 := evm_run rd3318 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64Hash (by decide) (by evm_ov),
    raw push4 ⟨0x6cb1c69b⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨225⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (endFlowVatIlksSelectorMem (endSkipCatIlksBaseMem I))
      (UInt256.ofNat 5) (by decide +native) mem_cost
      (by
        simp [endFlowVatIlksSelectorMem, endFlowVatIlksOutPtr,
          endSkipCatIlksBaseMem, hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 3 (endSkipCatIlksCalldataMem I) (UInt256.ofNat 6)
      (by decide +native) mem_cost
      (by
        simp [endSkipCatIlksCalldataMem, endFlowVatIlksCalldataMem,
          endFlowVatIlksArg0Mem, endFlowVatIlksOutPtr, endSkipCatIlksBaseMem])
      (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 endFlowVatIlksSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨96⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    convert rd3379 using 1
    all_goals
      try decide +native
      try simp [endFlowVatIlksOutPtr, endFlowVatIlksInSize,
        endSkipCatIlksOutSize, endFlowVatIlksEndPtr, hcatMaskRight, hinSize, hendPtr]
      try decide +native⟩

theorem endSkipX_catIlksNoCode {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3314⟩
      [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
      (endSkipCatIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3379⟩ := endSkipX_catIlksExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3379⟩) (okPc := ⟨3391⟩) rd3379
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_catIlksCallReady {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3314⟩
      [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel]
      (endSkipCatIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3394⟩
      (gasWord :: endSkipCatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSkipCatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endSkipCatWord σ I ::
        ⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipCatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd3379⟩ := endSkipX_catIlksExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd3394⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3379⟩) (okPc := ⟨3391⟩) rd3379
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd3394⟩

theorem endSkipX_catIlksPostCall {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3394⟩
      (gasWord :: endSkipCatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSkipCatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endSkipCatWord σ I ::
        ⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipCatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endSkipCatWord σ I))
          (toExecute σ (AccountAddress.ofUInt256 (endSkipCatWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSkipCatIlksCalldataMem I).readWithPadding
            endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3395⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFlowVatIlksEndPtr ::
            endFlowVatIlksSelectorWord :: endSkipCatWord σ I :: ⟨0⟩ ::
            endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
          (endSkipCatIlksPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd3395raw, hout⟩ :=
    RD.call h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endSkipCatIlksWriteLen_eq (out := out) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          endFlowVatIlksOutPtr.toNat endSkipCatIlksOutSize.toNat) = UInt256.ofNat 7 := by
      unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endSkipCatIlksOutSize
      decide +native
    simpa [endSkipCatIlksPostCallMem, endFlowVatIlksOutPtr, endFlowVatIlksInSize,
      endSkipCatIlksOutSize, endFlowVatIlksEndPtr, hmin, haw] using rd3395raw

theorem endSkipX_catIlksCallDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel gasWord : UInt256} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3394⟩
      (gasWord :: endSkipCatWord σ I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSkipCatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endSkipCatWord σ I ::
        ⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipCatIlksCalldataMem I) (UInt256.ofNat 6)
      ByteArray.empty (cA, σ) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3395⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endSkipCatWord σ I :: ⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipCatIlksCalldataMem I) (UInt256.ofNat 7)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k', C', rd3395raw⟩ :=
    RD.callDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endSkipCatIlksOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
        endFlowVatIlksOutPtr.toNat endSkipCatIlksOutSize.toNat) = UInt256.ofNat 7 := by
    unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endSkipCatIlksOutSize
    decide +native
  simpa [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endSkipCatIlksOutSize,
    endFlowVatIlksEndPtr, hmin, byteArray_write_len_zero, haw] using rd3395raw

theorem endSkipX_catIlksCallFailed {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3395⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endSkipCatWord σ I :: ⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3395⟩) (okPc := ⟨3411⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_catIlksCallSucceeded {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3395⟩
      (⟨1⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endSkipCatWord σ I :: ⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3416⟩
      (⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 7) rdata (cA', σ') k' C' := by
  obtain ⟨_, _, rd3413⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨3395⟩) (okPc := ⟨3411⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  have rd3416 := evm_run rd3413 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd3416⟩

theorem endSkipX_catIlksReturnDecodeOk {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3416⟩
      (⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipCatIlksPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k C)
    (hlo : 96 ≤ out.size) (hout : out.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3436⟩
      (endSkipCatIlkFlipWord out :: ⟨0⟩ :: endSkipIdWord I ::
        endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipCatIlksPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k' C' := by
  have hmload64 := endSkipCatIlksPostCallMem_mload64 I out
  have hmload128 := endSkipCatIlksPostCallMem_mload128_long I out hlo
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨96⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨96⟩ : UInt256).toNat = 96 from by decide, ulit_toNat' out.size hout]
    exact hlo
  have rd3425 := evm_run h with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by decide +native) (by evm_ov),
    raw push1 ⟨96⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨3433⟩ (by decide +native) (by evm_ov)]
  have rdJump := rd3425
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd3436 := evm_run rdJump with [
    raw jumpiT (by decide +native) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw mload 0 (endSkipCatIlkFlipWord out) (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload128 (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd3436⟩

theorem endSkipX_catIlksReturnDecodeShort {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {out : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3416⟩
      (⟨0⟩ :: endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipCatIlksPostCallMem I out) (UInt256.ofNat 7) out (cA', σ') k C)
    (hshort : out.size < 96) (hout : out.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 := endSkipCatIlksPostCallMem_mload64 I out
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨96⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨96⟩ : UInt256).toNat = 96 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rd3425 := evm_run h with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by decide +native) (by evm_ov),
    raw push1 ⟨96⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨3433⟩ (by decide +native) (by evm_ov)]
  have rdShort := rd3425
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFall
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_vatIlksExtcodesizeGuard {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3436⟩
      (endSkipCatIlkFlipWord catOut :: ⟨0⟩ :: endSkipIdWord I ::
        endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipCatIlksPostCallMem I catOut) (UInt256.ofNat 7) catOut
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3505⟩
      (endPackVatWord σ' I :: endPackVatWord σ' I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ' I ::
        ⟨0⟩ :: endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipVatIlksCalldataMem I catOut) (UInt256.ofNat 7)
      catOut (cA', σ') k' C' := by
  have hmload64Base := endSkipCatIlksPostCallMem_mload64 I catOut
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (endSkipVatIlksCalldataMem I catOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkipVatIlksCalldataMem I catOut).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endSkipVatIlksCalldataMem_size_long I catOut hloCat]; decide)
      (by decide)
      (endSkipVatIlksCalldataMem_read64_long I catOut hloCat)
  have hselectorShift :
      UInt256.shiftLeft (⟨0x6cb1c69b⟩ : UInt256) ⟨225⟩ =
        endFlowVatIlksSelectorShifted := by
    decide +native
  have hvatMask :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σ' I) = endPackVatWord σ' I := by
    simpa [endPackVatWord, solcAddrMask] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σ' I)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have hvatMaskRight :
      (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩).land
          (endSlotWord ⟨1⟩ σ' I) = endPackVatWord σ' I := by
    rw [haddrMask]
    exact hvatMask
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩) = endFlowVatIlksInSize := by
    decide +native
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨36⟩) = endFlowVatIlksEndPtr := by
    decide +native
  have rd3438 := evm_run h with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd3439raw⟩ := rd3438.sload (by decide +native) (by evm_ov)
  have rd3439 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3439⟩
        (endSlotWord ⟨1⟩ σ' I :: endSkipCatIlkFlipWord catOut :: ⟨0⟩ ::
          endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
        (endSkipCatIlksPostCallMem I catOut) (UInt256.ofNat 7)
        catOut (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd3439raw⟩
  obtain ⟨_, _, rd3439⟩ := rd3439
  have rd3505 := evm_run rd3439 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw push4 ⟨0x6cb1c69b⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨225⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (endFlowVatIlksSelectorMem (endSkipCatIlksPostCallMem I catOut))
      (UInt256.ofNat 7) (by decide +native) mem_cost
      (by
        simp [endFlowVatIlksSelectorMem, endFlowVatIlksOutPtr, hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipVatIlksCalldataMem I catOut) (UInt256.ofNat 7)
      (by decide +native) mem_cost
      (by
        simp [endSkipVatIlksCalldataMem, endFlowVatIlksCalldataMem,
          endFlowVatIlksArg0Mem, endFlowVatIlksOutPtr])
      (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 endFlowVatIlksSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    convert rd3505 using 1
    all_goals
      try decide +native
      try simp [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endFlowVatIlksOutSize,
        endFlowVatIlksEndPtr, hvatMaskRight, hinSize, hendPtr]
      try decide +native⟩

theorem endSkipX_vatIlksNoCode {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {catOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3436⟩
      (endSkipCatIlkFlipWord catOut :: ⟨0⟩ :: endSkipIdWord I ::
        endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipCatIlksPostCallMem I catOut) (UInt256.ofNat 7) catOut
      (cA', σ') k C)
    (hloCat : 96 ≤ catOut.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3505⟩ := endSkipX_vatIlksExtcodesizeGuard hloCat h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3505⟩) (okPc := ⟨3517⟩) rd3505
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_vatIlksCallReady {cA cA' gh bl σ σ' σ₀ A I} {g : Sat256}
    {sel : UInt256} {catOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3436⟩
      (endSkipCatIlkFlipWord catOut :: ⟨0⟩ :: endSkipIdWord I ::
        endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipCatIlksPostCallMem I catOut) (UInt256.ofNat 7) catOut
      (cA', σ') k C)
    (hloCat : 96 ≤ catOut.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3520⟩
      (gasWord :: endPackVatWord σ' I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σ' I ::
        ⟨0⟩ :: endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipVatIlksCalldataMem I catOut) (UInt256.ofNat 7)
      catOut (cA', σ') k' C' := by
  obtain ⟨_, _, rd3505⟩ := endSkipX_vatIlksExtcodesizeGuard hloCat h
  obtain ⟨gasWord, k', C', rd3520⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3505⟩) (okPc := ⟨3517⟩) rd3505
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd3520⟩

theorem endSkipX_vatIlksPostCall {cA cAcur gh bl σ σcur σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3520⟩
      (gasWord :: endPackVatWord σcur I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipVatIlksCalldataMem I catOut) (UInt256.ofNat 7)
      catOut (cAcur, σcur) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cAcur gh bl
          σcur σ₀ Ain (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σcur I))
          (toExecute σcur (AccountAddress.ofUInt256 (endPackVatWord σcur I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSkipVatIlksCalldataMem I catOut).readWithPadding
            endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3521⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFlowVatIlksEndPtr ::
            endFlowVatIlksSelectorWord :: endPackVatWord σcur I :: ⟨0⟩ ::
            endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
            endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
          (endSkipVatIlksPostCallMem I catOut out) (UInt256.ofNat 9) out
          (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd3521raw, hout⟩ :=
    RD.call h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endSkipVatIlksWriteLen_eq (out := out) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          endFlowVatIlksOutPtr.toNat endFlowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
      unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endFlowVatIlksOutSize
      decide +native
    simpa [endSkipVatIlksPostCallMem, endFlowVatIlksOutPtr, endFlowVatIlksInSize,
      endFlowVatIlksOutSize, endFlowVatIlksEndPtr, hmin, haw] using rd3521raw

theorem endSkipX_vatIlksCallDepthLimit {cA cAcur gh bl σ σcur σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3520⟩
      (gasWord :: endPackVatWord σcur I :: ⟨0⟩ :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endFlowVatIlksOutSize ::
        endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipVatIlksCalldataMem I catOut) (UInt256.ofNat 7)
      catOut (cAcur, σcur) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3521⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σcur I :: ⟨0⟩ :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipVatIlksCalldataMem I catOut) (UInt256.ofNat 9) ByteArray.empty
      (cAcur, σcur) k' C' := by
  obtain ⟨k', C', rd3521raw⟩ :=
    RD.callDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endFlowVatIlksOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
        endFlowVatIlksOutPtr.toNat endFlowVatIlksOutSize.toNat) = UInt256.ofNat 9 := by
    unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endFlowVatIlksOutSize
    decide +native
  simpa [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endFlowVatIlksOutSize,
    endFlowVatIlksEndPtr, hmin, byteArray_write_len_zero, haw] using rd3521raw

theorem endSkipX_vatIlksCallFailed {cA cA' gh bl σ σcur σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3521⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σcur I :: ⟨0⟩ :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3521⟩) (okPc := ⟨3537⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_vatIlksCallSucceeded {cA cA' gh bl σ σcur σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3521⟩
      (⟨1⟩ :: endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord ::
        endPackVatWord σcur I :: ⟨0⟩ :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3539⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 9) rdata (cA', σ') k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨3521⟩) (okPc := ⟨3537⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simp)

theorem endSkipX_vatIlksReturnDecodeOk {cA cA' gh bl σ σcur σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3539⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipVatIlksPostCallMem I catOut vatOut) (UInt256.ofNat 9) vatOut
      (cA', σ') k C)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hout : vatOut.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3565⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipVatIlksPostCallMem I catOut vatOut) (UInt256.ofNat 9) vatOut
      (cA', σ') k' C' := by
  have hmload64 := endSkipVatIlksPostCallMem_mload64 I catOut vatOut hloCat
  have hmload160 := endSkipVatIlksPostCallMem_mload160_long I catOut vatOut hloCat hloVat
  have hlt : UInt256.lt (UInt256.ofNat vatOut.size) (⟨160⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      ulit_toNat' vatOut.size hout]
    exact hloVat
  have rd3551 := evm_run h with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨3559⟩ (by decide +native) (by evm_ov)]
  have rdJump := rd3551
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd3565 := evm_run rdJump with [
    raw jumpiT (by decide +native) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mload 0 (endFlowVatIlkRateWord vatOut) (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload160 (by decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endFlowVatIlksEndPtr, endFlowVatIlksSelectorWord, endFlowVatIlksOutPtr,
      endFlowVatIlksInSize, endFlowVatIlksOutSize] using rd3565⟩

theorem endSkipX_vatIlksReturnDecodeShort {cA cA' gh bl σ σcur σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3539⟩
      (endFlowVatIlksEndPtr :: endFlowVatIlksSelectorWord :: endPackVatWord σcur I ::
        ⟨0⟩ :: endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipVatIlksPostCallMem I catOut vatOut) (UInt256.ofNat 9) vatOut
      (cA', σ') k C)
    (hloCat : 96 ≤ catOut.size) (hshort : vatOut.size < 160)
    (hout : vatOut.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 := endSkipVatIlksPostCallMem_mload64 I catOut vatOut hloCat
  have hlt : UInt256.lt (UInt256.ofNat vatOut.size) (⟨160⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      ulit_toNat' vatOut.size hout]
    exact hshort
  have rd3551 := evm_run h with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨3559⟩ (by decide +native) (by evm_ov)]
  have rdShort := rd3551
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFall
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_bidsExtcodesizeGuard {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3565⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipVatIlksPostCallMem I catOut vatOut) (UInt256.ofNat 9) vatOut
      (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3637⟩
      (endSkipCatIlkFlipTargetWord catOut :: endSkipCatIlkFlipTargetWord catOut ::
        endFlowVatIlksOutPtr :: endFlowVatIlksInSize :: endFlowVatIlksOutPtr ::
        endSkipBidsOutSize :: endFlowVatIlksEndPtr :: endSkipBidsSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipBidsCalldataMem I catOut vatOut) (UInt256.ofNat 9)
      vatOut (cA', σ') k' C' := by
  have hmload64Base := endSkipVatIlksPostCallMem_mload64 I catOut vatOut hloCat
  have hmload64Call :=
    endSkipBidsCalldataMem_mload64_long I catOut vatOut hloCat hloVat
  have hselectorShift :
      UInt256.shiftLeft endSkipBidsSelectorWord ⟨224⟩ =
        endSkipBidsSelectorShifted := by
    decide +native
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    decide +native
  have hflipMaskRight :
      (endSkipCatIlkFlipWord catOut).land
          (((⟨1⟩ : UInt256).shiftLeft ⟨160⟩).sub ⟨1⟩) =
        endSkipCatIlkFlipTargetWord catOut := by
    rw [haddrMask]
    simpa [endSkipCatIlkFlipTargetWord] using
      u256_land_comm (endSkipCatIlkFlipWord catOut) solcAddrMask
  have hinSize :
      (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨36⟩) =
        endFlowVatIlksInSize := by
    decide +native
  have hendPtr : ((⟨128⟩ : UInt256) + ⟨36⟩) = endFlowVatIlksEndPtr := by
    decide +native
  have rd3637 := evm_run h with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw push4 endSkipBidsSelectorWord (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipBidsSelectorMem I catOut vatOut) (UInt256.ofNat 9)
      (by decide +native) mem_cost
      (by
        simp [endSkipBidsSelectorMem, endFlowVatIlksOutPtr, hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipBidsCalldataMem I catOut vatOut) (UInt256.ofNat 9)
      (by decide +native) mem_cost
      (by simp [endSkipBidsCalldataMem, endFlowVatIlksOutPtr])
      (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 9) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 endSkipBidsSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push2 endSkipBidsOutSize (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    convert rd3637 using 1
    all_goals
      try decide +native
      try simp [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endSkipBidsOutSize,
        endFlowVatIlksEndPtr, hflipMaskRight, hinSize, hendPtr]
      try decide +native⟩

theorem endSkipX_bidsNoCode {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3565⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipVatIlksPostCallMem I catOut vatOut) (UInt256.ofNat 9) vatOut
      (cA', σ') k C)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (endSkipCatIlkFlipTargetWord catOut) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3637⟩ := endSkipX_bidsExtcodesizeGuard hloCat hloVat h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3637⟩) (okPc := ⟨3649⟩) rd3637
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_bidsCallReady {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3565⟩
      (endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipVatIlksPostCallMem I catOut vatOut) (UInt256.ofNat 9) vatOut
      (cA', σ') k C)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ'
        (endSkipCatIlkFlipTargetWord catOut) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3652⟩
      (gasWord :: endSkipCatIlkFlipTargetWord catOut :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSkipBidsOutSize ::
        endFlowVatIlksEndPtr :: endSkipBidsSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipBidsCalldataMem I catOut vatOut) (UInt256.ofNat 9)
      vatOut (cA', σ') k' C' := by
  obtain ⟨_, _, rd3637⟩ := endSkipX_bidsExtcodesizeGuard hloCat hloVat h
  obtain ⟨gasWord, k', C', rd3652⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3637⟩) (okPc := ⟨3649⟩) rd3637
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd3652⟩

theorem endSkipX_bidsPostStaticcall {cA cAcur gh bl σ σcur σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3652⟩
      (gasWord :: endSkipCatIlkFlipTargetWord catOut :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSkipBidsOutSize ::
        endFlowVatIlksEndPtr :: endSkipBidsSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipBidsCalldataMem I catOut vatOut) (UInt256.ofNat 9)
      vatOut (cAcur, σcur) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (bidOut : ByteArray) (Ain : Substate) (callGas : UInt256)
      (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, bidOut) =
          Ethereum.EVM.Θ I.blobVersionedHashes cAcur gh bl σcur σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (endSkipCatIlkFlipTargetWord catOut))
            (toExecute σcur
              (AccountAddress.ofUInt256 (endSkipCatIlkFlipTargetWord catOut)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endSkipBidsCalldataMem I catOut vatOut).readWithPadding
              endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
            (I.depth + 1) I.header false)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3653⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFlowVatIlksEndPtr ::
            endSkipBidsSelectorWord :: endSkipCatIlkFlipTargetWord catOut ::
            ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut ::
            endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
            endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
          (endSkipBidsPostCallMem I catOut vatOut bidOut) (UInt256.ofNat 12)
          bidOut (cA', σ') k' C'
      ∧ bidOut.size < UInt256.size := by
  obtain ⟨cA', σ', z, bidOut, Ain, callGas, k', C', hΘ, rd3653raw, hout⟩ :=
    RD.solcStaticcall h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨cA', σ', z, bidOut, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have hmin := endSkipBidsWriteLen_eq (out := bidOut) hout
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
          endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
          endFlowVatIlksOutPtr.toNat endSkipBidsOutSize.toNat) = UInt256.ofNat 12 := by
      unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endSkipBidsOutSize
      decide +native
    simpa [endSkipBidsPostCallMem, endFlowVatIlksOutPtr, endFlowVatIlksInSize,
      endSkipBidsOutSize, endFlowVatIlksEndPtr, hmin, haw] using rd3653raw

theorem endSkipX_bidsStaticcallDepthLimit {cA cAcur gh bl σ σcur σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3652⟩
      (gasWord :: endSkipCatIlkFlipTargetWord catOut :: endFlowVatIlksOutPtr ::
        endFlowVatIlksInSize :: endFlowVatIlksOutPtr :: endSkipBidsOutSize ::
        endFlowVatIlksEndPtr :: endSkipBidsSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipBidsCalldataMem I catOut vatOut) (UInt256.ofNat 9)
      vatOut (cAcur, σcur) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3653⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endSkipBidsSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipBidsCalldataMem I catOut vatOut) (UInt256.ofNat 12) ByteArray.empty
      (cAcur, σcur) k' C' := by
  obtain ⟨k', C', rd3653raw⟩ :=
    RD.solcStaticcallDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endSkipBidsOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 9).toNat
        endFlowVatIlksOutPtr.toNat endFlowVatIlksInSize.toNat)
        endFlowVatIlksOutPtr.toNat endSkipBidsOutSize.toNat) = UInt256.ofNat 12 := by
    unfold endFlowVatIlksOutPtr endFlowVatIlksInSize endSkipBidsOutSize
    decide +native
  simpa [endFlowVatIlksOutPtr, endFlowVatIlksInSize, endSkipBidsOutSize,
    endFlowVatIlksEndPtr, hmin, byteArray_write_len_zero, haw] using rd3653raw

theorem endSkipX_bidsCallFailed {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3653⟩
      (⟨0⟩ :: endFlowVatIlksEndPtr :: endSkipBidsSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3653⟩) (okPc := ⟨3669⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_bidsCallSucceeded {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut : ByteArray} {mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3653⟩
      (⟨1⟩ :: endFlowVatIlksEndPtr :: endSkipBidsSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3674⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σ') k' C' := by
  obtain ⟨_, _, rd3671⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨3653⟩) (okPc := ⟨3669⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  have rd3674 := evm_run rd3671 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd3674⟩

theorem endSkipX_bidsReturnDecodeOk {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3674⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipBidsPostCallMem I catOut vatOut bidOut) (UInt256.ofNat 12)
      bidOut (cA', σ') k C)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size) (hout : bidOut.size < UInt256.size) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3712⟩
      (endSkipTabWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endSkipUsrWord bidOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipBidsPostCallMem I catOut vatOut bidOut) (UInt256.ofNat 12)
      bidOut (cA', σ') k' C' := by
  have hmload64 := endSkipBidsPostCallMem_mload64 I catOut vatOut bidOut hloCat hloVat
  have hmload128 :=
    endSkipBidsPostCallMem_mload128_long I catOut vatOut bidOut hloCat hloVat hloBid
  have hmload160 :=
    endSkipBidsPostCallMem_mload160_long I catOut vatOut bidOut hloCat hloVat hloBid
  have hmload288 :=
    endSkipBidsPostCallMem_mload288_long I catOut vatOut bidOut hloCat hloVat hloBid
  have hmload352 :=
    endSkipBidsPostCallMem_mload352_long I catOut vatOut bidOut hloCat hloVat hloBid
  have hlt : UInt256.lt (UInt256.ofNat bidOut.size) (⟨256⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide,
      ulit_toNat' bidOut.size hout]
    exact hloBid
  have rd3684 := evm_run h with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by decide +native) (by evm_ov),
    raw push2 endSkipBidsOutSize (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨3692⟩ (by decide +native) (by evm_ov)]
  have rdJump := rd3684
  rw [hlt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rdJump
  have rd3712 := evm_run rdJump with [
    raw jumpiT (by decide +native) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov),
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 (endSkipBidWord bidOut) (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload128 (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mload 0 (endSkipLotWord bidOut) (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload160 (by decide) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mload 0 (endSkipUsrWord bidOut) (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload288 (by decide) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mload 0 (endSkipTabWord bidOut) (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload352 (by decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd3712⟩

theorem endSkipX_bidsReturnDecodeShort {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3674⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipBidsPostCallMem I catOut vatOut bidOut) (UInt256.ofNat 12)
      bidOut (cA', σ') k C)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hshort : bidOut.size < 256) (hout : bidOut.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmload64 := endSkipBidsPostCallMem_mload64 I catOut vatOut bidOut hloCat hloVat
  have hlt : UInt256.lt (UInt256.ofNat bidOut.size) (⟨256⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨256⟩ : UInt256).toNat = 256 from by decide,
      ulit_toNat' bidOut.size hout]
    exact hshort
  have rd3684 := evm_run h with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize (by decide +native) (by evm_ov),
    raw push2 endSkipBidsOutSize (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨3692⟩ (by decide +native) (by evm_ov)]
  have rdShort := rd3684
  rw [hlt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rdShort
  have rdFall := rdShort.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdFall
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_suck1ExtcodesizeGuard {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3712⟩
      (endSkipTabWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endSkipUsrWord bidOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipBidsPostCallMem I catOut vatOut bidOut) (UInt256.ofNat 12)
      bidOut (cA', σ') k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3805⟩
      (endPackVatWord σ' I :: endPackVatWord σ' I :: ⟨0⟩ ::
        endSkipSuckOutPtr :: endSkipSuckInSize :: endSkipSuckOutPtr ::
        endSkipSuckOutSize :: endSkipSuckEndPtr :: endSkipSuckSelectorWord ::
        endPackVatWord σ' I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck1CalldataMem σ' I catOut vatOut bidOut) (UInt256.ofNat 12)
      bidOut (cA', σ') k' C' := by
  have hmload64Base :=
    endSkipBidsPostCallMem_mload64 I catOut vatOut bidOut hloCat hloVat
  have hmload64Call :=
    endSkipSuck1CalldataMem_mload64 σ' I catOut vatOut bidOut hloCat hloVat hloBid
  have hselectorShift :
      UInt256.shiftLeft endSkipSuckSelectorWord ⟨224⟩ =
        endSkipSuckSelectorShifted := by
    decide +native
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    decide +native
  have hvatMask :
      UInt256.land (endSlotWord ⟨1⟩ σ' I) solcAddrMask = endPackVatWord σ' I := by
    rfl
  have hvatMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σ' I) = endPackVatWord σ' I := by
    simpa [endPackVatWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σ' I)
  have hvowMask :
      UInt256.land (endSlotWord ⟨4⟩ σ' I) solcAddrMask = endPackVowWord σ' I := by
    rfl
  have hvowMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨4⟩ σ' I) = endPackVowWord σ' I := by
    simpa [endPackVowWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨4⟩ σ' I)
  have rd3714 := evm_run h with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd3715raw⟩ := rd3714.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd3715⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3715⟩
        (endSlotWord ⟨1⟩ σ' I :: endSkipTabWord bidOut ::
          endSkipLotWord bidOut :: endSkipBidWord bidOut :: endSkipUsrWord bidOut ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: endFlowVatIlkRateWord vatOut ::
          endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
          endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
        (endSkipBidsPostCallMem I catOut vatOut bidOut) (UInt256.ofNat 12)
        bidOut (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd3715raw⟩
  have rd3718 := evm_run rd3715 with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd3719raw⟩ := rd3718.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd3719⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3719⟩
        (endSlotWord ⟨4⟩ σ' I :: ⟨4⟩ :: endSlotWord ⟨1⟩ σ' I ::
          endSkipTabWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
          endSkipUsrWord bidOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
          endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
          endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
          endSkipReturnPc :: sel :: [])
        (endSkipBidsPostCallMem I catOut vatOut bidOut) (UInt256.ofNat 12)
        bidOut (cA', σ') k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd3719raw⟩
  have rd3770 := evm_run rd3719 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw push4 endSkipSuckSelectorWord (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0
      (writeWord (endSkipBidsPostCallMem I catOut vatOut bidOut) 128
        endSkipSuckSelectorShifted)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 by decide +native]
        unfold Reasoning.Theory.writeWord
        rw [hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0
      (writeWord
        (writeWord (endSkipBidsPostCallMem I catOut vatOut bidOut) 128
          endSkipSuckSelectorShifted)
        132 (endPackVowWord σ' I))
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 by decide +native]
        rw [haddrMask, hvowMaskLeft]
        unfold Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw mstore 0
      (writeWord
        (writeWord
          (writeWord (endSkipBidsPostCallMem I catOut vatOut bidOut) 128
            endSkipSuckSelectorShifted)
          132 (endPackVowWord σ' I))
        164 (endPackVowWord σ' I))
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 by decide +native]
        rw [haddrMask, hvowMaskLeft]
        unfold Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipSuck1CalldataMem σ' I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 by decide +native]
        change (endSkipTabWord bidOut).toByteArray.write 0
          (writeWord
            (writeWord
              (writeWord (endSkipBidsPostCallMem I catOut vatOut bidOut) 128
                endSkipSuckSelectorShifted)
              132 (endPackVowWord σ' I))
            164 (endPackVowWord σ' I)) 196 32 =
          endSkipSuck1CalldataMem σ' I catOut vatOut bidOut
        simp [endSkipSuck1CalldataMem, writeCascade, Reasoning.Theory.writeWord])
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap6 (by decide +native) (by evm_ov),
    raw swap11 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov)]
  have rd3771 := RD.swap9 rd3770 (by decide +native) (by evm_ov)
  have rd3805raw := evm_run rd3771 with [
    raw pop (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw swap7 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap5 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 endSkipSuckSelectorWord (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 endSkipSuckInSize (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 endSkipSuckOutSize (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    convert rd3805raw using 1
    all_goals
      try decide +native
      try simp [endSkipSuckOutPtr, endSkipSuckInSize, endSkipSuckOutSize,
        endSkipSuckEndPtr, endSkipSuckSelectorWord, endPackVatWord, endPackVowWord,
        endSlotWord, solcSlotWord, solcAddrMask, haddrMask, hvatMask, hvatMaskLeft,
        hvowMask, hvowMaskLeft]
      try decide +native⟩

theorem endSkipX_suck1NoCode {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3712⟩
      (endSkipTabWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endSkipUsrWord bidOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipBidsPostCallMem I catOut vatOut bidOut) (UInt256.ofNat 12)
      bidOut (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3805⟩ := endSkipX_suck1ExtcodesizeGuard hloCat hloVat hloBid h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3805⟩) (okPc := ⟨3817⟩) rd3805
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_suck1CallReady {cA cA' gh bl σ σ' σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3712⟩
      (endSkipTabWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endSkipUsrWord bidOut :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipBidsPostCallMem I catOut vatOut bidOut) (UInt256.ofNat 12)
      bidOut (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (endPackVatWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3820⟩
      (gasWord :: endPackVatWord σ' I :: ⟨0⟩ ::
        endSkipSuckOutPtr :: endSkipSuckInSize :: endSkipSuckOutPtr ::
        endSkipSuckOutSize :: endSkipSuckEndPtr :: endSkipSuckSelectorWord ::
        endPackVatWord σ' I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck1CalldataMem σ' I catOut vatOut bidOut) (UInt256.ofNat 12)
      bidOut (cA', σ') k' C' := by
  obtain ⟨_, _, rd3805⟩ := endSkipX_suck1ExtcodesizeGuard hloCat hloVat hloBid h
  obtain ⟨gasWord, k', C', rd3820⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3805⟩) (okPc := ⟨3817⟩) rd3805
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd3820⟩

theorem endSkipX_suck1PostCall {cA cA' gh bl σ σpre σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut bidOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3820⟩
      (gasWord :: endPackVatWord σpre I :: ⟨0⟩ ::
        endSkipSuckOutPtr :: endSkipSuckInSize :: endSkipSuckOutPtr ::
        endSkipSuckOutSize :: endSkipSuckEndPtr :: endSkipSuckSelectorWord ::
        endPackVatWord σpre I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck1CalldataMem σpre I catOut vatOut bidOut) (UInt256.ofNat 12)
      bidOut (cA', σpre) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (ret : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, ret) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σpre σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σpre I))
          (toExecute σpre (AccountAddress.ofUInt256 (endPackVatWord σpre I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSkipSuck1CalldataMem σpre I catOut vatOut bidOut).readWithPadding
            endSkipSuckOutPtr.toNat endSkipSuckInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3821⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endSkipSuckEndPtr ::
            endSkipSuckSelectorWord :: endPackVatWord σpre I ::
            endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
            endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
            endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
            endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
          (endSkipSuck1PostCallMem σpre I catOut vatOut bidOut ret)
          (UInt256.ofNat 12) ret (cA'', σ'') k' C'
      ∧ ret.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, ret, Ain, callGas, k', C', hΘ, rd3821raw, hret⟩ :=
    RD.call h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, ret, Ain, callGas, k', C', ?_, ?_, hret⟩
  · simpa [initState] using hΘ
  · have hmin : (min endSkipSuckOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
        show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
        exact Nat.zero_le _
      simp [endSkipSuckOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
          endSkipSuckOutPtr.toNat endSkipSuckInSize.toNat)
          endSkipSuckOutPtr.toNat endSkipSuckOutSize.toNat) = UInt256.ofNat 12 := by
      unfold endSkipSuckOutPtr endSkipSuckInSize endSkipSuckOutSize
      decide +native
    simpa [endSkipSuck1PostCallMem, endSkipSuckOutPtr, endSkipSuckInSize,
      endSkipSuckOutSize, endSkipSuckEndPtr, hmin, byteArray_write_len_zero, haw]
      using rd3821raw

theorem endSkipX_suck1CallDepthLimit {cA cA' gh bl σ σpre σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut bidOut : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3820⟩
      (gasWord :: endPackVatWord σpre I :: ⟨0⟩ ::
        endSkipSuckOutPtr :: endSkipSuckInSize :: endSkipSuckOutPtr ::
        endSkipSuckOutSize :: endSkipSuckEndPtr :: endSkipSuckSelectorWord ::
        endPackVatWord σpre I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck1CalldataMem σpre I catOut vatOut bidOut) (UInt256.ofNat 12)
      bidOut (cA', σpre) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3821⟩
      (⟨0⟩ :: endSkipSuckEndPtr :: endSkipSuckSelectorWord ::
        endPackVatWord σpre I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck1CalldataMem σpre I catOut vatOut bidOut) (UInt256.ofNat 12)
      ByteArray.empty (cA', σpre) k' C' := by
  obtain ⟨k', C', rd3821raw⟩ :=
    RD.callDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endSkipSuckOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
        endSkipSuckOutPtr.toNat endSkipSuckInSize.toNat)
        endSkipSuckOutPtr.toNat endSkipSuckOutSize.toNat) = UInt256.ofNat 12 := by
    unfold endSkipSuckOutPtr endSkipSuckInSize endSkipSuckOutSize
    decide +native
  simpa [endSkipSuckOutPtr, endSkipSuckInSize, endSkipSuckOutSize,
    endSkipSuckEndPtr, hmin, byteArray_write_len_zero, haw] using rd3821raw

theorem endSkipX_suck1CallFailed {cA cA' gh bl σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3821⟩
      (⟨0⟩ :: endSkipSuckEndPtr :: endSkipSuckSelectorWord :: endPackVatWord σpre I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3821⟩) (okPc := ⟨3837⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_suck1CallSucceeded {cA cA' gh bl σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3821⟩
      (⟨1⟩ :: endSkipSuckEndPtr :: endSkipSuckSelectorWord :: endPackVatWord σpre I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3840⟩
      (endSkipSuckSelectorWord :: endPackVatWord σpre I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  obtain ⟨_, _, rd3839⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨3821⟩) (okPc := ⟨3837⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  have rd3840 := evm_run rd3839 with [
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd3840⟩

theorem endSkipX_suck2ExtcodesizeGuard {cA cA' gh bl σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3840⟩
      (endSkipSuckSelectorWord :: endPackVatWord σmem I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata)
      (UInt256.ofNat 12) rdata (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3924⟩
      (endPackVatWord σpost I :: endPackVatWord σpost I :: ⟨0⟩ ::
        endSkipSuckOutPtr :: endSkipSuckInSize :: endSkipSuckOutPtr ::
        endSkipSuckOutSize :: endSkipSuckEndPtr :: endSkipSuckSelectorWord ::
        endPackVatWord σpost I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck2CalldataMemFor σmem σpost I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  have hmload64Base :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata)
              |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    rw [endSkipSuck1PostCallMem_eq]
    exact endSkipSuck1CalldataMem_mload64 σmem I catOut vatOut bidOut
      hloCat hloVat hloBid
  have hmload64Call :=
    endSkipSuck2CalldataMemFor_mload64 σmem σpost I catOut vatOut bidOut
      hloCat hloVat hloBid
  have hselectorShift :
      UInt256.shiftLeft endSkipSuckSelectorWord ⟨224⟩ =
        endSkipSuckSelectorShifted := by
    decide +native
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    decide +native
  have hvatMask :
      UInt256.land (endSlotWord ⟨1⟩ σpost I) solcAddrMask = endPackVatWord σpost I := by
    rfl
  have hvatMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σpost I) =
        endPackVatWord σpost I := by
    simpa [endPackVatWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σpost I)
  have hvowMask :
      UInt256.land (endSlotWord ⟨4⟩ σpost I) solcAddrMask = endPackVowWord σpost I := by
    rfl
  have hvowMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨4⟩ σpost I) = endPackVowWord σpost I := by
    simpa [endPackVowWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨4⟩ σpost I)
  have rd3842 := evm_run h with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd3843raw⟩ := rd3842.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd3843⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3843⟩
        (endSlotWord ⟨1⟩ σpost I :: endSkipSuckSelectorWord ::
          endPackVatWord σmem I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
          endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
          endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
          endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
        (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata)
        (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd3843raw⟩
  have rd3846 := evm_run rd3843 with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd3847raw⟩ := rd3846.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd3847⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3847⟩
        (endSlotWord ⟨4⟩ σpost I :: ⟨4⟩ :: endSlotWord ⟨1⟩ σpost I ::
          endSkipSuckSelectorWord :: endPackVatWord σmem I ::
          endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
          endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
          endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
          endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
        (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata)
        (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd3847raw⟩
  have rd3879 := evm_run rd3847 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw push4 endSkipSuckSelectorWord (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0
      (writeWord (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata) 128
        endSkipSuckSelectorShifted)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 by decide +native]
        unfold Reasoning.Theory.writeWord
        rw [hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw mstore 0
      (writeWord
        (writeWord (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata) 128
          endSkipSuckSelectorShifted)
        132 (endPackVowWord σpost I))
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 by decide +native]
        rw [haddrMask, hvowMaskLeft]
        unfold Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov)]
  have rd3880 := RD.address rd3879 (by decide +native) (by evm_ov)
  have rd3924raw := evm_run rd3880 with [
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 0
      (writeWord
        (writeWord
          (writeWord (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata) 128
            endSkipSuckSelectorShifted)
          132 (endPackVowWord σpost I))
        164 (endSkipThisWord I))
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 by decide +native]
        change (endSkipThisWord I).toByteArray.write 0
          (writeWord
            (writeWord (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata) 128
              endSkipSuckSelectorShifted)
            132 (endPackVowWord σpost I)) 164 32 =
          writeWord
            (writeWord
              (writeWord (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata) 128
                endSkipSuckSelectorShifted)
              132 (endPackVowWord σpost I))
            164 (endSkipThisWord I)
        unfold Reasoning.Theory.writeWord
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup11 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipSuck2CalldataMemFor σmem σpost I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 by decide +native]
        change (endSkipBidWord bidOut).toByteArray.write 0
          (writeWord
            (writeWord
              (writeWord (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata) 128
                endSkipSuckSelectorShifted)
              132 (endPackVowWord σpost I))
            164 (endSkipThisWord I)) 196 32 =
          endSkipSuck2CalldataMemFor σmem σpost I catOut vatOut bidOut
        simp [endSkipSuck2CalldataMemFor, endSkipSuck1PostCallMem_eq, writeCascade,
          Reasoning.Theory.writeWord])
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push4 endSkipSuckSelectorWord (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 endSkipSuckInSize (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 endSkipSuckOutSize (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    convert rd3924raw using 1
    all_goals
      try decide +native
      try simp [endSkipSuckOutPtr, endSkipSuckInSize, endSkipSuckOutSize,
        endSkipSuckEndPtr, endSkipSuckSelectorWord, endPackVatWord, endPackVowWord,
        endSlotWord, solcSlotWord, solcAddrMask, haddrMask, hvatMask, hvatMaskLeft,
        hvowMask, hvowMaskLeft]
      try decide +native⟩

theorem endSkipX_suck2NoCode {cA cA' gh bl σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3840⟩
      (endSkipSuckSelectorWord :: endPackVatWord σmem I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σpost (endPackVatWord σpost I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd3924⟩ := endSkipX_suck2ExtcodesizeGuard hloCat hloVat hloBid h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3924⟩) (okPc := ⟨3936⟩) rd3924
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_suck2CallReady {cA cA' gh bl σ σmem σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3840⟩
      (endSkipSuckSelectorWord :: endPackVatWord σmem I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck1PostCallMem σmem I catOut vatOut bidOut rdata)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σpost (endPackVatWord σpost I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3939⟩
      (gasWord :: endPackVatWord σpost I :: ⟨0⟩ ::
        endSkipSuckOutPtr :: endSkipSuckInSize :: endSkipSuckOutPtr ::
        endSkipSuckOutSize :: endSkipSuckEndPtr :: endSkipSuckSelectorWord ::
        endPackVatWord σpost I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck2CalldataMemFor σmem σpost I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  obtain ⟨_, _, rd3924⟩ := endSkipX_suck2ExtcodesizeGuard hloCat hloVat hloBid h
  obtain ⟨gasWord, k', C', rd3939⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3924⟩) (okPc := ⟨3936⟩) rd3924
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd3939⟩

theorem endSkipX_suck2PostCall {cA cA' gh bl σ σmem σpost σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut bidOut rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3939⟩
      (gasWord :: endPackVatWord σpost I :: ⟨0⟩ ::
        endSkipSuckOutPtr :: endSkipSuckInSize :: endSkipSuckOutPtr ::
        endSkipSuckOutSize :: endSkipSuckEndPtr :: endSkipSuckSelectorWord ::
        endPackVatWord σpost I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck2CalldataMemFor σmem σpost I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (ret : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, ret) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σpost σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σpost I))
          (toExecute σpost (AccountAddress.ofUInt256 (endPackVatWord σpost I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSkipSuck2CalldataMemFor σmem σpost I catOut vatOut bidOut).readWithPadding
            endSkipSuckOutPtr.toNat endSkipSuckInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3940⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endSkipSuckEndPtr ::
            endSkipSuckSelectorWord :: endPackVatWord σpost I ::
            endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
            endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
            endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
            endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
          (endSkipSuck2PostCallMemFor σmem σpost I catOut vatOut bidOut ret)
          (UInt256.ofNat 12) ret (cA'', σ'') k' C'
      ∧ ret.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, ret, Ain, callGas, k', C', hΘ, rd3940raw, hret⟩ :=
    RD.call h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, ret, Ain, callGas, k', C', ?_, ?_, hret⟩
  · simpa [initState] using hΘ
  · have hmin : (min endSkipSuckOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
        show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
        exact Nat.zero_le _
      simp [endSkipSuckOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
          endSkipSuckOutPtr.toNat endSkipSuckInSize.toNat)
          endSkipSuckOutPtr.toNat endSkipSuckOutSize.toNat) = UInt256.ofNat 12 := by
      unfold endSkipSuckOutPtr endSkipSuckInSize endSkipSuckOutSize
      decide +native
    simpa [endSkipSuck2PostCallMemFor, endSkipSuckOutPtr, endSkipSuckInSize,
      endSkipSuckOutSize, endSkipSuckEndPtr, hmin, byteArray_write_len_zero, haw]
      using rd3940raw

theorem endSkipX_suck2CallDepthLimit {cA cA' gh bl σ σmem σpost σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut bidOut rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3939⟩
      (gasWord :: endPackVatWord σpost I :: ⟨0⟩ ::
        endSkipSuckOutPtr :: endSkipSuckInSize :: endSkipSuckOutPtr ::
        endSkipSuckOutSize :: endSkipSuckEndPtr :: endSkipSuckSelectorWord ::
        endPackVatWord σpost I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck2CalldataMemFor σmem σpost I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3940⟩
      (⟨0⟩ :: endSkipSuckEndPtr :: endSkipSuckSelectorWord ::
        endPackVatWord σpost I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck2CalldataMemFor σmem σpost I catOut vatOut bidOut)
      (UInt256.ofNat 12) ByteArray.empty (cA', σpost) k' C' := by
  obtain ⟨k', C', rd3940raw⟩ :=
    RD.callDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endSkipSuckOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
        endSkipSuckOutPtr.toNat endSkipSuckInSize.toNat)
        endSkipSuckOutPtr.toNat endSkipSuckOutSize.toNat) = UInt256.ofNat 12 := by
    unfold endSkipSuckOutPtr endSkipSuckInSize endSkipSuckOutSize
    decide +native
  simpa [endSkipSuckOutPtr, endSkipSuckInSize, endSkipSuckOutSize,
    endSkipSuckEndPtr, hmin, byteArray_write_len_zero, haw] using rd3940raw

theorem endSkipX_suck2CallFailed {cA cA' gh bl σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3940⟩
      (⟨0⟩ :: endSkipSuckEndPtr :: endSkipSuckSelectorWord :: endPackVatWord σpre I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨3940⟩) (okPc := ⟨3956⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_suck2CallSucceeded {cA cA' gh bl σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3940⟩
      (⟨1⟩ :: endSkipSuckEndPtr :: endSkipSuckSelectorWord :: endPackVatWord σpre I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3959⟩
      (endSkipSuckSelectorWord :: endPackVatWord σpre I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  obtain ⟨_, _, rd3958⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨3940⟩) (okPc := ⟨3956⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  have rd3959 := evm_run rd3958 with [
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd3959⟩

theorem endSkipX_hopeExtcodesizeGuard {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3959⟩
      (endSkipSuckSelectorWord :: endPackVatWord σcall I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
      (UInt256.ofNat 12) rdata (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4026⟩
      (endPackVatWord σpost I :: endPackVatWord σpost I :: ⟨0⟩ ::
        endSkipHopeOutPtr :: endSkipHopeInSize :: endSkipHopeOutPtr ::
        endSkipHopeOutSize :: endSkipHopeEndPtr :: endSkipHopeSelectorWord ::
        endPackVatWord σpost I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  have hmload64Base :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut rdata).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
              |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    rw [endSkipSuck2PostCallMemFor_eq]
    exact endSkipSuck2CalldataMemFor_mload64 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid
  have hmload64Call :=
    endSkipHopeCalldataMemFor_mload64 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid
  have hselectorShift :
      UInt256.shiftLeft (⟨0x28ec8bf1⟩ : UInt256) ⟨226⟩ =
        endSkipHopeSelectorShifted := by
    decide +native
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    decide +native
  have hvatMask :
      UInt256.land (endSlotWord ⟨1⟩ σpost I) solcAddrMask = endPackVatWord σpost I := by
    rfl
  have hvatMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σpost I) =
        endPackVatWord σpost I := by
    simpa [endPackVatWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σpost I)
  have hflipMaskLeft :
      UInt256.land solcAddrMask (endSkipCatIlkFlipWord catOut) =
        endSkipCatIlkFlipTargetWord catOut := by
    rfl
  have hflipMaskRight :
      UInt256.land (endSkipCatIlkFlipWord catOut) solcAddrMask =
        endSkipCatIlkFlipTargetWord catOut := by
    simpa [endSkipCatIlkFlipTargetWord] using
      u256_land_comm (endSkipCatIlkFlipWord catOut) solcAddrMask
  have rd3961 := evm_run h with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd3962raw⟩ := rd3961.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd3962⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3962⟩
        (endSlotWord ⟨1⟩ σpost I :: endSkipSuckSelectorWord ::
          endPackVatWord σcall I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
          endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
          endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
          endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
        (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
        (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd3962raw⟩
  have rd4026raw := evm_run rd3962 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw push4 ⟨0x28ec8bf1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨226⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0
      (writeWord (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
        128 endSkipHopeSelectorShifted)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 by decide +native]
        unfold Reasoning.Theory.writeWord
        rw [hselectorShift])
      (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup12 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨4⟩).toNat = 132 by decide +native]
        rw [haddrMask, hflipMaskLeft]
        change (endSkipCatIlkFlipTargetWord catOut).toByteArray.write 0
          (writeWord
            (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
            128 endSkipHopeSelectorShifted) 132 32 =
          endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut
        simp [endSkipHopeCalldataMemFor, endSkipSuck2PostCallMemFor_eq, writeCascade,
          Reasoning.Theory.writeWord])
      (by decide) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push4 endSkipHopeSelectorWord (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 endSkipHopeInSize (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 endSkipHopeOutSize (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    convert rd4026raw using 1
    all_goals
      try decide +native
      try simp [endSkipHopeOutPtr, endSkipHopeInSize, endSkipHopeOutSize,
        endSkipHopeEndPtr, endSkipHopeSelectorWord, endPackVatWord, endSlotWord,
        solcSlotWord, solcAddrMask, haddrMask, hvatMask, hvatMaskLeft,
        hflipMaskLeft, hflipMaskRight]
      try decide +native⟩

theorem endSkipX_hopeNoCode {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3959⟩
      (endSkipSuckSelectorWord :: endPackVatWord σcall I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σpost (endPackVatWord σpost I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4026⟩ := endSkipX_hopeExtcodesizeGuard hloCat hloVat hloBid h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4026⟩) (okPc := ⟨4038⟩) rd4026
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_hopeCallReady {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3959⟩
      (endSkipSuckSelectorWord :: endPackVatWord σcall I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipSuck2PostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σpost (endPackVatWord σpost I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4041⟩
      (gasWord :: endPackVatWord σpost I :: ⟨0⟩ ::
        endSkipHopeOutPtr :: endSkipHopeInSize :: endSkipHopeOutPtr ::
        endSkipHopeOutSize :: endSkipHopeEndPtr :: endSkipHopeSelectorWord ::
        endPackVatWord σpost I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  obtain ⟨_, _, rd4026⟩ := endSkipX_hopeExtcodesizeGuard hloCat hloVat hloBid h
  obtain ⟨gasWord, k', C', rd4041⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4026⟩) (okPc := ⟨4038⟩) rd4026
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd4041⟩

theorem endSkipX_hopePostCall {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut bidOut rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4041⟩
      (gasWord :: endPackVatWord σpost I :: ⟨0⟩ ::
        endSkipHopeOutPtr :: endSkipHopeInSize :: endSkipHopeOutPtr ::
        endSkipHopeOutSize :: endSkipHopeEndPtr :: endSkipHopeSelectorWord ::
        endPackVatWord σpost I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (ret : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, ret) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σpost σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σpost I))
          (toExecute σpost (AccountAddress.ofUInt256 (endPackVatWord σpost I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
            endSkipHopeOutPtr.toNat endSkipHopeInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4042⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endSkipHopeEndPtr ::
            endSkipHopeSelectorWord :: endPackVatWord σpost I ::
            endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
            endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
            endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
            endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
          (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut ret)
          (UInt256.ofNat 12) ret (cA'', σ'') k' C'
      ∧ ret.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, ret, Ain, callGas, k', C', hΘ, rd4042raw, hret⟩ :=
    RD.call h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, ret, Ain, callGas, k', C', ?_, ?_, hret⟩
  · simpa [initState] using hΘ
  · have hmin : (min endSkipHopeOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
        show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
        exact Nat.zero_le _
      simp [endSkipHopeOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
          endSkipHopeOutPtr.toNat endSkipHopeInSize.toNat)
          endSkipHopeOutPtr.toNat endSkipHopeOutSize.toNat) = UInt256.ofNat 12 := by
      unfold endSkipHopeOutPtr endSkipHopeInSize endSkipHopeOutSize
      decide +native
    simpa [endSkipHopePostCallMemFor, endSkipHopeOutPtr, endSkipHopeInSize,
      endSkipHopeOutSize, endSkipHopeEndPtr, hmin, byteArray_write_len_zero, haw]
      using rd4042raw

theorem endSkipX_hopeCallDepthLimit {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut bidOut rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4041⟩
      (gasWord :: endPackVatWord σpost I :: ⟨0⟩ ::
        endSkipHopeOutPtr :: endSkipHopeInSize :: endSkipHopeOutPtr ::
        endSkipHopeOutSize :: endSkipHopeEndPtr :: endSkipHopeSelectorWord ::
        endPackVatWord σpost I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4042⟩
      (⟨0⟩ :: endSkipHopeEndPtr :: endSkipHopeSelectorWord ::
        endPackVatWord σpost I :: endSkipTabWord bidOut :: endSkipUsrWord bidOut ::
        endSkipLotWord bidOut :: endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipHopeCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) ByteArray.empty (cA', σpost) k' C' := by
  obtain ⟨k', C', rd4042raw⟩ :=
    RD.callDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endSkipHopeOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
        endSkipHopeOutPtr.toNat endSkipHopeInSize.toNat)
        endSkipHopeOutPtr.toNat endSkipHopeOutSize.toNat) = UInt256.ofNat 12 := by
    unfold endSkipHopeOutPtr endSkipHopeInSize endSkipHopeOutSize
    decide +native
  simpa [endSkipHopeOutPtr, endSkipHopeInSize, endSkipHopeOutSize,
    endSkipHopeEndPtr, hmin, byteArray_write_len_zero, haw] using rd4042raw

theorem endSkipX_hopeCallFailed {cA cA' gh bl σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4042⟩
      (⟨0⟩ :: endSkipHopeEndPtr :: endSkipHopeSelectorWord :: endPackVatWord σpre I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4042⟩) (okPc := ⟨4058⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_hopeCallSucceeded {cA cA' gh bl σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4042⟩
      (⟨1⟩ :: endSkipHopeEndPtr :: endSkipHopeSelectorWord :: endPackVatWord σpre I ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4063⟩
      (endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  obtain ⟨_, _, rd4060⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨4042⟩) (okPc := ⟨4058⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  have rd4063 := evm_run rd4060 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd4063⟩

theorem endSkipX_yankExtcodesizeGuard {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4063⟩
      (endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
      (UInt256.ofNat 12) rdata (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4120⟩
      (endSkipCatIlkFlipTargetWord catOut :: endSkipCatIlkFlipTargetWord catOut ::
        ⟨0⟩ :: endSkipYankOutPtr :: endSkipYankInSize :: endSkipYankOutPtr ::
        endSkipYankOutSize :: endSkipYankEndPtr :: endSkipYankSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  have hmload64Base :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut rdata).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
              |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    rw [endSkipHopePostCallMemFor_eq]
    exact endSkipHopeCalldataMemFor_mload64 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid
  have hmload64Call :=
    endSkipYankCalldataMemFor_mload64 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    decide +native
  have hflipMaskLeft :
      UInt256.land solcAddrMask (endSkipCatIlkFlipWord catOut) =
        endSkipCatIlkFlipTargetWord catOut := by
    rfl
  have hflipMaskRight :
      UInt256.land (endSkipCatIlkFlipWord catOut) solcAddrMask =
        endSkipCatIlkFlipTargetWord catOut := by
    simpa [endSkipCatIlkFlipTargetWord] using
      u256_land_comm (endSkipCatIlkFlipWord catOut) solcAddrMask
  have hselectorMaskShift :
      UInt256.shiftLeft (UInt256.land endSkipYankSelectorWord ⟨0xffffffff⟩) ⟨224⟩ =
        endSkipYankSelectorShifted := by
    decide +native
  have hselectorMaskShiftLeft :
      UInt256.shiftLeft (UInt256.land ⟨0xffffffff⟩ endSkipYankSelectorWord) ⟨224⟩ =
        endSkipYankSelectorShifted := by
    decide +native
  have rd4120raw := evm_run h with [
    raw dup6 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push4 endSkipYankSelectorWord (by decide +native) (by evm_ov),
    raw dup10 (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64Base (by decide) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push4 ⟨0xffffffff⟩ (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0
      (writeWord (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
        128 endSkipYankSelectorShifted)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by rw [hselectorMaskShiftLeft]; rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 by decide +native]
        change (endSkipIdWord I).toByteArray.write 0
          (writeWord
            (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
            128 endSkipYankSelectorShifted) 132 32 =
          endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut
        simp [endSkipYankCalldataMemFor, endSkipHopePostCallMemFor_eq, writeCascade,
          Reasoning.Theory.writeWord])
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endSkipYankOutPtr, endSkipYankInSize, endSkipYankOutSize,
      endSkipYankEndPtr, endSkipYankSelectorWord, haddrMask, hflipMaskLeft,
      hflipMaskRight] using rd4120raw⟩

theorem endSkipX_yankNoCode {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4063⟩
      (endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σpost
        (endSkipCatIlkFlipTargetWord catOut) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4120⟩ := endSkipX_yankExtcodesizeGuard hloCat hloVat hloBid h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4120⟩) (okPc := ⟨4132⟩) rd4120
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_yankCallReady {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4063⟩
      (endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipHopePostCallMemFor σmem σcall I catOut vatOut bidOut rdata)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σpost
        (endSkipCatIlkFlipTargetWord catOut) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4135⟩
      (gasWord :: endSkipCatIlkFlipTargetWord catOut :: ⟨0⟩ ::
        endSkipYankOutPtr :: endSkipYankInSize :: endSkipYankOutPtr ::
        endSkipYankOutSize :: endSkipYankEndPtr :: endSkipYankSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  obtain ⟨_, _, rd4120⟩ := endSkipX_yankExtcodesizeGuard hloCat hloVat hloBid h
  obtain ⟨gasWord, k', C', rd4135⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4120⟩) (okPc := ⟨4132⟩) rd4120
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd4135⟩

theorem endSkipX_yankPostCall {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut bidOut rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4135⟩
      (gasWord :: endSkipCatIlkFlipTargetWord catOut :: ⟨0⟩ ::
        endSkipYankOutPtr :: endSkipYankInSize :: endSkipYankOutPtr ::
        endSkipYankOutSize :: endSkipYankEndPtr :: endSkipYankSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (ret : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, ret) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σpost σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endSkipCatIlkFlipTargetWord catOut))
          (toExecute σpost (AccountAddress.ofUInt256 (endSkipCatIlkFlipTargetWord catOut)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut).readWithPadding
            endSkipYankOutPtr.toNat endSkipYankInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4136⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endSkipYankEndPtr ::
            endSkipYankSelectorWord :: endSkipCatIlkFlipTargetWord catOut ::
            endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
            endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
            endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
            endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
          (endSkipYankPostCallMemFor σmem σcall I catOut vatOut bidOut ret)
          (UInt256.ofNat 12) ret (cA'', σ'') k' C'
      ∧ ret.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, ret, Ain, callGas, k', C', hΘ, rd4136raw, hret⟩ :=
    RD.call h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, ret, Ain, callGas, k', C', ?_, ?_, hret⟩
  · simpa [initState] using hΘ
  · have hmin : (min endSkipYankOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
        show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
        exact Nat.zero_le _
      simp [endSkipYankOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
          endSkipYankOutPtr.toNat endSkipYankInSize.toNat)
          endSkipYankOutPtr.toNat endSkipYankOutSize.toNat) = UInt256.ofNat 12 := by
      unfold endSkipYankOutPtr endSkipYankInSize endSkipYankOutSize
      decide +native
    simpa [endSkipYankPostCallMemFor, endSkipYankOutPtr, endSkipYankInSize,
      endSkipYankOutSize, endSkipYankEndPtr, hmin, byteArray_write_len_zero, haw]
      using rd4136raw

theorem endSkipX_yankCallDepthLimit {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut bidOut rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4135⟩
      (gasWord :: endSkipCatIlkFlipTargetWord catOut :: ⟨0⟩ ::
        endSkipYankOutPtr :: endSkipYankInSize :: endSkipYankOutPtr ::
        endSkipYankOutSize :: endSkipYankEndPtr :: endSkipYankSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4136⟩
      (⟨0⟩ :: endSkipYankEndPtr :: endSkipYankSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipYankCalldataMemFor σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) ByteArray.empty (cA', σpost) k' C' := by
  obtain ⟨k', C', rd4136raw⟩ :=
    RD.callDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endSkipYankOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
        endSkipYankOutPtr.toNat endSkipYankInSize.toNat)
        endSkipYankOutPtr.toNat endSkipYankOutSize.toNat) = UInt256.ofNat 12 := by
    unfold endSkipYankOutPtr endSkipYankInSize endSkipYankOutSize
    decide +native
  simpa [endSkipYankOutPtr, endSkipYankInSize, endSkipYankOutSize,
    endSkipYankEndPtr, hmin, byteArray_write_len_zero, haw] using rd4136raw

theorem endSkipX_yankCallFailed {cA cA' gh bl σ σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4136⟩
      (⟨0⟩ :: endSkipYankEndPtr :: endSkipYankSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4136⟩) (okPc := ⟨4152⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_yankCallSucceeded {cA cA' gh bl σ σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4136⟩
      (⟨1⟩ :: endSkipYankEndPtr :: endSkipYankSelectorWord ::
        endSkipCatIlkFlipTargetWord catOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4157⟩
      (endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  obtain ⟨_, _, rd4154⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨4136⟩) (okPc := ⟨4152⟩) h
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  have rd4157 := evm_run rd4154 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd4157⟩

theorem endSkipX_artDivZeroInvalid {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut ret : ByteArray} {k C : ℕ}
    (hrate : endFlowVatIlkRateWord vatOut = ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4157⟩
      (endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipYankPostCallMemFor σmem σcall I catOut vatOut bidOut ret)
      (UInt256.ofNat 12) ret (cA', σpost) k C) :
    X (g.toNat + 1) (D_J endBytecode 0)
        (initState cA gh bl σ σ₀ g A I) = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J endBytecode 0)
        (initState cA gh bl σ σ₀ g A I) = .error .InvalidInstruction := by
  have rd4165 := evm_run h with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push2 ⟨4167⟩ (by decide +native) (by evm_ov)]
  have rd4166 := rd4165.jumpiNT (by decide +native) (by simpa using hrate) (by evm_ov)
  exact endFlowInvalidError rd4166 (by decide +native)

theorem endSkipX_artAddEntry {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut ret : ByteArray} {k C : ℕ}
    (hsz68 : 68 ≤ I.calldata.size)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4157⟩
      (endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipYankPostCallMemFor σmem σcall I catOut vatOut bidOut ret)
      (UInt256.ofNat 12) ret (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      (endSkipArtWord vatOut bidOut :: endSkipArtOldWord σpost I :: ⟨4197⟩ ::
        endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      ret (cA', σpost) k' C' := by
  let key := endSkipIlkWord I
  let mem0 := endSkipYankPostCallMemFor σmem σcall I catOut vatOut bidOut ret
  let mem14 := endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut
  have hslot : endSkipArtSlot I = solcMappingSlot ⟨14⟩ key := by
    simpa [endSkipArtSlot, endSkipIlkKey, key] using
      endFlowArtSlot_eq (I := I) (by omega)
  have hmem0Size : mem0.size = 384 := by
    simpa [mem0, endSkipYankPostCallMemFor_eq] using
      endSkipYankCalldataMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (mem14.readWithPadding 0 64))) =
        solcMappingSlot ⟨14⟩ key := by
    simpa [mem14, endSkipArtHashMemFor, key, mem0, endSkipYankPostCallMemFor_eq] using
      endFlow_twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem0) ⟨14⟩ key
        (by rw [hmem0Size]; omega)
  have rd4165 := evm_run h with [
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push2 ⟨4167⟩ (by decide +native) (by evm_ov)]
  have rd4167 := rd4165.jumpiT (by decide +native) hrate (by jump_dest) (by evm_ov)
  have rd4171 := evm_run rd4167 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup13 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd4172 := rd4171.mstore 0 (wordAt0Mem key mem0) (UInt256.ofNat 12)
    (by decide +native) mem_cost (by simp [wordAt0Mem, key, mem0])
    (by decide +native) (by evm_ov)
  have rd4177 := evm_run rd4172 with [
    raw push1 ⟨14⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd4177' := rd4177.mstore 0 mem14 (UInt256.ofNat 12)
    (by decide +native) mem_cost
    (by
      change (⟨14⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem0) 32 32 =
        mem14
      simp [mem14, endSkipArtHashMemFor, twoWordHashMem, wordAt32Mem, key, mem0,
        endSkipYankPostCallMemFor_eq])
    (by decide +native) (by evm_ov)
  have rd4181 := evm_run rd4177' with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd4182 := rd4181.keccak256 0 (endSkipArtSlot I) (UInt256.ofNat 12)
    (by decide +native) mem_cost (by simpa [key, hslot] using hhash)
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4183raw⟩ := rd4182.sload (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd4183⟩ : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4183⟩
        (endSkipArtOldWord σpost I :: endSkipTabWord bidOut ::
          endFlowVatIlkRateWord vatOut :: ⟨0⟩ :: endSkipTabWord bidOut ::
          endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
          endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
          endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
          endSkipReturnPc :: sel :: [])
        mem14 (UInt256.ofNat 12) ret (cA', σpost) k' C' := by
    exact ⟨_, _, by
      simpa [endSkipArtOldWord, endSlotWord, solcSlotWord, hslot, key, mem14]
        using rd4183raw⟩
  have rd4196 := evm_run rd4183 with [
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push2 ⟨4197⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨10092⟩ (by decide +native) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endSkipArtWord, mem14] using
      rd4196.jump (by decide +native) (by jump_dest) (by evm_ov)⟩

theorem endSkipX_artAddReturns {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut ret : ByteArray} {k C : ℕ}
    (hfit :
      (endSkipArtOldWord σpost I).toNat + (endSkipArtWord vatOut bidOut).toNat <
        UInt256.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      (endSkipArtWord vatOut bidOut :: endSkipArtOldWord σpost I :: ⟨4197⟩ ::
        endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      ret (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4197⟩
      (endSkipArtNewWord σpost I vatOut bidOut :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      ret (cA', σpost) k' C' := by
  let old := endSkipArtOldWord σpost I
  let art := endSkipArtWord vatOut bidOut
  have hfit' : art.toNat + old.toNat < UInt256.size := by
    dsimp [old, art]
    simpa [Nat.add_comm] using hfit
  have haddNat : (art + old).toNat = art.toNat + old.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit']
  have hlt : UInt256.lt (art + old) old = ⟨0⟩ :=
    ult_zero (by rw [haddNat]; omega)
  have rd10099pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd10099 := evm_run rd10099pre with [raw lt (by decide +native) (by evm_ov)]
  have rd10099' := by
    simpa [old, art] using rd10099
  rw [hlt] at rd10099'
  have rd10100pre := evm_run rd10099' with [raw iszero (by decide +native) (by evm_ov)]
  have rd10100 := by
    simpa using rd10100pre
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd10100
  have rd10108pre := evm_run rd10100 with [
    raw push2 ⟨10108⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  have rd4197 := evm_run rd10108pre with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]
  have hcomm : art + old = old + art := u256_add_comm art old
  exact ⟨_, _, by simpa [endSkipArtNewWord, old, art, hcomm] using rd4197⟩

theorem endSkipX_artAddOverflow {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut ret : ByteArray} {k C : ℕ}
    (hover :
      UInt256.size ≤
        (endSkipArtOldWord σpost I).toNat + (endSkipArtWord vatOut bidOut).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨10092⟩
      (endSkipArtWord vatOut bidOut :: endSkipArtOldWord σpost I :: ⟨4197⟩ ::
        endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      ret (cA', σpost) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  let old := endSkipArtOldWord σpost I
  let art := endSkipArtWord vatOut bidOut
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
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd10099 := evm_run rd10099pre with [raw lt (by decide +native) (by evm_ov)]
  have rd10099' := by
    simpa [old, art] using rd10099
  rw [hlt] at rd10099'
  have rd10100pre := evm_run rd10099' with [raw iszero (by decide +native) (by evm_ov)]
  have rd10100 := by
    simpa using rd10100pre
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd10100
  have rd10104pre := evm_run rd10100 with [raw push2 ⟨10108⟩ (by decide +native) (by evm_ov)]
  have rd10104 := rd10104pre.jumpiNT (by decide +native) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact RD.solcPush1Dup1Revert0 rd10104 (by decide +native) (by decide +native)
    (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_artStoreAtHash {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut ret : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4197⟩
      (endSkipArtNewWord σpost I vatOut bidOut :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      ret (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4216⟩
      (⟨0⟩ :: endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      ret (cA', endSkipPostArtAccountMap σpost I
        (endSkipArtNewWord σpost I vatOut bidOut)) k' C' := by
  let key := endSkipIlkWord I
  let mem14 := endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut
  let memStore := endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut
  have hslot : endSkipArtSlot I = solcMappingSlot ⟨14⟩ key := by
    simpa [endSkipArtSlot, endSkipIlkKey, key] using
      endFlowArtSlot_eq (I := I) (by omega)
  have hpostSize :
      (endSkipYankPostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty).size =
        384 := by
    simpa [endSkipYankPostCallMemFor_eq] using
      endSkipYankCalldataMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid
  have hmem14SizeEq :
      mem14.size =
        (endSkipYankPostCallMemFor σmem σcall I catOut vatOut bidOut ByteArray.empty).size := by
    simpa [mem14, endSkipArtHashMemFor] using
      endFlow_twoWordHashMem_size_of_ge64 key ⟨14⟩ (by rw [hpostSize]; omega)
  have hmem14Size : mem14.size = 384 := by
    rw [hmem14SizeEq, hpostSize]
  have hhash :
      UInt256.ofNat (fromByteArrayBigEndian (ffi.KEC (memStore.readWithPadding 0 64))) =
        solcMappingSlot ⟨14⟩ key := by
    simpa [memStore, endSkipArtStoreHashMemFor, key, mem14] using
      endFlow_twoWordHashMem_solcMappingSlot_of_ge64 (mem := mem14) ⟨14⟩ key
        (by rw [hmem14Size]; omega)
  have rd4201 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup12 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd4202 := rd4201.mstore 0 (wordAt0Mem key mem14) (UInt256.ofNat 12)
    (by decide +native) mem_cost (by simp [wordAt0Mem, key, mem14])
    (by decide +native) (by evm_ov)
  have rd4207 := evm_run rd4202 with [
    raw push1 ⟨14⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd4207' := rd4207.mstore 0 memStore (UInt256.ofNat 12)
    (by decide +native) mem_cost
    (by
      change (⟨14⟩ : UInt256).toByteArray.write 0 (wordAt0Mem key mem14) 32 32 =
        memStore
      simp [memStore, endSkipArtStoreHashMemFor, twoWordHashMem, wordAt32Mem, key, mem14])
    (by decide +native) (by evm_ov)
  have rd4211 := evm_run rd4207' with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd4212 := rd4211.keccak256 0 (endSkipArtSlot I) (UInt256.ofNat 12)
    (by decide +native) mem_cost (by simpa [key, hslot] using hhash)
    (by decide +native) (by evm_ov)
  have rd4215 := evm_run rd4212 with [
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4216raw⟩ := rd4215.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [endSkipPostArtAccountMap, memStore] using rd4216raw⟩

theorem endSkipX_artStoreIntGuardOk {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut ret : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (hlot : (endSkipLotWord bidOut).toNat < 2 ^ 255)
    (hart : (endSkipArtWord vatOut bidOut).toNat < 2 ^ 255)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4197⟩
      (endSkipArtNewWord σpost I vatOut bidOut :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      ret (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4295⟩
      (endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      ret (cA', endSkipPostArtAccountMap σpost I
        (endSkipArtNewWord σpost I vatOut bidOut)) k' C' := by
  obtain ⟨_, _, rd4216⟩ := endSkipX_artStoreAtHash hperm hsz68 hloCat hloVat hloBid h
  have hsltLot :
      UInt256.slt (endSkipLotWord bidOut) (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa using
      (slt_lit_zero (a := endSkipLotWord bidOut) (m := 0)
        (by norm_num) (by omega) hlot)
  have hsltArt :
      UInt256.slt (endSkipArtWord vatOut bidOut) (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa using
      (slt_lit_zero (a := endSkipArtWord vatOut bidOut) (m := 0)
        (by norm_num) (by omega) hart)
  have rd4224pre := evm_run rd4216 with [
    raw dup5 (by decide +native) (by evm_ov),
    raw slt (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push2 ⟨4231⟩ (by decide +native) (by evm_ov)]
  rw [hsltLot, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4224pre
  have rd4225 := rd4224pre.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd4230pre := evm_run rd4225 with [
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw slt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov)]
  rw [hsltArt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4230pre
  have rd4295 := evm_run rd4230pre with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨4295⟩ (by decide +native) (by evm_ov),
    raw jumpiT (by decide +native) (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa using rd4295⟩

theorem endSkipX_artStoreIntGuardLotOverflow {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut ret : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (hlot : 2 ^ 255 ≤ (endSkipLotWord bidOut).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4197⟩
      (endSkipArtNewWord σpost I vatOut bidOut :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      ret (cA', σpost) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4216⟩ := endSkipX_artStoreAtHash hperm hsz68 hloCat hloVat hloBid h
  have hsltLot :
      UInt256.slt (endSkipLotWord bidOut) (⟨0⟩ : UInt256) = ⟨1⟩ := by
    simpa using
      (slt_lit_one_high (a := endSkipLotWord bidOut) (m := 0)
        (by norm_num) hlot)
  have rd4224pre := evm_run rd4216 with [
    raw dup5 (by decide +native) (by evm_ov),
    raw slt (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push2 ⟨4231⟩ (by decide +native) (by evm_ov)]
  rw [hsltLot, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4224pre
  have rd4231 := rd4224pre.jumpiT (by decide +native)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have rd4235pre := evm_run rd4231 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨4295⟩ (by decide +native) (by evm_ov)]
  have rd4236 := rd4235pre.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact endSkip_solcErrorStringRevertTail_aw12
    (pc := ⟨4236⟩) (len := ⟨12⟩)
    (rawWord := ⟨0x456e642f6f766572666c6f77⟩) (shift := ⟨160⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f6f766572666c6f77⟩ ⟨160⟩)
    (op := .PUSH12) (width := 12)
    rd4236
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) rfl
    (endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid)
    (endSkipArtStoreHashMemFor_read64 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_artStoreIntGuardArtOverflow {cA cA' gh bl σ σmem σcall σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut ret : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (hlot : (endSkipLotWord bidOut).toNat < 2 ^ 255)
    (hart : 2 ^ 255 ≤ (endSkipArtWord vatOut bidOut).toNat)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4197⟩
      (endSkipArtNewWord σpost I vatOut bidOut :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipArtHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      ret (cA', σpost) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4216⟩ := endSkipX_artStoreAtHash hperm hsz68 hloCat hloVat hloBid h
  have hsltLot :
      UInt256.slt (endSkipLotWord bidOut) (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa using
      (slt_lit_zero (a := endSkipLotWord bidOut) (m := 0)
        (by norm_num) (by omega) hlot)
  have hsltArt :
      UInt256.slt (endSkipArtWord vatOut bidOut) (⟨0⟩ : UInt256) = ⟨1⟩ := by
    simpa using
      (slt_lit_one_high (a := endSkipArtWord vatOut bidOut) (m := 0)
        (by norm_num) hart)
  have rd4224pre := evm_run rd4216 with [
    raw dup5 (by decide +native) (by evm_ov),
    raw slt (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push2 ⟨4231⟩ (by decide +native) (by evm_ov)]
  rw [hsltLot, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4224pre
  have rd4225 := rd4224pre.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd4230pre := evm_run rd4225 with [
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw slt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov)]
  rw [hsltArt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4230pre
  have rd4235pre := evm_run rd4230pre with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨4295⟩ (by decide +native) (by evm_ov)]
  have rd4236 := rd4235pre.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact endSkip_solcErrorStringRevertTail_aw12
    (pc := ⟨4236⟩) (len := ⟨12⟩)
    (rawWord := ⟨0x456e642f6f766572666c6f77⟩) (shift := ⟨160⟩)
    (word := UInt256.shiftLeft ⟨0x456e642f6f766572666c6f77⟩ ⟨160⟩)
    (op := .PUSH12) (width := 12)
    rd4236
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | decide +native)
    (by decide) rfl
    (endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid)
    (endSkipArtStoreHashMemFor_read64 σmem σcall I catOut vatOut bidOut
      hloCat hloVat hloBid)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_grabExtcodesizeGuard {cA cA' gh bl σ σCall σmem σcall σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4295⟩
      (endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      rdata (cA', σCall) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4397⟩
      (endPackVatWord σCall I :: endPackVatWord σCall I :: ⟨0⟩ ::
        endFreeGrabOutPtr :: endFreeGrabInSize :: endFreeGrabOutPtr ::
        endFreeGrabOutSize :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σCall I :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σCall) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
              |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue
      (by rw [endSkipArtStoreHashMemFor_size σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid]; decide)
      (by decide) (endSkipArtStoreHashMemFor_read64 σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid)
  have hmload64Grab :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSkipGrabMem7Trace σCall σmem σcall I catOut vatOut bidOut).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkipGrabMem7Trace σCall σmem σcall I catOut vatOut bidOut)
              |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    simpa [endSkipGrabMem7Trace_eq] using
      endSkipGrabCalldataMemForTrace_mload64 σCall σmem σcall I catOut vatOut bidOut
        hloCat hloVat hloBid
  have hselectorShift :
      UInt256.shiftLeft (⟨0x01eeacfd⟩ : UInt256) ⟨230⟩ =
        endFreeGrabSelectorShifted := by
    decide +native
  have hthisWord : EVM.word ↑I.codeOwner = endSkipThisWord I :=
    endSkipThisWordOfAddr I
  have husrMask :
      UInt256.land (endSkipUsrWord bidOut) solcAddrMask =
        endSkipUsrAddrWord bidOut := by
    simpa [endSkipUsrAddrWord] using
      u256_land_comm (endSkipUsrWord bidOut) solcAddrMask
  have husrMaskLeft :
      UInt256.land solcAddrMask (endSkipUsrWord bidOut) =
        endSkipUsrAddrWord bidOut := by
    rfl
  have hvowMask :
      UInt256.land (endSlotWord ⟨4⟩ σCall I) solcAddrMask = endPackVowWord σCall I := by
    rfl
  have hvowMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨4⟩ σCall I) = endPackVowWord σCall I := by
    simpa [endPackVowWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨4⟩ σCall I)
  have hvatMask :
      UInt256.land (endSlotWord ⟨1⟩ σCall I) solcAddrMask = endPackVatWord σCall I := by
    rfl
  have hvatMaskLeft :
      UInt256.land solcAddrMask (endSlotWord ⟨1⟩ σCall I) = endPackVatWord σCall I := by
    simpa [endPackVatWord] using
      u256_land_comm solcAddrMask (endSlotWord ⟨1⟩ σCall I)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have rd4298 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4299raw⟩ := rd4298.sload (by decide +native) (by evm_ov)
  have rd4299 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4299⟩
        (endSlotWord ⟨1⟩ σCall I :: endSkipArtWord vatOut bidOut ::
          endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
          endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
          endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
          endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
        (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        (UInt256.ofNat 12) rdata (cA', σCall) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd4299raw⟩
  obtain ⟨_, _, rd4299⟩ := rd4299
  have rd4302 := evm_run rd4299 with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  obtain ⟨_, _, rd4303raw⟩ := rd4302.sload (by decide +native) (by evm_ov)
  have rd4303 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4303⟩
        (endSlotWord ⟨4⟩ σCall I :: ⟨4⟩ :: endSlotWord ⟨1⟩ σCall I ::
          endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
          endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
          endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
          endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
          endSkipReturnPc :: sel :: [])
        (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut)
        (UInt256.ofNat 12) rdata (cA', σCall) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd4303raw⟩
  obtain ⟨_, _, rd4303⟩ := rd4303
  have rd4397raw := evm_run rd4303 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push4 ⟨0x01eeacfd⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨230⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipGrabMem1Trace σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by rw [hselectorShift]; rfl) (by decide) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup15 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipGrabMem2Trace σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipGrabMem3Trace σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨36⟩).toNat = 164 by decide +native]
        rw [haddrMask, husrMaskLeft]
        rfl)
      (by decide) (by evm_ov),
    raw address (by decide +native) (by evm_ov),
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipGrabMem4Trace σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨68⟩).toNat = 196 by decide +native]
        simp [endSkipGrabMem4Trace, Reasoning.Theory.writeWord, endSkipThisWord])
      (by decide) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨100⟩ (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipGrabMem5Trace σCall σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨100⟩).toNat = 228 by decide +native]
        rw [haddrMask, hvowMaskLeft]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨132⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipGrabMem6Trace σCall σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨132⟩).toNat = 260 by decide +native]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨164⟩ (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mstore 0 (endSkipGrabMem7Trace σCall σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) (by decide +native) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨164⟩).toNat = 292 by decide +native]
        rfl)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64Grab (by decide) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push4 ⟨0x7bab3f40⟩ (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw push1 ⟨196⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  have rd4397 : ∃ k' C',
      RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4397⟩
        (endPackVatWord σCall I :: endPackVatWord σCall I :: ⟨0⟩ ::
          endFreeGrabOutPtr :: endFreeGrabInSize :: endFreeGrabOutPtr ::
          endFreeGrabOutSize :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
          endPackVatWord σCall I :: endSkipArtWord vatOut bidOut ::
          endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
          endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
          endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
          endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
        (endSkipGrabMem7Trace σCall σmem σcall I catOut vatOut bidOut)
        (UInt256.ofNat 12) rdata (cA', σCall) k' C' := by
    exact ⟨_, _, by
      simpa [endFreeGrabOutPtr, endFreeGrabInSize, endFreeGrabOutSize,
        endFreeGrabEndPtr, endFreeGrabSelectorWord, endPackVatWord, endPackVowWord,
        endSlotWord, solcSlotWord, solcAddrMask, hvatMask, hvatMaskLeft, hvowMask,
        hvowMaskLeft, husrMask, husrMaskLeft, haddrMask, hthisWord] using rd4397raw⟩
  obtain ⟨k', C', rd4397⟩ := rd4397
  exact ⟨k', C', by simpa [endSkipGrabMem7Trace_eq] using rd4397⟩

theorem endSkipX_grabNoCode {cA cA' gh bl σ σCall σmem σcall σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4295⟩
      (endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      rdata (cA', σCall) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) = ⟨0⟩) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd4397⟩ := endSkipX_grabExtcodesizeGuard hloCat hloVat hloBid h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨4397⟩) (okPc := ⟨4409⟩) rd4397
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_grabCallReady {cA cA' gh bl σ σCall σmem σcall σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut rdata : ByteArray} {k C : ℕ}
    (hloCat : 96 ≤ catOut.size) (hloVat : 160 ≤ vatOut.size)
    (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4295⟩
      (endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipArtStoreHashMemFor σmem σcall I catOut vatOut bidOut) (UInt256.ofNat 12)
      rdata (cA', σCall) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4412⟩
      (gasWord :: endPackVatWord σCall I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σCall) k' C' := by
  obtain ⟨_, _, rd4397⟩ := endSkipX_grabExtcodesizeGuard hloCat hloVat hloBid h
  obtain ⟨gasWord, k', C', rd4412⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4397⟩) (okPc := ⟨4409⟩) rd4397
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd4412⟩

theorem endSkipX_grabPostCall {cA cA' gh bl σ σCall σmem σcall σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut bidOut rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4412⟩
      (gasWord :: endPackVatWord σCall I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σCall) k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (ret : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, ret) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σCall σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endPackVatWord σCall I))
          (toExecute σCall (AccountAddress.ofUInt256 (endPackVatWord σCall I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
            |>.readWithPadding endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4413⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endFreeGrabEndPtr ::
            endFreeGrabSelectorWord :: endPackVatWord σCall I ::
            endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
            endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
            endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
            endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
            endSkipReturnPc :: sel :: [])
          (endSkipGrabPostCallMemForTrace σCall σmem σcall I catOut vatOut bidOut ret)
          (UInt256.ofNat 12) ret (cA'', σ'') k' C'
      ∧ ret.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, ret, Ain, callGas, k', C', hΘ, rd4413raw, hret⟩ :=
    RD.call h (by decide +native) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, ret, Ain, callGas, k', C', ?_, ?_, hret⟩
  · simpa [initState] using hΘ
  · have hmin : (min endFreeGrabOutSize (UInt256.ofNat ret.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat ret.size := by
        show (0 : Nat) ≤ (UInt256.ofNat ret.size).toNat
        exact Nat.zero_le _
      simp [endFreeGrabOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
          endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
          endFreeGrabOutPtr.toNat endFreeGrabOutSize.toNat) = UInt256.ofNat 12 := by
      unfold endFreeGrabOutPtr endFreeGrabInSize endFreeGrabOutSize
      decide +native
    simpa [endSkipGrabPostCallMemForTrace, endFreeGrabOutPtr, endFreeGrabInSize,
      endFreeGrabOutSize, endFreeGrabEndPtr, hmin, byteArray_write_len_zero, haw]
      using rd4413raw

theorem endSkipX_grabCallDepthLimit {cA cA' gh bl σ σCall σmem σcall σ₀ A I}
    {g : Sat256} {sel gasWord : UInt256} {catOut vatOut bidOut rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4412⟩
      (gasWord :: endPackVatWord σCall I :: ⟨0⟩ :: endFreeGrabOutPtr ::
        endFreeGrabInSize :: endFreeGrabOutPtr :: endFreeGrabOutSize ::
        endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) rdata (cA', σCall) k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4413⟩
      (⟨0⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σCall I :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipGrabCalldataMemForTrace σCall σmem σcall I catOut vatOut bidOut)
      (UInt256.ofNat 12) ByteArray.empty (cA', σCall) k' C' := by
  obtain ⟨k', C', rd4413raw⟩ :=
    RD.callDepthLimit h (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endFreeGrabOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 12).toNat
        endFreeGrabOutPtr.toNat endFreeGrabInSize.toNat)
        endFreeGrabOutPtr.toNat endFreeGrabOutSize.toNat) = UInt256.ofNat 12 := by
    unfold endFreeGrabOutPtr endFreeGrabInSize endFreeGrabOutSize
    decide +native
  simpa [endFreeGrabOutPtr, endFreeGrabInSize, endFreeGrabOutSize,
    endFreeGrabEndPtr, hmin, byteArray_write_len_zero, haw] using rd4413raw

theorem endSkipX_grabCallFailed {cA cA' gh bl σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4413⟩
      (⟨0⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σpre I :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4413⟩) (okPc := ⟨4429⟩) h
    rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endSkipX_grabCallSucceeded {cA cA' gh bl σ σpre σpost σ₀ A I}
    {g : Sat256} {sel : UInt256} {catOut vatOut bidOut mem rdata : ByteArray}
    {k C : ℕ}
    (h : RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4413⟩
      (⟨1⟩ :: endFreeGrabEndPtr :: endFreeGrabSelectorWord ::
        endPackVatWord σpre I :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k C) :
    ∃ k' C', RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4431⟩
      (endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σpre I ::
        endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      mem (UInt256.ofNat 12) rdata (cA', σpost) k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨4413⟩) (okPc := ⟨4429⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simp)

theorem endSkipX_grabLogReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} {σCall σmem σcall : AccountMap}
    {catOut vatOut bidOut ret : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true) (hloCat : 96 ≤ catOut.size)
    (hloVat : 160 ≤ vatOut.size) (hloBid : 256 ≤ bidOut.size)
    (h : RD endBytecode I g s0 ⟨4431⟩
      (endFreeGrabEndPtr :: endFreeGrabSelectorWord :: endPackVatWord σCall I ::
        endSkipArtWord vatOut bidOut :: endSkipTabWord bidOut ::
        endSkipUsrWord bidOut :: endSkipLotWord bidOut :: endSkipBidWord bidOut ::
        endFlowVatIlkRateWord vatOut :: endSkipCatIlkFlipWord catOut ::
        endSkipCatIlkFlipWord catOut :: endSkipIdWord I :: endSkipIlkWord I ::
        endSkipReturnPc :: sel :: [])
      (endSkipGrabPostCallMemForTrace σCall σmem σcall I catOut vatOut bidOut ret)
      (UInt256.ofNat 12) ret acc k C) :
    RDret endBytecode g s0 acc ByteArray.empty := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSkipGrabPostCallMemForTrace σCall σmem σcall I catOut vatOut bidOut ret).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkipGrabPostCallMemForTrace σCall σmem σcall I catOut vatOut bidOut ret)
              |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endSkipGrabPostCallMemForTrace_size σCall σmem σcall I catOut vatOut
        bidOut ret hloCat hloVat hloBid]; decide)
      (by decide) (endSkipGrabPostCallMemForTrace_read64 σCall σmem σcall I catOut
        vatOut bidOut ret hloCat hloVat hloBid)
  have hmload64Log :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endSkipLogDataMem3ForTrace σCall σmem σcall I catOut vatOut bidOut ret).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endSkipLogDataMem3ForTrace σCall σmem σcall I catOut vatOut bidOut ret)
              |>.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [endSkipLogDataMem3ForTrace_size σCall σmem σcall I catOut vatOut bidOut
        ret hloCat hloVat hloBid]; decide)
      (by decide) (endSkipLogDataMem3ForTrace_read64 σCall σmem σcall I catOut vatOut
        bidOut ret hloCat hloVat hloBid)
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide +native
  have husrMaskLeft :
      UInt256.land solcAddrMask (endSkipUsrWord bidOut) =
        endSkipUsrAddrWord bidOut := by
    rfl
  have husrMask :
      UInt256.land (endSkipUsrWord bidOut) solcAddrMask =
        endSkipUsrAddrWord bidOut := by
    simpa [endSkipUsrAddrWord] using
      u256_land_comm (endSkipUsrWord bidOut) solcAddrMask
  let skipEvent : UInt256 :=
    ⟨0xbfa2310a8897203a59922debd0db38279196d8de5050df84608e2bb3e7790f69⟩
  have rd4438pre := evm_run h with [
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64 (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rdTabMem := rd4438pre.mstore 0
    (endSkipLogDataMemForTrace σCall σmem σcall I catOut vatOut bidOut ret)
    (UInt256.ofNat 12) (by decide +native) mem_cost (by rfl)
    (by decide +native) (by evm_ov)
  have rd4445pre := evm_run rdTabMem with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup9 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rdLotMem := rd4445pre.mstore 0
    (endSkipLogDataMem2ForTrace σCall σmem σcall I catOut vatOut bidOut ret)
    (UInt256.ofNat 12) (by decide +native) mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 by decide +native]
      rfl)
    (by decide +native) (by evm_ov)
  have rd4451pre := evm_run rdLotMem with [
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup6 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rdArtMem := rd4451pre.mstore 0
    (endSkipLogDataMem3ForTrace σCall σmem σcall I catOut vatOut bidOut ret)
    (UInt256.ofNat 12) (by decide +native) mem_cost
    (by
      rw [show ((⟨64⟩ : UInt256) + ⟨128⟩).toNat = 192 by decide +native]
      rfl)
    (by decide +native) (by evm_ov)
  have rd4471raw := evm_run rdArtMem with [
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by decide +native)
      mem_cost hmload64Log (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup13 (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup14 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov)]
  have rd4471 : ∃ k' C', RD endBytecode I g s0 ⟨4471⟩
      (⟨128⟩ :: ⟨128⟩ :: endSkipIlkWord I :: endSkipIdWord I ::
        endSkipUsrAddrWord bidOut :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipLogDataMem3ForTrace σCall σmem σcall I catOut vatOut bidOut ret)
      (UInt256.ofNat 12) ret acc k' C' := by
    exact ⟨_, _, by simpa [haddrMask, husrMask] using rd4471raw⟩
  obtain ⟨_, _, rd4471⟩ := rd4471
  have rdEvent := rd4471.pushConst skipEvent (width := 32) (op := .PUSH32)
    (by decide +native) (by decide +native) (by evm_ov)
  have rd4513raw := evm_run rdEvent with [
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨96⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd4513 : ∃ k' C', RD endBytecode I g s0 ⟨4513⟩
      (⟨128⟩ :: ⟨96⟩ :: skipEvent :: endSkipIlkWord I :: endSkipIdWord I ::
        endSkipUsrAddrWord bidOut :: endSkipArtWord vatOut bidOut ::
        endSkipTabWord bidOut :: endSkipUsrWord bidOut :: endSkipLotWord bidOut ::
        endSkipBidWord bidOut :: endFlowVatIlkRateWord vatOut ::
        endSkipCatIlkFlipWord catOut :: endSkipCatIlkFlipWord catOut ::
        endSkipIdWord I :: endSkipIlkWord I :: endSkipReturnPc :: sel :: [])
      (endSkipLogDataMem3ForTrace σCall σmem σcall I catOut vatOut bidOut ret)
      (UInt256.ofNat 12) ret acc k' C' := by
    exact ⟨_, _, by simpa [skipEvent] using rd4513raw⟩
  obtain ⟨_, _, rd4513⟩ := rd4513
  have rdLog := RD.log4
    (a := (⟨128⟩ : UInt256)) (b := (⟨96⟩ : UInt256))
    (c := skipEvent) (d := endSkipIlkWord I) (e := endSkipIdWord I)
    (f := endSkipUsrAddrWord bidOut)
    (t := [endSkipArtWord vatOut bidOut, endSkipTabWord bidOut,
      endSkipUsrWord bidOut, endSkipLotWord bidOut, endSkipBidWord bidOut,
      endFlowVatIlkRateWord vatOut, endSkipCatIlkFlipWord catOut,
      endSkipCatIlkFlipWord catOut, endSkipIdWord I, endSkipIlkWord I,
      endSkipReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 12).toNat (⟨128⟩ : UInt256).toNat
        (⟨96⟩ : UInt256).toNat))
    rd4513 (by decide +native) hperm mem_cost (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPopArt := RD.pop (a := endSkipArtWord vatOut bidOut)
    (t := [endSkipTabWord bidOut, endSkipUsrWord bidOut, endSkipLotWord bidOut,
      endSkipBidWord bidOut, endFlowVatIlkRateWord vatOut,
      endSkipCatIlkFlipWord catOut, endSkipCatIlkFlipWord catOut,
      endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel])
    rdLog (by decide +native) (by evm_ov)
  have rdPopTab := RD.pop (a := endSkipTabWord bidOut)
    (t := [endSkipUsrWord bidOut, endSkipLotWord bidOut, endSkipBidWord bidOut,
      endFlowVatIlkRateWord vatOut, endSkipCatIlkFlipWord catOut,
      endSkipCatIlkFlipWord catOut, endSkipIdWord I, endSkipIlkWord I,
      endSkipReturnPc, sel])
    rdPopArt (by decide +native) (by evm_ov)
  have rdPopUsr := RD.pop (a := endSkipUsrWord bidOut)
    (t := [endSkipLotWord bidOut, endSkipBidWord bidOut, endFlowVatIlkRateWord vatOut,
      endSkipCatIlkFlipWord catOut, endSkipCatIlkFlipWord catOut,
      endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel])
    rdPopTab (by decide +native) (by evm_ov)
  have rdPopLot := RD.pop (a := endSkipLotWord bidOut)
    (t := [endSkipBidWord bidOut, endFlowVatIlkRateWord vatOut,
      endSkipCatIlkFlipWord catOut, endSkipCatIlkFlipWord catOut,
      endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel])
    rdPopUsr (by decide +native) (by evm_ov)
  have rdPopBid := RD.pop (a := endSkipBidWord bidOut)
    (t := [endFlowVatIlkRateWord vatOut, endSkipCatIlkFlipWord catOut,
      endSkipCatIlkFlipWord catOut, endSkipIdWord I, endSkipIlkWord I,
      endSkipReturnPc, sel])
    rdPopLot (by decide +native) (by evm_ov)
  have rdPopRate := RD.pop (a := endFlowVatIlkRateWord vatOut)
    (t := [endSkipCatIlkFlipWord catOut, endSkipCatIlkFlipWord catOut,
      endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel])
    rdPopBid (by decide +native) (by evm_ov)
  have rdPopFlipA := RD.pop (a := endSkipCatIlkFlipWord catOut)
    (t := [endSkipCatIlkFlipWord catOut, endSkipIdWord I, endSkipIlkWord I,
      endSkipReturnPc, sel])
    rdPopRate (by decide +native) (by evm_ov)
  have rdPopFlipB := RD.pop (a := endSkipCatIlkFlipWord catOut)
    (t := [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, sel])
    rdPopFlipA (by decide +native) (by evm_ov)
  have rdPopId := RD.pop (a := endSkipIdWord I)
    (t := [endSkipIlkWord I, endSkipReturnPc, sel])
    rdPopFlipB (by decide +native) (by evm_ov)
  have rdPopIlk := RD.pop (a := endSkipIlkWord I)
    (t := [endSkipReturnPc, sel])
    rdPopId (by decide +native) (by evm_ov)
  have rd562 := RD.jump (a := endSkipReturnPc) (t := [sel]) rdPopIlk
    (by decide +native) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endSkipReturnPc) (stk := [sel]) rd562
    (by decide +native) (by evm_ov)
  exact RD.stop rd563 (by decide +native) (by evm_ov)

theorem evalExpr_endSkip_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := endSkipStore I } evm (.var "ilk") =
      .ok (.fixedBytes bytes32Width (endSkipIlkBytes I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable ((endSkipStore I).get? "ilk") =
    .ok (.fixedBytes bytes32Width (endSkipIlkBytes I))
  rw [endSkipStore_get_ilk]
  rfl

theorem evalStorageRef_endSkip_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalStorageRef config { contract := contract, locals := endSkipStore I } evm
      (tagRef (.var "ilk")) = .ok (endSkipTagEvaledRef I) := by
  have hargLen : min 32 (I.calldata.toList.length - 4) = bytes32Width.val + 1 := by
    have htlen : I.calldata.toList.length = I.calldata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [htlen]
    simp [bytes32Width]
    omega
  have hilk := evalExpr_endSkip_ilk evm I
  simp [endSkipTagEvaledRef, endSkipIlkKey, hilk, endSkipIlkBytes,
    endBytes32ArgKey, endBytes32ArgBytes, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, tagRef, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]
  rw [if_pos hargLen]

theorem evalExpr_endSkip_tag (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := endSkipStore I } evm
      (.storage (tagRef (.var "ilk"))) =
        .ok (.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endSkipTagSlot I)).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := endSkipStore I })
    (slot := tagRef (.var "ilk"))
    (er := endSkipTagEvaledRef I)
    (t := .int uint256Int)
    (loc := wordLoc (endSkipTagSlot I))
    (hbase := by simp [endSkipStore, tagRef])
    (her := evalStorageRef_endSkip_tag evm I hsz68)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := endStorageLocLoad_uint256 evm (endSkipTagSlot I))

theorem evalExpr_endSkip_tag_ne_false (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkipTagSlot I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkipStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm
        (.storage (tagRef (.var "ilk"))) = .ok (.int 0) := by
    simpa [htag] using evalExpr_endSkip_tag evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  exact endEvalExpr_ne_int_false hstorage hzero rfl

theorem evalExpr_endSkip_tag_ne_true (evm : EVM.State) (I : ExecutionEnv)
    (hsz68 : 68 ≤ I.calldata.size)
    (htag :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkipTagSlot I) ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := endSkipStore I } evm
      (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm
        (.storage (tagRef (.var "ilk"))) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endSkipTagSlot I)).toNat)) :=
    evalExpr_endSkip_tag evm I hsz68
  have hzero :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  apply endEvalExpr_ne_int_true hstorage hzero
  intro hbad
  exact htag (uint256_toNat_eq_zero (Int.ofNat.inj hbad))

theorem endSkipCatWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    endSkipCatWord σ I = endSkipCatWord τ I := by
  simp [endSkipCatWord, endSlotWord, solcSlotWord,
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩]

theorem endSkipCatAddr_eq_ofUInt256 (σ : AccountMap) (I : ExecutionEnv) :
    endSkipCatAddr σ I = AccountAddress.ofUInt256 (endSkipCatWord σ I) := by
  simpa [endSkipCatAddr] using
    (accountAddress_ofUInt256_eq_ofNat_toNat (endSkipCatWord σ I)).symm

theorem endSkipCatCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne : Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endSkipCatWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endSkipCatWord σ I)
  have htarget : endSkipCatWord σ I = endSkipCatWord τ I :=
    endSkipCatWord_accountMapEquiv hAccounts
  rw [hsame, htarget]
  exact hzero

theorem endSkipCatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endSkipCatWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endSkipCatWord σ I)
  have htarget : endSkipCatWord σ I = endSkipCatWord τ I :=
    endSkipCatWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem endSkipCatCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (endSkipCatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endSkipCatWord σ I) (addr := endSkipCatAddr σ I)
      (endSkipCatAddr_eq_ofUInt256 σ I) hzero

theorem endSkipCatCode_pos_of_codeSize_ne {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne : Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (endSkipCatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [initState, State.lookupAccount] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endSkipCatWord σ I) (addr := endSkipCatAddr σ I)
      (endSkipCatAddr_eq_ofUInt256 σ I) hne

theorem evalStorageRef_endSkip_cat {locals : Store} (_hbase : locals.get? "cat" = none)
    (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := locals } evm
      catRef = .ok ({ base := "cat", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, catRef, EvalResult.bind, pure, bind]

theorem evalExpr_endSkip_cat {locals : Store} (evm : EVM.State)
    (hbase : locals.get? "cat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage catRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := catRef)
    (er := ({ base := "cat", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨2⟩)
    (hbase := hbase)
    (her := evalStorageRef_endSkip_cat hbase evm)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := endStorageLocLoad_address_offset0 evm ⟨2⟩)

theorem endSkipCheckedCatIlksNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSkipStore I } evm0
      (checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
        "catIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.storage catRef) = .ok (.address (endSkipCatAddr σ I)) := by
    have hbase : (endSkipStore I).get? "cat" = none := by
      simp [endSkipStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkipCatAddr, endSkipCatWord, endSlotWord, solcSlotWord] using
      evalExpr_endSkip_cat (locals := endSkipStore I) evm0 hbase
  have hcodeZero :
      (UInt256.ofNat
        ((evm0.lookupAccount (endSkipCatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
    simpa [evm0] using
      endSkipCatCode_zero_of_codeSize_zero
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm0)
      (locals := endSkipStore I) (receiver := .storage catRef)
      (retVar := "catIlk") (name := "catIlks") (sendVal := 0)
      (args := [.var "ilk"]) (perm := true) hguard

theorem endSkipCheckedCatIlksFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSkipCatAddr σ I)) "catIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmCat, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSkipStore I } evm0
      (checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
        "catIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.storage catRef) = .ok (.address (endSkipCatAddr σ I)) := by
    have hbase : (endSkipStore I).get? "cat" = none := by
      simp [endSkipStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkipCatAddr, endSkipCatWord, endSlotWord, solcSlotWord] using
      evalExpr_endSkip_cat (locals := endSkipStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endSkipCatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endSkipCatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk := evalExpr_endSkip_ilk evm0 I
  have hargs :
      evalExprs? config { contract := contract, locals := endSkipStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, endSkipIlkBytes, endBytes32ArgBytes, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmCat)
      (locals := endSkipStore I) (receiver := .storage catRef)
      (retVar := "catIlk") (name := "catIlks") (target := endSkipCatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := out) (perm := true) hguard hreceiver hargs (by simpa [evm0] using hcall)

theorem endSkipCheckedCatIlksDecodeRevert {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSkipCatAddr σ I)) "catIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmCat, out) true)
    (hshort : out.size < 96) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSkipStore I } evm0
      (checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
        "catIlk") .reverted := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.storage catRef) = .ok (.address (endSkipCatAddr σ I)) := by
    have hbase : (endSkipStore I).get? "cat" = none := by
      simp [endSkipStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkipCatAddr, endSkipCatWord, endSlotWord, solcSlotWord] using
      evalExpr_endSkip_cat (locals := endSkipStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endSkipCatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endSkipCatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk := evalExpr_endSkip_ilk evm0 I
  have hargs :
      evalExprs? config { contract := contract, locals := endSkipStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, endSkipIlkBytes, endBytes32ArgBytes, EvalResult.bind, bind, pure]
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm0) (evm' := evmCat)
      (locals := endSkipStore I) (receiver := .storage catRef)
      (retVar := "catIlk") (name := "catIlks") (target := endSkipCatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := out) (perm := true) hguard hreceiver hargs
      (by simpa [evm0] using hcall) (endSkipCatIlksDecode_none_short hshort)

theorem endSkipCheckedCatIlksSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat : EVM.State} {out : ByteArray}
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSkipCatAddr σ I)) "catIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmCat, out) true)
    (hlo : 96 ≤ out.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSkipStore I } evm0
      (checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
        "catIlk")
      (.ok { contract := contract, locals := endSkipStoreCatIlk I out } evmCat) := by
  intro evm0
  have hreceiver :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.storage catRef) = .ok (.address (endSkipCatAddr σ I)) := by
    have hbase : (endSkipStore I).get? "cat" = none := by
      simp [endSkipStore]
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkipCatAddr, endSkipCatWord, endSlotWord, solcSlotWord] using
      evalExpr_endSkip_cat (locals := endSkipStore I) evm0 hbase
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm0.lookupAccount (endSkipCatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
    simpa [evm0] using
      endSkipCatCode_pos_of_codeSize_ne
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.binary .gt (.extCodeSize (.storage catRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hilk := evalExpr_endSkip_ilk evm0 I
  have hargs :
      evalExprs? config { contract := contract, locals := endSkipStore I } evm0 [.var "ilk"] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
    simp [evalExprs?, hilk, endSkipIlkBytes, endBytes32ArgBytes, EvalResult.bind, bind, pure]
  have hvalue := endSkipCatIlksDecode_ok (out := out) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm0) (evm' := evmCat)
    (locals := endSkipStore I) (receiver := .storage catRef)
    (retVar := "catIlk") (name := "catIlks") (target := endSkipCatAddr σ I)
    (sendVal := 0) (args := [.var "ilk"])
    (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
    (out := out) (perm := true)
    (value :=
      [.address (endSkipCatIlkFlipAddr out),
        .int (Int.ofNat (endSkipCatIlkChopWord out).toNat),
        .int (Int.ofNat (endSkipCatIlkLumpWord out).toNat)])
    hguard hreceiver hargs (by simpa [evm0] using hcall) hvalue
  simpa [checkedExternalCallStmts, endSkipStoreCatIlk, collapseReturns] using hblock

theorem evalExpr_endSkip_catIlk_flip (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreCatIlk I out } evm
      (.tupleGet (.var "catIlk") 0) =
        .ok (.address (endSkipCatIlkFlipAddr out)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSkipStoreCatIlk I out } evm
        (.var "catIlk") =
          .ok (.tuple [.address (endSkipCatIlkFlipAddr out),
            .int (Int.ofNat (endSkipCatIlkChopWord out).toNat),
            .int (Int.ofNat (endSkipCatIlkLumpWord out).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkipStoreCatIlk I out).get? "catIlk") =
        .ok (.tuple [.address (endSkipCatIlkFlipAddr out),
          .int (Int.ofNat (endSkipCatIlkChopWord out).toNat),
          .int (Int.ofNat (endSkipCatIlkLumpWord out).toNat)])
    rw [endSkipStoreCatIlk, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem endSkipStmtFlip (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkipStoreCatIlk I out } evm
      (.letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0))
      (.ok { contract := contract, locals := endSkipStoreFlip I out } evm) := by
  simpa [endSkipStoreFlip] using
    ExecStmt.letDecl (evalExpr_endSkip_catIlk_flip evm I out)

theorem endSkipBodyReverts_catIlksBlock {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord σ I ≠ ⟨0⟩)
    (hcatBlock :
      let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
          "catIlk") .reverted) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body .reverted := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSkipTagSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply htag
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkipTagWord, endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endSkip_tag_ne_true evm0 I hsz68 htagLoad
  have hcat :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
          "catIlk") .reverted := by
    simpa [evm0] using hcatBlock
  have hcatWithTail :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
          "catIlk" ++
        [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"] "flipBid"
          (perm := false) ++
        [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
          .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
          .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
          .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ] ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck1" ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, thisAddr, .var "bid"] "_suck2" ++
        checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0) [.var "flip"]
          "_hope" ++
        checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank" ++
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
        [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"] "flipBid"
          (perm := false) ++
        [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
          .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
          .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
          .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ] ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck1" ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, thisAddr, .var "bid"] "_suck2" ++
        checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0) [.var "flip"]
          "_hope" ++
        checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank" ++
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
      hcat (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        skipTransition.body .reverted := by
    simp only [skipTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    simpa [checkedExternalCallStmts, List.append_assoc] using hcatWithTail
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endSkipBodyReverts_catIlksNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body .reverted := by
  intro evm0
  exact endSkipBodyReverts_catIlksBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz68 htag
    (by
      simpa using
        (endSkipCheckedCatIlksNoCode
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcodeSize))

theorem endSkipBodyReverts_catIlksCallFailed {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSkipCatAddr σ I)) "catIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmCat, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body .reverted := by
  intro evm0
  exact endSkipBodyReverts_catIlksBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz68 htag
    (by
      simpa using
        (endSkipCheckedCatIlksFailure
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (evmCat := evmCat) (out := out)
          hcodeSize hcall))

theorem endSkipBodyReverts_catIlksDecodeShort {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSkipCatAddr σ I)) "catIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmCat, out) true)
    (hshort : out.size < 96) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body .reverted := by
  intro evm0
  exact endSkipBodyReverts_catIlksBlock
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hwv hsz68 htag
    (by
      simpa using
        (endSkipCheckedCatIlksDecodeRevert
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (evmCat := evmCat) (out := out)
          hcodeSize hcall hshort))

theorem endSkipPrefixFlipSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmCat : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord σ I ≠ ⟨0⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (endSkipCatAddr σ I)) "catIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmCat, out) true)
    (hlo : 96 ≤ out.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := endSkipStore I } evm0
      (nonpayable ++
        [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
          "catIlk" ++
        [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ])
      (.ok { contract := contract, locals := endSkipStoreFlip I out } evmCat) := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSkipTagSlot I) ≠ ⟨0⟩ := by
    intro hbad
    apply htag
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkipTagWord, endSlotWord, solcSlotWord] using hbad
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool true) :=
    evalExpr_endSkip_tag_ne_true evm0 I hsz68 htagLoad
  have hcat :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
          "catIlk")
        (.ok { contract := contract, locals := endSkipStoreCatIlk I out } evmCat) := by
    simpa [evm0] using
      endSkipCheckedCatIlksSuccess
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) (evmCat := evmCat) (out := out)
        hcodeSize hcall hlo
  have hflip :
      ExecBlock config { contract := contract, locals := endSkipStoreCatIlk I out } evmCat
        [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ]
        (.ok { contract := contract, locals := endSkipStoreFlip I out } evmCat) := by
    exact ExecBlock.consNormal (endSkipStmtFlip evmCat I out) ExecBlock.nil
  have hcatFlip :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
          "catIlk" ++
        [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ])
        (.ok { contract := contract, locals := endSkipStoreFlip I out } evmCat) := by
    exact execBlock_append hcat hflip
  simp only [nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  simpa [List.append_assoc] using hcatFlip

theorem endSkipVatReceiver_afterFlip {σ I catOut evm}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSkipStoreFlip I catOut } evm
      (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
  have hbase : (endSkipStoreFlip I catOut).get? "vat" = none := by
    simp [endSkipStoreFlip, endSkipStoreCatIlk, endSkipStore]
  simpa [hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
    evalExpr_endPack_vat (locals := endSkipStoreFlip I catOut) evm hbase

theorem endSkipVatCode_zero_afterFlip {σ I} {catOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hzero : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
  simpa [State.lookupAccount, hmap] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endPackVatWord σ I) (addr := endPackVatAddr σ I)
      (endPackVatAddr_eq_ofUInt256 σ I) hzero

theorem endSkipVatCode_pos_afterFlip {σ I} {catOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hne : Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (endPackVatAddr σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount, hmap] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endPackVatWord σ I) (addr := endPackVatAddr σ I)
      (endPackVatAddr_eq_ofUInt256 σ I) hne

theorem evalExprs_endSkip_vatIlksArgs_afterFlip (evm : EVM.State)
    (I : ExecutionEnv) (catOut : ByteArray) :
    evalExprs? config { contract := contract, locals := endSkipStoreFlip I catOut } evm
      [.var "ilk"] = .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I)] := by
  have hilk :
      evalExpr? config { contract := contract, locals := endSkipStoreFlip I catOut } evm
        (.var "ilk") = .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkipStoreFlip I catOut).get? "ilk") =
        .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I))
    rw [endSkipStoreFlip, store_get_ne _ _ (by decide +native),
      endSkipStoreCatIlk, store_get_ne _ _ (by decide +native), endSkipStore_get_ilk]
    rfl
  simp [evalExprs?, hilk, endSkipIlkBytes, endBytes32ArgBytes, EvalResult.bind, bind, pure]

theorem endSkipCheckedVatIlksNoCode {σ I} {catOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSkipStoreFlip I catOut } evm
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  have hreceiver := endSkipVatReceiver_afterFlip (σ := σ) (I := I) (catOut := catOut)
    (evm := evm) hmap howner
  have hcodeZero := endSkipVatCode_zero_afterFlip (σ := σ) (I := I) (catOut := catOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreFlip I catOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSkipStoreFlip I catOut) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (sendVal := 0)
      (args := [.var "ilk"]) (perm := true) hguard

theorem endSkipCheckedVatIlksFailure {σ I} {catOut vatOut : ByteArray}
    {evm evmVat : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (false, evmVat, vatOut) true) :
    ExecBlock config { contract := contract, locals := endSkipStoreFlip I catOut } evm
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  have hreceiver := endSkipVatReceiver_afterFlip (σ := σ) (I := I) (catOut := catOut)
    (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip (σ := σ) (I := I) (catOut := catOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreFlip I catOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_vatIlksArgs_afterFlip evm I catOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmVat)
      (locals := endSkipStoreFlip I catOut) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := vatOut) (perm := true) hguard hreceiver hargs hcall

theorem endSkipCheckedVatIlksDecodeRevert {σ I} {catOut vatOut : ByteArray}
    {evm evmVat : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, vatOut) true)
    (hshort : vatOut.size < 160) :
    ExecBlock config { contract := contract, locals := endSkipStoreFlip I catOut } evm
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk") .reverted := by
  have hreceiver := endSkipVatReceiver_afterFlip (σ := σ) (I := I) (catOut := catOut)
    (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip (σ := σ) (I := I) (catOut := catOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreFlip I catOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_vatIlksArgs_afterFlip evm I catOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evmVat)
      (locals := endSkipStoreFlip I catOut) (receiver := .storage vatRef)
      (retVar := "vatIlk") (name := "vatIlks") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "ilk"])
      (argVals := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
      (out := vatOut) (perm := true) hguard hreceiver hargs hcall
      (endFlowVatIlksDecode_none_short hshort)

theorem endSkipCheckedVatIlksSuccess {σ I} {catOut vatOut : ByteArray}
    {evm evmVat : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "vatIlks" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
        (true, evmVat, vatOut) true)
    (hlo : 160 ≤ vatOut.size) :
    ExecBlock config { contract := contract, locals := endSkipStoreFlip I catOut } evm
      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
        "vatIlk")
      (.ok { contract := contract, locals := endSkipStoreVatIlk I catOut vatOut }
        evmVat) := by
  have hreceiver := endSkipVatReceiver_afterFlip (σ := σ) (I := I) (catOut := catOut)
    (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip (σ := σ) (I := I) (catOut := catOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreFlip I catOut } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_vatIlksArgs_afterFlip evm I catOut
  have hvalue := endFlowVatIlksDecode_ok (out := vatOut) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmVat)
    (locals := endSkipStoreFlip I catOut) (receiver := .storage vatRef)
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
  simpa [checkedExternalCallStmts, endSkipStoreVatIlk, collapseReturns] using hblock

theorem evalExpr_endSkip_vatIlk_rate (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreVatIlk I catOut vatOut } evm
      (.tupleGet (.var "vatIlk") 1) =
        .ok (.int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSkipStoreVatIlk I catOut vatOut } evm
        (.var "vatIlk") =
          .ok (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord vatOut).toNat),
            .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat),
            .int (Int.ofNat (endFlowVatIlkSpotWord vatOut).toNat),
            .int (Int.ofNat (endFlowVatIlkLineWord vatOut).toNat),
            .int (Int.ofNat (endFlowVatIlkDustWord vatOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkipStoreVatIlk I catOut vatOut).get? "vatIlk") =
        .ok (.tuple [.int (Int.ofNat (endFlowVatIlkArtWord vatOut).toNat),
          .int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat),
          .int (Int.ofNat (endFlowVatIlkSpotWord vatOut).toNat),
          .int (Int.ofNat (endFlowVatIlkLineWord vatOut).toNat),
          .int (Int.ofNat (endFlowVatIlkDustWord vatOut).toNat)])
    rw [endSkipStoreVatIlk, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem endSkipStmtRate (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkipStoreVatIlk I catOut vatOut }
      evm (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
      (.ok { contract := contract, locals := endSkipStoreRate I catOut vatOut } evm) := by
  simpa [endSkipStoreRate] using
    ExecStmt.letDecl (evalExpr_endSkip_vatIlk_rate evm I catOut vatOut)

theorem endSkipPrefixRateSuccess {I} {catOut vatOut : ByteArray}
    {evm0 evmCat evmVat : EVM.State}
    (hprefix :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
            "catIlk" ++
          [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ])
        (.ok { contract := contract, locals := endSkipStoreFlip I catOut } evmCat))
    (hvat :
      ExecBlock config { contract := contract, locals := endSkipStoreFlip I catOut } evmCat
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk")
        (.ok { contract := contract, locals := endSkipStoreVatIlk I catOut vatOut }
          evmVat)) :
    ExecBlock config { contract := contract, locals := endSkipStore I } evm0
      (nonpayable ++
        [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
          "catIlk" ++
        [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
      (.ok { contract := contract, locals := endSkipStoreRate I catOut vatOut }
        evmVat) := by
  have hrate :
      ExecBlock config { contract := contract, locals := endSkipStoreVatIlk I catOut vatOut }
        evmVat
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ]
        (.ok { contract := contract, locals := endSkipStoreRate I catOut vatOut } evmVat) := by
    exact ExecBlock.consNormal (endSkipStmtRate evmVat I catOut vatOut) ExecBlock.nil
  have hvatRate :
      ExecBlock config { contract := contract, locals := endSkipStoreFlip I catOut } evmCat
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
        (.ok { contract := contract, locals := endSkipStoreRate I catOut vatOut }
          evmVat) := by
    exact execBlock_append hvat hrate
  have hseq := execBlock_append hprefix hvatRate
  simpa [List.append_assoc] using hseq

theorem endSkipBodyReverts_afterFlipVatIlksBlock {I} {catOut : ByteArray}
    {evm0 evmCat : EVM.State}
    (hprefix :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
            "catIlk" ++
          [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ])
        (.ok { contract := contract, locals := endSkipStoreFlip I catOut } evmCat))
    (hvat :
      ExecBlock config { contract := contract, locals := endSkipStoreFlip I catOut } evmCat
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk") .reverted) :
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body .reverted := by
  let afterVat : List Stmt :=
    [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
    checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"] "flipBid"
      (perm := false) ++
    [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
      .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
      .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
      .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ] ++
    checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
      [vowAddr, vowAddr, .var "tab"] "_suck1" ++
    checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
      [vowAddr, thisAddr, .var "bid"] "_suck2" ++
    checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0) [.var "flip"] "_hope" ++
    checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank" ++
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
      ExecBlock config { contract := contract, locals := endSkipStoreFlip I catOut } evmCat
        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++ afterVat) .reverted := by
    exact execBlock_append_term
      (s2 := afterVat) hvat (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        skipTransition.body .reverted := by
    have hseq := execBlock_append hprefix hvatWithTail
    simpa [skipTransition, afterVat, List.append_assoc] using hseq
  exact ExecFuncBody.execBlockRevert hblock

theorem endSkipCatIlkFlipAddr_eq_ofUInt256 (catOut : ByteArray) :
    endSkipCatIlkFlipAddr catOut =
      AccountAddress.ofUInt256 (endSkipCatIlkFlipTargetWord catOut) := by
  have hval :
      Solm.Value.address (endSkipCatIlkFlipAddr catOut) =
        Solm.Value.address (AccountAddress.ofUInt256 (endSkipCatIlkFlipTargetWord catOut)) := by
    simpa [endSkipCatIlkFlipAddr, endSkipCatIlkFlipTargetWord,
      accountAddress_ofUInt256_eq_ofNat_toNat] using
      solcAddressValue_masked (endSkipCatIlkFlipWord catOut)
  exact Solm.Value.address.inj hval

theorem endSkipBidsReceiver_afterRate {I catOut vatOut evm} :
    evalExpr? config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
      evm (.var "flip") = .ok (.address (endSkipCatIlkFlipAddr catOut)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((endSkipStoreRate I catOut vatOut).get? "flip") =
    .ok (.address (endSkipCatIlkFlipAddr catOut))
  rw [endSkipStoreRate, store_get_ne _ _ (by decide +native),
    endSkipStoreVatIlk, store_get_ne _ _ (by decide +native),
    endSkipStoreFlip, store_get_self]
  rfl

theorem endSkipBidsCode_zero_afterRate {σ : AccountMap} {catOut : ByteArray}
    {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) =
        ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (endSkipCatIlkFlipAddr catOut)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  simpa [State.lookupAccount, hmap] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endSkipCatIlkFlipTargetWord catOut)
      (addr := endSkipCatIlkFlipAddr catOut)
      (endSkipCatIlkFlipAddr_eq_ofUInt256 catOut) hzero

theorem endSkipBidsCode_pos_afterRate {σ : AccountMap} {catOut : ByteArray}
    {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) ≠
        ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (endSkipCatIlkFlipAddr catOut)).option 0
        (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount, hmap] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endSkipCatIlkFlipTargetWord catOut)
      (addr := endSkipCatIlkFlipAddr catOut)
      (endSkipCatIlkFlipAddr_eq_ofUInt256 catOut) hne

theorem endSkipBidsCodeSize_zero_accountMapEquiv {σ τ : AccountMap}
    (hAccounts : accountMapEquiv σ τ) (catOut : ByteArray)
    (hcode :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) =
        ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endSkipCatIlkFlipTargetWord catOut) =
      ⟨0⟩ := by
  rw [← Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
    (endSkipCatIlkFlipTargetWord catOut)]
  exact hcode

theorem endSkipBidsCodeSize_ne_accountMapEquiv {σ τ : AccountMap}
    (hAccounts : accountMapEquiv σ τ) (catOut : ByteArray)
    (hcode :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) ≠
        ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endSkipCatIlkFlipTargetWord catOut) ≠
      ⟨0⟩ := by
  intro hbad
  rw [← Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
    (endSkipCatIlkFlipTargetWord catOut)] at hbad
  exact hcode hbad

theorem evalExprs_endSkip_bidsArgs_afterRate (evm : EVM.State)
    (I : ExecutionEnv) (catOut vatOut : ByteArray) :
    evalExprs? config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
      evm [.var "id"] = .ok [.int (Int.ofNat (endSkipIdWord I).toNat)] := by
  have hid :
      evalExpr? config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
        evm (.var "id") = .ok (.int (Int.ofNat (endSkipIdWord I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endSkipStoreRate I catOut vatOut).get? "id") =
      .ok (.int (Int.ofNat (endSkipIdWord I).toNat))
    rw [endSkipStoreRate, store_get_ne _ _ (by decide +native),
      endSkipStoreVatIlk, store_get_ne _ _ (by decide +native),
      endSkipStoreFlip, store_get_ne _ _ (by decide +native),
      endSkipStoreCatIlk, store_get_ne _ _ (by decide +native),
      endSkipStore, store_get_self]
    rfl
  simp [evalExprs?, hid, EvalResult.bind, bind, pure]

theorem endSkipCheckedBidsNoCode {σ I} {catOut vatOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) =
        ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSkipStoreRate I catOut vatOut } evm
      (checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
        "flipBid" (perm := false)) .reverted := by
  have hreceiver := endSkipBidsReceiver_afterRate (I := I) (catOut := catOut)
    (vatOut := vatOut) (evm := evm)
  have hcodeZero := endSkipBidsCode_zero_afterRate (σ := σ) (catOut := catOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
        evm (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSkipStoreRate I catOut vatOut) (receiver := .var "flip")
      (retVar := "flipBid") (name := "bids") (sendVal := 0)
      (args := [.var "id"]) (perm := false) hguard

theorem endSkipCheckedBidsFailure {σ I} {catOut vatOut bidOut : ByteArray}
    {evm evmBids : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) ≠
        ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endSkipCatIlkFlipAddr catOut))
        "bids" 0 [.int (Int.ofNat (endSkipIdWord I).toNat)]
        (false, evmBids, bidOut) false) :
    ExecBlock config { contract := contract, locals := endSkipStoreRate I catOut vatOut } evm
      (checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
        "flipBid" (perm := false)) .reverted := by
  have hreceiver := endSkipBidsReceiver_afterRate (I := I) (catOut := catOut)
    (vatOut := vatOut) (evm := evm)
  have hcodePos := endSkipBidsCode_pos_afterRate (σ := σ) (catOut := catOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
        evm (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_bidsArgs_afterRate evm I catOut vatOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmBids)
      (locals := endSkipStoreRate I catOut vatOut) (receiver := .var "flip")
      (retVar := "flipBid") (name := "bids")
      (target := endSkipCatIlkFlipAddr catOut)
      (sendVal := 0) (args := [.var "id"])
      (argVals := [.int (Int.ofNat (endSkipIdWord I).toNat)])
      (out := bidOut) (perm := false) hguard hreceiver hargs hcall

theorem endSkipCheckedBidsDecodeRevert {σ I} {catOut vatOut bidOut : ByteArray}
    {evm evmBids : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) ≠
        ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endSkipCatIlkFlipAddr catOut))
        "bids" 0 [.int (Int.ofNat (endSkipIdWord I).toNat)]
        (true, evmBids, bidOut) false)
    (hshort : bidOut.size < 256) :
    ExecBlock config { contract := contract, locals := endSkipStoreRate I catOut vatOut } evm
      (checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
        "flipBid" (perm := false)) .reverted := by
  have hreceiver := endSkipBidsReceiver_afterRate (I := I) (catOut := catOut)
    (vatOut := vatOut) (evm := evm)
  have hcodePos := endSkipBidsCode_pos_afterRate (σ := σ) (catOut := catOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
        evm (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_bidsArgs_afterRate evm I catOut vatOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallDecodeRevert
      (cfg := config) (C := contract) (evm := evm) (evm' := evmBids)
      (locals := endSkipStoreRate I catOut vatOut) (receiver := .var "flip")
      (retVar := "flipBid") (name := "bids")
      (target := endSkipCatIlkFlipAddr catOut)
      (sendVal := 0) (args := [.var "id"])
      (argVals := [.int (Int.ofNat (endSkipIdWord I).toNat)])
      (out := bidOut) (perm := false) hguard hreceiver hargs hcall
      (endSkipBidsDecode_none_short hshort)

theorem endSkipCheckedBidsSuccess {σ I} {catOut vatOut bidOut : ByteArray}
    {evm evmBids : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) ≠
        ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endSkipCatIlkFlipAddr catOut))
        "bids" 0 [.int (Int.ofNat (endSkipIdWord I).toNat)]
        (true, evmBids, bidOut) false)
    (hlo : 256 ≤ bidOut.size) :
    ExecBlock config { contract := contract, locals := endSkipStoreRate I catOut vatOut } evm
      (checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
        "flipBid" (perm := false))
      (.ok { contract := contract, locals := endSkipStoreFlipBid I catOut vatOut bidOut }
        evmBids) := by
  have hreceiver := endSkipBidsReceiver_afterRate (I := I) (catOut := catOut)
    (vatOut := vatOut) (evm := evm)
  have hcodePos := endSkipBidsCode_pos_afterRate (σ := σ) (catOut := catOut)
    (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
        evm (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_bidsArgs_afterRate evm I catOut vatOut
  have hvalue := endSkipBidsDecode_ok (out := bidOut) hlo
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmBids)
    (locals := endSkipStoreRate I catOut vatOut) (receiver := .var "flip")
    (retVar := "flipBid") (name := "bids")
    (target := endSkipCatIlkFlipAddr catOut)
    (sendVal := 0) (args := [.var "id"])
    (argVals := [.int (Int.ofNat (endSkipIdWord I).toNat)])
    (out := bidOut) (perm := false)
    (value := [.int (Int.ofNat (endSkipBidWord bidOut).toNat),
      .int (Int.ofNat (endSkipLotWord bidOut).toNat),
      .address (AccountAddress.ofNat (endSkipBidGuyWord bidOut).toNat),
      .int (Int.ofNat ((endSkipBidTicWord bidOut).toNat % EVM.twoPow 48)),
      .int (Int.ofNat ((endSkipBidEndWord bidOut).toNat % EVM.twoPow 48)),
      .address (endSkipUsrAddr bidOut),
      .address (AccountAddress.ofNat (endSkipBidGalWord bidOut).toNat),
      .int (Int.ofNat (endSkipTabWord bidOut).toNat)])
    hguard hreceiver hargs hcall hvalue
  simpa [checkedExternalCallStmts, endSkipStoreFlipBid, collapseReturns] using hblock

theorem evalExpr_endSkip_flipBid_bid (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreFlipBid I catOut vatOut bidOut }
      evm (.tupleGet (.var "flipBid") 0) =
        .ok (.int (Int.ofNat (endSkipBidWord bidOut).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSkipStoreFlipBid I catOut vatOut bidOut }
        evm (.var "flipBid") =
          .ok (.tuple [.int (Int.ofNat (endSkipBidWord bidOut).toNat),
            .int (Int.ofNat (endSkipLotWord bidOut).toNat),
            .address (AccountAddress.ofNat (endSkipBidGuyWord bidOut).toNat),
            .int (Int.ofNat ((endSkipBidTicWord bidOut).toNat % EVM.twoPow 48)),
            .int (Int.ofNat ((endSkipBidEndWord bidOut).toNat % EVM.twoPow 48)),
            .address (endSkipUsrAddr bidOut),
            .address (AccountAddress.ofNat (endSkipBidGalWord bidOut).toNat),
            .int (Int.ofNat (endSkipTabWord bidOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkipStoreFlipBid I catOut vatOut bidOut).get? "flipBid") = _
    rw [endSkipStoreFlipBid, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalExpr_endSkip_flipBid_lot (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreBid I catOut vatOut bidOut }
      evm (.tupleGet (.var "flipBid") 1) =
        .ok (.int (Int.ofNat (endSkipLotWord bidOut).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSkipStoreBid I catOut vatOut bidOut }
        evm (.var "flipBid") =
          .ok (.tuple [.int (Int.ofNat (endSkipBidWord bidOut).toNat),
            .int (Int.ofNat (endSkipLotWord bidOut).toNat),
            .address (AccountAddress.ofNat (endSkipBidGuyWord bidOut).toNat),
            .int (Int.ofNat ((endSkipBidTicWord bidOut).toNat % EVM.twoPow 48)),
            .int (Int.ofNat ((endSkipBidEndWord bidOut).toNat % EVM.twoPow 48)),
            .address (endSkipUsrAddr bidOut),
            .address (AccountAddress.ofNat (endSkipBidGalWord bidOut).toNat),
            .int (Int.ofNat (endSkipTabWord bidOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkipStoreBid I catOut vatOut bidOut).get? "flipBid") = _
    rw [endSkipStoreBid, store_get_ne _ _ (by decide +native),
      endSkipStoreFlipBid, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalExpr_endSkip_flipBid_usr (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreLot I catOut vatOut bidOut }
      evm (.tupleGet (.var "flipBid") 5) =
        .ok (.address (endSkipUsrAddr bidOut)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSkipStoreLot I catOut vatOut bidOut }
        evm (.var "flipBid") =
          .ok (.tuple [.int (Int.ofNat (endSkipBidWord bidOut).toNat),
            .int (Int.ofNat (endSkipLotWord bidOut).toNat),
            .address (AccountAddress.ofNat (endSkipBidGuyWord bidOut).toNat),
            .int (Int.ofNat ((endSkipBidTicWord bidOut).toNat % EVM.twoPow 48)),
            .int (Int.ofNat ((endSkipBidEndWord bidOut).toNat % EVM.twoPow 48)),
            .address (endSkipUsrAddr bidOut),
            .address (AccountAddress.ofNat (endSkipBidGalWord bidOut).toNat),
            .int (Int.ofNat (endSkipTabWord bidOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkipStoreLot I catOut vatOut bidOut).get? "flipBid") = _
    rw [endSkipStoreLot, store_get_ne _ _ (by decide +native),
      endSkipStoreBid, store_get_ne _ _ (by decide +native),
      endSkipStoreFlipBid, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalExpr_endSkip_flipBid_tab (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreUsr I catOut vatOut bidOut }
      evm (.tupleGet (.var "flipBid") 7) =
        .ok (.int (Int.ofNat (endSkipTabWord bidOut).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := endSkipStoreUsr I catOut vatOut bidOut }
        evm (.var "flipBid") =
          .ok (.tuple [.int (Int.ofNat (endSkipBidWord bidOut).toNat),
            .int (Int.ofNat (endSkipLotWord bidOut).toNat),
            .address (AccountAddress.ofNat (endSkipBidGuyWord bidOut).toNat),
            .int (Int.ofNat ((endSkipBidTicWord bidOut).toNat % EVM.twoPow 48)),
            .int (Int.ofNat ((endSkipBidEndWord bidOut).toNat % EVM.twoPow 48)),
            .address (endSkipUsrAddr bidOut),
            .address (AccountAddress.ofNat (endSkipBidGalWord bidOut).toNat),
            .int (Int.ofNat (endSkipTabWord bidOut).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((endSkipStoreUsr I catOut vatOut bidOut).get? "flipBid") = _
    rw [endSkipStoreUsr, store_get_ne _ _ (by decide +native),
      endSkipStoreLot, store_get_ne _ _ (by decide +native),
      endSkipStoreBid, store_get_ne _ _ (by decide +native),
      endSkipStoreFlipBid, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem endSkipStmtBid (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkipStoreFlipBid I catOut vatOut bidOut }
      evm (.letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0))
      (.ok { contract := contract, locals := endSkipStoreBid I catOut vatOut bidOut } evm) := by
  simpa [endSkipStoreBid] using
    ExecStmt.letDecl (evalExpr_endSkip_flipBid_bid evm I catOut vatOut bidOut)

theorem endSkipStmtLot (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkipStoreBid I catOut vatOut bidOut }
      evm (.letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1))
      (.ok { contract := contract, locals := endSkipStoreLot I catOut vatOut bidOut } evm) := by
  simpa [endSkipStoreLot] using
    ExecStmt.letDecl (evalExpr_endSkip_flipBid_lot evm I catOut vatOut bidOut)

theorem endSkipStmtUsr (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkipStoreLot I catOut vatOut bidOut }
      evm (.letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5))
      (.ok { contract := contract, locals := endSkipStoreUsr I catOut vatOut bidOut } evm) := by
  simpa [endSkipStoreUsr] using
    ExecStmt.letDecl (evalExpr_endSkip_flipBid_usr evm I catOut vatOut bidOut)

theorem endSkipStmtTab (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) :
    ExecStmt config { contract := contract, locals := endSkipStoreUsr I catOut vatOut bidOut }
      evm (.letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7))
      (.ok { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut } evm) := by
  simpa [endSkipStoreTab] using
    ExecStmt.letDecl (evalExpr_endSkip_flipBid_tab evm I catOut vatOut bidOut)

theorem endSkipPrefixTabSuccess {I} {catOut vatOut bidOut : ByteArray}
    {evm0 evmVat evmBids : EVM.State}
    (hprefix :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
            "catIlk" ++
          [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
        (.ok { contract := contract, locals := endSkipStoreRate I catOut vatOut } evmVat))
    (hbids :
      ExecBlock config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
        evmVat
        (checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
          "flipBid" (perm := false))
        (.ok { contract := contract, locals := endSkipStoreFlipBid I catOut vatOut bidOut }
          evmBids)) :
    ExecBlock config { contract := contract, locals := endSkipStore I } evm0
      (nonpayable ++
        [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
        checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
          "catIlk" ++
        [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
          "flipBid" (perm := false) ++
        [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
          .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
          .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
          .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ])
      (.ok { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmBids) := by
  have hlets :
      ExecBlock config
        { contract := contract, locals := endSkipStoreFlipBid I catOut vatOut bidOut }
        evmBids
        [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
          .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
          .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
          .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ]
        (.ok { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
          evmBids) := by
    refine ExecBlock.consNormal (endSkipStmtBid evmBids I catOut vatOut bidOut) ?_
    refine ExecBlock.consNormal (endSkipStmtLot evmBids I catOut vatOut bidOut) ?_
    refine ExecBlock.consNormal (endSkipStmtUsr evmBids I catOut vatOut bidOut) ?_
    exact ExecBlock.consNormal (endSkipStmtTab evmBids I catOut vatOut bidOut) ExecBlock.nil
  have hbidsLets :
      ExecBlock config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
        evmVat
        (checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
          "flipBid" (perm := false) ++
        [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
          .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
          .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
          .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ])
        (.ok { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
          evmBids) := by
    exact execBlock_append hbids hlets
  have hseq := execBlock_append hprefix hbidsLets
  simpa [List.append_assoc] using hseq

theorem endSkipBodyReverts_afterRateBidsBlock {I} {catOut vatOut : ByteArray}
    {evm0 evmVat : EVM.State}
    (hprefix :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
            "catIlk" ++
          [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
        (.ok { contract := contract, locals := endSkipStoreRate I catOut vatOut } evmVat))
    (hbids :
      ExecBlock config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
        evmVat
        (checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
          "flipBid" (perm := false)) .reverted) :
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body .reverted := by
  let afterBids : List Stmt :=
    [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
      .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
      .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
      .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ] ++
    checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
      [vowAddr, vowAddr, .var "tab"] "_suck1" ++
    checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
      [vowAddr, thisAddr, .var "bid"] "_suck2" ++
    checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0) [.var "flip"] "_hope" ++
    checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank" ++
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
  have hbidsWithTail :
      ExecBlock config { contract := contract, locals := endSkipStoreRate I catOut vatOut }
        evmVat
        (checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
          "flipBid" (perm := false) ++ afterBids) .reverted := by
    exact execBlock_append_term
      (s2 := afterBids) hbids (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        skipTransition.body .reverted := by
    have hseq := execBlock_append hprefix hbidsWithTail
    simpa [skipTransition, afterBids, List.append_assoc] using hseq
  exact ExecFuncBody.execBlockRevert hblock

theorem endSkipVatReceiver_afterTab {σ I catOut vatOut bidOut evm}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evm (.storage vatRef) = .ok (.address (endPackVatAddr σ I)) := by
  have hbase : (endSkipStoreTab I catOut vatOut bidOut).get? "vat" = none := by
    simp [endSkipStoreTab, endSkipStoreUsr, endSkipStoreLot, endSkipStoreBid,
      endSkipStoreFlipBid, endSkipStoreRate, endSkipStoreVatIlk, endSkipStoreFlip,
      endSkipStoreCatIlk, endSkipStore]
  simpa [hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
    evalExpr_endPack_vat (locals := endSkipStoreTab I catOut vatOut bidOut) evm hbase

theorem evalExprs_endSkip_suck1Args_afterTab (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray)
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExprs? config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evm [vowAddr, vowAddr, .var "tab"] =
        .ok [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSkipTabWord bidOut).toNat)] := by
  have hvow :
      evalExpr? config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evm vowAddr = .ok (.address (endPackVowAddr σ I)) := by
    have hbase : (endSkipStoreTab I catOut vatOut bidOut).get? "vow" = none := by
      simp [endSkipStoreTab, endSkipStoreUsr, endSkipStoreLot, endSkipStoreBid,
        endSkipStoreFlipBid, endSkipStoreRate, endSkipStoreVatIlk, endSkipStoreFlip,
        endSkipStoreCatIlk, endSkipStore]
    simpa [vowAddr, hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVowAddr, endPackVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vow (locals := endSkipStoreTab I catOut vatOut bidOut) evm hbase
  have htab :
      evalExpr? config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evm (.var "tab") = .ok (.int (Int.ofNat (endSkipTabWord bidOut).toNat)) := by
    simpa [endSkipStoreTab] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkipStoreTab I catOut vatOut bidOut)
        (name := "tab") (value := endSkipTabWord bidOut)
        (by rw [endSkipStoreTab, store_get_self])
  simp [evalExprs?, hvow, htab, EvalResult.bind, bind, pure]

theorem endSkipCheckedSuck1NoCode {σ I} {catOut vatOut bidOut : ByteArray}
    {evm : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, vowAddr, .var "tab"] "_suck1") .reverted := by
  have hreceiver := endSkipVatReceiver_afterTab
    (σ := σ) (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut)
    (evm := evm) hmap howner
  have hcodeZero := endSkipVatCode_zero_afterFlip
    (σ := σ) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSkipStoreTab I catOut vatOut bidOut) (receiver := .storage vatRef)
      (retVar := "_suck1") (name := "suck") (sendVal := 0)
      (args := [vowAddr, vowAddr, .var "tab"]) (perm := true) hguard

theorem endSkipCheckedSuck1Failure {σ I} {catOut vatOut bidOut suckOut : ByteArray}
    {evm evmSuck : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "suck" 0
        [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSkipTabWord bidOut).toNat)]
        (false, evmSuck, suckOut) true) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, vowAddr, .var "tab"] "_suck1") .reverted := by
  have hreceiver := endSkipVatReceiver_afterTab
    (σ := σ) (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut)
    (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip
    (σ := σ) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_suck1Args_afterTab evm I σ catOut vatOut bidOut
    hmap howner
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmSuck)
      (locals := endSkipStoreTab I catOut vatOut bidOut) (receiver := .storage vatRef)
      (retVar := "_suck1") (name := "suck") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [vowAddr, vowAddr, .var "tab"])
      (argVals :=
        [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSkipTabWord bidOut).toNat)])
      (out := suckOut) (perm := true) hguard hreceiver hargs hcall

theorem endSkipCheckedSuck1Success {σ I} {catOut vatOut bidOut suckOut : ByteArray}
    {evm evmSuck : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "suck" 0
        [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
          .int (Int.ofNat (endSkipTabWord bidOut).toNat)]
        (true, evmSuck, suckOut) true) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, vowAddr, .var "tab"] "_suck1")
      (.ok { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evmSuck) := by
  have hreceiver := endSkipVatReceiver_afterTab
    (σ := σ) (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut)
    (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip
    (σ := σ) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_suck1Args_afterTab evm I σ catOut vatOut bidOut
    hmap howner
  have hdec : config.externalABI.decode? "suck" suckOut = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmSuck)
    (locals := endSkipStoreTab I catOut vatOut bidOut) (receiver := .storage vatRef)
    (retVar := "_suck1") (name := "suck") (target := endPackVatAddr σ I)
    (sendVal := 0) (args := [vowAddr, vowAddr, .var "tab"])
    (argVals :=
      [.address (endPackVowAddr σ I), .address (endPackVowAddr σ I),
        .int (Int.ofNat (endSkipTabWord bidOut).toNat)])
    (out := suckOut) (perm := true) (value := [])
    hguard hreceiver hargs hcall hdec
  simpa [checkedExternalCallStmts, endSkipStoreSuck1, collapseReturns] using hblock

theorem endSkipVatReceiver_afterSuck1 {σ I catOut vatOut bidOut evm}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
      evm (.storage vatRef) =
        .ok (.address (endPackVatAddr σ I)) := by
  have hbase : (endSkipStoreSuck1 I catOut vatOut bidOut).get? "vat" = none := by
    simp [endSkipStoreSuck1, endSkipStoreTab, endSkipStoreUsr, endSkipStoreLot,
      endSkipStoreBid, endSkipStoreFlipBid, endSkipStoreRate, endSkipStoreVatIlk,
      endSkipStoreFlip, endSkipStoreCatIlk, endSkipStore]
  simpa [hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
    evalExpr_endPack_vat
      (locals := endSkipStoreSuck1 I catOut vatOut bidOut) evm hbase

theorem evalExprs_endSkip_suck2Args_afterSuck1 (evm : EVM.State)
    (I : ExecutionEnv) (σ : AccountMap) (catOut vatOut bidOut : ByteArray)
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExprs? config
      { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
      evm [vowAddr, thisAddr, .var "bid"] =
        .ok [.address (endPackVowAddr σ I), .address I.codeOwner,
          .int (Int.ofNat (endSkipBidWord bidOut).toNat)] := by
  have hvow :
      evalExpr? config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evm vowAddr = .ok (.address (endPackVowAddr σ I)) := by
    have hbase : (endSkipStoreSuck1 I catOut vatOut bidOut).get? "vow" = none := by
      simp [endSkipStoreSuck1, endSkipStoreTab, endSkipStoreUsr, endSkipStoreLot,
        endSkipStoreBid, endSkipStoreFlipBid, endSkipStoreRate, endSkipStoreVatIlk,
        endSkipStoreFlip, endSkipStoreCatIlk, endSkipStore]
    simpa [vowAddr, hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
      endPackVowAddr, endPackVowWord, endSlotWord, solcSlotWord] using
      evalExpr_endPack_vow
        (locals := endSkipStoreSuck1 I catOut vatOut bidOut) evm hbase
  have hthis :
      evalExpr? config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evm thisAddr = .ok (.address I.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, howner, pure]
  have hbid :
      evalExpr? config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evm (.var "bid") = .ok (.int (Int.ofNat (endSkipBidWord bidOut).toNat)) := by
    simpa [endSkipStoreSuck1, endSkipStoreTab, endSkipStoreUsr, endSkipStoreLot,
      endSkipStoreBid] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkipStoreSuck1 I catOut vatOut bidOut)
        (name := "bid") (value := endSkipBidWord bidOut)
        (by
          rw [endSkipStoreSuck1, store_get_ne _ _ (by decide +native),
            endSkipStoreTab, store_get_ne _ _ (by decide +native),
            endSkipStoreUsr, store_get_ne _ _ (by decide +native),
            endSkipStoreLot, store_get_ne _ _ (by decide +native),
            endSkipStoreBid, store_get_self])
  simp [evalExprs?, hvow, hthis, hbid, EvalResult.bind, bind, pure]

theorem endSkipCheckedSuck2NoCode {σ I} {catOut vatOut bidOut : ByteArray}
    {evm : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut } evm
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, thisAddr, .var "bid"] "_suck2") .reverted := by
  have hreceiver := endSkipVatReceiver_afterSuck1
    (σ := σ) (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut)
    (evm := evm) hmap howner
  have hcodeZero := endSkipVatCode_zero_afterFlip
    (σ := σ) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSkipStoreSuck1 I catOut vatOut bidOut) (receiver := .storage vatRef)
      (retVar := "_suck2") (name := "suck") (sendVal := 0)
      (args := [vowAddr, thisAddr, .var "bid"]) (perm := true) hguard

theorem endSkipCheckedSuck2Failure {σ I} {catOut vatOut bidOut suckOut : ByteArray}
    {evm evmSuck : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "suck" 0
        [.address (endPackVowAddr σ I), .address I.codeOwner,
          .int (Int.ofNat (endSkipBidWord bidOut).toNat)]
        (false, evmSuck, suckOut) true) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut } evm
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, thisAddr, .var "bid"] "_suck2") .reverted := by
  have hreceiver := endSkipVatReceiver_afterSuck1
    (σ := σ) (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut)
    (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip
    (σ := σ) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_suck2Args_afterSuck1 evm I σ catOut vatOut bidOut
    hmap howner
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmSuck)
      (locals := endSkipStoreSuck1 I catOut vatOut bidOut) (receiver := .storage vatRef)
      (retVar := "_suck2") (name := "suck") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [vowAddr, thisAddr, .var "bid"])
      (argVals :=
        [.address (endPackVowAddr σ I), .address I.codeOwner,
          .int (Int.ofNat (endSkipBidWord bidOut).toNat)])
      (out := suckOut) (perm := true) hguard hreceiver hargs hcall

theorem endSkipCheckedSuck2Success {σ I} {catOut vatOut bidOut suckOut : ByteArray}
    {evm evmSuck : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "suck" 0
        [.address (endPackVowAddr σ I), .address I.codeOwner,
          .int (Int.ofNat (endSkipBidWord bidOut).toNat)]
        (true, evmSuck, suckOut) true) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut } evm
      (checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
        [vowAddr, thisAddr, .var "bid"] "_suck2")
      (.ok { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evmSuck) := by
  have hreceiver := endSkipVatReceiver_afterSuck1
    (σ := σ) (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut)
    (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip
    (σ := σ) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_suck2Args_afterSuck1 evm I σ catOut vatOut bidOut
    hmap howner
  have hdec : config.externalABI.decode? "suck" suckOut = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmSuck)
    (locals := endSkipStoreSuck1 I catOut vatOut bidOut) (receiver := .storage vatRef)
    (retVar := "_suck2") (name := "suck") (target := endPackVatAddr σ I)
    (sendVal := 0) (args := [vowAddr, thisAddr, .var "bid"])
    (argVals :=
      [.address (endPackVowAddr σ I), .address I.codeOwner,
        .int (Int.ofNat (endSkipBidWord bidOut).toNat)])
    (out := suckOut) (perm := true) (value := [])
    hguard hreceiver hargs hcall hdec
  simpa [checkedExternalCallStmts, endSkipStoreSuck2, collapseReturns] using hblock

theorem endSkipVatReceiver_afterSuck2 {σ I catOut vatOut bidOut evm}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
      evm (.storage vatRef) =
        .ok (.address (endPackVatAddr σ I)) := by
  have hbase : (endSkipStoreSuck2 I catOut vatOut bidOut).get? "vat" = none := by
    simp [endSkipStoreSuck2, endSkipStoreSuck1, endSkipStoreTab, endSkipStoreUsr,
      endSkipStoreLot, endSkipStoreBid, endSkipStoreFlipBid, endSkipStoreRate,
      endSkipStoreVatIlk, endSkipStoreFlip, endSkipStoreCatIlk, endSkipStore]
  simpa [hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
    evalExpr_endPack_vat
      (locals := endSkipStoreSuck2 I catOut vatOut bidOut) evm hbase

theorem evalExprs_endSkip_hopeArgs_afterSuck2 (evm : EVM.State)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) :
    evalExprs? config
      { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
      evm [.var "flip"] = .ok [.address (endSkipCatIlkFlipAddr catOut)] := by
  have hflip :
      evalExpr? config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evm (.var "flip") = .ok (.address (endSkipCatIlkFlipAddr catOut)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endSkipStoreSuck2 I catOut vatOut bidOut).get? "flip") =
      .ok (.address (endSkipCatIlkFlipAddr catOut))
    rw [endSkipStoreSuck2, store_get_ne _ _ (by decide +native),
      endSkipStoreSuck1, store_get_ne _ _ (by decide +native),
      endSkipStoreTab, store_get_ne _ _ (by decide +native),
      endSkipStoreUsr, store_get_ne _ _ (by decide +native),
      endSkipStoreLot, store_get_ne _ _ (by decide +native),
      endSkipStoreBid, store_get_ne _ _ (by decide +native),
      endSkipStoreFlipBid, store_get_ne _ _ (by decide +native),
      endSkipStoreRate, store_get_ne _ _ (by decide +native),
      endSkipStoreVatIlk, store_get_ne _ _ (by decide +native),
      endSkipStoreFlip, store_get_self]
    rfl
  simp [evalExprs?, hflip, EvalResult.bind, bind, pure]

theorem endSkipCheckedHopeNoCode {σ I} {catOut vatOut bidOut : ByteArray}
    {evm : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) = ⟨0⟩) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut } evm
      (checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
        [.var "flip"] "_hope") .reverted := by
  have hreceiver := endSkipVatReceiver_afterSuck2
    (σ := σ) (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut)
    (evm := evm) hmap howner
  have hcodeZero := endSkipVatCode_zero_afterFlip
    (σ := σ) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSkipStoreSuck2 I catOut vatOut bidOut) (receiver := .storage vatRef)
      (retVar := "_hope") (name := "hope") (sendVal := 0)
      (args := [.var "flip"]) (perm := true) hguard

theorem endSkipCheckedHopeFailure {σ I} {catOut vatOut bidOut hopeOut : ByteArray}
    {evm evmHope : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "hope" 0
        [.address (endSkipCatIlkFlipAddr catOut)] (false, evmHope, hopeOut) true) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut } evm
      (checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
        [.var "flip"] "_hope") .reverted := by
  have hreceiver := endSkipVatReceiver_afterSuck2
    (σ := σ) (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut)
    (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip
    (σ := σ) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_hopeArgs_afterSuck2 evm I catOut vatOut bidOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmHope)
      (locals := endSkipStoreSuck2 I catOut vatOut bidOut) (receiver := .storage vatRef)
      (retVar := "_hope") (name := "hope") (target := endPackVatAddr σ I)
      (sendVal := 0) (args := [.var "flip"])
      (argVals := [.address (endSkipCatIlkFlipAddr catOut)])
      (out := hopeOut) (perm := true) hguard hreceiver hargs hcall

theorem endSkipCheckedHopeSuccess {σ I} {catOut vatOut bidOut hopeOut : ByteArray}
    {evm evmHope : EVM.State}
    (hmap : evm.accountMap = σ) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endPackVatWord σ I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σ I)) "hope" 0
        [.address (endSkipCatIlkFlipAddr catOut)] (true, evmHope, hopeOut) true) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut } evm
      (checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
        [.var "flip"] "_hope")
      (.ok { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evmHope) := by
  have hreceiver := endSkipVatReceiver_afterSuck2
    (σ := σ) (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut)
    (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip
    (σ := σ) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_hopeArgs_afterSuck2 evm I catOut vatOut bidOut
  have hdec : config.externalABI.decode? "hope" hopeOut = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmHope)
    (locals := endSkipStoreSuck2 I catOut vatOut bidOut) (receiver := .storage vatRef)
    (retVar := "_hope") (name := "hope") (target := endPackVatAddr σ I)
    (sendVal := 0) (args := [.var "flip"])
    (argVals := [.address (endSkipCatIlkFlipAddr catOut)])
    (out := hopeOut) (perm := true) (value := [])
    hguard hreceiver hargs hcall hdec
  simpa [checkedExternalCallStmts, endSkipStoreHope, collapseReturns] using hblock

theorem endSkipFlipReceiver_afterHope {I catOut vatOut bidOut evm} :
    evalExpr? config { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
      evm (.var "flip") =
        .ok (.address (endSkipCatIlkFlipAddr catOut)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((endSkipStoreHope I catOut vatOut bidOut).get? "flip") =
    .ok (.address (endSkipCatIlkFlipAddr catOut))
  rw [endSkipStoreHope, store_get_ne _ _ (by decide +native),
    endSkipStoreSuck2, store_get_ne _ _ (by decide +native),
    endSkipStoreSuck1, store_get_ne _ _ (by decide +native),
    endSkipStoreTab, store_get_ne _ _ (by decide +native),
    endSkipStoreUsr, store_get_ne _ _ (by decide +native),
    endSkipStoreLot, store_get_ne _ _ (by decide +native),
    endSkipStoreBid, store_get_ne _ _ (by decide +native),
    endSkipStoreFlipBid, store_get_ne _ _ (by decide +native),
    endSkipStoreRate, store_get_ne _ _ (by decide +native),
    endSkipStoreVatIlk, store_get_ne _ _ (by decide +native),
    endSkipStoreFlip, store_get_self]
  rfl

theorem evalExprs_endSkip_yankArgs_afterHope (evm : EVM.State)
    (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) :
    evalExprs? config
      { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
      evm [.var "id"] = .ok [.int (Int.ofNat (endSkipIdWord I).toNat)] := by
  have hid :
      evalExpr? config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evm (.var "id") = .ok (.int (Int.ofNat (endSkipIdWord I).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((endSkipStoreHope I catOut vatOut bidOut).get? "id") =
      .ok (.int (Int.ofNat (endSkipIdWord I).toNat))
    rw [endSkipStoreHope, store_get_ne _ _ (by decide +native),
      endSkipStoreSuck2, store_get_ne _ _ (by decide +native),
      endSkipStoreSuck1, store_get_ne _ _ (by decide +native),
      endSkipStoreTab, store_get_ne _ _ (by decide +native),
      endSkipStoreUsr, store_get_ne _ _ (by decide +native),
      endSkipStoreLot, store_get_ne _ _ (by decide +native),
      endSkipStoreBid, store_get_ne _ _ (by decide +native),
      endSkipStoreFlipBid, store_get_ne _ _ (by decide +native),
      endSkipStoreRate, store_get_ne _ _ (by decide +native),
      endSkipStoreVatIlk, store_get_ne _ _ (by decide +native),
      endSkipStoreFlip, store_get_ne _ _ (by decide +native),
      endSkipStoreCatIlk, store_get_ne _ _ (by decide +native),
      endSkipStore, store_get_self]
    rfl
  simp [evalExprs?, hid, EvalResult.bind, bind, pure]

theorem endSkipCheckedYankNoCode {σ I} {catOut vatOut bidOut : ByteArray}
    {evm : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) =
        ⟨0⟩) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut } evm
      (checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank")
      .reverted := by
  have hreceiver := endSkipFlipReceiver_afterHope
    (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut) (evm := evm)
  have hcodeZero := endSkipBidsCode_zero_afterRate
    (σ := σ) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) =
        .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSkipStoreHope I catOut vatOut bidOut) (receiver := .var "flip")
      (retVar := "_yank") (name := "yank") (sendVal := 0)
      (args := [.var "id"]) (perm := true) hguard

theorem endSkipCheckedYankFailure {σ I} {catOut vatOut bidOut yankOut : ByteArray}
    {evm evmYank : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) ≠
        ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endSkipCatIlkFlipAddr catOut))
        "yank" 0 [.int (Int.ofNat (endSkipIdWord I).toNat)]
        (false, evmYank, yankOut) true) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut } evm
      (checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank")
      .reverted := by
  have hreceiver := endSkipFlipReceiver_afterHope
    (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut) (evm := evm)
  have hcodePos := endSkipBidsCode_pos_afterRate
    (σ := σ) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_yankArgs_afterHope evm I catOut vatOut bidOut
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmYank)
      (locals := endSkipStoreHope I catOut vatOut bidOut) (receiver := .var "flip")
      (retVar := "_yank") (name := "yank") (target := endSkipCatIlkFlipAddr catOut)
      (sendVal := 0) (args := [.var "id"])
      (argVals := [.int (Int.ofNat (endSkipIdWord I).toNat)])
      (out := yankOut) (perm := true) hguard hreceiver hargs hcall

theorem endSkipCheckedYankSuccess {σ I} {catOut vatOut bidOut yankOut : ByteArray}
    {evm evmYank : EVM.State}
    (hmap : evm.accountMap = σ)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endSkipCatIlkFlipTargetWord catOut) ≠
        ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endSkipCatIlkFlipAddr catOut))
        "yank" 0 [.int (Int.ofNat (endSkipIdWord I).toNat)]
        (true, evmYank, yankOut) true) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut } evm
      (checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank")
      (.ok { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
        evmYank) := by
  have hreceiver := endSkipFlipReceiver_afterHope
    (I := I) (catOut := catOut) (vatOut := vatOut) (bidOut := bidOut) (evm := evm)
  have hcodePos := endSkipBidsCode_pos_afterRate
    (σ := σ) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.var "flip")) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs := evalExprs_endSkip_yankArgs_afterHope evm I catOut vatOut bidOut
  have hdec : config.externalABI.decode? "yank" yankOut = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmYank)
    (locals := endSkipStoreHope I catOut vatOut bidOut) (receiver := .var "flip")
    (retVar := "_yank") (name := "yank") (target := endSkipCatIlkFlipAddr catOut)
    (sendVal := 0) (args := [.var "id"])
    (argVals := [.int (Int.ofNat (endSkipIdWord I).toNat)])
    (out := yankOut) (perm := true) (value := [])
    hguard hreceiver hargs hcall hdec
  simpa [checkedExternalCallStmts, endSkipStoreYank, collapseReturns] using hblock

theorem evalExpr_endSkip_tab_afterYank (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
      evm (.var "tab") = .ok (.int (Int.ofNat (endSkipTabWord bidOut).toNat)) := by
  simpa [endSkipStoreYank, endSkipStoreHope, endSkipStoreSuck2, endSkipStoreSuck1,
    endSkipStoreTab] using
    endEvalExpr_varUInt256 (evm := evm)
      (locals := endSkipStoreYank I catOut vatOut bidOut)
      (name := "tab") (value := endSkipTabWord bidOut)
      (by
        rw [endSkipStoreYank, store_get_ne _ _ (by decide +native),
          endSkipStoreHope, store_get_ne _ _ (by decide +native),
          endSkipStoreSuck2, store_get_ne _ _ (by decide +native),
          endSkipStoreSuck1, store_get_ne _ _ (by decide +native),
          endSkipStoreTab, store_get_self])

theorem evalExpr_endSkip_rate_afterYank (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
      evm (.var "rate") = .ok (.int (Int.ofNat (endFlowVatIlkRateWord vatOut).toNat)) := by
  simpa [endSkipStoreYank, endSkipStoreHope, endSkipStoreSuck2, endSkipStoreSuck1,
    endSkipStoreTab, endSkipStoreUsr, endSkipStoreLot, endSkipStoreBid,
    endSkipStoreFlipBid, endSkipStoreRate] using
    endEvalExpr_varUInt256 (evm := evm)
      (locals := endSkipStoreYank I catOut vatOut bidOut)
      (name := "rate") (value := endFlowVatIlkRateWord vatOut)
      (by
        rw [endSkipStoreYank, store_get_ne _ _ (by decide +native),
          endSkipStoreHope, store_get_ne _ _ (by decide +native),
          endSkipStoreSuck2, store_get_ne _ _ (by decide +native),
          endSkipStoreSuck1, store_get_ne _ _ (by decide +native),
          endSkipStoreTab, store_get_ne _ _ (by decide +native),
          endSkipStoreUsr, store_get_ne _ _ (by decide +native),
          endSkipStoreLot, store_get_ne _ _ (by decide +native),
          endSkipStoreBid, store_get_ne _ _ (by decide +native),
          endSkipStoreFlipBid, store_get_ne _ _ (by decide +native),
          endSkipStoreRate, store_get_self])

theorem endSkipStmtArt (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩) :
    ExecStmt config { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
      evm (.letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")))
      (.ok { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut } evm) := by
  have htab := evalExpr_endSkip_tab_afterYank evm I catOut vatOut bidOut
  have hrateExpr := evalExpr_endSkip_rate_afterYank evm I catOut vatOut bidOut
  have hdiv :
      evalExpr? config { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
        evm (.binary .div (.var "tab") (.var "rate")) =
          .ok (.int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)) :=
    endEvalExpr_div_uint256_ok htab hrateExpr hrate rfl
  simpa [endSkipStoreArt] using ExecStmt.letDecl hdiv

theorem endSkipStmtArtReverts (evm : EVM.State) (I : ExecutionEnv)
    (catOut vatOut bidOut : ByteArray)
    (hrate : endFlowVatIlkRateWord vatOut = ⟨0⟩) :
    ExecStmt config { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
      evm (.letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")))
      .reverted := by
  have htab := evalExpr_endSkip_tab_afterYank evm I catOut vatOut bidOut
  have hrateExpr := evalExpr_endSkip_rate_afterYank evm I catOut vatOut bidOut
  exact ExecStmt.letDeclRevert (endEvalExpr_div_uint256_revert_zero htab hrateExpr hrate)

theorem endSkipStoreArt_get_ilk (I : ExecutionEnv) (catOut vatOut bidOut : ByteArray) :
    (endSkipStoreArt I catOut vatOut bidOut).get? "ilk" = some (endFlowIlkValue I) := by
  rw [endSkipStoreArt, store_get_ne _ _ (by decide +native),
    endSkipStoreYank, store_get_ne _ _ (by decide +native),
    endSkipStoreHope, store_get_ne _ _ (by decide +native),
    endSkipStoreSuck2, store_get_ne _ _ (by decide +native),
    endSkipStoreSuck1, store_get_ne _ _ (by decide +native),
    endSkipStoreTab, store_get_ne _ _ (by decide +native),
    endSkipStoreUsr, store_get_ne _ _ (by decide +native),
    endSkipStoreLot, store_get_ne _ _ (by decide +native),
    endSkipStoreBid, store_get_ne _ _ (by decide +native),
    endSkipStoreFlipBid, store_get_ne _ _ (by decide +native),
    endSkipStoreRate, store_get_ne _ _ (by decide +native),
    endSkipStoreVatIlk, store_get_ne _ _ (by decide +native),
    endSkipStoreFlip, store_get_ne _ _ (by decide +native),
    endSkipStoreCatIlk, store_get_ne _ _ (by decide +native)]
  simpa [endFlowIlkValue, endBytes32ArgValue, endBytes32ArgBytes, endSkipIlkBytes]
    using endSkipStore_get_ilk I

theorem endSkipStmtArtNewAddReturns (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkipArtSlot I) =
        endSkipArtOldWord σ I)
    (hfit :
      (endSkipArtOldWord σ I).toNat + (endSkipArtWord vatOut bidOut).toNat <
        UInt256.size) :
    ExecStmt config { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut }
      evm (.internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew")
      (.ok { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
        evm) := by
  have hArt :
      evalExpr? config { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut }
        evm (.storage (ArtRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endSkipArtOldWord σ I).toNat)) := by
    have hbase : (endSkipStoreArt I catOut vatOut bidOut).get? "Art" = none := by
      simp [endSkipStoreArt, endSkipStoreYank, endSkipStoreHope, endSkipStoreSuck2,
        endSkipStoreSuck1, endSkipStoreTab, endSkipStoreUsr, endSkipStoreLot,
        endSkipStoreBid, endSkipStoreFlipBid, endSkipStoreRate, endSkipStoreVatIlk,
        endSkipStoreFlip, endSkipStoreCatIlk, endSkipStore]
    have hget := endSkipStoreArt_get_ilk I catOut vatOut bidOut
    have hstorage := evalExpr_endFlow_Art_of_get evm I hbase hget (by omega)
    simpa [hArtLoad, endSkipArtWord, endSkipArtOldWord, endSkipArtSlot,
      endFlowArtSlot, endSkipIlkKey, endFlowIlkKey] using hstorage
  have hart :
      evalExpr? config { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut }
        evm (.var "art") = .ok (.int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)) := by
    simpa [endSkipStoreArt] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkipStoreArt I catOut vatOut bidOut)
        (name := "art") (value := endSkipArtWord vatOut bidOut)
        (by rw [endSkipStoreArt, store_get_self])
  have hargs :
      evalExprs? config { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut }
        evm [.storage (ArtRef (.var "ilk")), .var "art"] =
          .ok [.int (Int.ofNat (endSkipArtOldWord σ I).toNat),
            .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)] := by
    simp [evalExprs?, hArt, hart, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat (endSkipArtOldWord σ I).toNat),
            .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)] =
        some (endUintBinaryLocals (endSkipArtOldWord σ I)
          (endSkipArtWord vatOut bidOut)) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecAddFunctionReturn (evm := evm)
      (x := endSkipArtOldWord σ I) (y := endSkipArtWord vatOut bidOut)
      (sum := endSkipArtNewWord σ I vatOut bidOut) rfl hfit
  have hstmt := internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut })
    (evm := evm) (name := "add") (retVar := "ArtNew")
    (args := [.storage (ArtRef (.var "ilk")), .var "art"])
    (argVals :=
      [.int (Int.ofNat (endSkipArtOldWord σ I).toNat),
        .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)])
    (callee := addFunction)
    (locals := endUintBinaryLocals (endSkipArtOldWord σ I)
      (endSkipArtWord vatOut bidOut))
    hargs (by rfl) hbind hbody
  simpa [endSkipStoreArtNew, resumeAfterInternalCall, collapseReturns,
    endSkipArtNewWord] using hstmt

theorem endSkipStmtArtNewAddReverts (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endSkipArtSlot I) =
        endSkipArtOldWord σ I)
    (hover :
      UInt256.size ≤
        (endSkipArtOldWord σ I).toNat + (endSkipArtWord vatOut bidOut).toNat) :
    ExecStmt config { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut }
      evm (.internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew")
      .reverted := by
  have hArt :
      evalExpr? config { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut }
        evm (.storage (ArtRef (.var "ilk"))) =
          .ok (.int (Int.ofNat (endSkipArtOldWord σ I).toNat)) := by
    have hbase : (endSkipStoreArt I catOut vatOut bidOut).get? "Art" = none := by
      simp [endSkipStoreArt, endSkipStoreYank, endSkipStoreHope, endSkipStoreSuck2,
        endSkipStoreSuck1, endSkipStoreTab, endSkipStoreUsr, endSkipStoreLot,
        endSkipStoreBid, endSkipStoreFlipBid, endSkipStoreRate, endSkipStoreVatIlk,
        endSkipStoreFlip, endSkipStoreCatIlk, endSkipStore]
    have hget := endSkipStoreArt_get_ilk I catOut vatOut bidOut
    have hstorage := evalExpr_endFlow_Art_of_get evm I hbase hget (by omega)
    simpa [hArtLoad, endSkipArtWord, endSkipArtOldWord, endSkipArtSlot,
      endFlowArtSlot, endSkipIlkKey, endFlowIlkKey] using hstorage
  have hart :
      evalExpr? config { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut }
        evm (.var "art") = .ok (.int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)) := by
    simpa [endSkipStoreArt] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkipStoreArt I catOut vatOut bidOut)
        (name := "art") (value := endSkipArtWord vatOut bidOut)
        (by rw [endSkipStoreArt, store_get_self])
  have hargs :
      evalExprs? config { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut }
        evm [.storage (ArtRef (.var "ilk")), .var "art"] =
          .ok [.int (Int.ofNat (endSkipArtOldWord σ I).toNat),
            .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)] := by
    simp [evalExprs?, hArt, hart, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? addFunction.params
          [.int (Int.ofNat (endSkipArtOldWord σ I).toNat),
            .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)] =
        some (endUintBinaryLocals (endSkipArtOldWord σ I)
          (endSkipArtWord vatOut bidOut)) := by
    simp [addFunction, uint256, bindParams?, endUintBinaryLocals]
  have hbody :=
    endExecAddFunctionRevert (evm := evm)
      (x := endSkipArtOldWord σ I) (y := endSkipArtWord vatOut bidOut) hover
  exact internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := endSkipStoreArt I catOut vatOut bidOut })
    (evm := evm) (name := "add") (retVar := "ArtNew")
    (args := [.storage (ArtRef (.var "ilk")), .var "art"])
    (argVals :=
      [.int (Int.ofNat (endSkipArtOldWord σ I).toNat),
        .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)])
    (callee := addFunction)
    (locals := endUintBinaryLocals (endSkipArtOldWord σ I)
      (endSkipArtWord vatOut bidOut))
    hargs (by rfl) hbind hbody

theorem endSkipAssignArt {locals : Store} (evm : EVM.State) (I : ExecutionEnv)
    (artNew : UInt256)
    (hbase : locals.get? "Art" = none)
    (hget : locals.get? "ilk" = some (endFlowIlkValue I))
    (hsz68 : 68 ≤ I.calldata.size) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (ArtRef (.var "ilk")) (.int (Int.ofNat artNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, endSkipPostArtState evm I artNew) := by
  have href := evalStorageRef_endFlow_Art_of_get evm I hget (by omega)
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (endSkipArtSlot I))
      (hbase := hbase)
      (her := by simpa [endSkipArtSlot, endFlowArtSlot, endSkipIlkKey, endFlowIlkKey] using href)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa only [endSkipPostArtState] using
    endStorageLocStore_uint256 evm (endSkipArtSlot I) artNew

theorem endSkipStmtArtAssign (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray)
    (hsz68 : 68 ≤ I.calldata.size) :
    ExecStmt config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
      evm (.assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"))
      (.ok { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
        (endSkipPostArtState evm I (endSkipArtNewWord σ I vatOut bidOut))) := by
  have hArtNew :
      evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
        evm (.var "ArtNew") =
        .ok (.int (Int.ofNat (endSkipArtNewWord σ I vatOut bidOut).toNat)) := by
    simpa [endSkipStoreArtNew] using
      endEvalExpr_varUInt256 (evm := evm)
        (locals := endSkipStoreArtNew σ I catOut vatOut bidOut)
        (name := "ArtNew") (value := endSkipArtNewWord σ I vatOut bidOut)
        (by rw [endSkipStoreArtNew, store_get_self])
  have hassign :
      assignStorageRef? config
        { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
        evm .storage (ArtRef (.var "ilk"))
        (.int (Int.ofNat (endSkipArtNewWord σ I vatOut bidOut).toNat)) =
          .ok ({ contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut },
            endSkipPostArtState evm I (endSkipArtNewWord σ I vatOut bidOut)) := by
    have hbase : (endSkipStoreArtNew σ I catOut vatOut bidOut).get? "Art" = none := by
      simp [endSkipStoreArtNew, endSkipStoreArt, endSkipStoreYank, endSkipStoreHope,
        endSkipStoreSuck2, endSkipStoreSuck1, endSkipStoreTab, endSkipStoreUsr,
        endSkipStoreLot, endSkipStoreBid, endSkipStoreFlipBid, endSkipStoreRate,
        endSkipStoreVatIlk, endSkipStoreFlip, endSkipStoreCatIlk, endSkipStore]
    have hget :
        (endSkipStoreArtNew σ I catOut vatOut bidOut).get? "ilk" =
          some (endFlowIlkValue I) := by
      rw [endSkipStoreArtNew, store_get_ne _ _ (by decide +native)]
      exact endSkipStoreArt_get_ilk I catOut vatOut bidOut
    exact endSkipAssignArt evm I (endSkipArtNewWord σ I vatOut bidOut) hbase hget hsz68
  exact ExecStmt.assign hArtNew hassign

theorem evalExpr_endSkip_lot_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
      evm (.var "lot") =
      .ok (.int (Int.ofNat (endSkipLotWord bidOut).toNat)) := by
  simpa [endSkipStoreArtNew, endSkipStoreArt, endSkipStoreYank, endSkipStoreHope,
    endSkipStoreSuck2, endSkipStoreSuck1, endSkipStoreTab, endSkipStoreUsr,
    endSkipStoreLot] using
    endEvalExpr_varUInt256 (evm := evm)
      (locals := endSkipStoreArtNew σ I catOut vatOut bidOut)
      (name := "lot") (value := endSkipLotWord bidOut)
      (by
        rw [endSkipStoreArtNew, store_get_ne _ _ (by decide +native),
          endSkipStoreArt, store_get_ne _ _ (by decide +native),
          endSkipStoreYank, store_get_ne _ _ (by decide +native),
          endSkipStoreHope, store_get_ne _ _ (by decide +native),
          endSkipStoreSuck2, store_get_ne _ _ (by decide +native),
          endSkipStoreSuck1, store_get_ne _ _ (by decide +native),
          endSkipStoreTab, store_get_ne _ _ (by decide +native),
          endSkipStoreUsr, store_get_ne _ _ (by decide +native),
          endSkipStoreLot, store_get_self])

theorem evalExpr_endSkip_art_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
      evm (.var "art") =
      .ok (.int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)) := by
  simpa [endSkipStoreArtNew, endSkipStoreArt] using
    endEvalExpr_varUInt256 (evm := evm)
      (locals := endSkipStoreArtNew σ I catOut vatOut bidOut)
      (name := "art") (value := endSkipArtWord vatOut bidOut)
      (by
        rw [endSkipStoreArtNew, store_get_ne _ _ (by decide +native),
          endSkipStoreArt, store_get_self])

theorem endSkipEvalExpr_intGuard_true (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray)
    (hlot : (endSkipLotWord bidOut).toNat < 2 ^ 255)
    (hart : (endSkipArtWord vatOut bidOut).toNat < 2 ^ 255) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) = .ok (.bool true) := by
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by decide +native
  have hlotExpr := evalExpr_endSkip_lot_afterArtNew evm I σ catOut vatOut bidOut
  have hartExpr := evalExpr_endSkip_art_afterArtNew evm I σ catOut vatOut bidOut
  have hlimitExpr :
      evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
        (.intLit int256Limit) = .ok (.int int256Limit) :=
    endSnipEvalExpr_intLimit evm
  have hlotLt :
      evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
        (.binary .lt (.var "lot") (.intLit int256Limit)) = .ok (.bool true) :=
    endSnipEvalExpr_lt_int_true hlotExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_lt.mpr hlot)
  have hartLt :
      evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
        (.binary .lt (.var "art") (.intLit int256Limit)) = .ok (.bool true) :=
    endSnipEvalExpr_lt_int_true hartExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_lt.mpr hart)
  simp [evalExpr?, EvalResult.bind, bind, hlotLt, hartLt, pure]

theorem endSkipEvalExpr_intGuard_false_lot (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray)
    (hlot : 2 ^ 255 ≤ (endSkipLotWord bidOut).toNat) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) = .ok (.bool false) := by
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by decide +native
  have hlotExpr := evalExpr_endSkip_lot_afterArtNew evm I σ catOut vatOut bidOut
  have hlimitExpr :
      evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
        (.intLit int256Limit) = .ok (.int int256Limit) :=
    endSnipEvalExpr_intLimit evm
  have hlotLt :
      evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
        (.binary .lt (.var "lot") (.intLit int256Limit)) = .ok (.bool false) :=
    endSnipEvalExpr_lt_int_false hlotExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_le.mpr hlot)
  simp [evalExpr?, EvalResult.bind, bind, hlotLt, pure]

theorem endSkipEvalExpr_intGuard_false_art (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray)
    (hlot : (endSkipLotWord bidOut).toNat < 2 ^ 255)
    (hart : 2 ^ 255 ≤ (endSkipArtWord vatOut bidOut).toNat) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) = .ok (.bool false) := by
  have hlimit : int256Limit = Int.ofNat (2 ^ 255) := by decide +native
  have hlotExpr := evalExpr_endSkip_lot_afterArtNew evm I σ catOut vatOut bidOut
  have hartExpr := evalExpr_endSkip_art_afterArtNew evm I σ catOut vatOut bidOut
  have hlimitExpr :
      evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
        (.intLit int256Limit) = .ok (.int int256Limit) :=
    endSnipEvalExpr_intLimit evm
  have hlotLt :
      evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
        (.binary .lt (.var "lot") (.intLit int256Limit)) = .ok (.bool true) :=
    endSnipEvalExpr_lt_int_true hlotExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_lt.mpr hlot)
  have hartLt :
      evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut } evm
        (.binary .lt (.var "art") (.intLit int256Limit)) = .ok (.bool false) :=
    endSnipEvalExpr_lt_int_false hartExpr hlimitExpr (by
      rw [hlimit]
      exact Int.ofNat_le.mpr hart)
  simp [evalExpr?, EvalResult.bind, bind, hlotLt, hartLt, pure]

theorem endSkipVatReceiver_afterArtNewFor {σCall σLoc I catOut vatOut bidOut evm}
    (hmap : evm.accountMap = σCall)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut } evm
      (.storage vatRef) = .ok (.address (endPackVatAddr σCall I)) := by
  have hbase : (endSkipStoreArtNew σLoc I catOut vatOut bidOut).get? "vat" = none := by
    simp [endSkipStoreArtNew, endSkipStoreArt, endSkipStoreYank, endSkipStoreHope,
      endSkipStoreSuck2, endSkipStoreSuck1, endSkipStoreTab, endSkipStoreUsr,
      endSkipStoreLot, endSkipStoreBid, endSkipStoreFlipBid, endSkipStoreRate,
      endSkipStoreVatIlk, endSkipStoreFlip, endSkipStoreCatIlk, endSkipStore]
  simpa [hmap, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVatAddr, endPackVatWord, endSlotWord, solcSlotWord] using
    evalExpr_endPack_vat
      (locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut) evm hbase

theorem evalExpr_endSkip_ilk_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
      evm (.var "ilk") =
      .ok (.fixedBytes bytes32Width (endBytes32ArgBytes I)) := by
  apply endEvalExpr_varFixedBytes
  rw [endSkipStoreArtNew, store_get_ne _ _ (by decide +native)]
  simpa [endFlowIlkValue, endBytes32ArgValue] using
    endSkipStoreArt_get_ilk I catOut vatOut bidOut

theorem evalExpr_endSkip_usr_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
      evm (.var "usr") = .ok (.address (endSkipUsrAddr bidOut)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
    ((endSkipStoreArtNew σ I catOut vatOut bidOut).get? "usr") =
      .ok (.address (endSkipUsrAddr bidOut))
  rw [endSkipStoreArtNew, store_get_ne _ _ (by decide +native),
    endSkipStoreArt, store_get_ne _ _ (by decide +native),
    endSkipStoreYank, store_get_ne _ _ (by decide +native),
    endSkipStoreHope, store_get_ne _ _ (by decide +native),
    endSkipStoreSuck2, store_get_ne _ _ (by decide +native),
    endSkipStoreSuck1, store_get_ne _ _ (by decide +native),
    endSkipStoreTab, store_get_ne _ _ (by decide +native),
    endSkipStoreUsr, store_get_self]
  rfl

theorem evalExpr_endSkip_this_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
      evm thisAddr = .ok (.address I.codeOwner) := by
  simp [thisAddr, evalExpr?, envValue, howner, pure]

theorem evalExpr_endSkip_vow_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
      evm vowAddr = .ok (.address (endPackVowAddr evm.accountMap I)) := by
  have hbase : (endSkipStoreArtNew σ I catOut vatOut bidOut).get? "vow" = none := by
    simp [endSkipStoreArtNew, endSkipStoreArt, endSkipStoreYank, endSkipStoreHope,
      endSkipStoreSuck2, endSkipStoreSuck1, endSkipStoreTab, endSkipStoreUsr,
      endSkipStoreLot, endSkipStoreBid, endSkipStoreFlipBid, endSkipStoreRate,
      endSkipStoreVatIlk, endSkipStoreFlip, endSkipStoreCatIlk, endSkipStore]
  simpa [vowAddr, howner, Solm.EVM.storageLoad, State.lookupAccount,
    endPackVowAddr, endPackVowWord, endSlotWord, solcSlotWord] using
    evalExpr_endPack_vow
      (locals := endSkipStoreArtNew σ I catOut vatOut bidOut) evm hbase

theorem evalExpr_endSkip_lot_asInt_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
      evm (asInt256 (.var "lot")) =
      .ok (.int (Int.ofNat (endSkipLotWord bidOut).toNat)) := by
  have hlot := evalExpr_endSkip_lot_afterArtNew evm I σ catOut vatOut bidOut
  simp only [asInt256, evalExpr?, hlot, castValue?, EvalResult.bind, bind, int256St,
    int256Int]
  rfl

theorem evalExpr_endSkip_art_asInt_afterArtNew (evm : EVM.State) (I : ExecutionEnv)
    (σ : AccountMap) (catOut vatOut bidOut : ByteArray) :
    evalExpr? config { contract := contract, locals := endSkipStoreArtNew σ I catOut vatOut bidOut }
      evm (asInt256 (.var "art")) =
      .ok (.int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)) := by
  have hart := evalExpr_endSkip_art_afterArtNew evm I σ catOut vatOut bidOut
  simp only [asInt256, evalExpr?, hart, castValue?, EvalResult.bind, bind, int256St,
    int256Int]
  rfl

theorem evalExprs_endSkip_grabArgs (evm : EVM.State) (I : ExecutionEnv)
    (σCall σLoc : AccountMap) (catOut vatOut bidOut : ByteArray)
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    evalExprs? config { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut } evm
      [.var "ilk", .var "usr", thisAddr, vowAddr,
        asInt256 (.var "lot"), asInt256 (.var "art")] =
        .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkipUsrAddr bidOut),
          .address I.codeOwner,
          .address (endPackVowAddr evm.accountMap I),
          .int (Int.ofNat (endSkipLotWord bidOut).toNat),
          .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)] := by
  have hilk := evalExpr_endSkip_ilk_afterArtNew evm I σLoc catOut vatOut bidOut
  have husr := evalExpr_endSkip_usr_afterArtNew evm I σLoc catOut vatOut bidOut
  have hthis := evalExpr_endSkip_this_afterArtNew evm I σLoc catOut vatOut bidOut howner
  have hvow := evalExpr_endSkip_vow_afterArtNew evm I σLoc catOut vatOut bidOut howner
  have hlot := evalExpr_endSkip_lot_asInt_afterArtNew evm I σLoc catOut vatOut bidOut
  have hart := evalExpr_endSkip_art_asInt_afterArtNew evm I σLoc catOut vatOut bidOut
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

theorem endSkipGrabTailReverts_noCodeFor {σCall σLoc I}
    {catOut vatOut bidOut : ByteArray} {evm : EVM.State}
    (hmap : evm.accountMap = σCall) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) = ⟨0⟩) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")] "_grab")
      .reverted := by
  have hreceiver := endSkipVatReceiver_afterArtNewFor
    (σCall := σCall) (σLoc := σLoc) (I := I) (catOut := catOut)
    (vatOut := vatOut) (bidOut := bidOut) (evm := evm) hmap howner
  have hcodeZero := endSkipVatCode_zero_afterFlip
    (σ := σCall) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut)
      (receiver := .storage vatRef) (retVar := "_grab") (name := "grab")
      (sendVal := 0)
      (args := [.var "ilk", .var "usr", thisAddr, vowAddr,
        asInt256 (.var "lot"), asInt256 (.var "art")])
      (perm := true) hguard

theorem endSkipGrabTailReverts_callFailedFor {σCall σLoc I}
    {catOut vatOut bidOut grabOut : ByteArray} {evm evmGrab : EVM.State}
    (hmap : evm.accountMap = σCall) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σCall I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkipUsrAddr bidOut),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (Int.ofNat (endSkipLotWord bidOut).toNat),
          .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)]
        (false, evmGrab, grabOut) true) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")] "_grab")
      .reverted := by
  have hreceiver := endSkipVatReceiver_afterArtNewFor
    (σCall := σCall) (σLoc := σLoc) (I := I) (catOut := catOut)
    (vatOut := vatOut) (bidOut := bidOut) (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip
    (σ := σCall) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargsRaw := evalExprs_endSkip_grabArgs evm I σCall σLoc catOut vatOut bidOut howner
  have hargs :
      evalExprs? config
        { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
        evm [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
            .address (endSkipUsrAddr bidOut),
            .address I.codeOwner,
            .address (endPackVowAddr σCall I),
            .int (Int.ofNat (endSkipLotWord bidOut).toNat),
            .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)] := by
    simpa [hmap] using hargsRaw
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evmGrab)
      (locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut)
      (receiver := .storage vatRef) (retVar := "_grab") (name := "grab")
      (target := endPackVatAddr σCall I) (sendVal := 0)
      (args := [.var "ilk", .var "usr", thisAddr, vowAddr,
        asInt256 (.var "lot"), asInt256 (.var "art")])
      (argVals :=
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkipUsrAddr bidOut),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (Int.ofNat (endSkipLotWord bidOut).toNat),
          .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)])
      (out := grabOut) (perm := true) hguard hreceiver hargs hcall

theorem endSkipGrabTailReturns_successFor {σCall σLoc I}
    {catOut vatOut bidOut grabOut : ByteArray} {evm evmGrab : EVM.State}
    (hmap : evm.accountMap = σCall) (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σCall (endPackVatWord σCall I) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm (EVM.address (endPackVatAddr σCall I)) "grab" 0
        [.fixedBytes bytes32Width (endBytes32ArgBytes I),
          .address (endSkipUsrAddr bidOut),
          .address I.codeOwner,
          .address (endPackVowAddr σCall I),
          .int (Int.ofNat (endSkipLotWord bidOut).toNat),
          .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)]
        (true, evmGrab, grabOut) true) :
    ExecBlock config
      { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
      evm
      (checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
        [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")] "_grab")
      (.ok { contract := contract, locals := endSkipStoreGrab σLoc I catOut vatOut bidOut }
        evmGrab) := by
  have hreceiver := endSkipVatReceiver_afterArtNewFor
    (σCall := σCall) (σLoc := σLoc) (I := I) (catOut := catOut)
    (vatOut := vatOut) (bidOut := bidOut) (evm := evm) hmap howner
  have hcodePos := endSkipVatCode_pos_afterFlip
    (σ := σCall) (I := I) (catOut := catOut) (evm := evm) hmap hcodeSize
  have hguard :
      evalExpr? config
        { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
        evm (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargsRaw := evalExprs_endSkip_grabArgs evm I σCall σLoc catOut vatOut bidOut howner
  have hargs :
      evalExprs? config
        { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
        evm [.var "ilk", .var "usr", thisAddr, vowAddr,
          asInt256 (.var "lot"), asInt256 (.var "art")] =
          .ok [.fixedBytes bytes32Width (endBytes32ArgBytes I),
            .address (endSkipUsrAddr bidOut),
            .address I.codeOwner,
            .address (endPackVowAddr σCall I),
            .int (Int.ofNat (endSkipLotWord bidOut).toNat),
            .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)] := by
    simpa [hmap] using hargsRaw
  have hdec : config.externalABI.decode? "grab" grabOut = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evmGrab)
    (locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut)
    (receiver := .storage vatRef) (retVar := "_grab") (name := "grab")
    (target := endPackVatAddr σCall I) (sendVal := 0)
    (args := [.var "ilk", .var "usr", thisAddr, vowAddr,
      asInt256 (.var "lot"), asInt256 (.var "art")])
    (argVals :=
      [.fixedBytes bytes32Width (endBytes32ArgBytes I),
        .address (endSkipUsrAddr bidOut),
        .address I.codeOwner,
        .address (endPackVowAddr σCall I),
        .int (Int.ofNat (endSkipLotWord bidOut).toNat),
        .int (Int.ofNat (endSkipArtWord vatOut bidOut).toNat)])
    (out := grabOut) (perm := true) (value := [])
    hguard hreceiver hargs hcall hdec
  simpa [checkedExternalCallStmts, endSkipStoreGrab, collapseReturns] using hblock

abbrev endSkipSuck1Stmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
    [vowAddr, vowAddr, .var "tab"] "_suck1"

abbrev endSkipSuck2Stmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
    [vowAddr, thisAddr, .var "bid"] "_suck2"

abbrev endSkipHopeStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0) [.var "flip"] "_hope"

abbrev endSkipYankStmts : List Stmt :=
  checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank"

abbrev endSkipArtStmts : List Stmt :=
  [ .letDecl "art" (some uint256) (.binary .div (.var "tab") (.var "rate")),
    .internalCall "add" [.storage (ArtRef (.var "ilk")), .var "art"] "ArtNew",
    .assign .storage (ArtRef (.var "ilk")) (.var "ArtNew"),
    .require
      (.binary .and
        (.binary .lt (.var "lot") (.intLit int256Limit))
        (.binary .lt (.var "art") (.intLit int256Limit))) ]

abbrev endSkipGrabStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "grab" (.intLit 0)
    [.var "ilk", .var "usr", thisAddr, vowAddr, asInt256 (.var "lot"),
      asInt256 (.var "art")] "_grab"

abbrev endSkipTailNoGrabStmts : List Stmt :=
  endSkipSuck1Stmts ++ endSkipSuck2Stmts ++ endSkipHopeStmts ++
    endSkipYankStmts ++ endSkipArtStmts

theorem endSkipTailAfterTabReturns {I σLoc}
    {catOut vatOut bidOut : ByteArray}
    {evmTab evmSuck1 evmSuck2 evmHope evmYank : EVM.State}
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evmYank evmYank.executionEnv.codeOwner (endSkipArtSlot I) =
        endSkipArtOldWord σLoc I)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (hfit :
      (endSkipArtOldWord σLoc I).toNat + (endSkipArtWord vatOut bidOut).toNat <
        UInt256.size)
    (hlot : (endSkipLotWord bidOut).toNat < 2 ^ 255)
    (hart : (endSkipArtWord vatOut bidOut).toNat < 2 ^ 255)
    (hsuck1 :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipSuck1Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
          evmSuck1))
    (hsuck2 :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evmSuck1 endSkipSuck2Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
          evmSuck2))
    (hhope :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evmSuck2 endSkipHopeStmts
        (.ok { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
          evmHope))
    (hyank :
      ExecBlock config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evmHope endSkipYankStmts
        (.ok { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
          evmYank)) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evmTab endSkipTailNoGrabStmts
      (.ok { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
        (endSkipPostArtState evmYank I (endSkipArtNewWord σLoc I vatOut bidOut))) := by
  have hartBlock :
      ExecBlock config { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
        evmYank endSkipArtStmts
        (.ok { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
          (endSkipPostArtState evmYank I (endSkipArtNewWord σLoc I vatOut bidOut))) := by
    refine ExecBlock.consNormal (endSkipStmtArt evmYank I catOut vatOut bidOut hrate) ?_
    refine ExecBlock.consNormal
      (endSkipStmtArtNewAddReturns evmYank I σLoc catOut vatOut bidOut hsz68 hArtLoad hfit) ?_
    refine ExecBlock.consNormal
      (endSkipStmtArtAssign evmYank I σLoc catOut vatOut bidOut hsz68) ?_
    exact ExecBlock.consNormal
      (ExecStmt.requireTrue
        (endSkipEvalExpr_intGuard_true
          (endSkipPostArtState evmYank I (endSkipArtNewWord σLoc I vatOut bidOut))
          I σLoc catOut vatOut bidOut hlot hart))
      ExecBlock.nil
  have htail2 := execBlock_append hsuck1 hsuck2
  have htail3 := execBlock_append htail2 hhope
  have htail4 := execBlock_append htail3 hyank
  simpa [endSkipTailNoGrabStmts, List.append_assoc] using
   execBlock_append htail4 hartBlock

theorem endSkipTailReverts_suck1 {I} {catOut vatOut bidOut : ByteArray}
    {evmTab : EVM.State}
    (hsuck1 :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipSuck1Stmts .reverted) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evmTab endSkipTailNoGrabStmts .reverted := by
  simpa [endSkipTailNoGrabStmts, List.append_assoc] using
   execBlock_append_term hsuck1 (by intro f' e' h; cases h)

theorem endSkipTailReverts_suck2 {I} {catOut vatOut bidOut : ByteArray}
    {evmTab evmSuck1 : EVM.State}
    (hsuck1 :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipSuck1Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
          evmSuck1))
    (hsuck2 :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evmSuck1 endSkipSuck2Stmts .reverted) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evmTab endSkipTailNoGrabStmts .reverted := by
  have hsuck2Tail :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evmSuck1
        (endSkipSuck2Stmts ++ endSkipHopeStmts ++ endSkipYankStmts ++ endSkipArtStmts)
        .reverted := by
    simpa [List.append_assoc] using
      (Reasoning.Theory.execBlock_append_term
        (s2 := endSkipHopeStmts ++ endSkipYankStmts ++ endSkipArtStmts)
        hsuck2 (by intro f' e' h; cases h))
  simpa [endSkipTailNoGrabStmts, List.append_assoc] using
   execBlock_append hsuck1 hsuck2Tail

theorem endSkipTailReverts_hope {I} {catOut vatOut bidOut : ByteArray}
    {evmTab evmSuck1 evmSuck2 : EVM.State}
    (hsuck1 :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipSuck1Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
          evmSuck1))
    (hsuck2 :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evmSuck1 endSkipSuck2Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
          evmSuck2))
    (hhope :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evmSuck2 endSkipHopeStmts .reverted) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evmTab endSkipTailNoGrabStmts .reverted := by
  have hhopeTail :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evmSuck2 (endSkipHopeStmts ++ endSkipYankStmts ++ endSkipArtStmts)
        .reverted := by
    simpa [List.append_assoc] using
      (Reasoning.Theory.execBlock_append_term
        (s2 := endSkipYankStmts ++ endSkipArtStmts)
        hhope (by intro f' e' h; cases h))
  have htail2 := execBlock_append hsuck1 hsuck2
  simpa [endSkipTailNoGrabStmts, List.append_assoc] using
   execBlock_append htail2 hhopeTail

theorem endSkipTailReverts_yank {I} {catOut vatOut bidOut : ByteArray}
    {evmTab evmSuck1 evmSuck2 evmHope : EVM.State}
    (hsuck1 :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipSuck1Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
          evmSuck1))
    (hsuck2 :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evmSuck1 endSkipSuck2Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
          evmSuck2))
    (hhope :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evmSuck2 endSkipHopeStmts
        (.ok { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
          evmHope))
    (hyank :
      ExecBlock config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evmHope endSkipYankStmts .reverted) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evmTab endSkipTailNoGrabStmts .reverted := by
  have hyankTail :
      ExecBlock config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evmHope (endSkipYankStmts ++ endSkipArtStmts) .reverted := by
    exact execBlock_append_term hyank (by intro f' e' h; cases h)
  have htail2 := execBlock_append hsuck1 hsuck2
  have htail3 := execBlock_append htail2 hhope
  simpa [endSkipTailNoGrabStmts, List.append_assoc] using
   execBlock_append htail3 hyankTail

theorem endSkipTailReverts_artDivZero {I} {catOut vatOut bidOut : ByteArray}
    {evmTab evmSuck1 evmSuck2 evmHope evmYank : EVM.State}
    (hrate : endFlowVatIlkRateWord vatOut = ⟨0⟩)
    (hsuck1 :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipSuck1Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
          evmSuck1))
    (hsuck2 :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evmSuck1 endSkipSuck2Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
          evmSuck2))
    (hhope :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evmSuck2 endSkipHopeStmts
        (.ok { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
          evmHope))
    (hyank :
      ExecBlock config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evmHope endSkipYankStmts
        (.ok { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
          evmYank)) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evmTab endSkipTailNoGrabStmts .reverted := by
  have hartRevert :
      ExecBlock config { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
        evmYank endSkipArtStmts .reverted :=
    ExecBlock.consRevert (endSkipStmtArtReverts evmYank I catOut vatOut bidOut hrate)
  have htail2 := execBlock_append hsuck1 hsuck2
  have htail3 := execBlock_append htail2 hhope
  have htail4 := execBlock_append htail3 hyank
  simpa [endSkipTailNoGrabStmts, List.append_assoc] using
   execBlock_append htail4 hartRevert

theorem endSkipTailReverts_artAddOverflow {I σLoc}
    {catOut vatOut bidOut : ByteArray}
    {evmTab evmSuck1 evmSuck2 evmHope evmYank : EVM.State}
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evmYank evmYank.executionEnv.codeOwner (endSkipArtSlot I) =
        endSkipArtOldWord σLoc I)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (hover :
      UInt256.size ≤
        (endSkipArtOldWord σLoc I).toNat + (endSkipArtWord vatOut bidOut).toNat)
    (hsuck1 :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipSuck1Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
          evmSuck1))
    (hsuck2 :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evmSuck1 endSkipSuck2Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
          evmSuck2))
    (hhope :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evmSuck2 endSkipHopeStmts
        (.ok { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
          evmHope))
    (hyank :
      ExecBlock config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evmHope endSkipYankStmts
        (.ok { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
          evmYank)) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evmTab endSkipTailNoGrabStmts .reverted := by
  have hartBlock :
      ExecBlock config { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
        evmYank endSkipArtStmts .reverted := by
    refine ExecBlock.consNormal (endSkipStmtArt evmYank I catOut vatOut bidOut hrate) ?_
    exact ExecBlock.consRevert
      (endSkipStmtArtNewAddReverts evmYank I σLoc catOut vatOut bidOut hsz68 hArtLoad hover)
  have htail2 := execBlock_append hsuck1 hsuck2
  have htail3 := execBlock_append htail2 hhope
  have htail4 := execBlock_append htail3 hyank
  simpa [endSkipTailNoGrabStmts, List.append_assoc] using
   execBlock_append htail4 hartBlock

theorem endSkipTailReverts_intGuardLot {I σLoc}
    {catOut vatOut bidOut : ByteArray}
    {evmTab evmSuck1 evmSuck2 evmHope evmYank : EVM.State}
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evmYank evmYank.executionEnv.codeOwner (endSkipArtSlot I) =
        endSkipArtOldWord σLoc I)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (hfit :
      (endSkipArtOldWord σLoc I).toNat + (endSkipArtWord vatOut bidOut).toNat <
        UInt256.size)
    (hlot : 2 ^ 255 ≤ (endSkipLotWord bidOut).toNat)
    (hsuck1 :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipSuck1Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
          evmSuck1))
    (hsuck2 :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evmSuck1 endSkipSuck2Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
          evmSuck2))
    (hhope :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evmSuck2 endSkipHopeStmts
        (.ok { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
          evmHope))
    (hyank :
      ExecBlock config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evmHope endSkipYankStmts
        (.ok { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
          evmYank)) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evmTab endSkipTailNoGrabStmts .reverted := by
  have hartBlock :
      ExecBlock config { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
        evmYank endSkipArtStmts .reverted := by
    refine ExecBlock.consNormal (endSkipStmtArt evmYank I catOut vatOut bidOut hrate) ?_
    refine ExecBlock.consNormal
      (endSkipStmtArtNewAddReturns evmYank I σLoc catOut vatOut bidOut hsz68 hArtLoad hfit) ?_
    refine ExecBlock.consNormal
      (endSkipStmtArtAssign evmYank I σLoc catOut vatOut bidOut hsz68) ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endSkipEvalExpr_intGuard_false_lot
          (endSkipPostArtState evmYank I (endSkipArtNewWord σLoc I vatOut bidOut))
          I σLoc catOut vatOut bidOut hlot))
  have htail2 := execBlock_append hsuck1 hsuck2
  have htail3 := execBlock_append htail2 hhope
  have htail4 := execBlock_append htail3 hyank
  simpa [endSkipTailNoGrabStmts, List.append_assoc] using
   execBlock_append htail4 hartBlock

theorem endSkipTailReverts_intGuardArt {I σLoc}
    {catOut vatOut bidOut : ByteArray}
    {evmTab evmSuck1 evmSuck2 evmHope evmYank : EVM.State}
    (hsz68 : 68 ≤ I.calldata.size)
    (hArtLoad :
      Solm.EVM.storageLoad evmYank evmYank.executionEnv.codeOwner (endSkipArtSlot I) =
        endSkipArtOldWord σLoc I)
    (hrate : endFlowVatIlkRateWord vatOut ≠ ⟨0⟩)
    (hfit :
      (endSkipArtOldWord σLoc I).toNat + (endSkipArtWord vatOut bidOut).toNat <
        UInt256.size)
    (hlot : (endSkipLotWord bidOut).toNat < 2 ^ 255)
    (hart : 2 ^ 255 ≤ (endSkipArtWord vatOut bidOut).toNat)
    (hsuck1 :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipSuck1Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
          evmSuck1))
    (hsuck2 :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck1 I catOut vatOut bidOut }
        evmSuck1 endSkipSuck2Stmts
        (.ok { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
          evmSuck2))
    (hhope :
      ExecBlock config
        { contract := contract, locals := endSkipStoreSuck2 I catOut vatOut bidOut }
        evmSuck2 endSkipHopeStmts
        (.ok { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
          evmHope))
    (hyank :
      ExecBlock config
        { contract := contract, locals := endSkipStoreHope I catOut vatOut bidOut }
        evmHope endSkipYankStmts
        (.ok { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
          evmYank)) :
    ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
      evmTab endSkipTailNoGrabStmts .reverted := by
  have hartBlock :
      ExecBlock config { contract := contract, locals := endSkipStoreYank I catOut vatOut bidOut }
        evmYank endSkipArtStmts .reverted := by
    refine ExecBlock.consNormal (endSkipStmtArt evmYank I catOut vatOut bidOut hrate) ?_
    refine ExecBlock.consNormal
      (endSkipStmtArtNewAddReturns evmYank I σLoc catOut vatOut bidOut hsz68 hArtLoad hfit) ?_
    refine ExecBlock.consNormal
      (endSkipStmtArtAssign evmYank I σLoc catOut vatOut bidOut hsz68) ?_
    exact ExecBlock.consRevert
      (ExecStmt.requireFalse
        (endSkipEvalExpr_intGuard_false_art
          (endSkipPostArtState evmYank I (endSkipArtNewWord σLoc I vatOut bidOut))
          I σLoc catOut vatOut bidOut hlot hart))
  have htail2 := execBlock_append hsuck1 hsuck2
  have htail3 := execBlock_append htail2 hhope
  have htail4 := execBlock_append htail3 hyank
  simpa [endSkipTailNoGrabStmts, List.append_assoc] using
   execBlock_append htail4 hartBlock

theorem endSkipBodyReverts_afterTabTailReverted {I} {catOut vatOut bidOut : ByteArray}
    {evm0 evmTab : EVM.State}
    (hprefixTab :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
            "catIlk" ++
          [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
            "flipBid" (perm := false) ++
          [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
            .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
            .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
            .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ])
        (.ok { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
          evmTab))
    (htail :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipTailNoGrabStmts .reverted) :
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body .reverted := by
  have htailWithGrab :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab (endSkipTailNoGrabStmts ++ endSkipGrabStmts) .reverted := by
    exact execBlock_append_term htail (by intro f' e' h; cases h)
  have hblock :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        skipTransition.body .reverted := by
    have hseq := execBlock_append hprefixTab htailWithGrab
    simpa [skipTransition, endSkipTailNoGrabStmts, endSkipGrabStmts, endSkipSuck1Stmts,
      endSkipSuck2Stmts, endSkipHopeStmts, endSkipYankStmts, endSkipArtStmts,
      List.append_assoc] using hseq
  exact ExecFuncBody.execBlockRevert hblock

theorem endSkipBodyReverts_afterTabTailGrabReverted {I σLoc}
    {catOut vatOut bidOut : ByteArray} {evm0 evmTab evmPost : EVM.State}
    (hprefixTab :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
            "catIlk" ++
          [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
            "flipBid" (perm := false) ++
          [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
            .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
            .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
            .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ])
        (.ok { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
          evmTab))
    (htail :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipTailNoGrabStmts
        (.ok { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
          evmPost))
    (hgrab :
      ExecBlock config
        { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
        evmPost endSkipGrabStmts .reverted) :
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body .reverted := by
  have htailWithGrab :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab (endSkipTailNoGrabStmts ++ endSkipGrabStmts) .reverted := by
    exact execBlock_append htail hgrab
  have hblock :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        skipTransition.body .reverted := by
    have hseq := execBlock_append hprefixTab htailWithGrab
    simpa [skipTransition, endSkipTailNoGrabStmts, endSkipGrabStmts, endSkipSuck1Stmts,
      endSkipSuck2Stmts, endSkipHopeStmts, endSkipYankStmts, endSkipArtStmts,
      List.append_assoc] using hseq
  exact ExecFuncBody.execBlockRevert hblock

theorem endSkipBodyReturns_afterTabTailGrabSuccess {I σLoc}
    {catOut vatOut bidOut : ByteArray}
    {evm0 evmTab evmPost evmGrab : EVM.State}
    (hprefixTab :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        (nonpayable ++
          [ .require (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
          checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
            "catIlk" ++
          [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
            "vatIlk" ++
          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
          checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"]
            "flipBid" (perm := false) ++
          [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
            .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
            .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
            .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ])
        (.ok { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
          evmTab))
    (htail :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab endSkipTailNoGrabStmts
        (.ok { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
          evmPost))
    (hgrab :
      ExecBlock config
        { contract := contract, locals := endSkipStoreArtNew σLoc I catOut vatOut bidOut }
        evmPost endSkipGrabStmts
        (.ok { contract := contract, locals := endSkipStoreGrab σLoc I catOut vatOut bidOut }
          evmGrab)) :
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body
      (.returned { contract := contract, locals := endSkipStoreGrab σLoc I catOut vatOut bidOut }
        evmGrab none) := by
  have htailWithGrab :
      ExecBlock config { contract := contract, locals := endSkipStoreTab I catOut vatOut bidOut }
        evmTab (endSkipTailNoGrabStmts ++ endSkipGrabStmts)
        (.ok { contract := contract, locals := endSkipStoreGrab σLoc I catOut vatOut bidOut }
          evmGrab) := by
    exact execBlock_append htail hgrab
  have hblock :
      ExecBlock config { contract := contract, locals := endSkipStore I } evm0
        skipTransition.body
        (.ok { contract := contract, locals := endSkipStoreGrab σLoc I catOut vatOut bidOut }
          evmGrab) := by
    have hseq := execBlock_append hprefixTab htailWithGrab
    simpa [skipTransition, endSkipTailNoGrabStmts, endSkipGrabStmts, endSkipSuck1Stmts,
      endSkipSuck2Stmts, endSkipHopeStmts, endSkipYankStmts, endSkipArtStmts,
      List.append_assoc] using hseq
  exact ExecFuncBody.execBlockOK hblock

theorem endSkipBodyReverts_tagZero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) (hsz68 : 68 ≤ I.calldata.size)
    (htag : endSkipTagWord σ I = ⟨0⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (endSkipStore I) skipTransition.body .reverted := by
  intro evm0
  have htagLoad :
      Solm.EVM.storageLoad evm0 evm0.executionEnv.codeOwner (endSkipTagSlot I) = ⟨0⟩ := by
    simpa [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
      endSkipTagWord, endSlotWord, solcSlotWord] using htag
  have hguard :
      evalExpr? config { contract := contract, locals := endSkipStore I } evm0
        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) = .ok (.bool false) :=
    evalExpr_endSkip_tag_ne_false evm0 I hsz68 htagLoad
  refine ExecFuncBody.execBlockRevert ?_
  simpa [skipTransition, nonpayable, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := endSkipStore I })
      (evm := evm0)
      (guard := .binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0))
      (rest :=
        checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0) [.var "ilk"]
          "catIlk" ++
        [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
        checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0) [.var "ilk"]
          "vatIlk" ++
        [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ] ++
        checkedExternalCallStmts (.var "flip") "bids" (.intLit 0) [.var "id"] "flipBid"
          (perm := false) ++
        [ .letDecl "bid" (some uint256) (.tupleGet (.var "flipBid") 0),
          .letDecl "lot" (some uint256) (.tupleGet (.var "flipBid") 1),
          .letDecl "usr" (some addr) (.tupleGet (.var "flipBid") 5),
          .letDecl "tab" (some uint256) (.tupleGet (.var "flipBid") 7) ] ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, vowAddr, .var "tab"] "_suck1" ++
        checkedExternalCallStmts (.storage vatRef) "suck" (.intLit 0)
          [vowAddr, thisAddr, .var "bid"] "_suck2" ++
        checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0) [.var "flip"]
          "_hope" ++
        checkedExternalCallStmts (.var "flip") "yank" (.intLit 0) [.var "id"] "_yank" ++
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

theorem endSkipX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endSkipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := endSkipEntryPc) (ret := endSkipReturnPc)
    (decoded := endSkipDecodedPc) (need := ⟨64⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

theorem endSkipBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some skipTransition)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) endSkipEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (endSkipX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (endDecode_skip_none_short hsz4 hshort)

theorem endSkipBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf skipTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endSkipConcreteSelector := by
    simpa [endSkipSelectorBytes, endSkipConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endSkipConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some skipTransition :=
    endDispatchSkip hsel
  have hreach := endReachSkipBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_skip_ok (I := I) hsz68
    obtain ⟨_, _, hbodyReach⟩ :=
      endSkipX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have htagCouple : endSkipTagWord σ_evm I = endSkipTagWord σ_solm I := by
      simpa [endSkipTagWord, endSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner (endSkipTagSlot I) ⟨0⟩
    by_cases htag : endSkipTagWord σ_evm I = ⟨0⟩
    · have htagSolm : endSkipTagWord σ_solm I = ⟨0⟩ := by
        rw [← htagCouple]
        exact htag
      have hbody :
          ExecTransitionBody config contract evmSolm (endSkipStore I)
            skipTransition.body .reverted := by
        simpa [evmSolm] using
          endSkipBodyReverts_tagZero
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hsz68 htagSolm
      exact (endSkipX_tagZero (g := Sat256.ofUInt256 g) hsz68 htag hbodyReach)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have htagNE : endSkipTagWord σ_evm I ≠ ⟨0⟩ := htag
      have htagSolmNE : endSkipTagWord σ_solm I ≠ ⟨0⟩ := by
        intro hbad
        exact htagNE (by rw [htagCouple, hbad])
      obtain ⟨kTag, CTag, htagPcRaw⟩ :=
        endSkipX_tagNonzero (g := Sat256.ofUInt256 g) hsz68 htagNE hbodyReach
      have htagPc :
          RD endBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3314⟩
            [endSkipIdWord I, endSkipIlkWord I, endSkipReturnPc, endSelWord I]
            (endSkipCatIlksBaseMem I) (UInt256.ofNat 3) ByteArray.empty
            (cA, σ_evm) kTag CTag := by
        simpa [endSkipCatIlksBaseMem] using htagPcRaw
      have hAddressId (a : AccountAddress) : EVM.address a = a := by
        apply Fin.ext
        show ↑a % EVM.twoPow 160 = ↑a
        rw [Nat.mod_eq_of_lt]
        exact a.isLt
      by_cases hcatCode :
          Reasoning.Theory.extCodeSizeWord σ_evm (endSkipCatWord σ_evm I) =
            ⟨0⟩
      · have hcatCodeSolm :
            Reasoning.Theory.extCodeSizeWord σ_solm
              (endSkipCatWord σ_solm I) = ⟨0⟩ :=
          endSkipCatCodeSize_zero_accountMapEquiv hAccounts hcatCode
        have hbody :
            ExecTransitionBody config contract evmSolm (endSkipStore I)
              skipTransition.body .reverted := by
          simpa [evmSolm] using
            endSkipBodyReverts_catIlksNoCode
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hsz68 htagSolmNE hcatCodeSolm
        exact (endSkipX_catIlksNoCode (g := Sat256.ofUInt256 g) htagPc hcatCode)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hcatCodeNE :
            Reasoning.Theory.extCodeSizeWord σ_evm (endSkipCatWord σ_evm I) ≠
              ⟨0⟩ := hcatCode
        have hcatCodeSolmNE :
            Reasoning.Theory.extCodeSizeWord σ_solm
              (endSkipCatWord σ_solm I) ≠ ⟨0⟩ :=
          endSkipCatCodeSize_ne_accountMapEquiv hAccounts hcatCodeNE
        obtain ⟨catGasWord, _, _, hcatReady⟩ :=
          endSkipX_catIlksCallReady
            (g := Sat256.ofUInt256 g) htagPc hcatCodeNE
        by_cases hdepthLt : I.depth.val < 1024
        · obtain ⟨cA_cat, σ_cat, zCat, catOut, AinCat, callGasCat, _, _, hΘCat,
              rd3395, hcatOutSize⟩ :=
            endSkipX_catIlksPostCall hcatReady hdepthLt
          rcases hΘCat with ⟨gCat'', ACat, hΘCatEq⟩
          have hdepthNe :
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.depth ≠
              1024 := by
            intro hbad
            have hbadI : I.depth = 1024 := by
              simpa [initState] using hbad
            have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
            omega
          have htgtCat :
              EVM.address (endSkipCatAddr σ_evm I) =
              AccountAddress.ofUInt256 (endSkipCatWord σ_evm I) := by
            calc
              EVM.address (endSkipCatAddr σ_evm I)
                  = EVM.address
                      (AccountAddress.ofUInt256 (endSkipCatWord σ_evm I)) := by
                    rw [endSkipCatAddr_eq_ofUInt256]
              _ = AccountAddress.ofUInt256 (endSkipCatWord σ_evm I) :=
                    hAddressId (AccountAddress.ofUInt256 (endSkipCatWord σ_evm I))
          obtain ⟨σ_cat_solm, A_cat_solm, hcallCatSolmRaw, hAccountsCat,
              hSubstateCat⟩ :=
            endCallMade_accountMapEquiv_with_substate
              (cfg := config)
              (evm_evm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
              (evm_solm := evmSolm)
              (tgt := EVM.address (endSkipCatAddr σ_evm I))
              (targetWord := endSkipCatWord σ_evm I)
              (name := "catIlks")
              (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
              (cA' := cA_cat) (σ' := σ_cat) (A' := ACat) (A_in := AinCat)
              (z := zCat) (out := catOut) (g'' := gCat'')
              (callGas := callGasCat)
              (mem := endSkipCatIlksCalldataMem I)
              (inOff := endFlowVatIlksOutPtr) (inSize := endFlowVatIlksInSize)
              (callPerm := true)
              hdepthNe htgtCat
              (endSkipCatIlksEncode_eq I hsz68 (endSkipCatIlksBaseMem_size I))
              (by simpa [initState, hperm] using hΘCatEq)
              (by simpa [initState] using hAccounts)
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
              (by simp [evmSolm, initState])
          have hCatAddr : endSkipCatAddr σ_evm I = endSkipCatAddr σ_solm I := by
            simp [endSkipCatAddr, endSkipCatWord_accountMapEquiv hAccounts]
          have hcallCatSolm :
              typedCallViaEVM config evmSolm
              (EVM.address (endSkipCatAddr σ_solm I)) "catIlks" 0
              [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
              (zCat,
                { evmSolm with
                  accountMap := σ_cat_solm
                  substate := A_cat_solm
                  createdAccounts := cA_cat },
                catOut) true := by
            simpa [evmSolm, hCatAddr] using hcallCatSolmRaw
          cases zCat
          · have hbody :
              ExecTransitionBody config contract evmSolm (endSkipStore I)
                skipTransition.body .reverted := by
              simpa [evmSolm] using
                endSkipBodyReverts_catIlksCallFailed
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                  (evmCat :=
                    { evmSolm with
                      accountMap := σ_cat_solm
                      substate := A_cat_solm
                      createdAccounts := cA_cat })
                  (out := catOut)
                  hwv hsz68 htagSolmNE hcatCodeSolmNE
                  (by simpa [evmSolm] using hcallCatSolm)
            exact (endSkipX_catIlksCallFailed rd3395 hcatOutSize)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · let evmCatEvm :=
              { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ_cat
              substate := ACat
              createdAccounts := cA_cat }
            let evmCatSolm :=
              { evmSolm with
              accountMap := σ_cat_solm
              substate := A_cat_solm
              createdAccounts := cA_cat }
            have hStateCat : EVMStateEquiv evmCatEvm evmCatSolm := by
              refine ⟨rfl, rfl, ?_⟩
              simpa [evmCatEvm, evmCatSolm] using hAccountsCat
            obtain ⟨_, _, rd3416⟩ :=
              endSkipX_catIlksCallSucceeded (g := Sat256.ofUInt256 g) rd3395
            by_cases hshortCat : catOut.size < 96
            · have hbody :
                ExecTransitionBody config contract evmSolm (endSkipStore I)
                  skipTransition.body .reverted := by
                simpa [evmCatSolm, evmSolm] using
                  endSkipBodyReverts_catIlksDecodeShort
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    (evmCat := evmCatSolm) (out := catOut)
                    hwv hsz68 htagSolmNE hcatCodeSolmNE
                    (by simpa [evmCatSolm, evmSolm] using hcallCatSolm)
                    hshortCat
              exact (endSkipX_catIlksReturnDecodeShort rd3416 hshortCat hcatOutSize)
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hloCat : 96 ≤ catOut.size := Nat.le_of_not_gt hshortCat
              obtain ⟨_, _, rd3436⟩ :=
                endSkipX_catIlksReturnDecodeOk rd3416 hloCat hcatOutSize
              have hprefix :
                ExecBlock config { contract := contract, locals := endSkipStore I }
                  evmSolm
                  (nonpayable ++
                    [ .require
                        (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
                    checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0)
                      [.var "ilk"] "catIlk" ++
                    [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ])
                  (.ok { contract := contract, locals := endSkipStoreFlip I catOut }
                    evmCatSolm) := by
                simpa [evmCatSolm, evmSolm] using
                  endSkipPrefixFlipSuccess
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                    (evmCat := evmCatSolm) (out := catOut)
                    hwv hsz68 htagSolmNE hcatCodeSolmNE
                    (by simpa [evmCatSolm, evmSolm] using hcallCatSolm)
                    hloCat
              by_cases hvatCode :
                  Reasoning.Theory.extCodeSizeWord σ_cat
                    (endPackVatWord σ_cat I) = ⟨0⟩
              · have hvatCodeSolm :
                    Reasoning.Theory.extCodeSizeWord σ_cat_solm
                      (endPackVatWord σ_cat_solm I) = ⟨0⟩ :=
                  endPackVatCodeSize_zero_accountMapEquiv hAccountsCat hvatCode
                have hvatBlock :
                    ExecBlock config
                      { contract := contract, locals := endSkipStoreFlip I catOut }
                      evmCatSolm
                      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk") .reverted := by
                  exact endSkipCheckedVatIlksNoCode
                    (σ := σ_cat_solm) (I := I) (catOut := catOut) (evm := evmCatSolm)
                    (by simp [evmCatSolm])
                    (by simp [evmCatSolm, evmSolm, initState])
                    hvatCodeSolm
                have hbody :
                    ExecTransitionBody config contract evmSolm (endSkipStore I)
                      skipTransition.body .reverted := by
                  exact endSkipBodyReverts_afterFlipVatIlksBlock hprefix hvatBlock
                exact (endSkipX_vatIlksNoCode rd3436 hloCat hvatCode)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have hvatCodeNE :
                    Reasoning.Theory.extCodeSizeWord σ_cat
                      (endPackVatWord σ_cat I) ≠ ⟨0⟩ := hvatCode
                have hvatCodeSolmNE :
                    Reasoning.Theory.extCodeSizeWord σ_cat_solm
                      (endPackVatWord σ_cat_solm I) ≠ ⟨0⟩ :=
                  endPackVatCodeSize_ne_accountMapEquiv hAccountsCat hvatCodeNE
                obtain ⟨gasWordVat, _, _, hvatReady⟩ :=
                  endSkipX_vatIlksCallReady rd3436 hloCat hvatCodeNE
                obtain ⟨cA_vat, σ_vat, zVat, vatOut, AinVat, callGasVat, _, _,
                    hΘVat, rd3521, hvatOutSize⟩ :=
                  endSkipX_vatIlksPostCall hvatReady hdepthLt
                rcases hΘVat with ⟨gVat'', AVat, hΘVatEq⟩
                have htgtVat :
                    EVM.address (endPackVatAddr σ_cat I) =
                      AccountAddress.ofUInt256 (endPackVatWord σ_cat I) := by
                  calc
                    EVM.address (endPackVatAddr σ_cat I)
                        = EVM.address
                            (AccountAddress.ofUInt256 (endPackVatWord σ_cat I)) := by
                          rw [endPackVatAddr_eq_ofUInt256]
                    _ = AccountAddress.ofUInt256 (endPackVatWord σ_cat I) :=
                          hAddressId (AccountAddress.ofUInt256 (endPackVatWord σ_cat I))
                obtain ⟨σ_vat_solm, A_vat_solm, hcallVatSolmRaw, hAccountsVat,
                    hSubstateVat⟩ :=
                  endCallMade_accountMapEquiv_with_substate
                    (cfg := config)
                    (evm_evm := evmCatEvm)
                    (evm_solm := evmCatSolm)
                    (tgt := EVM.address (endPackVatAddr σ_cat I))
                    (targetWord := endPackVatWord σ_cat I)
                    (name := "vatIlks")
                    (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
                    (cA' := cA_vat) (σ' := σ_vat) (A' := AVat) (A_in := AinVat)
                    (z := zVat) (out := vatOut) (g'' := gVat'')
                    (callGas := callGasVat)
                    (mem := endSkipVatIlksCalldataMem I catOut)
                    (inOff := endFlowVatIlksOutPtr) (inSize := endFlowVatIlksInSize)
                    (callPerm := true)
                    (by simpa [evmCatEvm, initState] using hdepthNe)
                    htgtVat
                    (endSkipVatIlksEncode_eq I catOut hsz68 hloCat)
                    (by simpa [evmCatEvm, initState, hperm] using hΘVatEq)
                    (by simpa [evmCatEvm, evmCatSolm] using hAccountsCat)
                    (by rfl)
                    (by simpa using hStateCat.createdAccounts.symm)
                    (by rfl)
                    (by rfl)
                    (by simpa using hStateCat.executionEnv.symm)
                have hVatAddr : endPackVatAddr σ_cat I = endPackVatAddr σ_cat_solm I := by
                  simp [endPackVatAddr, endPackVatWord_accountMapEquiv hAccountsCat]
                have hcallVatSolm :
                    typedCallViaEVM config evmCatSolm
                    (EVM.address (endPackVatAddr σ_cat_solm I)) "vatIlks" 0
                    [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
                    (zVat,
                      { evmCatSolm with
                        accountMap := σ_vat_solm
                        substate := A_vat_solm
                        createdAccounts := cA_vat },
                      vatOut) true := by
                  simpa [evmCatSolm, hVatAddr] using hcallVatSolmRaw
                cases zVat
                · have hvatBlock :
                    ExecBlock config
                      { contract := contract, locals := endSkipStoreFlip I catOut }
                      evmCatSolm
                      (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                        [.var "ilk"] "vatIlk") .reverted := by
                    exact endSkipCheckedVatIlksFailure
                      (σ := σ_cat_solm) (I := I) (catOut := catOut) (vatOut := vatOut)
                      (evm := evmCatSolm)
                      (evmVat :=
                        { evmCatSolm with
                          accountMap := σ_vat_solm
                          substate := A_vat_solm
                          createdAccounts := cA_vat })
                      (by simp [evmCatSolm])
                      (by simp [evmCatSolm, evmSolm, initState])
                      hvatCodeSolmNE
                      (by simpa [evmCatSolm] using hcallVatSolm)
                  have hbody :
                      ExecTransitionBody config contract evmSolm (endSkipStore I)
                        skipTransition.body .reverted := by
                    exact endSkipBodyReverts_afterFlipVatIlksBlock hprefix hvatBlock
                  exact (endSkipX_vatIlksCallFailed rd3521 hvatOutSize)
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · let evmVatEvm :=
                    { evmCatEvm with
                    accountMap := σ_vat
                    substate := AVat
                    createdAccounts := cA_vat }
                  let evmVatSolm :=
                    { evmCatSolm with
                    accountMap := σ_vat_solm
                    substate := A_vat_solm
                    createdAccounts := cA_vat }
                  have hStateVat : EVMStateEquiv evmVatEvm evmVatSolm := by
                    refine ⟨rfl, rfl, ?_⟩
                    simpa [evmVatEvm, evmVatSolm] using hAccountsVat
                  obtain ⟨_, _, rd3541⟩ :=
                    endSkipX_vatIlksCallSucceeded (g := Sat256.ofUInt256 g) rd3521
                  by_cases hshortVat : vatOut.size < 160
                  · have hvatBlock :
                      ExecBlock config
                        { contract := contract, locals := endSkipStoreFlip I catOut }
                        evmCatSolm
                        (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                          [.var "ilk"] "vatIlk") .reverted := by
                      exact endSkipCheckedVatIlksDecodeRevert
                        (σ := σ_cat_solm) (I := I) (catOut := catOut) (vatOut := vatOut)
                        (evm := evmCatSolm) (evmVat := evmVatSolm)
                        (by simp [evmCatSolm])
                        (by simp [evmCatSolm, evmSolm, initState])
                        hvatCodeSolmNE
                        (by simpa [evmVatSolm, evmCatSolm] using hcallVatSolm)
                        hshortVat
                    have hbody :
                        ExecTransitionBody config contract evmSolm (endSkipStore I)
                          skipTransition.body .reverted := by
                      exact endSkipBodyReverts_afterFlipVatIlksBlock hprefix hvatBlock
                    exact (endSkipX_vatIlksReturnDecodeShort rd3541 hloCat hshortVat hvatOutSize)
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hloVat : 160 ≤ vatOut.size := Nat.le_of_not_gt hshortVat
                    obtain ⟨_, _, rd3565⟩ :=
                      endSkipX_vatIlksReturnDecodeOk rd3541 hloCat hloVat hvatOutSize
                    have hvatBlock :
                        ExecBlock config
                          { contract := contract, locals := endSkipStoreFlip I catOut }
                          evmCatSolm
                          (checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                            [.var "ilk"] "vatIlk")
                          (.ok
                            { contract := contract,
                              locals := endSkipStoreVatIlk I catOut vatOut }
                            evmVatSolm) := by
                      exact endSkipCheckedVatIlksSuccess
                        (σ := σ_cat_solm) (I := I) (catOut := catOut) (vatOut := vatOut)
                        (evm := evmCatSolm) (evmVat := evmVatSolm)
                        (by simp [evmCatSolm])
                        (by simp [evmCatSolm, evmSolm, initState])
                        hvatCodeSolmNE
                        (by simpa [evmVatSolm, evmCatSolm] using hcallVatSolm)
                        hloVat
                    have hprefixRate :
                        ExecBlock config { contract := contract, locals := endSkipStore I }
                          evmSolm
                          (nonpayable ++
                          [ .require
                              (.binary .ne (.storage (tagRef (.var "ilk"))) (.intLit 0)) ] ++
                          checkedExternalCallStmts (.storage catRef) "catIlks" (.intLit 0)
                            [.var "ilk"] "catIlk" ++
                          [ .letDecl "flip" (some addr) (.tupleGet (.var "catIlk") 0) ] ++
                          checkedExternalCallStmts (.storage vatRef) "vatIlks" (.intLit 0)
                            [.var "ilk"] "vatIlk" ++
                          [ .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1) ])
                        (.ok
                          { contract := contract,
                              locals := endSkipStoreRate I catOut vatOut }
                            evmVatSolm) := by
                      exact endSkipPrefixRateSuccess hprefix hvatBlock
                    by_cases hbidsCode :
                        Reasoning.Theory.extCodeSizeWord σ_vat
                          (endSkipCatIlkFlipTargetWord catOut) = ⟨0⟩
                    · have hbidsCodeSolm :
                          Reasoning.Theory.extCodeSizeWord σ_vat_solm
                            (endSkipCatIlkFlipTargetWord catOut) = ⟨0⟩ :=
                        endSkipBidsCodeSize_zero_accountMapEquiv
                          hAccountsVat catOut hbidsCode
                      have hbidsBlock :
                          ExecBlock config
                            { contract := contract,
                              locals := endSkipStoreRate I catOut vatOut }
                            evmVatSolm
                            (checkedExternalCallStmts (.var "flip") "bids"
                              (.intLit 0) [.var "id"] "flipBid" (perm := false))
                            .reverted := by
                        exact endSkipCheckedBidsNoCode
                          (σ := σ_vat_solm) (I := I) (catOut := catOut)
                          (vatOut := vatOut) (evm := evmVatSolm)
                          (by rfl)
                          hbidsCodeSolm
                      have hbody :
                          ExecTransitionBody config contract evmSolm (endSkipStore I)
                            skipTransition.body .reverted := by
                        exact endSkipBodyReverts_afterRateBidsBlock
                          hprefixRate hbidsBlock
                      exact (endSkipX_bidsNoCode rd3565 hloCat hloVat hbidsCode)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hbidsCodeNE :
                          Reasoning.Theory.extCodeSizeWord σ_vat
                            (endSkipCatIlkFlipTargetWord catOut) ≠ ⟨0⟩ := hbidsCode
                      have hbidsCodeSolmNE :
                          Reasoning.Theory.extCodeSizeWord σ_vat_solm
                            (endSkipCatIlkFlipTargetWord catOut) ≠ ⟨0⟩ :=
                        endSkipBidsCodeSize_ne_accountMapEquiv
                          hAccountsVat catOut hbidsCodeNE
                      obtain ⟨gasWordBids, _, _, hbidsReady⟩ :=
                        endSkipX_bidsCallReady rd3565 hloCat hloVat hbidsCodeNE
                      obtain ⟨cA_bids, σ_bids, zBids, bidOut, AinBids,
                          callGasBids, _, _, hΘBids, rd3653, hbidOutSize⟩ :=
                        endSkipX_bidsPostStaticcall hbidsReady hdepthLt
                      rcases hΘBids with ⟨gBids'', ABids, hΘBidsEq⟩
                      have htgtBids :
                          EVM.address (endSkipCatIlkFlipAddr catOut) =
                            AccountAddress.ofUInt256 (endSkipCatIlkFlipTargetWord catOut) := by
                        calc
                          EVM.address (endSkipCatIlkFlipAddr catOut)
                              = EVM.address
                                  (AccountAddress.ofUInt256
                                    (endSkipCatIlkFlipTargetWord catOut)) := by
                                rw [endSkipCatIlkFlipAddr_eq_ofUInt256]
                          _ = AccountAddress.ofUInt256
                                (endSkipCatIlkFlipTargetWord catOut) :=
                                hAddressId
                                  (AccountAddress.ofUInt256
                                    (endSkipCatIlkFlipTargetWord catOut))
                      obtain ⟨σ_bids_solm, A_bids_solm, hcallBidsSolmRaw,
                          hAccountsBids, hSubstateBids⟩ :=
                        endCallMade_accountMapEquiv_with_substate
                          (cfg := config)
                          (evm_evm := evmVatEvm)
                          (evm_solm := evmVatSolm)
                          (tgt := EVM.address (endSkipCatIlkFlipAddr catOut))
                          (targetWord := endSkipCatIlkFlipTargetWord catOut)
                          (name := "bids")
                          (args := [.int (Int.ofNat (endSkipIdWord I).toNat)])
                          (cA' := cA_bids) (σ' := σ_bids) (A' := ABids)
                          (A_in := AinBids) (z := zBids) (out := bidOut)
                          (g'' := gBids'') (callGas := callGasBids)
                          (mem := endSkipBidsCalldataMem I catOut vatOut)
                          (inOff := endFlowVatIlksOutPtr)
                          (inSize := endFlowVatIlksInSize)
                          (callPerm := false)
                          (by simpa [evmVatEvm, evmCatEvm, initState] using hdepthNe)
                          htgtBids
                          (endSkipBidsEncode_eq I catOut vatOut hloCat hloVat)
                          (by simpa [evmVatEvm, evmCatEvm, initState] using hΘBidsEq)
                          (by simpa [evmVatEvm, evmVatSolm] using hAccountsVat)
                          (by rfl)
                          (by simpa using hStateVat.createdAccounts.symm)
                          (by rfl)
                          (by rfl)
                          (by simpa using hStateVat.executionEnv.symm)
                      let evmBidsSolm :=
                        { evmVatSolm with
                          accountMap := σ_bids_solm
                          substate := A_bids_solm
                          createdAccounts := cA_bids }
                      have hcallBidsSolm :
                          typedCallViaEVM config evmVatSolm
                          (EVM.address (endSkipCatIlkFlipAddr catOut)) "bids" 0
                          [.int (Int.ofNat (endSkipIdWord I).toNat)]
                          (zBids, evmBidsSolm, bidOut) false := by
                        change typedCallViaEVM config evmVatSolm
                          (EVM.address (endSkipCatIlkFlipAddr catOut)) "bids" 0
                          [.int (Int.ofNat (endSkipIdWord I).toNat)]
                          (zBids,
                            { evmVatSolm with
                              accountMap := σ_bids_solm
                              substate := A_bids_solm
                              createdAccounts := cA_bids },
                            bidOut) false
                        exact hcallBidsSolmRaw
                      cases zBids
                      · have rd3653Failed := by
                          simpa only [if_false] using rd3653
                        have hbidsBlock :
                            ExecBlock config
                              { contract := contract,
                                locals := endSkipStoreRate I catOut vatOut }
                              evmVatSolm
                              (checkedExternalCallStmts (.var "flip") "bids"
                                (.intLit 0) [.var "id"] "flipBid" (perm := false))
                              .reverted := by
                          exact endSkipCheckedBidsFailure
                            (σ := σ_vat_solm) (I := I) (catOut := catOut)
                            (vatOut := vatOut) (bidOut := bidOut)
                            (evm := evmVatSolm)
                            (evmBids := evmBidsSolm)
                            (by rfl)
                            hbidsCodeSolmNE
                            hcallBidsSolm
                        have hbody :
                            ExecTransitionBody config contract evmSolm (endSkipStore I)
                              skipTransition.body .reverted := by
                          exact endSkipBodyReverts_afterRateBidsBlock
                            hprefixRate hbidsBlock
                        exact (endSkipX_bidsCallFailed rd3653Failed hbidOutSize)
                          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · let evmBidsEvm :=
                          { evmVatEvm with
                          accountMap := σ_bids
                          substate := ABids
                          createdAccounts := cA_bids }
                        have hStateBids : EVMStateEquiv evmBidsEvm evmBidsSolm := by
                          refine ⟨rfl, rfl, ?_⟩
                          simpa [evmBidsEvm, evmBidsSolm] using hAccountsBids
                        have rd3653Success := by
                          simpa only [if_true] using rd3653
                        obtain ⟨_, _, rd3674⟩ :=
                          endSkipX_bidsCallSucceeded
                            (g := Sat256.ofUInt256 g) rd3653Success
                        by_cases hshortBid : bidOut.size < 256
                        · have hbidsBlock :
                              ExecBlock config
                                { contract := contract,
                                  locals := endSkipStoreRate I catOut vatOut }
                                evmVatSolm
                                (checkedExternalCallStmts (.var "flip") "bids"
                                  (.intLit 0) [.var "id"] "flipBid" (perm := false))
                                .reverted := by
                            exact endSkipCheckedBidsDecodeRevert
                              (σ := σ_vat_solm) (I := I) (catOut := catOut)
                              (vatOut := vatOut) (bidOut := bidOut)
                              (evm := evmVatSolm) (evmBids := evmBidsSolm)
                              (by rfl)
                              hbidsCodeSolmNE
                              hcallBidsSolm
                              hshortBid
                          have hbody :
                              ExecTransitionBody config contract evmSolm
                                (endSkipStore I) skipTransition.body .reverted := by
                            exact endSkipBodyReverts_afterRateBidsBlock
                              hprefixRate hbidsBlock
                          exact (endSkipX_bidsReturnDecodeShort rd3674 hloCat hloVat
                              hshortBid hbidOutSize)
                            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · have hloBid : 256 ≤ bidOut.size := Nat.le_of_not_gt hshortBid
                          have hbidsBlock :
                              ExecBlock config
                                { contract := contract,
                                  locals := endSkipStoreRate I catOut vatOut }
                                evmVatSolm
                                (checkedExternalCallStmts (.var "flip") "bids"
                                  (.intLit 0) [.var "id"] "flipBid" (perm := false))
                                (.ok
                                  { contract := contract,
                                    locals :=
                                      endSkipStoreFlipBid I catOut vatOut bidOut }
                                  evmBidsSolm) := by
                            exact endSkipCheckedBidsSuccess
                              (σ := σ_vat_solm) (I := I) (catOut := catOut)
                              (vatOut := vatOut) (bidOut := bidOut)
                              (evm := evmVatSolm) (evmBids := evmBidsSolm)
                              (by rfl)
                              hbidsCodeSolmNE
                              hcallBidsSolm
                              hloBid
                          have hprefixTab :=
                            endSkipPrefixTabSuccess hprefixRate hbidsBlock
                          obtain ⟨_, _, rd3712⟩ :=
                            endSkipX_bidsReturnDecodeOk rd3674 hloCat hloVat hloBid
                              hbidOutSize
                          have hmapBidsSolm : evmBidsSolm.accountMap = σ_bids_solm := by
                            rfl
                          have hownerBidsSolm :
                              evmBidsSolm.executionEnv.codeOwner = I.codeOwner := by
                            rfl
                          by_cases hsuck1Code :
                              Reasoning.Theory.extCodeSizeWord σ_bids
                                (endPackVatWord σ_bids I) = ⟨0⟩
                          · have hsuck1CodeSolm :
                                Reasoning.Theory.extCodeSizeWord σ_bids_solm
                                  (endPackVatWord σ_bids_solm I) = ⟨0⟩ :=
                              endPackVatCodeSize_zero_accountMapEquiv hAccountsBids
                                hsuck1Code
                            have hsuck1Block :=
                              endSkipCheckedSuck1NoCode
                                (σ := σ_bids_solm) (I := I) (catOut := catOut)
                                (vatOut := vatOut) (bidOut := bidOut)
                                (evm := evmBidsSolm) hmapBidsSolm hownerBidsSolm
                                hsuck1CodeSolm
                            have htail := endSkipTailReverts_suck1 hsuck1Block
                            have hbody :
                                ExecTransitionBody config contract evmSolm
                                  (endSkipStore I) skipTransition.body .reverted := by
                              exact endSkipBodyReverts_afterTabTailReverted
                                hprefixTab htail
                            exact
                              (endSkipX_suck1NoCode
                                (g := Sat256.ofUInt256 g) hloCat hloVat hloBid
                                rd3712 hsuck1Code)
                                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                          · have hsuck1CodeNE :
                                Reasoning.Theory.extCodeSizeWord σ_bids
                                  (endPackVatWord σ_bids I) ≠ ⟨0⟩ := hsuck1Code
                            have hsuck1CodeSolmNE :
                                Reasoning.Theory.extCodeSizeWord σ_bids_solm
                                  (endPackVatWord σ_bids_solm I) ≠ ⟨0⟩ :=
                              endPackVatCodeSize_ne_accountMapEquiv hAccountsBids
                                hsuck1CodeNE
                            obtain ⟨suck1GasWord, _, _, rdSuck1Ready⟩ :=
                              endSkipX_suck1CallReady
                                (g := Sat256.ofUInt256 g) hloCat hloVat hloBid
                                rd3712 hsuck1CodeNE
                            obtain ⟨cA_suck1, σ_suck1, zSuck1, suck1Out, AinSuck1,
                                callGasSuck1, _, _, hΘSuck1, rd3821,
                                hsuck1OutSize⟩ :=
                              endSkipX_suck1PostCall rdSuck1Ready hdepthLt
                            rcases hΘSuck1 with ⟨gSuck1'', ASuck1, hΘSuck1Eq⟩
                            have hdepthNeSuck1 :
                                evmBidsEvm.executionEnv.depth ≠ 1024 := by
                              intro hbad
                              have hbadI : I.depth = 1024 := by
                                simpa [evmBidsEvm, evmVatEvm, evmCatEvm, initState]
                                  using hbad
                              have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
                              omega
                            have htgtSuck1 :
                                EVM.address (endPackVatAddr σ_bids I) =
                                  AccountAddress.ofUInt256 (endPackVatWord σ_bids I) := by
                              calc
                                EVM.address (endPackVatAddr σ_bids I)
                                    = EVM.address
                                        (AccountAddress.ofUInt256
                                          (endPackVatWord σ_bids I)) := by
                                      rw [endPackVatAddr_eq_ofUInt256]
                                _ = AccountAddress.ofUInt256 (endPackVatWord σ_bids I) :=
                                      hAddressId
                                        (AccountAddress.ofUInt256 (endPackVatWord σ_bids I))
                            obtain ⟨σ_suck1_solm, A_suck1_solm, hcallSuck1SolmRaw,
                                hAccountsSuck1, hSubstateSuck1⟩ :=
                              endCallMade_accountMapEquiv_with_substate
                                (cfg := config) (evm_evm := evmBidsEvm)
                                (evm_solm := evmBidsSolm)
                                (tgt := EVM.address (endPackVatAddr σ_bids I))
                                (targetWord := endPackVatWord σ_bids I)
                                (name := "suck")
                                (args :=
                                  [.address (endPackVowAddr σ_bids I),
                                    .address (endPackVowAddr σ_bids I),
                                    .int (Int.ofNat (endSkipTabWord bidOut).toNat)])
                                (cA' := cA_suck1) (σ' := σ_suck1) (A' := ASuck1)
                                (A_in := AinSuck1) (z := zSuck1) (out := suck1Out)
                                (g'' := gSuck1'') (callGas := callGasSuck1)
                                (mem := endSkipSuck1CalldataMem σ_bids I catOut vatOut
                                  bidOut)
                                (inOff := endSkipSuckOutPtr) (inSize := endSkipSuckInSize)
                                (callPerm := true)
                                hdepthNeSuck1 htgtSuck1
                                (endSkipSuck1Encode_eq σ_bids I catOut vatOut bidOut
                                  hloCat hloVat hloBid)
                                (by simpa [evmBidsEvm, evmVatEvm, evmCatEvm, initState,
                                  hperm] using hΘSuck1Eq)
                                (by simpa [evmBidsEvm, evmBidsSolm] using hAccountsBids)
                                (by rfl)
                                (by simpa using hStateBids.createdAccounts.symm)
                                (by rfl)
                                (by rfl)
                                (by simpa using hStateBids.executionEnv.symm)
                            have hVatWordSuck1 :
                                endPackVatWord σ_bids I =
                                  endPackVatWord σ_bids_solm I :=
                              endPackVatWord_accountMapEquiv hAccountsBids
                            have hVatAddrSuck1 :
                                endPackVatAddr σ_bids I =
                                  endPackVatAddr σ_bids_solm I := by
                              simp [endPackVatAddr, hVatWordSuck1]
                            have hVowWordSuck1 :
                                endPackVowWord σ_bids I =
                                  endPackVowWord σ_bids_solm I :=
                              endPackVowWord_accountMapEquiv hAccountsBids
                            have hVowAddrSuck1 :
                                endPackVowAddr σ_bids I =
                                  endPackVowAddr σ_bids_solm I := by
                              simp [endPackVowAddr, hVowWordSuck1]
                            let evmSuck1Solm :=
                              { evmBidsSolm with
                                accountMap := σ_suck1_solm
                                substate := A_suck1_solm
                                createdAccounts := cA_suck1 }
                            have hcallSuck1Solm :
                                typedCallViaEVM config evmBidsSolm
                                  (EVM.address (endPackVatAddr σ_bids_solm I)) "suck" 0
                                  [.address (endPackVowAddr σ_bids_solm I),
                                    .address (endPackVowAddr σ_bids_solm I),
                                    .int (Int.ofNat (endSkipTabWord bidOut).toNat)]
                                  (zSuck1, evmSuck1Solm, suck1Out) true := by
                              change typedCallViaEVM config evmBidsSolm
                                (EVM.address (endPackVatAddr σ_bids_solm I)) "suck" 0
                                [.address (endPackVowAddr σ_bids_solm I),
                                  .address (endPackVowAddr σ_bids_solm I),
                                  .int (Int.ofNat (endSkipTabWord bidOut).toNat)]
                                (zSuck1,
                                  { evmBidsSolm with
                                    accountMap := σ_suck1_solm
                                    substate := A_suck1_solm
                                    createdAccounts := cA_suck1 },
                                  suck1Out) true
                              rw [← hVatAddrSuck1, ← hVowAddrSuck1]
                              exact hcallSuck1SolmRaw
                            cases zSuck1
                            · have hsuck1Block :=
                                endSkipCheckedSuck1Failure
                                  (σ := σ_bids_solm) (I := I) (catOut := catOut)
                                  (vatOut := vatOut) (bidOut := bidOut)
                                  (suckOut := suck1Out) (evm := evmBidsSolm)
                                  (evmSuck := evmSuck1Solm)
                                  hmapBidsSolm hownerBidsSolm hsuck1CodeSolmNE
                                  hcallSuck1Solm
                              have htail := endSkipTailReverts_suck1 hsuck1Block
                              have hbody :
                                  ExecTransitionBody config contract evmSolm
                                    (endSkipStore I) skipTransition.body .reverted := by
                                exact endSkipBodyReverts_afterTabTailReverted
                                  hprefixTab htail
                              have rd3821Fail := by
                                simpa only [if_false] using rd3821
                              exact (endSkipX_suck1CallFailed rd3821Fail hsuck1OutSize)
                                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                            · let evmSuck1Evm :=
                                { evmBidsEvm with
                                  accountMap := σ_suck1
                                  substate := ASuck1
                                  createdAccounts := cA_suck1 }
                              have hStateSuck1 : EVMStateEquiv evmSuck1Evm evmSuck1Solm := by
                                refine ⟨rfl, rfl, ?_⟩
                                simpa [evmSuck1Evm, evmSuck1Solm] using hAccountsSuck1
                              have hmapSuck1Solm :
                                  evmSuck1Solm.accountMap = σ_suck1_solm := by
                                rfl
                              have hownerSuck1Solm :
                                  evmSuck1Solm.executionEnv.codeOwner = I.codeOwner := by
                                rfl
                              have hsuck1Block :=
                                endSkipCheckedSuck1Success
                                  (σ := σ_bids_solm) (I := I) (catOut := catOut)
                                  (vatOut := vatOut) (bidOut := bidOut)
                                  (suckOut := suck1Out) (evm := evmBidsSolm)
                                  (evmSuck := evmSuck1Solm)
                                  hmapBidsSolm hownerBidsSolm hsuck1CodeSolmNE
                                  hcallSuck1Solm
                              have rd3821Succ := by
                                simpa only [if_true] using rd3821
                              obtain ⟨_, _, rd3840⟩ :=
                                endSkipX_suck1CallSucceeded rd3821Succ
                              by_cases hsuck2Code :
                                  Reasoning.Theory.extCodeSizeWord σ_suck1
                                    (endPackVatWord σ_suck1 I) = ⟨0⟩
                              · have hsuck2CodeSolm :
                                    Reasoning.Theory.extCodeSizeWord σ_suck1_solm
                                      (endPackVatWord σ_suck1_solm I) = ⟨0⟩ :=
                                  endPackVatCodeSize_zero_accountMapEquiv hAccountsSuck1
                                    hsuck2Code
                                have hsuck2Block :=
                                  endSkipCheckedSuck2NoCode
                                    (σ := σ_suck1_solm) (I := I) (catOut := catOut)
                                    (vatOut := vatOut) (bidOut := bidOut)
                                    (evm := evmSuck1Solm) hmapSuck1Solm hownerSuck1Solm
                                    hsuck2CodeSolm
                                have htail := endSkipTailReverts_suck2 hsuck1Block hsuck2Block
                                have hbody :
                                    ExecTransitionBody config contract evmSolm
                                      (endSkipStore I) skipTransition.body .reverted := by
                                  exact endSkipBodyReverts_afterTabTailReverted
                                    hprefixTab htail
                                exact
                                  (endSkipX_suck2NoCode
                                    (g := Sat256.ofUInt256 g)
                                    (σmem := σ_bids) (σpost := σ_suck1)
                                    hloCat hloVat hloBid rd3840 hsuck2Code)
                                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                              · have hsuck2CodeNE :
                                    Reasoning.Theory.extCodeSizeWord σ_suck1
                                      (endPackVatWord σ_suck1 I) ≠ ⟨0⟩ := hsuck2Code
                                have hsuck2CodeSolmNE :
                                    Reasoning.Theory.extCodeSizeWord σ_suck1_solm
                                      (endPackVatWord σ_suck1_solm I) ≠ ⟨0⟩ :=
                                  endPackVatCodeSize_ne_accountMapEquiv hAccountsSuck1
                                    hsuck2CodeNE
                                obtain ⟨suck2GasWord, _, _, rdSuck2Ready⟩ :=
                                  endSkipX_suck2CallReady
                                    (g := Sat256.ofUInt256 g)
                                    (σmem := σ_bids) (σpost := σ_suck1)
                                    hloCat hloVat hloBid rd3840 hsuck2CodeNE
                                obtain ⟨cA_suck2, σ_suck2, zSuck2, suck2Out,
                                    AinSuck2, callGasSuck2, _, _, hΘSuck2, rd3940,
                                    hsuck2OutSize⟩ :=
                                  endSkipX_suck2PostCall
                                    (σmem := σ_bids) (σpost := σ_suck1)
                                    rdSuck2Ready hdepthLt
                                rcases hΘSuck2 with ⟨gSuck2'', ASuck2, hΘSuck2Eq⟩
                                have hdepthNeSuck2 :
                                    evmSuck1Evm.executionEnv.depth ≠ 1024 := by
                                  intro hbad
                                  have hbadI : I.depth = 1024 := by
                                    simpa [evmSuck1Evm, evmBidsEvm, evmVatEvm, evmCatEvm,
                                      initState] using hbad
                                  have hbadVal : I.depth.val = 1024 :=
                                    congrArg Fin.val hbadI
                                  omega
                                have htgtSuck2 :
                                    EVM.address (endPackVatAddr σ_suck1 I) =
                                      AccountAddress.ofUInt256
                                        (endPackVatWord σ_suck1 I) := by
                                  calc
                                    EVM.address (endPackVatAddr σ_suck1 I)
                                        = EVM.address
                                            (AccountAddress.ofUInt256
                                              (endPackVatWord σ_suck1 I)) := by
                                          rw [endPackVatAddr_eq_ofUInt256]
                                    _ = AccountAddress.ofUInt256
                                          (endPackVatWord σ_suck1 I) :=
                                          hAddressId
                                            (AccountAddress.ofUInt256
                                              (endPackVatWord σ_suck1 I))
                                obtain ⟨σ_suck2_solm, A_suck2_solm,
                                    hcallSuck2SolmRaw, hAccountsSuck2,
                                    hSubstateSuck2⟩ :=
                                  endCallMade_accountMapEquiv_with_substate
                                    (cfg := config) (evm_evm := evmSuck1Evm)
                                    (evm_solm := evmSuck1Solm)
                                    (tgt := EVM.address (endPackVatAddr σ_suck1 I))
                                    (targetWord := endPackVatWord σ_suck1 I)
                                    (name := "suck")
                                    (args :=
                                      [.address (endPackVowAddr σ_suck1 I),
                                        .address I.codeOwner,
                                        .int (Int.ofNat (endSkipBidWord bidOut).toNat)])
                                    (cA' := cA_suck2) (σ' := σ_suck2) (A' := ASuck2)
                                    (A_in := AinSuck2) (z := zSuck2) (out := suck2Out)
                                    (g'' := gSuck2'') (callGas := callGasSuck2)
                                    (mem := endSkipSuck2CalldataMemFor σ_bids σ_suck1
                                      I catOut vatOut bidOut)
                                    (inOff := endSkipSuckOutPtr)
                                    (inSize := endSkipSuckInSize) (callPerm := true)
                                    hdepthNeSuck2 htgtSuck2
                                    (endSkipSuck2EncodeFor_eq σ_bids σ_suck1 I
                                      catOut vatOut bidOut hloCat hloVat hloBid)
                                    (by simpa [evmSuck1Evm, evmBidsEvm, evmVatEvm,
                                      evmCatEvm, initState, hperm] using hΘSuck2Eq)
                                    (by simpa [evmSuck1Evm, evmSuck1Solm] using
                                      hAccountsSuck1)
                                    (by rfl)
                                    (by simpa using hStateSuck1.createdAccounts.symm)
                                    (by rfl)
                                    (by rfl)
                                    (by simpa using hStateSuck1.executionEnv.symm)
                                have hVatWordSuck2 :
                                    endPackVatWord σ_suck1 I =
                                      endPackVatWord σ_suck1_solm I :=
                                  endPackVatWord_accountMapEquiv hAccountsSuck1
                                have hVatAddrSuck2 :
                                    endPackVatAddr σ_suck1 I =
                                      endPackVatAddr σ_suck1_solm I := by
                                  simp [endPackVatAddr, hVatWordSuck2]
                                have hVowWordSuck2 :
                                    endPackVowWord σ_suck1 I =
                                      endPackVowWord σ_suck1_solm I :=
                                  endPackVowWord_accountMapEquiv hAccountsSuck1
                                have hVowAddrSuck2 :
                                    endPackVowAddr σ_suck1 I =
                                      endPackVowAddr σ_suck1_solm I := by
                                  simp [endPackVowAddr, hVowWordSuck2]
                                let evmSuck2Solm :=
                                  { evmSuck1Solm with
                                    accountMap := σ_suck2_solm
                                    substate := A_suck2_solm
                                    createdAccounts := cA_suck2 }
                                have hcallSuck2Solm :
                                    typedCallViaEVM config evmSuck1Solm
                                      (EVM.address (endPackVatAddr σ_suck1_solm I))
                                      "suck" 0
                                      [.address (endPackVowAddr σ_suck1_solm I),
                                        .address I.codeOwner,
                                        .int (Int.ofNat (endSkipBidWord bidOut).toNat)]
                                      (zSuck2, evmSuck2Solm, suck2Out) true := by
                                  change typedCallViaEVM config evmSuck1Solm
                                    (EVM.address (endPackVatAddr σ_suck1_solm I))
                                    "suck" 0
                                    [.address (endPackVowAddr σ_suck1_solm I),
                                      .address I.codeOwner,
                                      .int (Int.ofNat (endSkipBidWord bidOut).toNat)]
                                    (zSuck2,
                                      { evmSuck1Solm with
                                        accountMap := σ_suck2_solm
                                        substate := A_suck2_solm
                                        createdAccounts := cA_suck2 },
                                      suck2Out) true
                                  rw [← hVatAddrSuck2, ← hVowAddrSuck2]
                                  exact hcallSuck2SolmRaw
                                cases zSuck2
                                · have hsuck2Block :=
                                    endSkipCheckedSuck2Failure
                                      (σ := σ_suck1_solm) (I := I) (catOut := catOut)
                                      (vatOut := vatOut) (bidOut := bidOut)
                                      (suckOut := suck2Out) (evm := evmSuck1Solm)
                                      (evmSuck := evmSuck2Solm)
                                      hmapSuck1Solm hownerSuck1Solm hsuck2CodeSolmNE
                                      hcallSuck2Solm
                                  have htail :=
                                    endSkipTailReverts_suck2 hsuck1Block hsuck2Block
                                  have hbody :
                                      ExecTransitionBody config contract evmSolm
                                        (endSkipStore I) skipTransition.body .reverted := by
                                    exact endSkipBodyReverts_afterTabTailReverted
                                      hprefixTab htail
                                  have rd3940Fail := by
                                    simpa only [if_false] using rd3940
                                  exact
                                    (endSkipX_suck2CallFailed
                                      (σpre := σ_suck1) rd3940Fail hsuck2OutSize)
                                      |>.reEquivExecutionRevert hcode hdispatch hdecode
                                        hbody
                                · let evmSuck2Evm :=
                                    { evmSuck1Evm with
                                      accountMap := σ_suck2
                                      substate := ASuck2
                                      createdAccounts := cA_suck2 }
                                  have hStateSuck2 :
                                      EVMStateEquiv evmSuck2Evm evmSuck2Solm := by
                                    refine ⟨rfl, rfl, ?_⟩
                                    simpa [evmSuck2Evm, evmSuck2Solm] using
                                      hAccountsSuck2
                                  have hmapSuck2Solm :
                                      evmSuck2Solm.accountMap = σ_suck2_solm := by
                                    rfl
                                  have hownerSuck2Solm :
                                      evmSuck2Solm.executionEnv.codeOwner = I.codeOwner := by
                                    rfl
                                  have hsuck2Block :=
                                    endSkipCheckedSuck2Success
                                      (σ := σ_suck1_solm) (I := I) (catOut := catOut)
                                      (vatOut := vatOut) (bidOut := bidOut)
                                      (suckOut := suck2Out) (evm := evmSuck1Solm)
                                      (evmSuck := evmSuck2Solm)
                                      hmapSuck1Solm hownerSuck1Solm hsuck2CodeSolmNE
                                      hcallSuck2Solm
                                  have rd3940Succ := by
                                    simpa only [if_true] using rd3940
                                  obtain ⟨_, _, rd3959⟩ :=
                                    endSkipX_suck2CallSucceeded rd3940Succ
                                  by_cases hhopeCode :
                                      Reasoning.Theory.extCodeSizeWord σ_suck2
                                        (endPackVatWord σ_suck2 I) = ⟨0⟩
                                  · have hhopeCodeSolm :
                                        Reasoning.Theory.extCodeSizeWord
                                          σ_suck2_solm
                                          (endPackVatWord σ_suck2_solm I) = ⟨0⟩ :=
                                      endPackVatCodeSize_zero_accountMapEquiv
                                        hAccountsSuck2 hhopeCode
                                    have hhopeBlock :=
                                      endSkipCheckedHopeNoCode
                                        (σ := σ_suck2_solm) (I := I) (catOut := catOut)
                                        (vatOut := vatOut) (bidOut := bidOut)
                                        (evm := evmSuck2Solm) hmapSuck2Solm
                                        hownerSuck2Solm hhopeCodeSolm
                                    have htail :=
                                      endSkipTailReverts_hope hsuck1Block hsuck2Block
                                        hhopeBlock
                                    have hbody :
                                        ExecTransitionBody config contract evmSolm
                                          (endSkipStore I) skipTransition.body
                                          .reverted := by
                                      exact endSkipBodyReverts_afterTabTailReverted
                                        hprefixTab htail
                                    exact
                                      (endSkipX_hopeNoCode
                                        (g := Sat256.ofUInt256 g)
                                        (σmem := σ_bids) (σcall := σ_suck1)
                                        (σpost := σ_suck2)
                                        hloCat hloVat hloBid rd3959 hhopeCode)
                                        |>.reEquivExecutionRevert hcode hdispatch
                                          hdecode hbody
                                  · have hhopeCodeNE :
                                        Reasoning.Theory.extCodeSizeWord σ_suck2
                                          (endPackVatWord σ_suck2 I) ≠ ⟨0⟩ := hhopeCode
                                    have hhopeCodeSolmNE :
                                        Reasoning.Theory.extCodeSizeWord
                                          σ_suck2_solm
                                          (endPackVatWord σ_suck2_solm I) ≠ ⟨0⟩ :=
                                      endPackVatCodeSize_ne_accountMapEquiv
                                        hAccountsSuck2 hhopeCodeNE
                                    obtain ⟨hopeGasWord, _, _, rdHopeReady⟩ :=
                                      endSkipX_hopeCallReady
                                        (g := Sat256.ofUInt256 g)
                                        (σmem := σ_bids) (σcall := σ_suck1)
                                        (σpost := σ_suck2)
                                        hloCat hloVat hloBid rd3959 hhopeCodeNE
                                    obtain ⟨cA_hope, σ_hope, zHope, hopeOut, AinHope,
                                        callGasHope, _, _, hΘHope, rd4042,
                                        hhopeOutSize⟩ :=
                                      endSkipX_hopePostCall
                                        (σmem := σ_bids) (σcall := σ_suck1)
                                        (σpost := σ_suck2)
                                        rdHopeReady hdepthLt
                                    rcases hΘHope with ⟨gHope'', AHope, hΘHopeEq⟩
                                    have hdepthNeHope :
                                        evmSuck2Evm.executionEnv.depth ≠ 1024 := by
                                      intro hbad
                                      have hbadI : I.depth = 1024 := by
                                        simpa [evmSuck2Evm, evmSuck1Evm, evmBidsEvm,
                                          evmVatEvm, evmCatEvm, initState] using hbad
                                      have hbadVal : I.depth.val = 1024 :=
                                        congrArg Fin.val hbadI
                                      omega
                                    have htgtHope :
                                        EVM.address (endPackVatAddr σ_suck2 I) =
                                          AccountAddress.ofUInt256
                                            (endPackVatWord σ_suck2 I) := by
                                      calc
                                        EVM.address (endPackVatAddr σ_suck2 I)
                                            = EVM.address
                                                (AccountAddress.ofUInt256
                                                  (endPackVatWord σ_suck2 I)) := by
                                              rw [endPackVatAddr_eq_ofUInt256]
                                        _ = AccountAddress.ofUInt256
                                              (endPackVatWord σ_suck2 I) :=
                                              hAddressId
                                                (AccountAddress.ofUInt256
                                                  (endPackVatWord σ_suck2 I))
                                    obtain ⟨σ_hope_solm, A_hope_solm, hcallHopeSolmRaw,
                                        hAccountsHope, hSubstateHope⟩ :=
                                      endCallMade_accountMapEquiv_with_substate
                                        (cfg := config) (evm_evm := evmSuck2Evm)
                                        (evm_solm := evmSuck2Solm)
                                        (tgt := EVM.address (endPackVatAddr σ_suck2 I))
                                        (targetWord := endPackVatWord σ_suck2 I)
                                        (name := "hope")
                                        (args := [.address (endSkipCatIlkFlipAddr catOut)])
                                        (cA' := cA_hope) (σ' := σ_hope) (A' := AHope)
                                        (A_in := AinHope) (z := zHope) (out := hopeOut)
                                        (g'' := gHope'') (callGas := callGasHope)
                                        (mem := endSkipHopeCalldataMemFor σ_bids σ_suck1
                                          I catOut vatOut bidOut)
                                        (inOff := endSkipHopeOutPtr)
                                        (inSize := endSkipHopeInSize) (callPerm := true)
                                        hdepthNeHope htgtHope
                                        (endSkipHopeEncodeFor_eq σ_bids σ_suck1 I
                                          catOut vatOut bidOut hloCat hloVat hloBid)
                                        (by simpa [evmSuck2Evm, evmSuck1Evm, evmBidsEvm,
                                          evmVatEvm, evmCatEvm, initState, hperm] using
                                          hΘHopeEq)
                                        (by simpa [evmSuck2Evm, evmSuck2Solm] using
                                          hAccountsSuck2)
                                        (by rfl)
                                        (by simpa using hStateSuck2.createdAccounts.symm)
                                        (by rfl)
                                        (by rfl)
                                        (by simpa using hStateSuck2.executionEnv.symm)
                                    have hVatWordHope :
                                        endPackVatWord σ_suck2 I =
                                          endPackVatWord σ_suck2_solm I :=
                                      endPackVatWord_accountMapEquiv hAccountsSuck2
                                    have hVatAddrHope :
                                        endPackVatAddr σ_suck2 I =
                                          endPackVatAddr σ_suck2_solm I := by
                                      simp [endPackVatAddr, hVatWordHope]
                                    let evmHopeSolm :=
                                      { evmSuck2Solm with
                                        accountMap := σ_hope_solm
                                        substate := A_hope_solm
                                        createdAccounts := cA_hope }
                                    have hcallHopeSolm :
                                        typedCallViaEVM config evmSuck2Solm
                                          (EVM.address (endPackVatAddr σ_suck2_solm I))
                                          "hope" 0
                                          [.address (endSkipCatIlkFlipAddr catOut)]
                                          (zHope, evmHopeSolm, hopeOut) true := by
                                      change typedCallViaEVM config evmSuck2Solm
                                        (EVM.address (endPackVatAddr σ_suck2_solm I))
                                        "hope" 0
                                        [.address (endSkipCatIlkFlipAddr catOut)]
                                        (zHope,
                                          { evmSuck2Solm with
                                            accountMap := σ_hope_solm
                                            substate := A_hope_solm
                                            createdAccounts := cA_hope },
                                          hopeOut) true
                                      rw [← hVatAddrHope]
                                      exact hcallHopeSolmRaw
                                    cases zHope
                                    · have hhopeBlock :=
                                        endSkipCheckedHopeFailure
                                          (σ := σ_suck2_solm) (I := I) (catOut := catOut)
                                          (vatOut := vatOut) (bidOut := bidOut)
                                          (hopeOut := hopeOut) (evm := evmSuck2Solm)
                                          (evmHope := evmHopeSolm)
                                          hmapSuck2Solm hownerSuck2Solm hhopeCodeSolmNE
                                          hcallHopeSolm
                                      have htail :=
                                        endSkipTailReverts_hope hsuck1Block hsuck2Block
                                          hhopeBlock
                                      have hbody :
                                          ExecTransitionBody config contract evmSolm
                                            (endSkipStore I) skipTransition.body
                                            .reverted := by
                                        exact endSkipBodyReverts_afterTabTailReverted
                                          hprefixTab htail
                                      have rd4042Fail := by
                                        simpa only [if_false] using rd4042
                                      exact
                                        (endSkipX_hopeCallFailed
                                          (σpre := σ_suck2) rd4042Fail hhopeOutSize)
                                          |>.reEquivExecutionRevert hcode hdispatch
                                            hdecode hbody
                                    · let evmHopeEvm :=
                                        { evmSuck2Evm with
                                          accountMap := σ_hope
                                          substate := AHope
                                          createdAccounts := cA_hope }
                                      have hStateHope :
                                          EVMStateEquiv evmHopeEvm evmHopeSolm := by
                                        refine ⟨rfl, rfl, ?_⟩
                                        simpa [evmHopeEvm, evmHopeSolm] using
                                          hAccountsHope
                                      have hmapHopeSolm :
                                          evmHopeSolm.accountMap = σ_hope_solm := by
                                        rfl
                                      have hhopeBlock :=
                                        endSkipCheckedHopeSuccess
                                          (σ := σ_suck2_solm) (I := I) (catOut := catOut)
                                          (vatOut := vatOut) (bidOut := bidOut)
                                          (hopeOut := hopeOut) (evm := evmSuck2Solm)
                                          (evmHope := evmHopeSolm)
                                          hmapSuck2Solm hownerSuck2Solm hhopeCodeSolmNE
                                          hcallHopeSolm
                                      have rd4042Succ := by
                                        simpa only [if_true] using rd4042
                                      obtain ⟨_, _, rd4063⟩ :=
                                        endSkipX_hopeCallSucceeded rd4042Succ
                                      by_cases hyankCode :
                                          Reasoning.Theory.extCodeSizeWord σ_hope
                                            (endSkipCatIlkFlipTargetWord catOut) = ⟨0⟩
                                      · have hyankCodeSolm :
                                            Reasoning.Theory.extCodeSizeWord
                                              σ_hope_solm
                                              (endSkipCatIlkFlipTargetWord catOut) = ⟨0⟩ :=
                                          endSkipBidsCodeSize_zero_accountMapEquiv
                                            hAccountsHope catOut hyankCode
                                        have hyankBlock :=
                                          endSkipCheckedYankNoCode
                                            (σ := σ_hope_solm) (I := I) (catOut := catOut)
                                            (vatOut := vatOut) (bidOut := bidOut)
                                            (evm := evmHopeSolm) hmapHopeSolm
                                            hyankCodeSolm
                                        have htail :=
                                          endSkipTailReverts_yank hsuck1Block hsuck2Block
                                            hhopeBlock hyankBlock
                                        have hbody :
                                            ExecTransitionBody config contract evmSolm
                                              (endSkipStore I) skipTransition.body
                                              .reverted := by
                                          exact endSkipBodyReverts_afterTabTailReverted
                                            hprefixTab htail
                                        exact
                                          (endSkipX_yankNoCode
                                            (g := Sat256.ofUInt256 g)
                                            (σmem := σ_bids) (σcall := σ_suck1)
                                            (σpost := σ_hope)
                                            hloCat hloVat hloBid rd4063 hyankCode)
                                            |>.reEquivExecutionRevert hcode hdispatch
                                              hdecode hbody
                                      · have hyankCodeNE :
                                            Reasoning.Theory.extCodeSizeWord σ_hope
                                              (endSkipCatIlkFlipTargetWord catOut) ≠ ⟨0⟩ :=
                                          hyankCode
                                        have hyankCodeSolmNE :
                                            Reasoning.Theory.extCodeSizeWord
                                              σ_hope_solm
                                              (endSkipCatIlkFlipTargetWord catOut) ≠ ⟨0⟩ :=
                                          endSkipBidsCodeSize_ne_accountMapEquiv
                                            hAccountsHope catOut hyankCodeNE
                                        obtain ⟨yankGasWord, _, _, rdYankReady⟩ :=
                                          endSkipX_yankCallReady
                                            (g := Sat256.ofUInt256 g)
                                            (σmem := σ_bids) (σcall := σ_suck1)
                                            (σpost := σ_hope)
                                            hloCat hloVat hloBid rd4063 hyankCodeNE
                                        obtain ⟨cA_yank, σ_yank, zYank, yankOut, AinYank,
                                            callGasYank, _, _, hΘYank, rd4136,
                                            hyankOutSize⟩ :=
                                          endSkipX_yankPostCall
                                            (σmem := σ_bids) (σcall := σ_suck1)
                                            (σpost := σ_hope)
                                            rdYankReady hdepthLt
                                        rcases hΘYank with ⟨gYank'', AYank, hΘYankEq⟩
                                        have hdepthNeYank :
                                            evmHopeEvm.executionEnv.depth ≠ 1024 := by
                                          intro hbad
                                          have hbadI : I.depth = 1024 := by
                                            simpa [evmHopeEvm, evmSuck2Evm, evmSuck1Evm,
                                              evmBidsEvm, evmVatEvm, evmCatEvm, initState]
                                              using hbad
                                          have hbadVal : I.depth.val = 1024 :=
                                            congrArg Fin.val hbadI
                                          omega
                                        obtain ⟨σ_yank_solm, A_yank_solm,
                                            hcallYankSolmRaw, hAccountsYank,
                                            hSubstateYank⟩ :=
                                          endCallMade_accountMapEquiv_with_substate
                                            (cfg := config) (evm_evm := evmHopeEvm)
                                            (evm_solm := evmHopeSolm)
                                            (tgt := EVM.address (endSkipCatIlkFlipAddr catOut))
                                            (targetWord := endSkipCatIlkFlipTargetWord catOut)
                                            (name := "yank")
                                            (args := [.int (Int.ofNat (endSkipIdWord I).toNat)])
                                            (cA' := cA_yank) (σ' := σ_yank) (A' := AYank)
                                            (A_in := AinYank) (z := zYank) (out := yankOut)
                                            (g'' := gYank'') (callGas := callGasYank)
                                            (mem := endSkipYankCalldataMemFor σ_bids
                                              σ_suck1 I catOut vatOut bidOut)
                                            (inOff := endSkipYankOutPtr)
                                            (inSize := endSkipYankInSize) (callPerm := true)
                                            hdepthNeYank htgtBids
                                            (endSkipYankEncodeFor_eq σ_bids σ_suck1 I
                                              catOut vatOut bidOut hloCat hloVat hloBid)
                                            (by simpa [evmHopeEvm, evmSuck2Evm,
                                              evmSuck1Evm, evmBidsEvm, evmVatEvm,
                                              evmCatEvm, initState, hperm] using
                                              hΘYankEq)
                                            (by simpa [evmHopeEvm, evmHopeSolm] using
                                              hAccountsHope)
                                            (by rfl)
                                            (by simpa using hStateHope.createdAccounts.symm)
                                            (by rfl)
                                            (by rfl)
                                            (by simpa using hStateHope.executionEnv.symm)
                                        let evmYankSolm :=
                                          { evmHopeSolm with
                                            accountMap := σ_yank_solm
                                            substate := A_yank_solm
                                            createdAccounts := cA_yank }
                                        have hcallYankSolm :
                                            typedCallViaEVM config evmHopeSolm
                                              (EVM.address (endSkipCatIlkFlipAddr catOut))
                                              "yank" 0
                                              [.int (Int.ofNat (endSkipIdWord I).toNat)]
                                              (zYank, evmYankSolm, yankOut) true := by
                                          change typedCallViaEVM config evmHopeSolm
                                            (EVM.address (endSkipCatIlkFlipAddr catOut))
                                            "yank" 0
                                            [.int (Int.ofNat (endSkipIdWord I).toNat)]
                                            (zYank,
                                              { evmHopeSolm with
                                                accountMap := σ_yank_solm
                                                substate := A_yank_solm
                                                createdAccounts := cA_yank },
                                              yankOut) true
                                          exact hcallYankSolmRaw
                                        cases zYank
                                        · have hyankBlock :=
                                            endSkipCheckedYankFailure
                                              (σ := σ_hope_solm) (I := I) (catOut := catOut)
                                              (vatOut := vatOut) (bidOut := bidOut)
                                              (yankOut := yankOut) (evm := evmHopeSolm)
                                              (evmYank := evmYankSolm)
                                              hmapHopeSolm hyankCodeSolmNE hcallYankSolm
                                          have htail :=
                                            endSkipTailReverts_yank hsuck1Block hsuck2Block
                                              hhopeBlock hyankBlock
                                          have hbody :
                                              ExecTransitionBody config contract evmSolm
                                                (endSkipStore I) skipTransition.body
                                                .reverted := by
                                            exact endSkipBodyReverts_afterTabTailReverted
                                              hprefixTab htail
                                          have rd4136Fail := by
                                            simpa only [if_false] using rd4136
                                          exact
                                            (endSkipX_yankCallFailed
                                              (σpost := σ_yank) rd4136Fail hyankOutSize)
                                              |>.reEquivExecutionRevert hcode hdispatch
                                                hdecode hbody
                                        · let evmYankEvm :=
                                            { evmHopeEvm with
                                              accountMap := σ_yank
                                              substate := AYank
                                              createdAccounts := cA_yank }
                                          have hyankBlock :=
                                            endSkipCheckedYankSuccess
                                              (σ := σ_hope_solm) (I := I) (catOut := catOut)
                                              (vatOut := vatOut) (bidOut := bidOut)
                                              (yankOut := yankOut) (evm := evmHopeSolm)
                                              (evmYank := evmYankSolm)
                                              hmapHopeSolm hyankCodeSolmNE hcallYankSolm
                                          have rd4136Succ := by
                                            simpa only [if_true] using rd4136
                                          obtain ⟨_, _, rd4157⟩ :=
                                            endSkipX_yankCallSucceeded
                                              (σpost := σ_yank) rd4136Succ
                                          have hStateYank :
                                              EVMStateEquiv evmYankEvm evmYankSolm := by
                                            refine ⟨?_, rfl, ?_⟩
                                            · simpa [evmYankEvm, evmYankSolm] using
                                                hStateHope.executionEnv
                                            · simpa [evmYankEvm, evmYankSolm] using
                                                hAccountsYank
                                          have hArtCoupleYank :
                                              endSkipArtOldWord σ_yank I =
                                                endSkipArtOldWord σ_yank_solm I := by
                                            simpa [endSkipArtOldWord, endSlotWord] using
                                              accountMapEquiv_storage_findD hAccountsYank
                                                I.codeOwner (endSkipArtSlot I) ⟨0⟩
                                          have hArtLoadSolm :
                                              Solm.EVM.storageLoad evmYankSolm
                                                evmYankSolm.executionEnv.codeOwner
                                                (endSkipArtSlot I) =
                                                  endSkipArtOldWord σ_yank_solm I := by
                                            simp [evmYankSolm, Solm.EVM.storageLoad,
                                              State.lookupAccount, evmHopeSolm,
                                              evmSuck2Solm, evmSuck1Solm, evmBidsSolm,
                                              evmVatSolm, evmCatSolm, evmSolm,
                                              initState, endSkipArtOldWord, endSlotWord,
                                              solcSlotWord, Account.lookupStorage]
                                          by_cases hrate :
                                              endFlowVatIlkRateWord vatOut = ⟨0⟩
                                          · have htail :=
                                              endSkipTailReverts_artDivZero hrate
                                                hsuck1Block hsuck2Block hhopeBlock
                                                hyankBlock
                                            have hbody :
                                                ExecTransitionBody config contract evmSolm
                                                  (endSkipStore I) skipTransition.body
                                                  .reverted := by
                                              exact endSkipBodyReverts_afterTabTailReverted
                                                hprefixTab htail
                                            have hinvalidOr :=
                                              endSkipX_artDivZeroInvalid
                                                (g := Sat256.ofUInt256 g)
                                                (σmem := σ_bids) (σcall := σ_suck1)
                                                (σpost := σ_yank) hrate rd4157
                                            rcases hinvalidOr with hoog | hinvalid
                                            · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
                                                rw [← hcode] at hoog
                                                simpa [initState, Sat256.ofUInt256] using
                                                  hoog))
                                            · have hxi :
                                                  Ξ cA gh bl σ_evm σ₀ g A I =
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
                                              endSkipX_artAddEntry
                                                (g := Sat256.ofUInt256 g)
                                                (σmem := σ_bids) (σcall := σ_suck1)
                                                (σpost := σ_yank) hsz68 hloCat hloVat
                                                hloBid hrateNE rd4157
                                            by_cases hover :
                                                UInt256.size ≤
                                                  (endSkipArtOldWord σ_yank I).toNat +
                                                    (endSkipArtWord vatOut bidOut).toNat
                                            · have hoverSolm :
                                                  UInt256.size ≤
                                                    (endSkipArtOldWord σ_yank_solm I).toNat +
                                                      (endSkipArtWord vatOut bidOut).toNat := by
                                                simpa [← hArtCoupleYank] using hover
                                              have htail :=
                                                endSkipTailReverts_artAddOverflow
                                                  hsz68 hArtLoadSolm hrateNE hoverSolm
                                                  hsuck1Block hsuck2Block hhopeBlock
                                                  hyankBlock
                                              have hbody :
                                                  ExecTransitionBody config contract evmSolm
                                                    (endSkipStore I) skipTransition.body
                                                    .reverted := by
                                                exact endSkipBodyReverts_afterTabTailReverted
                                                  hprefixTab htail
                                              exact
                                                (endSkipX_artAddOverflow
                                                  (g := Sat256.ofUInt256 g)
                                                  (σmem := σ_bids) (σcall := σ_suck1)
                                                  (σpost := σ_yank) hover rd10092)
                                                  |>.reEquivExecutionRevert hcode hdispatch
                                                    hdecode hbody
                                            · have hfit :
                                                  (endSkipArtOldWord σ_yank I).toNat +
                                                    (endSkipArtWord vatOut bidOut).toNat <
                                                      UInt256.size :=
                                                Nat.lt_of_not_ge hover
                                              have hfitSolm :
                                                  (endSkipArtOldWord σ_yank_solm I).toNat +
                                                    (endSkipArtWord vatOut bidOut).toNat <
                                                      UInt256.size := by
                                                simpa [← hArtCoupleYank] using hfit
                                              obtain ⟨_, _, rd4197⟩ :=
                                                endSkipX_artAddReturns
                                                  (g := Sat256.ofUInt256 g)
                                                  (σmem := σ_bids) (σcall := σ_suck1)
                                                  (σpost := σ_yank) hfit rd10092
                                              let int256Bound : Nat :=
                                                57896044618658097711785492504343953926634992332820282019728792003956564819968
                                              have hint256Bound : int256Bound = 2 ^ 255 := by
                                                decide +native
                                              by_cases hlotBound :
                                                  (endSkipLotWord bidOut).toNat < int256Bound
                                              · have hlot :
                                                    (endSkipLotWord bidOut).toNat <
                                                      2 ^ 255 := by
                                                  simpa [hint256Bound] using hlotBound
                                                by_cases hartBound :
                                                    (endSkipArtWord vatOut bidOut).toNat <
                                                      int256Bound
                                                · have hart :
                                                      (endSkipArtWord vatOut bidOut).toNat <
                                                        2 ^ 255 := by
                                                    simpa [hint256Bound] using hartBound
                                                  obtain ⟨_, _, rd4295⟩ :=
                                                    endSkipX_artStoreIntGuardOk
                                                      (g := Sat256.ofUInt256 g)
                                                      (σmem := σ_bids) (σcall := σ_suck1)
                                                      (σpost := σ_yank) hperm hsz68
                                                      hloCat hloVat hloBid hlot hart rd4197
                                                  have htailOk :=
                                                    endSkipTailAfterTabReturns hsz68
                                                      hArtLoadSolm hrateNE hfitSolm hlot hart
                                                      hsuck1Block hsuck2Block hhopeBlock
                                                      hyankBlock
                                                  let σ_post :=
                                                    endSkipPostArtAccountMap σ_yank I
                                                      (endSkipArtNewWord σ_yank I vatOut bidOut)
                                                  let σ_post_solm :=
                                                    endSkipPostArtAccountMap σ_yank_solm I
                                                      (endSkipArtNewWord σ_yank_solm I vatOut
                                                        bidOut)
                                                  let evmPostEvm :=
                                                    endSkipPostArtState evmYankEvm I
                                                      (endSkipArtNewWord σ_yank I vatOut bidOut)
                                                  let evmPostSolm :=
                                                    endSkipPostArtState evmYankSolm I
                                                      (endSkipArtNewWord σ_yank_solm I vatOut
                                                        bidOut)
                                                  have hArtNewCouple :
                                                      endSkipArtNewWord σ_yank I vatOut bidOut =
                                                        endSkipArtNewWord σ_yank_solm I vatOut
                                                          bidOut := by
                                                    simp [endSkipArtNewWord, hArtCoupleYank]
                                                  have hStatePost :
                                                      EVMStateEquiv evmPostEvm evmPostSolm := by
                                                    simpa [evmPostEvm, evmPostSolm,
                                                      endSkipPostArtState] using
                                                      hStateYank.storageStore_codeOwner
                                                        (endSkipArtSlot I) hArtNewCouple
                                                  have hAccountsPost :
                                                      accountMapEquiv σ_post σ_post_solm := by
                                                    simpa [evmPostEvm, evmPostSolm, σ_post,
                                                      σ_post_solm, endSkipPostArtState,
                                                      endSkipPostArtAccountMap,
                                                      storageStore_accountMap] using
                                                      hStatePost.accountMap
                                                  have hmapPostSolm :
                                                      evmPostSolm.accountMap = σ_post_solm := by
                                                    simp [evmPostSolm, σ_post_solm,
                                                      endSkipPostArtState,
                                                      endSkipPostArtAccountMap,
                                                      storageStore_accountMap, evmYankSolm,
                                                      evmHopeSolm, evmSuck2Solm,
                                                      evmSuck1Solm, evmBidsSolm, evmVatSolm,
                                                      evmCatSolm, evmSolm, initState]
                                                  have hownerPostSolm :
                                                      evmPostSolm.executionEnv.codeOwner =
                                                        I.codeOwner := by
                                                    simp [evmPostSolm, endSkipPostArtState,
                                                      storageStore_executionEnv, evmYankSolm,
                                                      evmHopeSolm, evmSuck2Solm,
                                                      evmSuck1Solm, evmBidsSolm, evmVatSolm,
                                                      evmCatSolm, evmSolm, initState]
                                                  by_cases hgrabCode :
                                                      Reasoning.Theory.extCodeSizeWord
                                                        σ_post (endPackVatWord σ_post I) = ⟨0⟩
                                                  · have hgrabCodeSolm :
                                                        Reasoning.Theory.extCodeSizeWord
                                                          σ_post_solm
                                                          (endPackVatWord σ_post_solm I) = ⟨0⟩ :=
                                                      endPackVatCodeSize_zero_accountMapEquiv
                                                        hAccountsPost hgrabCode
                                                    have hgrab :=
                                                      endSkipGrabTailReverts_noCodeFor
                                                        (σCall := σ_post_solm)
                                                        (σLoc := σ_yank_solm) (I := I)
                                                        (catOut := catOut) (vatOut := vatOut)
                                                        (bidOut := bidOut) (evm := evmPostSolm)
                                                        hmapPostSolm hownerPostSolm
                                                        hgrabCodeSolm
                                                    have hbody :
                                                        ExecTransitionBody config contract
                                                          evmSolm (endSkipStore I)
                                                          skipTransition.body .reverted := by
                                                      exact
                                                        endSkipBodyReverts_afterTabTailGrabReverted
                                                          hprefixTab htailOk hgrab
                                                    exact
                                                      (endSkipX_grabNoCode
                                                        (g := Sat256.ofUInt256 g)
                                                        (σCall := σ_post) (σmem := σ_bids)
                                                        (σcall := σ_suck1)
                                                        hloCat hloVat hloBid rd4295
                                                        hgrabCode)
                                                        |>.reEquivExecutionRevert hcode
                                                          hdispatch hdecode hbody
                                                  · have hgrabCodeNE :
                                                        Reasoning.Theory.extCodeSizeWord
                                                          σ_post (endPackVatWord σ_post I) ≠
                                                            ⟨0⟩ := hgrabCode
                                                    have hgrabCodeSolmNE :
                                                        Reasoning.Theory.extCodeSizeWord
                                                          σ_post_solm
                                                          (endPackVatWord σ_post_solm I) ≠
                                                            ⟨0⟩ :=
                                                      endPackVatCodeSize_ne_accountMapEquiv
                                                        hAccountsPost hgrabCodeNE
                                                    obtain ⟨grabGasWord, _, _, rdGrabReady⟩ :=
                                                      endSkipX_grabCallReady
                                                        (g := Sat256.ofUInt256 g)
                                                        (σCall := σ_post) (σmem := σ_bids)
                                                        (σcall := σ_suck1)
                                                        hloCat hloVat hloBid rd4295
                                                        hgrabCodeNE
                                                    obtain ⟨cA_grab, σ_grab, zGrab, ret,
                                                        AinGrab, callGasGrab, _, _, hΘGrab,
                                                        rd4413, hretSize⟩ :=
                                                      endSkipX_grabPostCall
                                                        (g := Sat256.ofUInt256 g)
                                                        (σCall := σ_post) (σmem := σ_bids)
                                                        (σcall := σ_suck1)
                                                        rdGrabReady hdepthLt
                                                    rcases hΘGrab with ⟨gGrab'', AGrab,
                                                      hΘGrabEq⟩
                                                    have hdepthNeGrab :
                                                        evmPostEvm.executionEnv.depth ≠
                                                          1024 := by
                                                      intro hbad
                                                      have hbadI : I.depth = 1024 := by
                                                        simpa [evmPostEvm, endSkipPostArtState,
                                                          storageStore_executionEnv,
                                                          evmYankEvm, evmHopeEvm,
                                                          evmSuck2Evm, evmSuck1Evm,
                                                          evmBidsEvm, evmVatEvm, evmCatEvm,
                                                          initState] using hbad
                                                      have hbadVal : I.depth.val = 1024 :=
                                                        congrArg Fin.val hbadI
                                                      omega
                                                    have htgtGrab :
                                                        EVM.address (endPackVatAddr σ_post I) =
                                                          AccountAddress.ofUInt256
                                                            (endPackVatWord σ_post I) := by
                                                      calc
                                                        EVM.address (endPackVatAddr σ_post I)
                                                            = EVM.address
                                                                (AccountAddress.ofUInt256
                                                                  (endPackVatWord σ_post I)) := by
                                                              rw [endPackVatAddr_eq_ofUInt256]
                                                        _ = AccountAddress.ofUInt256
                                                              (endPackVatWord σ_post I) :=
                                                              hAddressId
                                                                (AccountAddress.ofUInt256
                                                                  (endPackVatWord σ_post I))
                                                    obtain ⟨σ_grab_solm, A_grab_solm,
                                                        hgrabCallSolmRaw, hAccountsGrab,
                                                        hSubstateGrab⟩ :=
                                                      endCallMade_accountMapEquiv_with_substate
                                                        (cfg := config)
                                                        (evm_evm := evmPostEvm)
                                                        (evm_solm := evmPostSolm)
                                                        (tgt :=
                                                          EVM.address (endPackVatAddr σ_post I))
                                                        (targetWord := endPackVatWord σ_post I)
                                                        (name := "grab")
                                                        (args :=
                                                          [.fixedBytes bytes32Width
                                                              (endBytes32ArgBytes I),
                                                            .address (endSkipUsrAddr bidOut),
                                                            .address I.codeOwner,
                                                            .address (endPackVowAddr σ_post I),
                                                            .int (Int.ofNat
                                                              (endSkipLotWord bidOut).toNat),
                                                            .int (Int.ofNat
                                                              (endSkipArtWord vatOut bidOut).toNat)])
                                                        (cA' := cA_grab) (σ' := σ_grab)
                                                        (A' := AGrab) (A_in := AinGrab)
                                                        (z := zGrab) (out := ret)
                                                        (g'' := gGrab'')
                                                        (callGas := callGasGrab)
                                                        (mem :=
                                                          endSkipGrabCalldataMemForTrace
                                                            σ_post σ_bids σ_suck1 I catOut
                                                            vatOut bidOut)
                                                        (inOff := endFreeGrabOutPtr)
                                                        (inSize := endFreeGrabInSize)
                                                        (callPerm := true)
                                                        hdepthNeGrab htgtGrab
                                                        (endSkipGrabEncodeForTrace_eq σ_post
                                                          σ_bids σ_suck1 I catOut vatOut
                                                          bidOut hsz68 hloCat hloVat hloBid
                                                          hlot hart)
                                                        (by simpa [evmPostEvm,
                                                          endSkipPostArtState,
                                                          storageStore_executionEnv,
                                                          storageStore_createdAccounts,
                                                          storageStore_accountMap,
                                                          endSkip_storageStore_σ₀,
                                                          endSkip_storageStore_genesisBlockHeader,
                                                          endSkip_storageStore_blocks, σ_post,
                                                          endSkipPostArtAccountMap, evmYankEvm,
                                                          evmHopeEvm, evmSuck2Evm,
                                                          evmSuck1Evm, evmBidsEvm, evmVatEvm,
                                                          evmCatEvm, initState, hperm] using
                                                          hΘGrabEq)
                                                        hStatePost.accountMap
                                                        (by simp [evmPostEvm, evmPostSolm,
                                                          endSkipPostArtState,
                                                          endSkip_storageStore_σ₀, evmYankEvm,
                                                          evmYankSolm, evmHopeEvm,
                                                          evmHopeSolm, evmSuck2Evm,
                                                          evmSuck2Solm, evmSuck1Evm,
                                                          evmSuck1Solm, evmBidsEvm,
                                                          evmBidsSolm, evmVatEvm, evmVatSolm,
                                                          evmCatEvm, evmCatSolm, evmSolm,
                                                          initState])
                                                        (by simpa [evmPostEvm, evmPostSolm]
                                                          using hStatePost.createdAccounts.symm)
                                                        (by simp [evmPostEvm, evmPostSolm,
                                                          endSkipPostArtState,
                                                          endSkip_storageStore_genesisBlockHeader,
                                                          evmYankEvm, evmYankSolm,
                                                          evmHopeEvm, evmHopeSolm,
                                                          evmSuck2Evm, evmSuck2Solm,
                                                          evmSuck1Evm, evmSuck1Solm,
                                                          evmBidsEvm, evmBidsSolm, evmVatEvm,
                                                          evmVatSolm, evmCatEvm, evmCatSolm,
                                                          evmSolm, initState])
                                                        (by simp [evmPostEvm, evmPostSolm,
                                                          endSkipPostArtState,
                                                          endSkip_storageStore_blocks,
                                                          evmYankEvm, evmYankSolm,
                                                          evmHopeEvm, evmHopeSolm,
                                                          evmSuck2Evm, evmSuck2Solm,
                                                          evmSuck1Evm, evmSuck1Solm,
                                                          evmBidsEvm, evmBidsSolm, evmVatEvm,
                                                          evmVatSolm, evmCatEvm, evmCatSolm,
                                                          evmSolm, initState])
                                                        (by simpa [evmPostEvm, evmPostSolm]
                                                          using hStatePost.executionEnv.symm)
                                                    have hVatWordGrab :
                                                        endPackVatWord σ_post I =
                                                          endPackVatWord σ_post_solm I :=
                                                      endPackVatWord_accountMapEquiv
                                                        hAccountsPost
                                                    have hVatAddrGrab :
                                                        endPackVatAddr σ_post I =
                                                          endPackVatAddr σ_post_solm I := by
                                                      simp [endPackVatAddr, hVatWordGrab]
                                                    have hVowWordGrab :
                                                        endPackVowWord σ_post I =
                                                          endPackVowWord σ_post_solm I :=
                                                      endPackVowWord_accountMapEquiv
                                                        hAccountsPost
                                                    have hVowAddrGrab :
                                                        endPackVowAddr σ_post I =
                                                          endPackVowAddr σ_post_solm I := by
                                                      simp [endPackVowAddr, hVowWordGrab]
                                                    have hgrabCallSolm :
                                                        typedCallViaEVM config evmPostSolm
                                                          (EVM.address
                                                            (endPackVatAddr σ_post_solm I))
                                                          "grab" 0
                                                          [.fixedBytes bytes32Width
                                                              (endBytes32ArgBytes I),
                                                            .address (endSkipUsrAddr bidOut),
                                                            .address I.codeOwner,
                                                            .address
                                                              (endPackVowAddr σ_post_solm I),
                                                            .int (Int.ofNat
                                                              (endSkipLotWord bidOut).toNat),
                                                            .int (Int.ofNat
                                                              (endSkipArtWord vatOut bidOut).toNat)]
                                                          (zGrab,
                                                            { evmPostSolm with
                                                              accountMap := σ_grab_solm
                                                              substate := A_grab_solm
                                                              createdAccounts := cA_grab },
                                                            ret) true := by
                                                      simpa [hVatAddrGrab, hVowAddrGrab] using
                                                        hgrabCallSolmRaw
                                                    cases zGrab
                                                    · have hgrab :=
                                                        endSkipGrabTailReverts_callFailedFor
                                                          (σCall := σ_post_solm)
                                                          (σLoc := σ_yank_solm) (I := I)
                                                          (catOut := catOut) (vatOut := vatOut)
                                                          (bidOut := bidOut) (grabOut := ret)
                                                          (evm := evmPostSolm)
                                                          (evmGrab :=
                                                            { evmPostSolm with
                                                              accountMap := σ_grab_solm
                                                              substate := A_grab_solm
                                                              createdAccounts := cA_grab })
                                                          hmapPostSolm hownerPostSolm
                                                          hgrabCodeSolmNE
                                                          (by simpa using hgrabCallSolm)
                                                      have hbody :
                                                          ExecTransitionBody config contract
                                                            evmSolm (endSkipStore I)
                                                            skipTransition.body .reverted := by
                                                        exact
                                                          endSkipBodyReverts_afterTabTailGrabReverted
                                                            hprefixTab htailOk hgrab
                                                      have rd4413Fail := by
                                                        simpa only [if_false] using rd4413
                                                      exact
                                                        (endSkipX_grabCallFailed rd4413Fail
                                                          hretSize)
                                                          |>.reEquivExecutionRevert hcode
                                                            hdispatch hdecode hbody
                                                    · let evmGrabEvm :=
                                                        { evmPostEvm with
                                                          accountMap := σ_grab
                                                          substate := AGrab
                                                          createdAccounts := cA_grab }
                                                      let evmGrabSolm :=
                                                        { evmPostSolm with
                                                          accountMap := σ_grab_solm
                                                          substate := A_grab_solm
                                                          createdAccounts := cA_grab }
                                                      have hStateGrab :
                                                          EVMStateEquiv evmGrabEvm
                                                            evmGrabSolm := by
                                                        refine ⟨?_, ?_, ?_⟩
                                                        · simpa [evmGrabEvm, evmGrabSolm] using
                                                            hStatePost.executionEnv
                                                        · simp [evmGrabEvm, evmGrabSolm]
                                                        · simpa [evmGrabEvm, evmGrabSolm] using
                                                            hAccountsGrab
                                                      have rd4413Succ := by
                                                        simpa only [if_true] using rd4413
                                                      obtain ⟨_, _, rd4431⟩ :=
                                                        endSkipX_grabCallSucceeded rd4413Succ
                                                      have hretEvm :=
                                                        endSkipX_grabLogReturn
                                                          (σCall := σ_post) (σmem := σ_bids)
                                                          (σcall := σ_suck1)
                                                          (catOut := catOut) (vatOut := vatOut)
                                                          (bidOut := bidOut) (ret := ret)
                                                          hperm hloCat hloVat hloBid rd4431
                                                      have hgrab :=
                                                        endSkipGrabTailReturns_successFor
                                                          (σCall := σ_post_solm)
                                                          (σLoc := σ_yank_solm) (I := I)
                                                          (catOut := catOut) (vatOut := vatOut)
                                                          (bidOut := bidOut) (grabOut := ret)
                                                          (evm := evmPostSolm)
                                                          (evmGrab := evmGrabSolm)
                                                          hmapPostSolm hownerPostSolm
                                                          hgrabCodeSolmNE
                                                          (by simpa [evmGrabSolm] using
                                                            hgrabCallSolm)
                                                      have hbody :
                                                          ExecTransitionBody config contract
                                                            evmSolm (endSkipStore I)
                                                            skipTransition.body
                                                            (.returned
                                                              { contract := contract,
                                                                locals :=
                                                                  endSkipStoreGrab
                                                                    σ_yank_solm I catOut
                                                                    vatOut bidOut }
                                                              evmGrabSolm none) := by
                                                        exact
                                                          endSkipBodyReturns_afterTabTailGrabSuccess
                                                            hprefixTab htailOk hgrab
                                                      exact hretEvm.reEquivExecutionGenEVMStateEquiv
                                                        (evm'_evm := evmGrabEvm)
                                                        (evm'_solm := evmGrabSolm)
                                                        hcode hdispatch hdecode hbody
                                                        (by simp [evmGrabEvm])
                                                        (by
                                                          simpa [evmGrabEvm] using
                                                            accountMapEquiv.refl σ_grab)
                                                        hStateGrab
                                                        (by
                                                          simpa [skipTransition] using
                                                            (returnEquiv.fallthrough
                                                              (o := ByteArray.empty) (r := none)
                                                              (t := []) (dvs := []) rfl
                                                              (by decide +native)
                                                              (by decide +native)))
                                                · have hartOverflowBound :
                                                    int256Bound ≤
                                                      (endSkipArtWord vatOut bidOut).toNat :=
                                                    Nat.le_of_not_gt hartBound
                                                  have hartOverflow :
                                                      2 ^ 255 ≤
                                                        (endSkipArtWord vatOut bidOut).toNat := by
                                                    simpa [hint256Bound] using hartOverflowBound
                                                  have htail :=
                                                    endSkipTailReverts_intGuardArt hsz68
                                                      hArtLoadSolm hrateNE hfitSolm hlot
                                                      hartOverflow hsuck1Block hsuck2Block
                                                      hhopeBlock hyankBlock
                                                  have hbody :
                                                      ExecTransitionBody config contract evmSolm
                                                        (endSkipStore I) skipTransition.body
                                                        .reverted := by
                                                    exact endSkipBodyReverts_afterTabTailReverted
                                                      hprefixTab htail
                                                  exact
                                                    (endSkipX_artStoreIntGuardArtOverflow
                                                      (g := Sat256.ofUInt256 g)
                                                      (σmem := σ_bids) (σcall := σ_suck1)
                                                      (σpost := σ_yank) hperm hsz68
                                                      hloCat hloVat hloBid hlot
                                                      hartOverflow rd4197)
                                                      |>.reEquivExecutionRevert hcode hdispatch
                                                        hdecode hbody
                                              · have hlotOverflowBound :
                                                    int256Bound ≤
                                                      (endSkipLotWord bidOut).toNat :=
                                                  Nat.le_of_not_gt hlotBound
                                                have hlotOverflow :
                                                    2 ^ 255 ≤
                                                      (endSkipLotWord bidOut).toNat := by
                                                  simpa [hint256Bound] using hlotOverflowBound
                                                have htail :=
                                                  endSkipTailReverts_intGuardLot hsz68
                                                    hArtLoadSolm hrateNE hfitSolm hlotOverflow
                                                    hsuck1Block hsuck2Block hhopeBlock
                                                    hyankBlock
                                                have hbody :
                                                    ExecTransitionBody config contract evmSolm
                                                      (endSkipStore I) skipTransition.body
                                                      .reverted := by
                                                  exact endSkipBodyReverts_afterTabTailReverted
                                                    hprefixTab htail
                                                exact
                                                  (endSkipX_artStoreIntGuardLotOverflow
                                                    (g := Sat256.ofUInt256 g)
                                                    (σmem := σ_bids) (σcall := σ_suck1)
                                                    (σpost := σ_yank) hperm hsz68
                                                    hloCat hloVat hloBid hlotOverflow
                                                    rd4197)
                                                    |>.reEquivExecutionRevert hcode hdispatch
                                                      hdecode hbody
        · rw [not_lt] at hdepthLt
          have hdepthEq : I.depth = 1024 :=
            Fin.ext (by have := I.depth.isLt; omega)
          obtain ⟨_, _, rd3395⟩ :=
            endSkipX_catIlksCallDepthLimit
              (g := Sat256.ofUInt256 g) hcatReady hdepthEq
          let A_cat :=
            (evmSolm.addAccessedAccount
              (EVM.address (endSkipCatAddr σ_solm I))).substate
          have hcallSolm :
              typedCallViaEVM config evmSolm
                (EVM.address (endSkipCatAddr σ_solm I)) "catIlks" 0
                [.fixedBytes bytes32Width (endBytes32ArgBytes I)]
                (false, { evmSolm with substate := A_cat }, ByteArray.empty) true := by
            simpa [A_cat] using
              (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
                (tgt := EVM.address (endSkipCatAddr σ_solm I))
                (name := "catIlks")
                (args := [.fixedBytes bytes32Width (endBytes32ArgBytes I)])
                (callPerm := true)
                (endSkipCatIlksEncode_eq I hsz68 (endSkipCatIlksBaseMem_size I))
                (by simpa [evmSolm, initState] using hdepthEq))
          have hbody :
              ExecTransitionBody config contract evmSolm (endSkipStore I)
                skipTransition.body .reverted := by
            simpa [evmSolm] using
              endSkipBodyReverts_catIlksCallFailed
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g)
                (evmCat := { evmSolm with substate := A_cat })
                (out := ByteArray.empty)
                hwv hsz68 htagSolmNE hcatCodeSolmNE
                (by simpa using hcallSolm)
          exact (endSkipX_catIlksCallFailed rd3395 (by decide +native))
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact endSkipBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.End
