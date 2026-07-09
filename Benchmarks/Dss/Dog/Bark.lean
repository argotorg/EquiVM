import Benchmarks.Dss.Dog.Dispatch
import Reasoning.MemCascade
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Reasoning.Theory

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

theorem dup16_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.DUP16, .none))
    (hstk : s.machineState.stack =
      a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
    (hov : t.length + 17 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok
          (stSwap s
            (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll ::
              mm :: nn :: oo :: pp :: t),
            .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.DUP16, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_dup16 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
          nn :: oo :: pp :: t).length - 16 + 17 > 1024) := by
    simp only [List.length_cons]; omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

end Reasoning.Theory

namespace Reasoning.Reach

theorem RD.dup12 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State}
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
  h.stepSwap (fun _ hc hp hs => Reasoning.Theory.dup12_xstep hc hp hdec hs hov)

theorem RD.dup16 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj kk ll mm nn oo pp : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc
      (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm :: nn ::
        oo :: pp :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.DUP16, .none)) (hov : t.length + 17 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (pp :: a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: kk :: ll :: mm ::
        nn :: oo :: pp :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  h.stepSwap (fun _ hc hp hs => Reasoning.Theory.dup16_xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace Benchmarks.Dss.Dog

/-! ## `bark(bytes32,address,address)` -/

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

noncomputable abbrev barkVatUrnsSelectorMem (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem 128 barkVatUrnsSelectorWord

noncomputable abbrev barkVatUrnsIlkMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsSelectorMem mem) 132 (barkIlkWord I)

noncomputable abbrev barkVatUrnsCallMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsIlkMem I mem) 164 (barkUrnKey I)

noncomputable abbrev barkVatUrnsPostCallMem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  out.write 0 (barkVatUrnsCallMem I mem) 128
    (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat

noncomputable abbrev barkVatUrnsTupleFreeMem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsPostCallMem I mem out) 64 ⟨256⟩

noncomputable abbrev barkVatUrnsTupleWord0Mem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsTupleFreeMem I mem out) 128 ⟨0⟩

noncomputable abbrev barkVatUrnsTupleWord1Mem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsTupleWord0Mem I mem out) 160 ⟨0⟩

noncomputable abbrev barkVatUrnsTupleWord2Mem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatUrnsTupleWord1Mem I mem out) 192 ⟨0⟩

noncomputable abbrev barkVatUrnsTupleMem
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
      (dogAddressReturnWord (barkIlksClipSlotFor I) evm.accountMap evm.executionEnv).toNat))

abbrev barkLocalsMilkChop (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    Store :=
  (barkLocalsMilkClip evm I out).insert "milkChop"
    (.int (Int.ofNat (dogSlotWord (barkIlksChopSlotFor I) evm.accountMap
      evm.executionEnv).toNat))

abbrev barkLocalsMilkHole (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    Store :=
  (barkLocalsMilkChop evm I out).insert "milkHole"
    (.int (Int.ofNat (dogSlotWord (barkIlksHoleSlotFor I) evm.accountMap
      evm.executionEnv).toNat))

abbrev barkLocalsMilkDirt (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    Store :=
  (barkLocalsMilkHole evm I out).insert "milkDirt"
    (.int (Int.ofNat (dogSlotWord (barkIlksDirtSlotFor I) evm.accountMap
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

noncomputable abbrev barkIlksHashMem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  twoWordHashMem (barkIlkWord I) ⟨1⟩ (barkVatUrnsTupleMem I mem out)

noncomputable abbrev barkIlksAllocMem
    (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksHashMem I mem out) 64 ⟨384⟩

noncomputable abbrev barkIlksClipMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksAllocMem I mem out) 256 (barkIlksClipWord σ I)

noncomputable abbrev barkIlksChopMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksClipMem σ I mem out) 288 (barkIlksChopWord σ I)

noncomputable abbrev barkIlksHoleMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksChopMem σ I mem out) 320 (barkIlksHoleWord σ I)

noncomputable abbrev barkIlksMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksHoleMem σ I mem out) 352 (barkIlksDirtWord σ I)

abbrev barkVatIlksSelectorWord : UInt256 :=
  UInt256.shiftLeft ⟨1823590043⟩ ⟨225⟩

noncomputable abbrev barkVatIlksSelectorMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkIlksMem σ I mem out) 384 barkVatIlksSelectorWord

noncomputable abbrev barkVatIlksCallMem
    (σ : AccountMap) (I : ExecutionEnv) (mem out : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatIlksSelectorMem σ I mem out) 388 (barkIlkWord I)

noncomputable abbrev barkVatIlksPostCallMem
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
  UInt256.sub (dogSlotWord ⟨4⟩ σ I) (dogSlotWord ⟨5⟩ σ I)

abbrev barkIlkRoomWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub (barkIlksHoleWord σ I) (barkIlksDirtWord σ I)

abbrev barkRoomWord (σ σMem : AccountMap) (I : ExecutionEnv) : UInt256 :=
  if (barkGlobalRoomWord σ I).toNat ≤ (barkIlkRoomWord σMem I).toNat then
    barkGlobalRoomWord σ I
  else
    barkIlkRoomWord σMem I

abbrev barkSourceGlobalRoomWord (evmIlks : EVM.State) : UInt256 :=
  UInt256.sub (dogSlotWord ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv)
    (dogSlotWord ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv)

abbrev barkSourceIlkRoomWord (evmUrns : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.sub
    (dogSlotWord (barkIlksHoleSlotFor I) evmUrns.accountMap evmUrns.executionEnv)
    (dogSlotWord (barkIlksDirtSlotFor I) evmUrns.accountMap evmUrns.executionEnv)

abbrev barkSourceRoomWord (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) : UInt256 :=
  if (barkSourceGlobalRoomWord evmIlks).toNat ≤ (barkSourceIlkRoomWord evmUrns I).toNat then
    barkSourceGlobalRoomWord evmIlks
  else
    barkSourceIlkRoomWord evmUrns I

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

abbrev barkBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev dogWadWord : UInt256 :=
  ⟨1000000000000000000⟩

abbrev dogInt256LimitWord : UInt256 :=
  UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩

abbrev barkVowWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (dogSlotWord ⟨2⟩ σ I)

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

noncomputable abbrev barkVatGrabSelectorMem (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem 384 barkVatGrabSelectorShifted

noncomputable abbrev barkVatGrabIlkMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabSelectorMem mem) 388 (barkIlkWord I)

noncomputable abbrev barkVatGrabUrnMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabIlkMem I mem) 420 (barkUrnKey I)

noncomputable abbrev barkVatGrabClipMem
    (σMem : AccountMap) (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabUrnMem I mem) 452 (barkIlksClipWord σMem I)

noncomputable abbrev barkVatGrabVowMem
    (σ σMem : AccountMap) (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabClipMem σMem I mem) 484 (barkVowWord σ I)

noncomputable abbrev barkVatGrabDinkMem
    (σ σMem : AccountMap) (I : ExecutionEnv) (mem : ByteArray) (dink : UInt256) :
    ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabVowMem σ σMem I mem) 516 (UInt256.sub ⟨0⟩ dink)

noncomputable abbrev barkVatGrabCallMem
    (σ σMem : AccountMap) (I : ExecutionEnv) (mem : ByteArray)
    (dink dart : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (barkVatGrabDinkMem σ σMem I mem dink) 548
    (UInt256.sub ⟨0⟩ dart)

noncomputable abbrev barkVatGrabPostCallMem
    (σ σMem : AccountMap) (I : ExecutionEnv) (mem out : ByteArray)
    (dink dart : UInt256) : ByteArray :=
  out.write 0 (barkVatGrabCallMem σ σMem I mem dink dart) barkVatGrabOutPtr.toNat
    (min barkVatGrabOutSize (UInt256.ofNat out.size)).toNat

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

abbrev dogNotLiveRawWord : UInt256 :=
  ⟨21179658712531102354511591013⟩

abbrev dogNotUnsafeRawWord : UInt256 :=
  ⟨1388030113384438323915188657546853⟩

abbrev dogLiquidationLimitHitRawWord : UInt256 :=
  ⟨429574513270148286153109682416655011243695164593862324283764⟩

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
        (dogSlotWord (barkIlksHoleSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  rw [barkLocalsArtRateUnsafe, store_get_ne _ _ (by decide), barkLocalsInkSpot,
    store_get_ne _ _ (by decide), barkLocalsDust, store_get_ne _ _ (by decide),
    barkLocalsSpot, store_get_ne _ _ (by decide), barkLocalsRate,
    store_get_ne _ _ (by decide), barkLocalsVatIlk, store_get_ne _ _ (by decide),
    barkLocalsMilkDirt, store_get_ne _ _ (by decide), barkLocalsMilkHole, store_get_self]

theorem barkLocalsArtRateUnsafe_get_milkDirt
    (evm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsArtRateUnsafe evm I out outIlks).get? "milkDirt" =
      some (.int (Int.ofNat
        (dogSlotWord (barkIlksDirtSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
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
        (dogSlotWord (barkIlksHoleSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat)) := by
  rw [barkLocalsGlobalRoom, store_get_ne _ _ (by decide),
    barkLocalsArtRateUnsafe_get_milkHole]

theorem barkLocalsGlobalRoom_get_milkDirt
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    (barkLocalsGlobalRoom evmUrns evmIlks I out outIlks).get? "milkDirt" =
      some (.int (Int.ofNat
        (dogSlotWord (barkIlksDirtSlotFor I) evmUrns.accountMap
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

theorem barkBinaryLocals_get_x (x y : UInt256) :
    (barkBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [barkBinaryLocals, store_get_self]

theorem barkBinaryLocals_get_y (x y : UInt256) :
    (barkBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [barkBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem dogSlotWord_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) (slot : UInt256) :
    dogSlotWord slot σ I = dogSlotWord slot τ I := by
  have hslot := accountMapEquiv_storage_findD h I.codeOwner slot (⟨0⟩ : UInt256)
  simpa [dogSlotWord, solcSlotWord] using hslot

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
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatUrnsPostCallMem I mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatUrnsPostCallMem I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by
      have hgt := barkVatUrnsPostCallMem_size_gt64 (I := I) hmem hshort hout
      omega)
    (by decide)
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
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatUrnsPostCallMem I mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatUrnsPostCallMem I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [barkVatUrnsPostCallMem_size_long hmem hlong hout]; decide)
    (by decide)
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
    (if (⟨128⟩ : UInt256).toNat ≥ (barkVatUrnsPostCallMem I mem out).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatUrnsPostCallMem I mem out).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      barkVatUrnsInkWord out := by
  unfold barkVatUrnsInkWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((barkVatUrnsPostCallMem I mem out).readWithPadding 128 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
    rw [barkVatUrnsPostCallMem_read128_long hmem hlong hout]
  · exact not_or.mpr
      ⟨by rw [barkVatUrnsPostCallMem_size_long hmem hlong hout]; decide,
        by native_decide⟩

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
    (if (⟨160⟩ : UInt256).toNat ≥ (barkVatUrnsPostCallMem I mem out).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 7 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatUrnsPostCallMem I mem out).readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      barkVatUrnsArtWord out := by
  unfold barkVatUrnsArtWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((barkVatUrnsPostCallMem I mem out).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))
    rw [barkVatUrnsPostCallMem_read160_long hmem hlong hout]
  · exact not_or.mpr
      ⟨by rw [barkVatUrnsPostCallMem_size_long hmem hlong hout]; decide,
        by native_decide⟩

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
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatUrnsTupleMem I mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatUrnsTupleMem I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨256⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 8) (v := (⟨256⟩ : UInt256))
    (by rw [barkVatUrnsTupleMem_size hmem hlong hout]; decide)
    (by native_decide)
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

theorem barkIlksHoleWord_eq_slotFor {σ : AccountMap} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    barkIlksHoleWord σ I = dogSlotWord (barkIlksHoleSlotFor I) σ I := by
  simp [barkIlksHoleWord, dogSlotWord, barkIlksSlot, barkIlksHoleSlotFor_eq hsz100]

theorem barkIlksDirtWord_eq_slotFor {σ : AccountMap} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    barkIlksDirtWord σ I = dogSlotWord (barkIlksDirtSlotFor I) σ I := by
  simp [barkIlksDirtWord, dogSlotWord, barkIlksSlot, barkIlksDirtSlotFor_eq hsz100,
    u256_add_comm]

theorem barkUrn_value_masked (I : ExecutionEnv) :
    (.address (barkUrn I) : Value) =
      .address (AccountAddress.ofNat (barkUrnKey I).toNat) := by
  simpa [barkUrn, barkUrnKey, barkUrnWord] using
    (solcAddressValue_masked (calldataWord I.calldata 36))

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

theorem barkVatUrnsEncodeWords {v : DogImmutables} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    (config v).externalABI.encode? "urns"
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

theorem barkVatUrnsEncode_eq {v : DogImmutables} {I : ExecutionEnv} {mem : ByteArray}
    (hsz100 : 100 ≤ I.calldata.size) (hmem : mem.size = 96) :
    (config v).externalABI.encode? "urns"
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] =
      some ((barkVatUrnsCallMem I mem).readWithPadding 128 68) := by
  rw [barkVatUrnsCallMem_read128_68 hmem]
  exact barkVatUrnsEncodeWords (v := v) (I := I) hsz100

theorem barkWordOfIntSubToUInt256 (x y : UInt256) :
    EVM.wordOfInt ((x.toNat : Int) - (y.toNat : Int)) = UInt256.sub x y := by
  by_cases hle : y.toNat ≤ x.toNat
  · have hnonneg : 0 ≤ (x.toNat : Int) - (y.toNat : Int) := by omega
    rw [wordOfInt_nonneg _ hnonneg]
    apply u256_inj
    have htoNat : ((x.toNat : Int) - (y.toNat : Int)).toNat = x.toNat - y.toNat := by
      omega
    rw [usub_toNat (a := x) (b := y) hle]
    simp [EVM.word, EVM.uintN, htoNat]
    exact Nat.mod_eq_of_lt (by exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.val.isLt)
  · have hlt : x.toNat < y.toNat := Nat.lt_of_not_ge hle
    rw [EVM.wordOfInt]
    have hwordMod : EVM.wordModulus = UInt256.size := by native_decide
    have hneg : (x.toNat : Int) - (y.toNat : Int) < 0 := by omega
    rw [if_pos hneg]
    have hnatAbs :
        Int.natAbs ((x.toNat : Int) - (y.toNat : Int)) = y.toNat - x.toNat := by
      omega
    have hdiffMod :
        (y.toNat - x.toNat) % EVM.wordModulus = y.toNat - x.toNat := by
      apply Nat.mod_eq_of_lt
      rw [hwordMod]
      have hy : y.toNat < UInt256.size := y.val.isLt
      omega
    have hdiffNe : y.toNat - x.toNat ≠ 0 := by omega
    rw [hnatAbs, hdiffMod, if_neg hdiffNe]
    apply u256_inj
    rw [usub_toNat_underflow (a := x) (b := y) hlt]
    have hword :
        EVM.wordModulus - (y.toNat - x.toNat) =
          UInt256.size + x.toNat - y.toNat := by
      rw [hwordMod]
      omega
    simp [EVM.word, EVM.uintN, hword, show EVM.twoPow 256 = UInt256.size from by native_decide]
    exact Nat.mod_eq_of_lt (by
      have hy : y.toNat < UInt256.size := y.val.isLt
      omega)

theorem barkInt256NegArgEncoding (w : UInt256)
    (hw : w.toNat ≤ dogInt256LimitWord.toNat) :
    ABI.encodeABIValue? (.elem (.int int256Int)) (.int (-(Int.ofNat w.toNat))) =
      some (EVM.Word.toBytesBE (UInt256.sub ⟨0⟩ w)) := by
  have hword :
      EVM.wordOfInt (-(Int.ofNat w.toNat)) = UInt256.sub ⟨0⟩ w := by
    simpa using barkWordOfIntSubToUInt256 (⟨0⟩ : UInt256) w
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

theorem barkAddressWord_ofUInt256_masked (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    EVM.word ↑(AccountAddress.ofUInt256 w) = w := by
  have hcanonVal : ↑w.val < EVM.addressModulus := by
    simpa [UInt256.toNat] using hcanon
  apply u256_inj
  simp only [EVM.word, EVM.uintN, UInt256.toNat, AccountAddress.ofUInt256, Fin.ofNat]
  rw [show AccountAddress.size = EVM.addressModulus from by decide]
  rw [Nat.mod_eq_of_lt hcanonVal]
  rw [Nat.mod_eq_of_lt hcanonVal]
  rw [Nat.mod_eq_of_lt (by exact w.val.isLt)]

theorem barkAddressArgEncodingMasked (w : UInt256)
    (hcanon : w.toNat < EVM.addressModulus) :
    ABI.encodeABIValue? (.elem .address) (.address (AccountAddress.ofUInt256 w)) =
      some (EVM.Word.toBytesBE w) := by
  simp [ABI.encodeABIValue?, ABI.encodeABIWord?, barkAddressWord_ofUInt256_masked w hcanon]

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

theorem twoWordHashMem_solcMappingSlot_256 (baseSlot key : UInt256) {mem : ByteArray}
    (hmem : mem.size = 256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_256 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

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
    (if (⟨64⟩ : UInt256).toNat ≥ (barkIlksHashMem I mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkIlksHashMem I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨256⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 8) (v := (⟨256⟩ : UInt256))
    (by rw [barkIlksHashMem_size hmem hlong hout]; decide)
    (by native_decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
      barkIlksHashMem_read64 hmem hlong hout)

theorem barkIlksHashMem_slot {I : ExecutionEnv} {mem out : ByteArray}
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((barkIlksHashMem I mem out).readWithPadding 0 64))) =
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
    (if (⟨64⟩ : UInt256).toNat ≥ (barkIlksMem σ I mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkIlksMem σ I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 12) (v := (⟨384⟩ : UInt256))
    (by rw [barkIlksMem_size hmem hlong hout]; decide)
    (by native_decide)
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
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatIlksCallMem σ I mem out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 14 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksCallMem σ I mem out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 14) (v := (⟨384⟩ : UInt256))
    (by rw [barkVatIlksCallMem_size hmem hlong hout]; decide)
    (by native_decide)
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
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 17) (v := (⟨384⟩ : UInt256))
    (by
      have hgt := barkVatIlksPostCallMem_size_gt64 (σ := σ) (I := I) hmem hlong
        hout hshort houtIlks
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hgt)
    (by native_decide)
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
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 17) (v := (⟨384⟩ : UInt256))
    (by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]; decide)
    (by native_decide)
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
    (if (⟨256⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size
        ∨ (⟨256⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨256⟩ : UInt256).toNat 32))) =
      barkIlksClipWord σ I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨256⟩ : UInt256)) (aw := UInt256.ofNat 17)
    (v := barkIlksClipWord σ I)
    (by
      rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]
      native_decide)
    (by native_decide)
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
    (if (⟨288⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size
        ∨ (⟨288⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨288⟩ : UInt256).toNat 32))) =
      barkIlksChopWord σ I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨288⟩ : UInt256)) (aw := UInt256.ofNat 17)
    (v := barkIlksChopWord σ I)
    (by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]; decide)
    (by native_decide)
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
    (if (⟨320⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size
        ∨ (⟨320⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨320⟩ : UInt256).toNat 32))) =
      barkIlksHoleWord σ I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨320⟩ : UInt256)) (aw := UInt256.ofNat 17)
    (v := barkIlksHoleWord σ I)
    (by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]; decide)
    (by native_decide)
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
    (if (⟨352⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size
        ∨ (⟨352⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨352⟩ : UInt256).toNat 32))) =
      barkIlksDirtWord σ I := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨352⟩ : UInt256)) (aw := UInt256.ofNat 17)
    (v := barkIlksDirtWord σ I)
    (by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks]; decide)
    (by native_decide)
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
    (if (⟨416⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size
        ∨ (⟨416⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨416⟩ : UInt256).toNat 32))) =
      barkVatIlksRateWord outIlks := by
  unfold barkVatIlksRateWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 416 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (outIlks.extract 32 64))
    rw [barkVatIlksPostCallMem_read416_long hmem hlong hout hlongIlks houtIlks]
  · exact not_or.mpr
      ⟨by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks];
          decide,
        by native_decide⟩

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
    (if (⟨448⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size
        ∨ (⟨448⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨448⟩ : UInt256).toNat 32))) =
      barkVatIlksSpotWord outIlks := by
  unfold barkVatIlksSpotWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 448 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (outIlks.extract 64 96))
    rw [barkVatIlksPostCallMem_read448_long hmem hlong hout hlongIlks houtIlks]
  · exact not_or.mpr
      ⟨by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks];
          decide,
        by native_decide⟩

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
    (if (⟨512⟩ : UInt256).toNat ≥ (barkVatIlksPostCallMem σ I mem out outIlks).size
        ∨ (⟨512⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding
          (⟨512⟩ : UInt256).toNat 32))) =
      barkVatIlksDustWord outIlks := by
  unfold barkVatIlksDustWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian
        ((barkVatIlksPostCallMem σ I mem out outIlks).readWithPadding 512 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (outIlks.extract 128 160))
    rw [barkVatIlksPostCallMem_read512_long hmem hlong hout hlongIlks houtIlks]
  · exact not_or.mpr
      ⟨by rw [barkVatIlksPostCallMem_size_long hmem hlong hout hlongIlks houtIlks];
          decide,
        by native_decide⟩

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
    (if (⟨64⟩ : UInt256).toNat ≥ (barkVatGrabCallMem σ σMem I mem dink dart).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 19 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkVatGrabCallMem σ σMem I mem dink dart).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 19) (v := (⟨384⟩ : UInt256))
    (by rw [barkVatGrabCallMem_size hmem]; decide)
    (by native_decide)
    (by
      have hread := barkVatGrabCallMem_read64 (σ := σ) (σMem := σMem) (I := I)
        (mem := mem) (dink := dink) (dart := dart) hmem hread64
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread)

noncomputable abbrev barkPostIlksErrorStringMem0 (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord mem 384 solcErrorStringSelector

noncomputable abbrev barkPostIlksErrorStringMem1 (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkPostIlksErrorStringMem0 mem) 388 ⟨32⟩

noncomputable abbrev barkPostIlksErrorStringMem2 (len : UInt256) (mem : ByteArray) :
    ByteArray :=
  Reasoning.Theory.writeWord (barkPostIlksErrorStringMem1 mem) 420 len

noncomputable abbrev barkPostIlksErrorStringMem3
    (len word : UInt256) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (barkPostIlksErrorStringMem2 len mem) 452 word

theorem barkPostIlksErrorStringMem0_size {mem : ByteArray} (hmem : mem.size = 544) :
    (barkPostIlksErrorStringMem0 mem).size = 544 := by
  unfold barkPostIlksErrorStringMem0
  rw [Reasoning.Theory.writeWord_size mem 384 solcErrorStringSelector
    (by rw [hmem]; native_decide)]
  rw [hmem]
  norm_num

theorem barkPostIlksErrorStringMem1_size {mem : ByteArray} (hmem : mem.size = 544) :
    (barkPostIlksErrorStringMem1 mem).size = 544 := by
  unfold barkPostIlksErrorStringMem1
  rw [Reasoning.Theory.writeWord_size (barkPostIlksErrorStringMem0 mem) 388 ⟨32⟩
    (by rw [barkPostIlksErrorStringMem0_size hmem]; native_decide)]
  rw [barkPostIlksErrorStringMem0_size hmem]
  norm_num

theorem barkPostIlksErrorStringMem2_size (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544) :
    (barkPostIlksErrorStringMem2 len mem).size = 544 := by
  unfold barkPostIlksErrorStringMem2
  rw [Reasoning.Theory.writeWord_size (barkPostIlksErrorStringMem1 mem) 420 len
    (by rw [barkPostIlksErrorStringMem1_size hmem]; native_decide)]
  rw [barkPostIlksErrorStringMem1_size hmem]
  norm_num

theorem barkPostIlksErrorStringMem3_size (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544) :
    (barkPostIlksErrorStringMem3 len word mem).size = 544 := by
  unfold barkPostIlksErrorStringMem3
  rw [Reasoning.Theory.writeWord_size (barkPostIlksErrorStringMem2 len mem) 452 word
    (by rw [barkPostIlksErrorStringMem2_size len hmem]; native_decide)]
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
    (by rw [barkPostIlksErrorStringMem2_size len hmem]; native_decide)
    (by left; rw [barkPostIlksErrorStringMem2_size len hmem]; omega)]
  unfold barkPostIlksErrorStringMem2
  rw [Reasoning.Theory.writeWord_read_preserved
    (barkPostIlksErrorStringMem1 mem) 420 64 len
    (by rw [barkPostIlksErrorStringMem1_size hmem]; native_decide)
    (by left; rw [barkPostIlksErrorStringMem1_size hmem]; omega)]
  unfold barkPostIlksErrorStringMem1
  rw [Reasoning.Theory.writeWord_read_preserved
    (barkPostIlksErrorStringMem0 mem) 388 64 (⟨32⟩ : UInt256)
    (by rw [barkPostIlksErrorStringMem0_size hmem]; native_decide)
    (by left; rw [barkPostIlksErrorStringMem0_size hmem]; omega)]
  unfold barkPostIlksErrorStringMem0
  rw [Reasoning.Theory.writeWord_read_preserved mem 384 64 solcErrorStringSelector
    (by rw [hmem]; native_decide) (by left; rw [hmem]; omega)]
  exact hread64

theorem barkPostIlksErrorStringMem3_mload64 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (barkPostIlksErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((barkPostIlksErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨384⟩ := by
  exact mloadWordValue_of_readWithPadding
    (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 17) (v := (⟨384⟩ : UInt256))
    (by rw [barkPostIlksErrorStringMem3_size len word hmem]; decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using
        barkPostIlksErrorStringMem3_read64 len word hmem hread64)

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

theorem barkVatIlksEncodeWords {v : DogImmutables} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    (config v).externalABI.encode? "ilks" [.fixedBytes bytes32Width (barkIlkBytes I)] =
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

theorem barkVatIlksEncode_eq {v : DogImmutables} {σ : AccountMap} {I : ExecutionEnv}
    {mem out : ByteArray}
    (hsz100 : 100 ≤ I.calldata.size)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (config v).externalABI.encode? "ilks" [.fixedBytes bytes32Width (barkIlkBytes I)] =
      some ((barkVatIlksCallMem σ I mem out).readWithPadding 384 36) := by
  rw [barkVatIlksCallMem_read384_36 hmem hlong hout]
  exact barkVatIlksEncodeWords (v := v) (I := I) hsz100

theorem dogLiveGuardEval_false {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : dogSlotWord ⟨3⟩ σ I ≠ ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have her :
      evalStorageRef (config v) { contract := contract v, locals := locals }
        (initState cA gh bl σ σ₀ g A I) liveRef =
          .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
    simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  let w := Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨3⟩
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hlive (by simpa [w, dogSlotWord] using hw)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc ⟨3⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])]
  rw [dogStorageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals native_decide

theorem dogLiveGuardEval_true {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "live" = none)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩) :
    evalExpr? (config v) { contract := contract v, locals := locals }
      (initState cA gh bl σ σ₀ g A I)
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have her :
      evalStorageRef (config v) { contract := contract v, locals := locals }
        (initState cA gh bl σ σ₀ g A I) liveRef =
          .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
    simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  let w := Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨3⟩
  have hload : w = ⟨1⟩ := by
    simpa [w, dogSlotWord] using hlive
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc ⟨3⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])]
  rw [dogStorageLocLoad_uint256]
  have hload' :
      Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨3⟩ = ⟨1⟩ := by
    simpa [w] using hload
  simp only [initState] at hload' ⊢
  rw [hload']
  simp [evalExpr?, evalBinaryOp?]
  all_goals native_decide

theorem dogAddrLitEval_locals {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store} (a : EVM.Address) :
    evalExpr? (config v) { contract := contract v, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (addrLit a) =
      .ok (Value.address (AccountAddress.ofNat a.toNat)) := by
  dsimp [addrLit]
  have hint :
      evalExpr? (config v) { contract := contract v, locals := locals }
        (initState cA gh bl σ σ₀ g A I) (.intLit (↑↑a)) =
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
    {cA gh bl σ σ₀ A I} {g : Sat256} {locals : Store} :
    evalExpr? (config v) { contract := contract v, locals := locals }
      (initState cA gh bl σ σ₀ g A I) (vatExpr v) =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
  simpa [vatExpr] using
    (dogAddrLitEval_locals (v := v) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (locals := locals) v.vat)

theorem evalExpr_barkVatCodeGuard_true {v : DogImmutables}
    {evm : EVM.State} {locals : Store}
    (hreceiver :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (vatExpr v) =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)))
    (hcode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat]
  simpa using hcode

theorem evalExpr_barkVatCodeGuard_false {v : DogImmutables}
    {evm : EVM.State} {locals : Store}
    (hreceiver :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (vatExpr v) =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)))
    (hcode :
      (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat]
  simpa using hcode

theorem evalExprs_barkVatUrnsArgs {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I)))
    (hurn : locals.get? "urn" = some (.address (barkUrn I))) :
    evalExprs? (config v) { contract := contract v, locals := locals } evm
      [.var "ilk", .var "urn"] =
        .ok [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] := by
  simp only [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]
  rw [hilk, hurn]
  rfl

theorem evalExprs_barkVatIlksArgs {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I))) :
    evalExprs? (config v) { contract := contract v, locals := locals } evm
      [.var "ilk"] = .ok [.fixedBytes bytes32Width (barkIlkBytes I)] := by
  simp only [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]
  rw [hilk]
  rfl

theorem evalExpr_barkVatUrnInk {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {out : ByteArray}
    (hvatUrn : locals.get? "vatUrn" = some (barkVatUrnValue out)) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
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
    evalExpr? (config v) { contract := contract v, locals := locals } evm
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
    evalExpr? (config v) { contract := contract v, locals := locals } evm
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
    evalExpr? (config v) { contract := contract v, locals := locals } evm
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
    evalExpr? (config v) { contract := contract v, locals := locals } evm
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
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem evalExpr_bark_mul256_ok {v : DogImmutables} {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? (config v) { contract := contract v, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? (config v) { contract := contract v, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = a * b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (mul256 x y) =
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
    (hx : evalExpr? (config v) { contract := contract v, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? (config v) { contract := contract v, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (mul256 x y) =
      .revert := by
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem evalExpr_bark_sub256_ok {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {x y : Expr} {a b diff : UInt256}
    (hx : evalExpr? (config v) { contract := contract v, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? (config v) { contract := contract v, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hdiff : diff = UInt256.sub a b) (hle : b.toNat ≤ a.toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (sub256 x y) =
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

theorem evalExpr_bark_div_uint256_ok {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {x y : Expr} {a b q : UInt256}
    (hx : evalExpr? (config v) { contract := contract v, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? (config v) { contract := contract v, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b ≠ ⟨0⟩)
    (hq : q = UInt256.div a b) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.binary .div x y) =
      .ok (.int (Int.ofNat q.toNat)) := by
  have hbNat : ¬ b.toNat = 0 := by
    intro hzero
    exact hb (uint256_toNat_eq_zero hzero)
  have hqNat : q.toNat = a.toNat / b.toNat := by
    rw [hq, udiv_toNat]
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, hbNat, hqNat]

theorem evalExpr_bark_eq_int_true {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? (config v) { contract := contract v, locals := locals } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? (config v) { contract := contract v, locals := locals } evm rhs =
      .ok (.int b))
    (h : a = b) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq lhs rhs) = .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem evalExpr_bark_eq_int_false {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? (config v) { contract := contract v, locals := locals } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? (config v) { contract := contract v, locals := locals } evm rhs =
      .ok (.int b))
    (h : a ≠ b) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_lt_int_true {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? (config v) { contract := contract v, locals := locals } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? (config v) { contract := contract v, locals := locals } evm rhs =
      .ok (.int b))
    (h : a < b) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .lt lhs rhs) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_lt_int_false {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? (config v) { contract := contract v, locals := locals } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? (config v) { contract := contract v, locals := locals } evm rhs =
      .ok (.int b))
    (h : ¬ a < b) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .lt lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_gt_int_true {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? (config v) { contract := contract v, locals := locals } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? (config v) { contract := contract v, locals := locals } evm rhs =
      .ok (.int b))
    (h : a > b) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt lhs rhs) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_gt_int_false {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? (config v) { contract := contract v, locals := locals } evm lhs =
      .ok (.int a))
    (hrhs : evalExpr? (config v) { contract := contract v, locals := locals } evm rhs =
      .ok (.int b))
    (h : ¬ a > b) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .gt lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_bark_or_true_left {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr}
    (hlhs : evalExpr? (config v) { contract := contract v, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .or lhs rhs) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem evalExpr_bark_or_false_right {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? (config v) { contract := contract v, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? (config v) { contract := contract v, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .or lhs rhs) = .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem evalExpr_bark_and_false_left {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr}
    (hlhs : evalExpr? (config v) { contract := contract v, locals := locals } evm lhs =
      .ok (.bool false)) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .and lhs rhs) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem evalExpr_bark_and_true_right {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? (config v) { contract := contract v, locals := locals } evm lhs =
      .ok (.bool true))
    (hrhs : evalExpr? (config v) { contract := contract v, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .and lhs rhs) = .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem execBarkMinFunctionReturn {v : DogImmutables} (evm : EVM.State)
    (x y : UInt256) :
    ExecFuncBody (config v) { contract := contract v, locals := barkBinaryLocals x y } evm
      minFunction.body
      (.returned { contract := contract v, locals := barkBinaryLocals x y } evm
        (some [.int (Int.ofNat ((if x.toNat ≤ y.toNat then x else y).toNat))])) := by
  let locals := barkBinaryLocals x y
  have hx :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
        (name := "x") (value := x) (barkBinaryLocals_get_x x y)
  have hy :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals)
        (name := "y") (value := y) (barkBinaryLocals_get_y x y)
  by_cases hle : x.toNat ≤ y.toNat
  · have hcond :
        evalExpr? (config v) { contract := contract v, locals := locals } evm
          (.binary .le (.var "x") (.var "y")) = .ok (.bool true) := by
      simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]
      exact_mod_cast hle
    have hret :
        evalExprs? (config v) { contract := contract v, locals := locals } evm
          [.var "x"] = .ok [.int (Int.ofNat x.toNat)] := by
      simp [evalExprs?, hx, EvalResult.bind, bind, pure]
    have hthen :
        ExecBlock (config v) { contract := contract v, locals := locals } evm
          [.return [.var "x"]]
          (.returned { contract := contract v, locals := locals } evm
            (some [.int (Int.ofNat x.toNat)])) :=
      ExecBlock.consReturn (ExecStmt.return hret)
    have hblock :
        ExecBlock (config v) { contract := contract v, locals := locals } evm
          minFunction.body
          (.returned { contract := contract v, locals := locals } evm
            (some [.int (Int.ofNat x.toNat)])) := by
      simpa [minFunction] using ExecBlock.consReturn (ExecStmt.iteTrue hcond hthen)
    simpa [ExecFuncBody, locals, hle] using ExecFuncBody.execBlockRet hblock
  · have hcond :
        evalExpr? (config v) { contract := contract v, locals := locals } evm
          (.binary .le (.var "x") (.var "y")) = .ok (.bool false) := by
      simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]
      exact_mod_cast (Nat.lt_of_not_ge hle)
    have hret :
        evalExprs? (config v) { contract := contract v, locals := locals } evm
          [.var "y"] = .ok [.int (Int.ofNat y.toNat)] := by
      simp [evalExprs?, hy, EvalResult.bind, bind, pure]
    have helse :
        ExecBlock (config v) { contract := contract v, locals := locals } evm
          [.return [.var "y"]]
          (.returned { contract := contract v, locals := locals } evm
            (some [.int (Int.ofNat y.toNat)])) :=
      ExecBlock.consReturn (ExecStmt.return hret)
    have hblock :
        ExecBlock (config v) { contract := contract v, locals := locals } evm
          minFunction.body
          (.returned { contract := contract v, locals := locals } evm
            (some [.int (Int.ofNat y.toNat)])) := by
      simpa [minFunction] using ExecBlock.consReturn (ExecStmt.iteFalse hcond helse)
    simpa [ExecFuncBody, locals, hle] using ExecFuncBody.execBlockRet hblock

theorem dog_u256_mul_div_overflow_ne (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (y * x) y ≠ x := by
  intro hEq
  have hyNatNe : y.toNat ≠ 0 := by
    intro hy0
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hy0]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hnat := congrArg UInt256.toNat hEq
  rw [udiv_toNat, u256_mul_op_toNat] at hnat
  have hremLt : y.toNat * x.toNat % UInt256.size < y.toNat * x.toNat := by
    have hmodLt : y.toNat * x.toNat % UInt256.size < UInt256.size :=
      Nat.mod_lt _ (by norm_num [UInt256.size])
    have hover' : UInt256.size ≤ y.toNat * x.toNat := by
      simpa [Nat.mul_comm] using hover
    omega
  have hle0 :=
    Nat.mul_div_le (y.toNat * x.toNat % UInt256.size) y.toNat
  rw [hnat] at hle0
  have hle : y.toNat * x.toNat ≤ y.toNat * x.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega

theorem evalExpr_barkVat_state {v : DogImmutables} {evm : EVM.State} {locals : Store} :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (vatExpr v) =
      .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
  dsimp [vatExpr, addrLit]
  have hint :
      evalExpr? (config v) { contract := contract v, locals := locals } evm
        (.intLit (↑↑v.vat)) = .ok (.int (↑↑v.vat)) := by
    simp [evalExpr?, pure]
  unfold evalExpr?
  rw [hint]
  change (if (↑↑v.vat : Int) < 0 then EvalResult.error EvalError.typeError
      else EvalResult.ok
        (Value.address (AccountAddress.ofNat (Int.toNat (↑↑v.vat : Int))))) =
    EvalResult.ok (Value.address (AccountAddress.ofNat ↑v.vat))
  rw [if_neg (by omega)]
  simp

theorem evalExpr_barkStorageMilkClip {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage (ilksF (.var "ilk") "clip")) =
        .ok (.address (AccountAddress.ofNat
          (dogAddressReturnWord (barkIlksClipSlotFor I) evm.accountMap
            evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := { contract := contract v, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "clip") (er := barkIlksClipEvaledRef I)
    (t := .address) (loc := addrLoc (barkIlksClipSlotFor I))
    (value := .address (AccountAddress.ofNat
      (dogAddressReturnWord (barkIlksClipSlotFor I) evm.accountMap
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
    (by simpa [dogAddressReturnWord, dogSlotWord] using
      dogStorageLocLoad_address_offset0 evm (barkIlksClipSlotFor I))

theorem evalExpr_barkStorageMilkChop {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage (ilksF (.var "ilk") "chop")) =
        .ok (.int (Int.ofNat
          (dogSlotWord (barkIlksChopSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := { contract := contract v, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "chop") (er := barkIlksChopEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (barkIlksChopSlotFor I))
    (value := .int (Int.ofNat
      (dogSlotWord (barkIlksChopSlotFor I) evm.accountMap evm.executionEnv).toNat))
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
    (by simpa [dogSlotWord] using dogStorageLocLoad_uint256 evm (barkIlksChopSlotFor I))

theorem evalExpr_barkStorageMilkHole {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage (ilksF (.var "ilk") "hole")) =
        .ok (.int (Int.ofNat
          (dogSlotWord (barkIlksHoleSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := { contract := contract v, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "hole") (er := barkIlksHoleEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (barkIlksHoleSlotFor I))
    (value := .int (Int.ofNat
      (dogSlotWord (barkIlksHoleSlotFor I) evm.accountMap evm.executionEnv).toNat))
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
    (by simpa [dogSlotWord] using dogStorageLocLoad_uint256 evm (barkIlksHoleSlotFor I))

theorem evalExpr_barkStorageMilkDirt {v : DogImmutables} {evm : EVM.State}
    {locals : Store} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (barkIlkBytes I))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage (ilksF (.var "ilk") "dirt")) =
        .ok (.int (Int.ofNat
          (dogSlotWord (barkIlksDirtSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := { contract := contract v, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "dirt") (er := barkIlksDirtEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (barkIlksDirtSlotFor I))
    (value := .int (Int.ofNat
      (dogSlotWord (barkIlksDirtSlotFor I) evm.accountMap evm.executionEnv).toNat))
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
    (by simpa [dogSlotWord] using dogStorageLocLoad_uint256 evm (barkIlksDirtSlotFor I))

theorem evalExpr_barkStorageHole {v : DogImmutables} {evm : EVM.State}
    {locals : Store}
    (hHole : locals.get? "Hole" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage HoleRef) =
        .ok (.int (Int.ofNat (dogSlotWord ⟨4⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := { contract := contract v, locals := locals }) (evm := evm)
    (slot := HoleRef) (er := ({ base := "Hole", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨4⟩)
    (value := .int (Int.ofNat (dogSlotWord ⟨4⟩ evm.accountMap evm.executionEnv).toNat))
    hHole
    (by simp [evalStorageRef, evalStorageRefSteps, HoleRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [dogSlotWord] using dogStorageLocLoad_uint256 evm ⟨4⟩)

theorem evalExpr_barkStorageDirt {v : DogImmutables} {evm : EVM.State}
    {locals : Store}
    (hDirt : locals.get? "Dirt" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.storage DirtRef) =
        .ok (.int (Int.ofNat (dogSlotWord ⟨5⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config v) (solm := { contract := contract v, locals := locals }) (evm := evm)
    (slot := DirtRef) (er := ({ base := "Dirt", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨5⟩)
    (value := .int (Int.ofNat (dogSlotWord ⟨5⟩ evm.accountMap evm.executionEnv).toNat))
    hDirt
    (by simp [evalStorageRef, evalStorageRefSteps, DirtRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [dogSlotWord] using dogStorageLocLoad_uint256 evm ⟨5⟩)

theorem barkVat_eq_vatKey (v : DogImmutables) :
    AccountAddress.ofNat v.vat.toNat = AccountAddress.ofUInt256 (barkVatWord v) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  have hword : (barkVatWord v).toNat = v.vat.toNat := by
    change (UInt256.ofNat v.vat.toNat).toNat = v.vat.toNat
    rw [UInt256.toNat_ofNat_of_lt]
    exact lt_of_lt_of_le v.vat.isLt (show AccountAddress.size ≤ UInt256.size from by decide)
  rw [hword]

theorem barkVatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {v : DogImmutables}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) = ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (barkVatWord v) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts (barkVatWord v)
  rw [← hsame]
  exact hzero

theorem barkVatCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {v : DogImmutables}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩) :
    Reasoning.Theory.uniswapExtCodeSizeWord τ (barkVatWord v) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts (barkVatWord v)
  rw [hsame]
  exact hzero

theorem barkVatCode_zero_of_codeSize_zero {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  rw [barkVat_eq_vatKey v]
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 (barkVatWord v)) with
  | none =>
      simpa [initState, State.lookupAccount, hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [initState, State.lookupAccount, hacc] using hword

theorem barkVatCode_pos_of_codeSize_ne {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat := by
  rw [barkVat_eq_vatKey v]
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 (barkVatWord v)) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [initState, State.lookupAccount, hacc] using Nat.pos_of_ne_zero htoNatNe

theorem barkVatCode_zero_of_state_codeSize_zero {v : DogImmutables} {evm : EVM.State}
    (hzero :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap (barkVatWord v) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  rw [barkVat_eq_vatKey v]
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hzero
  cases hacc : evm.accountMap.find? (AccountAddress.ofUInt256 (barkVatWord v)) with
  | none =>
      simpa [State.lookupAccount, hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [State.lookupAccount, hacc] using hword

theorem barkVatCode_pos_of_state_codeSize_ne {v : DogImmutables} {evm : EVM.State}
    (hne :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap (barkVatWord v) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((evm.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
        (fun acc => acc.code.size))).toNat := by
  rw [barkVat_eq_vatKey v]
  unfold Reasoning.Theory.uniswapExtCodeSizeWord at hne
  cases hacc : evm.accountMap.find? (AccountAddress.ofUInt256 (barkVatWord v)) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [State.lookupAccount, hacc] using Nat.pos_of_ne_zero htoNatNe

private theorem dogAccountMapExtensionalEq_of_accountMapEquiv {σ τ : AccountMap}
    (hστ : accountMapEquiv σ τ) : accountMapExtensionalEq σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

private theorem dogAccountMapEquiv_of_accountMapExtensionalEq {σ τ : AccountMap}
    (hστ : accountMapExtensionalEq σ τ) : accountMapEquiv σ τ := by
  intro addr
  specialize hστ addr
  cases hσ : σ.find? addr <;> cases hτ : τ.find? addr <;>
    simp [hσ, hτ] at hστ ⊢
  exact ⟨hστ.1, hστ.2.1, hστ.2.2.1, hστ.2.2.2.1, hστ.2.2.2.2⟩

theorem dogTypedCallViaEVM_accountMapEquiv_noSubstate {cfg : Config}
    {evm_evm evm_solm evm'_evm : EVM.State}
    {tgt : EVM.Address} {name : Ident} {value : ℤ} {args : List Value} {z : Bool}
    {out : ByteArray} {callPerm : Bool}
    (hcall : typedCallViaEVM cfg evm_evm tgt name value args (z, evm'_evm, out) callPerm)
    (hAccounts : accountMapEquiv evm_evm.accountMap evm_solm.accountMap)
    (hOriginalAccounts : evm_evm.σ₀ = evm_solm.σ₀)
    (hCreated : evm_solm.createdAccounts = evm_evm.createdAccounts)
    (hGenesis : evm_solm.genesisBlockHeader = evm_evm.genesisBlockHeader)
    (hBlocks : evm_solm.blocks = evm_evm.blocks)
    (hEnv : evm_solm.executionEnv = evm_evm.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM cfg evm_solm tgt name value args
        (z,
          { evm_solm with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := evm'_evm.createdAccounts },
          out) callPerm ∧
      accountMapEquiv evm'_evm.accountMap σ'_solm := by
  obtain ⟨calldata, hdecode, hcall⟩ := hcall
  have h_ext_eq : accountMapExtensionalEq evm_evm.accountMap evm_solm.accountMap :=
    dogAccountMapExtensionalEq_of_accountMapEquiv hAccounts
  cases hcall with
  | callMade hvalue hTheta hevm' hvalue' hdepth =>
      obtain ⟨callGas, A_in, hTheta⟩ := hTheta
      rename_i valueWord cA' σ' g' A'
      generalize htheta_solm :
        Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes evm_solm.createdAccounts
          evm_solm.genesisBlockHeader evm_solm.blocks evm_solm.accountMap evm_solm.σ₀ A_in
          evm_solm.executionEnv.codeOwner evm_solm.executionEnv.sender tgt
          (toExecute evm_solm.accountMap tgt) callGas
          (UInt256.ofNat evm_solm.executionEnv.gasPrice) valueWord valueWord calldata
          (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header
          callPerm = thetaRes
      have hcode_equiv :
          toExecute evm_evm.accountMap tgt = toExecute evm_solm.accountMap tgt :=
        accountMapExtensionalEq_toExecute h_ext_eq tgt
      have htheta_solm' :
          Ethereum.EVM.Θ evm_evm.executionEnv.blobVersionedHashes evm_evm.createdAccounts
            evm_evm.genesisBlockHeader evm_evm.blocks evm_solm.accountMap evm_evm.σ₀ A_in
            evm_evm.executionEnv.codeOwner evm_evm.executionEnv.sender tgt
            (toExecute evm_evm.accountMap tgt) callGas
            (UInt256.ofNat evm_evm.executionEnv.gasPrice) valueWord valueWord calldata
            (evm_evm.executionEnv.depth + 1) evm_evm.executionEnv.header
            callPerm =
            (thetaRes.1, thetaRes.2.1, thetaRes.2.2.1, thetaRes.2.2.2.1,
              thetaRes.2.2.2.2.1, thetaRes.2.2.2.2.2) := by
        rw [← htheta_solm]
        rw [hCreated, ← hOriginalAccounts, hGenesis, hBlocks, hEnv, hcode_equiv]
      let a1 : AccountAddress := ⟨0, by simp [AccountAddress.size]⟩
      have hTheta_rel :=
        (accountMap_extensionality_of_Theta_and_Lambda
        (blobVersionedHashes := evm_evm.executionEnv.blobVersionedHashes)
        (createdAccounts := evm_evm.createdAccounts)
        (genesisBlockHeader := evm_evm.genesisBlockHeader)
        (blocks := evm_evm.blocks)
        (σ₁ := evm_evm.accountMap)
        (σ₂ := evm_solm.accountMap)
        (σ₀ := evm_evm.σ₀)
        (A := A_in)
        (s := evm_evm.executionEnv.codeOwner)
        (o := evm_evm.executionEnv.sender)
        (r := tgt)
        (g := callGas)
        (p := UInt256.ofNat evm_evm.executionEnv.gasPrice)
        (v := valueWord)
        (v' := valueWord)
        (d := calldata)
        (i := ByteArray.empty)
        (ζ := none)
        (H := evm_evm.executionEnv.header)
        (w := callPerm)
        a1 a1
        (toExecute evm_evm.accountMap tgt)
        cA' thetaRes.1
        σ' thetaRes.2.1
        g' thetaRes.2.2.1
        A' thetaRes.2.2.2.1
        z thetaRes.2.2.2.2.1
        out thetaRes.2.2.2.2.2
        (evm_evm.executionEnv.depth + 1)
        h_ext_eq).1 hTheta.symm htheta_solm'
      have hCreated' : evm'_evm.createdAccounts = thetaRes.1 := by
        simp [hevm', hTheta_rel.1]
      have hTheta_s :
          (evm'_evm.createdAccounts, thetaRes.2.1, thetaRes.2.2.1,
              thetaRes.2.2.2.1, z, out) =
            Ethereum.EVM.Θ evm_solm.executionEnv.blobVersionedHashes
              evm_solm.createdAccounts evm_solm.genesisBlockHeader evm_solm.blocks
              evm_solm.accountMap evm_solm.σ₀ A_in evm_solm.executionEnv.codeOwner
              evm_solm.executionEnv.sender tgt (toExecute evm_solm.accountMap tgt) callGas
              (UInt256.ofNat evm_solm.executionEnv.gasPrice) valueWord valueWord calldata
              (evm_solm.executionEnv.depth + 1) evm_solm.executionEnv.header
              callPerm := by
        rw [hTheta_rel.2.2.2.1, hTheta_rel.2.2.2.2.1]
        rw [hCreated']
        exact htheta_solm.symm
      use thetaRes.2.1
      use thetaRes.2.2.2.1
      constructor
      · refine ⟨calldata, hdecode, ?_⟩
        exact callViaEVM.callMade (perm := callPerm) hvalue
          ⟨callGas, A_in, hTheta_s⟩ rfl
          (by
            rw [hEnv]
            rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
            exact hvalue')
          (by
            rw [hEnv]
            exact hdepth)
      · have hσext : accountMapExtensionalEq σ' thetaRes.2.1 := hTheta_rel.2.2.2.2.2
        simpa [hevm'] using dogAccountMapEquiv_of_accountMapExtensionalEq hσext
  | callNotMade _hsubstate hevm' hvalue =>
      let A' := (State.addAccessedAccount evm_solm tgt).substate
      use evm_solm.accountMap
      use A'
      constructor
      · refine ⟨calldata, hdecode, ?_⟩
        apply callViaEVM.callNotMade (perm := callPerm)
        · rfl
        · simp [A', hCreated, hevm']
        · rw [hEnv]
          rw [← accountMapExtensionalEq_balanceOf h_ext_eq evm_evm.executionEnv.codeOwner]
          exact hvalue
      · simpa [hevm'] using hAccounts

theorem dogBarkVatUrnsNoCodeSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodeZero :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hliveGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, locals] using
      dogLiveGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I) (barkLocals_get_live I) hlive
  have hvat :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (vatExpr v) =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
    simpa [evm0, locals] using
      (evalExpr_barkVat (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I))
  have hcodeGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_barkVatCodeGuard_false (v := v) (locals := locals) hvat
      (by simpa [evm0] using hcodeZero)
  have hcallvalue :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 3) .reverted := by
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hcallvalue) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) <|
          ExecBlock.consRevert (ExecStmt.requireFalse hcodeGuard) :
        ExecBlock (config v) { contract := contract v, locals := locals } evm0
          [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) ]
          .reverted)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
    have hfull :
        ExecBlock (config v) { contract := contract v, locals := locals } evm0
          ((barkTransition v).body.take 3 ++ (barkTransition v).body.drop 3)
          .reverted :=
      execBlock_append_term (s2 := (barkTransition v).body.drop 3) hprefix
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatUrnsCallFailureSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (false, evmCall, out) false) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hliveGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, locals] using
      dogLiveGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I) (barkLocals_get_live I) hlive
  have hvat :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (vatExpr v) =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
    simpa [evm0, locals] using
      (evalExpr_barkVat (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I))
  have hcodeGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_barkVatCodeGuard_true (v := v) (locals := locals) hvat
      (by simpa [evm0] using hcodePos)
  have hargs :
      evalExprs? (config v) { contract := contract v, locals := locals } evm0
        [.var "ilk", .var "urn"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] :=
    evalExprs_barkVatUrnsArgs (v := v) (evm := evm0) (I := I)
      (locals := locals)
      (by simpa [locals] using barkLocals_get_ilk I)
      (by simpa [locals] using barkLocals_get_urn I)
  have hcall' :
      typedCallViaEVM (config v) evm0 (EVM.address (AccountAddress.ofNat v.vat.toNat))
        "urns" 0 [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (false, evmCall, out) false := by
    simpa [evm0] using hcall
  have hcallStmt :
      ExecStmt (config v) { contract := contract v, locals := locals } evm0
        (.externalCall (vatExpr v) "urns" (.intLit 0) [.var "ilk", .var "urn"]
          "vatUrn" (perm := false))
        .reverted :=
    ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargs hcall'
  have hcallvalue :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 4) .reverted := by
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hcallvalue) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) <|
          ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
            ExecBlock.consRevert hcallStmt :
        ExecBlock (config v) { contract := contract v, locals := locals } evm0
          [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)),
            .externalCall (vatExpr v) "urns" (.intLit 0) [.var "ilk", .var "urn"]
              "vatUrn" (perm := false) ]
          .reverted)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
    have hfull :
        ExecBlock (config v) { contract := contract v, locals := locals } evm0
          ((barkTransition v).body.take 4 ++ (barkTransition v).body.drop 4)
          .reverted :=
      execBlock_append_term (s2 := (barkTransition v).body.drop 4) hprefix
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatUrnsDecodeRevertSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmCall, out) false)
    (hdec : (config v).externalABI.decode? "urns" out = none) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hliveGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, locals] using
      dogLiveGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I) (barkLocals_get_live I) hlive
  have hvat :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (vatExpr v) =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
    simpa [evm0, locals] using
      (evalExpr_barkVat (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I))
  have hcodeGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_barkVatCodeGuard_true (v := v) (locals := locals) hvat
      (by simpa [evm0] using hcodePos)
  have hargs :
      evalExprs? (config v) { contract := contract v, locals := locals } evm0
        [.var "ilk", .var "urn"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] :=
    evalExprs_barkVatUrnsArgs (v := v) (evm := evm0) (I := I)
      (locals := locals)
      (by simpa [locals] using barkLocals_get_ilk I)
      (by simpa [locals] using barkLocals_get_urn I)
  have hcall' :
      typedCallViaEVM (config v) evm0 (EVM.address (AccountAddress.ofNat v.vat.toNat))
        "urns" 0 [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmCall, out) false := by
    simpa [evm0] using hcall
  have hcallStmt :
      ExecStmt (config v) { contract := contract v, locals := locals } evm0
        (.externalCall (vatExpr v) "urns" (.intLit 0) [.var "ilk", .var "urn"]
          "vatUrn" (perm := false))
        .reverted :=
    ExecStmt.externalCallReturnDecodeRevert hvat (by simp [evalExpr?, pure]) hargs
      hcall' hdec
  have hcallvalue :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 4) .reverted := by
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using
      (ExecBlock.consNormal (ExecStmt.requireTrue hcallvalue) <|
        ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) <|
          ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
            ExecBlock.consRevert hcallStmt :
        ExecBlock (config v) { contract := contract v, locals := locals } evm0
          [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
            .require (.binary .eq (.storage liveRef) (.intLit 1)),
            .require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)),
            .externalCall (vatExpr v) "urns" (.intLit 0) [.var "ilk", .var "urn"]
              "vatUrn" (perm := false) ]
          .reverted)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
    have hfull :
        ExecBlock (config v) { contract := contract v, locals := locals } evm0
          ((barkTransition v).body.take 4 ++ (barkTransition v).body.drop 4)
          .reverted :=
      execBlock_append_term (s2 := (barkTransition v).body.drop 4) hprefix
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatUrnsSuccessIlksPrefix {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmCall : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcall :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmCall, out) false)
    (hdec : (config v).externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock (config v) { contract := contract v, locals := locals } evm0
      ((barkTransition v).body.take 10)
      (.ok { contract := contract v, locals := barkLocalsMilkDirt evmCall I out }
        evmCall) := by
  intro locals evm0
  have hliveGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, locals] using
      dogLiveGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I) (barkLocals_get_live I) hlive
  have hvat :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (vatExpr v) =
        .ok (.address (AccountAddress.ofNat v.vat.toNat)) := by
    simpa [evm0, locals] using
      (evalExpr_barkVat (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := barkLocals I))
  have hcodeGuard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_barkVatCodeGuard_true (v := v) (locals := locals) hvat
      (by simpa [evm0] using hcodePos)
  have hargs :
      evalExprs? (config v) { contract := contract v, locals := locals } evm0
        [.var "ilk", .var "urn"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)] :=
    evalExprs_barkVatUrnsArgs (v := v) (evm := evm0) (I := I)
      (locals := locals)
      (by simpa [locals] using barkLocals_get_ilk I)
      (by simpa [locals] using barkLocals_get_urn I)
  have hcall' :
      typedCallViaEVM (config v) evm0 (EVM.address (AccountAddress.ofNat v.vat.toNat))
        "urns" 0 [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmCall, out) false := by
    simpa [evm0] using hcall
  have hcallStmt :
      ExecStmt (config v) { contract := contract v, locals := locals } evm0
        (.externalCall (vatExpr v) "urns" (.intLit 0) [.var "ilk", .var "urn"]
          "vatUrn" (perm := false))
        (.ok { contract := contract v, locals := barkLocalsVatUrn I out } evmCall) := by
    have heth :
        evalExpr? (config v) { contract := contract v, locals := locals } evm0
          (.intLit 0) = .ok (.int 0) := by
      simp [evalExpr?, pure]
    simpa [locals, barkLocalsVatUrn, barkVatUrnValue, collapseReturns] using
      (ExecStmt.externalCallSuccess (retVar := "vatUrn") hvat heth hargs hcall' hdec)
  have hinkExpr :
      evalExpr? (config v) { contract := contract v, locals := barkLocalsVatUrn I out }
        evmCall (.tupleGet (.var "vatUrn") 0) =
          .ok (.int (Int.ofNat (barkVatUrnsInkWord out).toNat)) :=
    evalExpr_barkVatUrnInk (v := v) (evm := evmCall)
      (locals := barkLocalsVatUrn I out) (out := out)
      (barkLocalsVatUrn_get_vatUrn I out)
  have hinkStmt :
      ExecStmt (config v) { contract := contract v, locals := barkLocalsVatUrn I out }
        evmCall (.letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0))
        (.ok { contract := contract v, locals := barkLocalsInk I out } evmCall) := by
    simpa [barkLocalsInk] using (ExecStmt.letDecl (cfg := config v) hinkExpr)
  have hartExpr :
      evalExpr? (config v) { contract := contract v, locals := barkLocalsInk I out }
        evmCall (.tupleGet (.var "vatUrn") 1) =
          .ok (.int (Int.ofNat (barkVatUrnsArtWord out).toNat)) :=
    evalExpr_barkVatUrnArt (v := v) (evm := evmCall)
      (locals := barkLocalsInk I out) (out := out)
      (barkLocalsInk_get_vatUrn I out)
  have hartStmt :
      ExecStmt (config v) { contract := contract v, locals := barkLocalsInk I out }
        evmCall (.letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1))
        (.ok { contract := contract v, locals := barkLocalsArt I out } evmCall) := by
    simpa [barkLocalsArt] using (ExecStmt.letDecl (cfg := config v) hartExpr)
  have hclipExpr :
      evalExpr? (config v) { contract := contract v, locals := barkLocalsArt I out }
        evmCall (.storage (ilksF (.var "ilk") "clip")) =
          .ok (.address (AccountAddress.ofNat
            (dogAddressReturnWord (barkIlksClipSlotFor I) evmCall.accountMap
              evmCall.executionEnv).toNat)) :=
    evalExpr_barkStorageMilkClip (v := v) (evm := evmCall)
      (locals := barkLocalsArt I out) (I := I) hsz100
      (barkLocalsArt_get_ilks I out) (barkLocalsArt_get_ilk I out)
  have hclipStmt :
      ExecStmt (config v) { contract := contract v, locals := barkLocalsArt I out }
        evmCall (.letDecl "milkClip" (some addr) (.storage (ilksF (.var "ilk") "clip")))
        (.ok { contract := contract v, locals := barkLocalsMilkClip evmCall I out }
          evmCall) := by
    simpa [barkLocalsMilkClip] using (ExecStmt.letDecl (cfg := config v) hclipExpr)
  have hchopExpr :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkClip evmCall I out } evmCall
        (.storage (ilksF (.var "ilk") "chop")) =
          .ok (.int (Int.ofNat
            (dogSlotWord (barkIlksChopSlotFor I) evmCall.accountMap
              evmCall.executionEnv).toNat)) :=
    evalExpr_barkStorageMilkChop (v := v) (evm := evmCall)
      (locals := barkLocalsMilkClip evmCall I out) (I := I) hsz100
      (barkLocalsMilkClip_get_ilks evmCall I out)
      (barkLocalsMilkClip_get_ilk evmCall I out)
  have hchopStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsMilkClip evmCall I out } evmCall
        (.letDecl "milkChop" (some uint256) (.storage (ilksF (.var "ilk") "chop")))
        (.ok { contract := contract v, locals := barkLocalsMilkChop evmCall I out }
          evmCall) := by
    simpa [barkLocalsMilkChop] using (ExecStmt.letDecl (cfg := config v) hchopExpr)
  have hholeExpr :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkChop evmCall I out } evmCall
        (.storage (ilksF (.var "ilk") "hole")) =
          .ok (.int (Int.ofNat
            (dogSlotWord (barkIlksHoleSlotFor I) evmCall.accountMap
              evmCall.executionEnv).toNat)) :=
    evalExpr_barkStorageMilkHole (v := v) (evm := evmCall)
      (locals := barkLocalsMilkChop evmCall I out) (I := I) hsz100
      (barkLocalsMilkChop_get_ilks evmCall I out)
      (barkLocalsMilkChop_get_ilk evmCall I out)
  have hholeStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsMilkChop evmCall I out } evmCall
        (.letDecl "milkHole" (some uint256) (.storage (ilksF (.var "ilk") "hole")))
        (.ok { contract := contract v, locals := barkLocalsMilkHole evmCall I out }
          evmCall) := by
    simpa [barkLocalsMilkHole] using (ExecStmt.letDecl (cfg := config v) hholeExpr)
  have hdirtExpr :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkHole evmCall I out } evmCall
        (.storage (ilksF (.var "ilk") "dirt")) =
          .ok (.int (Int.ofNat
            (dogSlotWord (barkIlksDirtSlotFor I) evmCall.accountMap
              evmCall.executionEnv).toNat)) :=
    evalExpr_barkStorageMilkDirt (v := v) (evm := evmCall)
      (locals := barkLocalsMilkHole evmCall I out) (I := I) hsz100
      (barkLocalsMilkHole_get_ilks evmCall I out)
      (barkLocalsMilkHole_get_ilk evmCall I out)
  have hdirtStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsMilkHole evmCall I out } evmCall
        (.letDecl "milkDirt" (some uint256) (.storage (ilksF (.var "ilk") "dirt")))
        (.ok { contract := contract v, locals := barkLocalsMilkDirt evmCall I out }
          evmCall) := by
    simpa [barkLocalsMilkDirt] using (ExecStmt.letDecl (cfg := config v) hdirtExpr)
  have hcallvalue :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
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
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)),
          .externalCall (vatExpr v) "urns" (.intLit 0) [.var "ilk", .var "urn"]
            "vatUrn" (perm := false),
          .letDecl "ink" (some uint256) (.tupleGet (.var "vatUrn") 0),
          .letDecl "art" (some uint256) (.tupleGet (.var "vatUrn") 1),
          .letDecl "milkClip" (some addr) (.storage (ilksF (.var "ilk") "clip")),
          .letDecl "milkChop" (some uint256) (.storage (ilksF (.var "ilk") "chop")),
          .letDecl "milkHole" (some uint256) (.storage (ilksF (.var "ilk") "hole")),
          .letDecl "milkDirt" (some uint256) (.storage (ilksF (.var "ilk") "dirt")) ]
        (.ok { contract := contract v, locals := barkLocalsMilkDirt evmCall I out }
          evmCall))

theorem dogBarkVatIlksNoCodeSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmUrns : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : (config v).externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodeZero :
      (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 10)
        (.ok { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
          evmUrns) := by
    simpa [locals, evm0] using
      dogBarkVatUrnsSuccessIlksPrefix (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCall := evmUrns) (out := out) hwv hlive hcodePos hcallUrns hdecUrns hsz100
  have hvat :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (vatExpr v) =
          .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evmUrns)
      (locals := barkLocalsMilkDirt evmUrns I out)
  have hcodeGuard :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_barkVatCodeGuard_false (v := v)
      (locals := barkLocalsMilkDirt evmUrns I out) hvat hcodeZero
  have hsecond :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out } evmUrns
        [ .require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) ] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse hcodeGuard)
  have hprefixRevert :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 11) .reverted := by
    have hcombined := execBlock_append hprefix hsecond
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using hcombined
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
    have hfull :
        ExecBlock (config v) { contract := contract v, locals := locals } evm0
          ((barkTransition v).body.take 11 ++ (barkTransition v).body.drop 11)
          .reverted :=
      execBlock_append_term (s2 := (barkTransition v).body.drop 11) hprefixRevert
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksCallFailureSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : (config v).externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (false, evmIlks, outIlks) false)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 10)
        (.ok { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
          evmUrns) := by
    simpa [locals, evm0] using
      dogBarkVatUrnsSuccessIlksPrefix (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCall := evmUrns) (out := out) hwv hlive hcodePos hcallUrns hdecUrns hsz100
  have hvat :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (vatExpr v) =
          .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evmUrns)
      (locals := barkLocalsMilkDirt evmUrns I out)
  have hcodeGuard :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_barkVatCodeGuard_true (v := v)
      (locals := barkLocalsMilkDirt evmUrns I out) hvat hcodePosIlks
  have hargs :
      evalExprs? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns [.var "ilk"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I)] :=
    evalExprs_barkVatIlksArgs (v := v) (evm := evmUrns) (I := I)
      (locals := barkLocalsMilkDirt evmUrns I out)
      (barkLocalsMilkDirt_get_ilk evmUrns I out)
  have heth :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hcallStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out } evmUrns
        (.externalCall (vatExpr v) "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
          (perm := false))
        .reverted :=
    ExecStmt.externalCallFailure hvat heth hargs hcallIlks
  have hsecond :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out } evmUrns
        [ .require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)),
          .externalCall (vatExpr v) "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
            (perm := false) ] .reverted :=
    ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
      ExecBlock.consRevert hcallStmt
  have hprefixRevert :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 12) .reverted := by
    have hcombined := execBlock_append hprefix hsecond
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using hcombined
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
    have hfull :
        ExecBlock (config v) { contract := contract v, locals := locals } evm0
          ((barkTransition v).body.take 12 ++ (barkTransition v).body.drop 12)
          .reverted :=
      execBlock_append_term (s2 := (barkTransition v).body.drop 12) hprefixRevert
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksDecodeRevertSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : (config v).externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : (config v).externalABI.decode? "ilks" outIlks = none)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 10)
        (.ok { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
          evmUrns) := by
    simpa [locals, evm0] using
      dogBarkVatUrnsSuccessIlksPrefix (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCall := evmUrns) (out := out) hwv hlive hcodePos hcallUrns hdecUrns hsz100
  have hvat :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (vatExpr v) =
          .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evmUrns)
      (locals := barkLocalsMilkDirt evmUrns I out)
  have hcodeGuard :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_barkVatCodeGuard_true (v := v)
      (locals := barkLocalsMilkDirt evmUrns I out) hvat hcodePosIlks
  have hargs :
      evalExprs? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns [.var "ilk"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I)] :=
    evalExprs_barkVatIlksArgs (v := v) (evm := evmUrns) (I := I)
      (locals := barkLocalsMilkDirt evmUrns I out)
      (barkLocalsMilkDirt_get_ilk evmUrns I out)
  have heth :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hcallStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out } evmUrns
        (.externalCall (vatExpr v) "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
          (perm := false))
        .reverted :=
    ExecStmt.externalCallReturnDecodeRevert hvat heth hargs hcallIlks hdecIlks
  have hsecond :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out } evmUrns
        [ .require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)),
          .externalCall (vatExpr v) "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
            (perm := false) ] .reverted :=
    ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
      ExecBlock.consRevert hcallStmt
  have hprefixRevert :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 12) .reverted := by
    have hcombined := execBlock_append hprefix hsecond
    simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using hcombined
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
    have hfull :
        ExecBlock (config v) { contract := contract v, locals := locals } evm0
          ((barkTransition v).body.take 12 ++ (barkTransition v).body.drop 12)
          .reverted :=
      execBlock_append_term (s2 := (barkTransition v).body.drop 12) hprefixRevert
        (by intro f e h; cases h)
    simpa [List.take_append_drop] using hfull
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksSuccessDustPrefix {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : (config v).externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : (config v).externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecBlock (config v) { contract := contract v, locals := locals } evm0
      ((barkTransition v).body.take 15)
      (.ok { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks) := by
  intro locals evm0
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 10)
        (.ok { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
          evmUrns) := by
    simpa [locals, evm0] using
      dogBarkVatUrnsSuccessIlksPrefix (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCall := evmUrns) (out := out) hwv hlive hcodePos hcallUrns hdecUrns hsz100
  have hvat :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (vatExpr v) =
          .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evmUrns)
      (locals := barkLocalsMilkDirt evmUrns I out)
  have hcodeGuard :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_barkVatCodeGuard_true (v := v)
      (locals := barkLocalsMilkDirt evmUrns I out) hvat hcodePosIlks
  have hargs :
      evalExprs? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns [.var "ilk"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I)] :=
    evalExprs_barkVatIlksArgs (v := v) (evm := evmUrns) (I := I)
      (locals := barkLocalsMilkDirt evmUrns I out)
      (barkLocalsMilkDirt_get_ilk evmUrns I out)
  have heth :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hcallStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out } evmUrns
        (.externalCall (vatExpr v) "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
          (perm := false))
        (.ok { contract := contract v, locals := barkLocalsVatIlk evmUrns I out outIlks }
          evmIlks) := by
    simpa [barkLocalsVatIlk, barkVatIlkValue, collapseReturns] using
      (ExecStmt.externalCallSuccess (retVar := "vatIlk") hvat heth hargs hcallIlks hdecIlks)
  have hrateExpr :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsVatIlk evmUrns I out outIlks }
        evmIlks (.tupleGet (.var "vatIlk") 1) =
          .ok (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) :=
    evalExpr_barkVatIlkRate (v := v) (evm := evmIlks)
      (locals := barkLocalsVatIlk evmUrns I out outIlks) (out := outIlks)
      (barkLocalsVatIlk_get_vatIlk evmUrns I out outIlks)
  have hrateStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsVatIlk evmUrns I out outIlks }
        evmIlks (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract v, locals := barkLocalsRate evmUrns I out outIlks }
          evmIlks) := by
    simpa [barkLocalsRate] using (ExecStmt.letDecl (cfg := config v) hrateExpr)
  have hspotExpr :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsRate evmUrns I out outIlks }
        evmIlks (.tupleGet (.var "vatIlk") 2) =
          .ok (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat)) :=
    evalExpr_barkVatIlkSpot (v := v) (evm := evmIlks)
      (locals := barkLocalsRate evmUrns I out outIlks) (out := outIlks)
      (barkLocalsRate_get_vatIlk evmUrns I out outIlks)
  have hspotStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsRate evmUrns I out outIlks }
        evmIlks (.letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2))
        (.ok { contract := contract v, locals := barkLocalsSpot evmUrns I out outIlks }
          evmIlks) := by
    simpa [barkLocalsSpot] using (ExecStmt.letDecl (cfg := config v) hspotExpr)
  have hdustExpr :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsSpot evmUrns I out outIlks }
        evmIlks (.tupleGet (.var "vatIlk") 4) =
          .ok (.int (Int.ofNat (barkVatIlksDustWord outIlks).toNat)) :=
    evalExpr_barkVatIlkDust (v := v) (evm := evmIlks)
      (locals := barkLocalsSpot evmUrns I out outIlks) (out := outIlks)
      (barkLocalsSpot_get_vatIlk evmUrns I out outIlks)
  have hdustStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsSpot evmUrns I out outIlks }
        evmIlks (.letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4))
        (.ok { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
          evmIlks) := by
    simpa [barkLocalsDust] using (ExecStmt.letDecl (cfg := config v) hdustExpr)
  have hsecond :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out } evmUrns
        [ .require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)),
          .externalCall (vatExpr v) "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
            (perm := false),
          .letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1),
          .letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2),
          .letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4) ]
        (.ok { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
          evmIlks) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hcodeGuard) <|
      ExecBlock.consNormal hcallStmt <|
        ExecBlock.consNormal hrateStmt <|
          ExecBlock.consNormal hspotStmt <|
            ExecBlock.consNormal hdustStmt ExecBlock.nil
  have hcombined := execBlock_append hprefix hsecond
  simpa [barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts] using hcombined

theorem dogBarkVatIlksInkSpotOverflowSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : (config v).externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : (config v).externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hfitOverflow :
      UInt256.size ≤ (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 10)
        (.ok { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
          evmUrns) := by
    simpa [locals, evm0] using
      dogBarkVatUrnsSuccessIlksPrefix (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmCall := evmUrns) (out := out) hwv hlive hcodePos hcallUrns hdecUrns hsz100
  have hvat :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (vatExpr v) =
          .ok (.address (AccountAddress.ofNat v.vat.toNat)) :=
    evalExpr_barkVat_state (v := v) (evm := evmUrns)
      (locals := barkLocalsMilkDirt evmUrns I out)
  have hcodeGuard :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_barkVatCodeGuard_true (v := v)
      (locals := barkLocalsMilkDirt evmUrns I out) hvat hcodePosIlks
  have hargs :
      evalExprs? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns [.var "ilk"] =
          .ok [.fixedBytes bytes32Width (barkIlkBytes I)] :=
    evalExprs_barkVatIlksArgs (v := v) (evm := evmUrns) (I := I)
      (locals := barkLocalsMilkDirt evmUrns I out)
      (barkLocalsMilkDirt_get_ilk evmUrns I out)
  have heth :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out }
        evmUrns (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hcallStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out } evmUrns
        (.externalCall (vatExpr v) "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
          (perm := false))
        (.ok { contract := contract v, locals := barkLocalsVatIlk evmUrns I out outIlks }
          evmIlks) := by
    simpa [barkLocalsVatIlk, barkVatIlkValue, collapseReturns] using
      (ExecStmt.externalCallSuccess (retVar := "vatIlk") hvat heth hargs hcallIlks hdecIlks)
  have hrateExpr :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsVatIlk evmUrns I out outIlks }
        evmIlks (.tupleGet (.var "vatIlk") 1) =
          .ok (.int (Int.ofNat (barkVatIlksRateWord outIlks).toNat)) :=
    evalExpr_barkVatIlkRate (v := v) (evm := evmIlks)
      (locals := barkLocalsVatIlk evmUrns I out outIlks) (out := outIlks)
      (barkLocalsVatIlk_get_vatIlk evmUrns I out outIlks)
  have hrateStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsVatIlk evmUrns I out outIlks }
        evmIlks (.letDecl "rate" (some uint256) (.tupleGet (.var "vatIlk") 1))
        (.ok { contract := contract v, locals := barkLocalsRate evmUrns I out outIlks }
          evmIlks) := by
    simpa [barkLocalsRate] using (ExecStmt.letDecl (cfg := config v) hrateExpr)
  have hspotExpr :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsRate evmUrns I out outIlks }
        evmIlks (.tupleGet (.var "vatIlk") 2) =
          .ok (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat)) :=
    evalExpr_barkVatIlkSpot (v := v) (evm := evmIlks)
      (locals := barkLocalsRate evmUrns I out outIlks) (out := outIlks)
      (barkLocalsRate_get_vatIlk evmUrns I out outIlks)
  have hspotStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsRate evmUrns I out outIlks }
        evmIlks (.letDecl "spot" (some uint256) (.tupleGet (.var "vatIlk") 2))
        (.ok { contract := contract v, locals := barkLocalsSpot evmUrns I out outIlks }
          evmIlks) := by
    simpa [barkLocalsSpot] using (ExecStmt.letDecl (cfg := config v) hspotExpr)
  have hdustExpr :
      evalExpr? (config v)
        { contract := contract v, locals := barkLocalsSpot evmUrns I out outIlks }
        evmIlks (.tupleGet (.var "vatIlk") 4) =
          .ok (.int (Int.ofNat (barkVatIlksDustWord outIlks).toNat)) :=
    evalExpr_barkVatIlkDust (v := v) (evm := evmIlks)
      (locals := barkLocalsSpot evmUrns I out outIlks) (out := outIlks)
      (barkLocalsSpot_get_vatIlk evmUrns I out outIlks)
  have hdustStmt :
      ExecStmt (config v)
        { contract := contract v, locals := barkLocalsSpot evmUrns I out outIlks }
        evmIlks (.letDecl "dust" (some uint256) (.tupleGet (.var "vatIlk") 4))
        (.ok { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
          evmIlks) := by
    simpa [barkLocalsDust] using (ExecStmt.letDecl (cfg := config v) hdustExpr)
  let localsDust := barkLocalsDust evmUrns I out outIlks
  have hink :
      evalExpr? (config v) { contract := contract v, locals := localsDust } evmIlks
        (.var "ink") =
          .ok (.int (Int.ofNat (barkVatUrnsInkWord out).toNat)) := by
    simpa [localsDust] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDust)
        (name := "ink") (value := barkVatUrnsInkWord out)
        (barkLocalsDust_get_ink evmUrns I out outIlks)
  have hspot :
      evalExpr? (config v) { contract := contract v, locals := localsDust } evmIlks
        (.var "spot") =
          .ok (.int (Int.ofNat (barkVatIlksSpotWord outIlks).toNat)) := by
    simpa [localsDust] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := localsDust)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsDust_get_spot evmUrns I out outIlks)
  have hmul :
      evalExpr? (config v) { contract := contract v, locals := localsDust } evmIlks
        (mul256 (.var "ink") (.var "spot")) = .revert :=
    evalExpr_bark_mul256_revert hink hspot hfitOverflow
  have hsecond :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsMilkDirt evmUrns I out } evmUrns
        ([ .require (.binary .gt (.extCodeSize (vatExpr v)) (.intLit 0)),
          .externalCall (vatExpr v) "ilks" (.intLit 0) [.var "ilk"] "vatIlk"
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
          checkedExternalCallStmts (vatExpr v) "grab" (.intLit 0)
            [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
              .unary .neg (asInt256 (.var "dink")),
              .unary .neg (asInt256 (.var "dart")) ] "_grabRet" ++
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
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
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
    ExecBlock (config v)
      { contract := contract v, locals := barkLocalsDust localsEvm I out outIlks } evm
      (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
      (.ok { contract := contract v, locals := barkLocalsInkSpot localsEvm I out outIlks }
        evm) := by
  let locals0 := barkLocalsDust localsEvm I out outIlks
  let locals1 := barkLocalsInkSpot localsEvm I out outIlks
  let ink := barkVatUrnsInkWord out
  let spot := barkVatIlksSpotWord outIlks
  let inkSpot := barkInkSpotWord out outIlks
  have hink0 :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evm (.var "ink") =
        .ok (.int (Int.ofNat ink.toNat)) := by
    simpa [locals0, ink] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "ink") (value := barkVatUrnsInkWord out)
        (barkLocalsDust_get_ink localsEvm I out outIlks)
  have hspot0 :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evm (.var "spot") =
        .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals0, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsDust_get_spot localsEvm I out outIlks)
  have hmul :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evm
        (mul256 (.var "ink") (.var "spot")) =
          .ok (.int (Int.ofNat inkSpot.toNat)) := by
    exact evalExpr_bark_mul256_ok hink0 hspot0 (by simp [inkSpot, ink, spot, barkInkSpotWord])
      (by simpa [ink, spot] using hfit)
  have hlet :
      ExecStmt (config v) { contract := contract v, locals := locals0 } evm
        (.letDecl "inkSpot" (some uint256) (mul256 (.var "ink") (.var "spot")))
        (.ok { contract := contract v, locals := locals1 } evm) := by
    simpa [locals0, locals1, inkSpot, barkLocalsInkSpot] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := { contract := contract v, locals := locals0 })
        (evm := evm) (name := "inkSpot") (ty := some uint256)
        (expr := mul256 (.var "ink") (.var "spot"))
        (value := .int (Int.ofNat inkSpot.toNat)) hmul)
  have hspot1 :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evm (.var "spot") =
        .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals1, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsInkSpot_get_spot localsEvm I out outIlks)
  have hink1 :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evm (.var "ink") =
        .ok (.int (Int.ofNat ink.toNat)) := by
    simpa [locals1, ink] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "ink") (value := barkVatUrnsInkWord out)
        (barkLocalsInkSpot_get_ink localsEvm I out outIlks)
  have hinkSpot1 :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evm
        (.var "inkSpot") =
          .ok (.int (Int.ofNat inkSpot.toNat)) := by
    simpa [locals1, inkSpot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "inkSpot") (value := barkInkSpotWord out outIlks)
        (barkLocalsInkSpot_get_inkSpot localsEvm I out outIlks)
  have hzero :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evm
        (.binary .or
          (.binary .eq (.var "spot") (.intLit 0))
          (.binary .eq (.binary .div (.var "inkSpot") (.var "spot")) (.var "ink"))) =
        .ok (.bool true) := by
    by_cases hspotZero : spot = ⟨0⟩
    · have heqZero :
          evalExpr? (config v) { contract := contract v, locals := locals1 } evm
            (.binary .eq (.var "spot") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_bark_eq_int_true hspot1 hzero
        simp [hspotZero]
      exact evalExpr_bark_or_true_left heqZero
    · have hspotNatNe : spot.toNat ≠ 0 := by
        intro hnat
        exact hspotZero (uint256_toNat_eq_zero hnat)
      have heqZero :
          evalExpr? (config v) { contract := contract v, locals := locals1 } evm
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
          evalExpr? (config v) { contract := contract v, locals := locals1 } evm
            (.binary .div (.var "inkSpot") (.var "spot")) =
              .ok (.int (Int.ofNat ink.toNat)) := by
        have h := evalExpr_bark_div_uint256_ok (v := v) (evm := evm) (locals := locals1)
          (x := .var "inkSpot") (y := .var "spot")
          (a := inkSpot) (b := spot) (q := UInt256.div inkSpot spot)
          hinkSpot1 hspot1 hspotZero rfl
        simpa [hdivWord] using h
      have hright :
          evalExpr? (config v) { contract := contract v, locals := locals1 } evm
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
    ExecBlock (config v)
      { contract := contract v, locals := barkLocalsInkSpot localsEvm I out outIlks } evm
      (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) .reverted := by
  let locals0 := barkLocalsInkSpot localsEvm I out outIlks
  let art := barkVatUrnsArtWord out
  let rate := barkVatIlksRateWord outIlks
  have hart :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evm (.var "art") =
        .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "art") (value := barkVatUrnsArtWord out)
        (barkLocalsInkSpot_get_art localsEvm I out outIlks)
  have hrate :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evm (.var "rate") =
        .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [locals0, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "rate") (value := barkVatIlksRateWord outIlks)
        (barkLocalsInkSpot_get_rate localsEvm I out outIlks)
  have hmul :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evm
        (mul256 (.var "art") (.var "rate")) = .revert :=
    evalExpr_bark_mul256_revert hart hrate (by simpa [art, rate] using hover)
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmul)

theorem dogBarkArtRateUnsafeCheckedMulOk {v : DogImmutables}
    (evm localsEvm : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hfit :
      (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat <
        UInt256.size) :
    ExecBlock (config v)
      { contract := contract v, locals := barkLocalsInkSpot localsEvm I out outIlks } evm
      (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
      (.ok { contract := contract v, locals := barkLocalsArtRateUnsafe localsEvm I out outIlks }
        evm) := by
  let locals0 := barkLocalsInkSpot localsEvm I out outIlks
  let locals1 := barkLocalsArtRateUnsafe localsEvm I out outIlks
  let art := barkVatUrnsArtWord out
  let rate := barkVatIlksRateWord outIlks
  let artRate := barkArtRateUnsafeWord out outIlks
  have hart0 :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evm (.var "art") =
        .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals0, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "art") (value := barkVatUrnsArtWord out)
        (barkLocalsInkSpot_get_art localsEvm I out outIlks)
  have hrate0 :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evm (.var "rate") =
        .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [locals0, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals0)
        (name := "rate") (value := barkVatIlksRateWord outIlks)
        (barkLocalsInkSpot_get_rate localsEvm I out outIlks)
  have hmul :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evm
        (mul256 (.var "art") (.var "rate")) =
          .ok (.int (Int.ofNat artRate.toNat)) := by
    exact evalExpr_bark_mul256_ok hart0 hrate0
      (by simp [artRate, art, rate, barkArtRateUnsafeWord])
      (by simpa [art, rate] using hfit)
  have hlet :
      ExecStmt (config v) { contract := contract v, locals := locals0 } evm
        (.letDecl "artRateUnsafe" (some uint256) (mul256 (.var "art") (.var "rate")))
        (.ok { contract := contract v, locals := locals1 } evm) := by
    simpa [locals0, locals1, artRate, barkLocalsArtRateUnsafe] using
      (ExecStmt.letDecl
        (cfg := config v) (solm := { contract := contract v, locals := locals0 })
        (evm := evm) (name := "artRateUnsafe") (ty := some uint256)
        (expr := mul256 (.var "art") (.var "rate"))
        (value := .int (Int.ofNat artRate.toNat)) hmul)
  have hrate1 :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evm (.var "rate") =
        .ok (.int (Int.ofNat rate.toNat)) := by
    simpa [locals1, rate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "rate") (value := barkVatIlksRateWord outIlks)
        (barkLocalsArtRateUnsafe_get_rate localsEvm I out outIlks)
  have hart1 :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evm (.var "art") =
        .ok (.int (Int.ofNat art.toNat)) := by
    simpa [locals1, art] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "art") (value := barkVatUrnsArtWord out)
        (barkLocalsArtRateUnsafe_get_art localsEvm I out outIlks)
  have hartRate1 :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evm
        (.var "artRateUnsafe") =
          .ok (.int (Int.ofNat artRate.toNat)) := by
    simpa [locals1, artRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evm) (locals := locals1)
        (name := "artRateUnsafe") (value := barkArtRateUnsafeWord out outIlks)
        (barkLocalsArtRateUnsafe_get_artRateUnsafe localsEvm I out outIlks)
  have hzero :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evm (.intLit 0) =
        .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hreq :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evm
        (.binary .or
          (.binary .eq (.var "rate") (.intLit 0))
          (.binary .eq (.binary .div (.var "artRateUnsafe") (.var "rate")) (.var "art"))) =
        .ok (.bool true) := by
    by_cases hrateZero : rate = ⟨0⟩
    · have heqZero :
          evalExpr? (config v) { contract := contract v, locals := locals1 } evm
            (.binary .eq (.var "rate") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_bark_eq_int_true hrate1 hzero
        simp [hrateZero]
      exact evalExpr_bark_or_true_left heqZero
    · have hrateNatNe : rate.toNat ≠ 0 := by
        intro hnat
        exact hrateZero (uint256_toNat_eq_zero hnat)
      have heqZero :
          evalExpr? (config v) { contract := contract v, locals := locals1 } evm
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
          evalExpr? (config v) { contract := contract v, locals := locals1 } evm
            (.binary .div (.var "artRateUnsafe") (.var "rate")) =
              .ok (.int (Int.ofNat art.toNat)) := by
        have h := evalExpr_bark_div_uint256_ok (v := v) (evm := evm) (locals := locals1)
          (x := .var "artRateUnsafe") (y := .var "rate")
          (a := artRate) (b := rate) (q := UInt256.div artRate rate)
          hartRate1 hrate1 hrateZero rfl
        simpa [hdivWord] using h
      have hright :
          evalExpr? (config v) { contract := contract v, locals := locals1 } evm
            (.binary .eq (.binary .div (.var "artRateUnsafe") (.var "rate")) (.var "art")) =
              .ok (.bool true) :=
        evalExpr_bark_eq_int_true hdiv hart1 rfl
      exact evalExpr_bark_or_false_right heqZero hright
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consNormal hlet (ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkVatIlksArtRateOverflowSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : (config v).externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : (config v).externalABI.decode? "ilks" outIlks =
      some (barkVatIlksReturnValues outIlks))
    (hfitInk :
      (barkVatUrnsInkWord out).toNat * (barkVatIlksSpotWord outIlks).toNat <
        UInt256.size)
    (hoverArt :
      UInt256.size ≤ (barkVatUrnsArtWord out).toNat * (barkVatIlksRateWord outIlks).toNat)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 15)
        (.ok { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
          evmIlks) := by
    simpa [locals, evm0] using
      dogBarkVatIlksSuccessDustPrefix (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmUrns := evmUrns) (evmIlks := evmIlks) (out := out)
        (outIlks := outIlks) hwv hlive hcodePos hcallUrns hdecUrns hcodePosIlks
        hcallIlks hdecIlks hsz100
  have hInkBlock :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
        (.ok { contract := contract v, locals := barkLocalsInkSpot evmUrns I out outIlks }
          evmIlks) :=
    dogBarkInkSpotCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitInk
  have hArtRevert :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsInkSpot evmUrns I out outIlks }
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
    checkedExternalCallStmts (vatExpr v) "grab" (.intLit 0)
      [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
        .unary .neg (asInt256 (.var "dink")),
        .unary .neg (asInt256 (.var "dart")) ] "_grabRet" ++
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
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        .reverted :=
    execBlock_append hInkBlock hArtRevert
  have htail :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        ((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++ rest)
        .reverted :=
    execBlock_append_term (s2 := rest) htailPrefix (by intro f e h; cases h)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
    have hcombined := execBlock_append hprefix htail
    simpa [rest, barkTransition, barkBodyRest, nonpayable, checkedExternalCallStmts,
      checkedMulUintInto, List.append_assoc] using hcombined
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksNotUnsafeSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : (config v).externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : (config v).externalABI.decode? "ilks" outIlks =
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
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 15)
        (.ok { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
          evmIlks) := by
    simpa [locals, evm0] using
      dogBarkVatIlksSuccessDustPrefix (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmUrns := evmUrns) (evmIlks := evmIlks) (out := out)
        (outIlks := outIlks) hwv hlive hcodePos hcallUrns hdecUrns hcodePosIlks
        hcallIlks hdecIlks hsz100
  have hInkBlock :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
        (.ok { contract := contract v, locals := barkLocalsInkSpot evmUrns I out outIlks }
          evmIlks) :=
    dogBarkInkSpotCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitInk
  have hArtBlock :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsInkSpot evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract v, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks }
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
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "spot") = .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals2, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsArtRateUnsafe_get_spot evmUrns I out outIlks)
  have hzero :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hinkSpot :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "inkSpot") = .ok (.int (Int.ofNat inkSpot.toNat)) := by
    simpa [locals2, inkSpot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "inkSpot") (value := barkInkSpotWord out outIlks)
        (barkLocalsArtRateUnsafe_get_inkSpot evmUrns I out outIlks)
  have hartRate :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "artRateUnsafe") = .ok (.int (Int.ofNat artRate.toNat)) := by
    simpa [locals2, artRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "artRateUnsafe") (value := barkArtRateUnsafeWord out outIlks)
        (barkLocalsArtRateUnsafe_get_artRateUnsafe evmUrns I out outIlks)
  have hreq :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        unsafeGuard = .ok (.bool false) := by
    by_cases hspotPos : 0 < spot.toNat
    · have hgt :
          evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
            (.binary .gt (.var "spot") (.intLit 0)) = .ok (.bool true) := by
        apply evalExpr_bark_gt_int_true hspot hzero
        show (0 : Int) < Int.ofNat spot.toNat
        exact Int.ofNat_lt.mpr hspotPos
      have hnotLt : ¬ inkSpot.toNat < artRate.toNat := by
        intro hlt
        exact hnotSafe ⟨by simpa [spot] using hspotPos, by simpa [inkSpot, artRate] using hlt⟩
      have hltFalse :
          evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
            (.binary .lt (.var "inkSpot") (.var "artRateUnsafe")) = .ok (.bool false) := by
        apply evalExpr_bark_lt_int_false hinkSpot hartRate
        intro hlt
        exact hnotLt (Int.ofNat_lt.mp hlt)
      simpa [unsafeGuard] using evalExpr_bark_and_true_right hgt hltFalse
    · have hgt :
          evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
            (.binary .gt (.var "spot") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_bark_gt_int_false hspot hzero
        intro hgt
        exact hspotPos (Int.ofNat_lt.mp hgt)
      simpa [unsafeGuard] using evalExpr_bark_and_false_left hgt
  have hchecked :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract v, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks }
          evmIlks) :=
    execBlock_append hInkBlock hArtBlock
  have hreqBlock :
      ExecBlock (config v) { contract := contract v, locals := locals2 } evmIlks
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
    checkedExternalCallStmts (vatExpr v) "grab" (.intLit 0)
      [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
        .unary .neg (asInt256 (.var "dink")),
        .unary .neg (asInt256 (.var "dart")) ] "_grabRet" ++
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
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        ((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard])
        .reverted :=
    execBlock_append hchecked (by simpa [locals2] using hreqBlock)
  have htail :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard]) ++ rest)
        .reverted :=
    execBlock_append_term (s2 := rest) hcheckedReq (by intro f e h; cases h)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
    have hcombined := execBlock_append hprefix htail
    simpa [unsafeGuard, rest, barkTransition, barkBodyRest, nonpayable,
      checkedExternalCallStmts, checkedMulUintInto, List.append_assoc] using hcombined
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkVatIlksLiquidationLimitHitSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : (config v).externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : (config v).externalABI.decode? "ilks" outIlks =
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
      ¬ ((dogSlotWord ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv).toNat <
          (dogSlotWord ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv).toNat ∧
        (dogSlotWord (barkIlksDirtSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat <
          (dogSlotWord (barkIlksHoleSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat))
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 15)
        (.ok { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
          evmIlks) := by
    simpa [locals, evm0] using
      dogBarkVatIlksSuccessDustPrefix (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmUrns := evmUrns) (evmIlks := evmIlks) (out := out)
        (outIlks := outIlks) hwv hlive hcodePos hcallUrns hdecUrns hcodePosIlks
        hcallIlks hdecIlks hsz100
  have hInkBlock :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
        (.ok { contract := contract v, locals := barkLocalsInkSpot evmUrns I out outIlks }
          evmIlks) :=
    dogBarkInkSpotCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitInk
  have hArtBlock :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsInkSpot evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract v, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks }
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
  let hole := dogSlotWord ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv
  let dirt := dogSlotWord ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv
  let milkHole :=
    dogSlotWord (barkIlksHoleSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  let milkDirt :=
    dogSlotWord (barkIlksDirtSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  have hspot :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "spot") = .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals2, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsArtRateUnsafe_get_spot evmUrns I out outIlks)
  have hzero :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hinkSpot :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "inkSpot") = .ok (.int (Int.ofNat inkSpot.toNat)) := by
    simpa [locals2, inkSpot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "inkSpot") (value := barkInkSpotWord out outIlks)
        (barkLocalsArtRateUnsafe_get_inkSpot evmUrns I out outIlks)
  have hartRate :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "artRateUnsafe") = .ok (.int (Int.ofNat artRate.toNat)) := by
    simpa [locals2, artRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "artRateUnsafe") (value := barkArtRateUnsafeWord out outIlks)
        (barkLocalsArtRateUnsafe_get_artRateUnsafe evmUrns I out outIlks)
  have hunsafeReq :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        unsafeGuard = .ok (.bool true) := by
    have hgt :
        evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
          (.binary .gt (.var "spot") (.intLit 0)) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hspot hzero
      show (0 : Int) < Int.ofNat spot.toNat
      exact Int.ofNat_lt.mpr (by simpa [spot] using hspotPos)
    have hlt :
        evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
          (.binary .lt (.var "inkSpot") (.var "artRateUnsafe")) = .ok (.bool true) := by
      apply evalExpr_bark_lt_int_true hinkSpot hartRate
      exact Int.ofNat_lt.mpr (by simpa [inkSpot, artRate] using hsafeLt)
    simpa [unsafeGuard] using evalExpr_bark_and_true_right hgt hlt
  have hHoleExpr :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.storage HoleRef) = .ok (.int (Int.ofNat hole.toNat)) := by
    simpa [locals2, hole] using
      evalExpr_barkStorageHole (v := v) (evm := evmIlks) (locals := locals2)
        (barkLocalsArtRateUnsafe_get_Hole evmUrns I out outIlks)
  have hDirtExpr :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt.toNat)) := by
    simpa [locals2, dirt] using
      evalExpr_barkStorageDirt (v := v) (evm := evmIlks) (locals := locals2)
        (barkLocalsArtRateUnsafe_get_Dirt evmUrns I out outIlks)
  have hmilkHoleExpr :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "milkHole") = .ok (.int (Int.ofNat milkHole.toNat)) := by
    simpa [locals2, milkHole] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "milkHole")
        (value := dogSlotWord (barkIlksHoleSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv)
        (barkLocalsArtRateUnsafe_get_milkHole evmUrns I out outIlks)
  have hmilkDirtExpr :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "milkDirt") = .ok (.int (Int.ofNat milkDirt.toNat)) := by
    simpa [locals2, milkDirt] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "milkDirt")
        (value := dogSlotWord (barkIlksDirtSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv)
        (barkLocalsArtRateUnsafe_get_milkDirt evmUrns I out outIlks)
  have hlimitReq :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        limitGuard = .ok (.bool false) := by
    by_cases hglobal : dirt.toNat < hole.toNat
    · have hgtGlobal :
          evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
            (.binary .gt (.storage HoleRef) (.storage DirtRef)) = .ok (.bool true) := by
        apply evalExpr_bark_gt_int_true hHoleExpr hDirtExpr
        exact Int.ofNat_lt.mpr hglobal
      have hmilkNot : ¬ milkDirt.toNat < milkHole.toNat := by
        intro hmilk
        exact hlimitFalse ⟨by simpa [dirt, hole] using hglobal,
          by simpa [milkDirt, milkHole] using hmilk⟩
      have hgtMilk :
          evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
            (.binary .gt (.var "milkHole") (.var "milkDirt")) = .ok (.bool false) := by
        apply evalExpr_bark_gt_int_false hmilkHoleExpr hmilkDirtExpr
        intro hbad
        exact hmilkNot (Int.ofNat_lt.mp hbad)
      simpa [limitGuard] using evalExpr_bark_and_true_right hgtGlobal hgtMilk
    · have hgtGlobal :
          evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
            (.binary .gt (.storage HoleRef) (.storage DirtRef)) = .ok (.bool false) := by
        apply evalExpr_bark_gt_int_false hHoleExpr hDirtExpr
        intro hbad
        exact hglobal (Int.ofNat_lt.mp hbad)
      simpa [limitGuard] using evalExpr_bark_and_false_left hgtGlobal
  have hchecked :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract v, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks }
          evmIlks) :=
    execBlock_append hInkBlock hArtBlock
  have hunsafeBlock :
      ExecBlock (config v) { contract := contract v, locals := locals2 } evmIlks
        [.require unsafeGuard]
        (.ok { contract := contract v, locals := locals2 } evmIlks) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hunsafeReq) ExecBlock.nil
  have hlimitBlock :
      ExecBlock (config v) { contract := contract v, locals := locals2 } evmIlks
        [.require limitGuard] .reverted :=
    ExecBlock.consRevert (ExecStmt.requireFalse hlimitReq)
  have hcheckedUnsafe :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        ((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard])
        (.ok { contract := contract v, locals := locals2 } evmIlks) :=
    execBlock_append hchecked (by simpa [locals2] using hunsafeBlock)
  have hcheckedUnsafeLimit :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
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
    checkedExternalCallStmts (vatExpr v) "grab" (.intLit 0)
      [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
        .unary .neg (asInt256 (.var "dink")),
        .unary .neg (asInt256 (.var "dart")) ] "_grabRet" ++
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
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        ((((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard]) ++ [.require limitGuard]) ++ afterLimit)
        .reverted :=
    execBlock_append_term (s2 := afterLimit) hcheckedUnsafeLimit (by intro f e h; cases h)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
    have hcombined := execBlock_append hprefix htail
    simpa [unsafeGuard, limitGuard, afterLimit, barkTransition, barkBodyRest, nonpayable,
      checkedExternalCallStmts, checkedMulUintInto, List.append_assoc] using hcombined
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem dogBarkGlobalRoomCheckedSubOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hglobal :
      (dogSlotWord ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv).toNat <
        (dogSlotWord ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv).toNat) :
    ExecBlock (config v)
      { contract := contract v, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks }
      evmIlks (checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef))
      (.ok { contract := contract v, locals := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks }
        evmIlks) := by
  let locals0 := barkLocalsArtRateUnsafe evmUrns I out outIlks
  let locals1 := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks
  let hole := dogSlotWord ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv
  let dirt := dogSlotWord ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv
  let globalRoom := barkSourceGlobalRoomWord evmIlks
  have hdirtLe : dirt.toNat ≤ hole.toNat := by
    simpa [hole, dirt] using le_of_lt hglobal
  have hHole0 :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (.storage HoleRef) = .ok (.int (Int.ofNat hole.toNat)) := by
    simpa [locals0, hole] using
      evalExpr_barkStorageHole (v := v) (evm := evmIlks) (locals := locals0)
        (barkLocalsArtRateUnsafe_get_Hole evmUrns I out outIlks)
  have hDirt0 :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt.toNat)) := by
    simpa [locals0, dirt] using
      evalExpr_barkStorageDirt (v := v) (evm := evmIlks) (locals := locals0)
        (barkLocalsArtRateUnsafe_get_Dirt evmUrns I out outIlks)
  have hsub :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (sub256 (.storage HoleRef) (.storage DirtRef)) =
          .ok (.int (Int.ofNat globalRoom.toNat)) := by
    exact evalExpr_bark_sub256_ok hHole0 hDirt0
      (by simp [globalRoom, barkSourceGlobalRoomWord, hole, dirt]) hdirtLe
  have hlet :
      ExecStmt (config v) { contract := contract v, locals := locals0 } evmIlks
        (.letDecl "globalRoom" (some uint256) (sub256 (.storage HoleRef) (.storage DirtRef)))
        (.ok { contract := contract v, locals := locals1 } evmIlks) := by
    simpa [locals0, locals1, globalRoom, barkLocalsGlobalRoom] using
      (ExecStmt.letDecl (cfg := config v)
        (solm := { contract := contract v, locals := locals0 }) (evm := evmIlks)
        (name := "globalRoom") (ty := some uint256)
        (expr := sub256 (.storage HoleRef) (.storage DirtRef))
        (value := .int (Int.ofNat globalRoom.toNat)) hsub)
  have hglobalExpr :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evmIlks
        (.var "globalRoom") = .ok (.int (Int.ofNat globalRoom.toNat)) := by
    simpa [locals1, globalRoom] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals1)
        (name := "globalRoom") (value := globalRoom)
        (barkLocalsGlobalRoom_get_globalRoom evmUrns evmIlks I out outIlks)
  have hHole1 :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evmIlks
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
      evalExpr? (config v) { contract := contract v, locals := locals1 } evmIlks
        (.binary .le (.var "globalRoom") (.storage HoleRef)) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hglobalExpr, hHole1, evalBinaryOp?]
    exact_mod_cast hglobalLe
  simpa [checkedSubUintInto, locals0, locals1] using
    (ExecBlock.consNormal hlet <|
      ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkIlkRoomCheckedSubOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hmilk :
      (dogSlotWord (barkIlksDirtSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat <
        (dogSlotWord (barkIlksHoleSlotFor I) evmUrns.accountMap
          evmUrns.executionEnv).toNat) :
    ExecBlock (config v)
      { contract := contract v, locals := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks }
      evmIlks (checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt"))
      (.ok { contract := contract v, locals := barkLocalsIlkRoom evmUrns evmIlks I out outIlks }
        evmIlks) := by
  let locals0 := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks
  let locals1 := barkLocalsIlkRoom evmUrns evmIlks I out outIlks
  let milkHole :=
    dogSlotWord (barkIlksHoleSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  let milkDirt :=
    dogSlotWord (barkIlksDirtSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  let ilkRoom := barkSourceIlkRoomWord evmUrns I
  have hmilkLe : milkDirt.toNat ≤ milkHole.toNat := by
    simpa [milkDirt, milkHole] using le_of_lt hmilk
  have hHole0 :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (.var "milkHole") = .ok (.int (Int.ofNat milkHole.toNat)) := by
    simpa [locals0, milkHole] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "milkHole") (value := milkHole)
        (barkLocalsGlobalRoom_get_milkHole evmUrns evmIlks I out outIlks)
  have hDirt0 :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (.var "milkDirt") = .ok (.int (Int.ofNat milkDirt.toNat)) := by
    simpa [locals0, milkDirt] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "milkDirt") (value := milkDirt)
        (barkLocalsGlobalRoom_get_milkDirt evmUrns evmIlks I out outIlks)
  have hsub :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (sub256 (.var "milkHole") (.var "milkDirt")) =
          .ok (.int (Int.ofNat ilkRoom.toNat)) := by
    exact evalExpr_bark_sub256_ok hHole0 hDirt0
      (by simp [ilkRoom, barkSourceIlkRoomWord, milkHole, milkDirt]) hmilkLe
  have hlet :
      ExecStmt (config v) { contract := contract v, locals := locals0 } evmIlks
        (.letDecl "ilkRoom" (some uint256) (sub256 (.var "milkHole") (.var "milkDirt")))
        (.ok { contract := contract v, locals := locals1 } evmIlks) := by
    simpa [locals0, locals1, ilkRoom, barkLocalsIlkRoom] using
      (ExecStmt.letDecl (cfg := config v)
        (solm := { contract := contract v, locals := locals0 }) (evm := evmIlks)
        (name := "ilkRoom") (ty := some uint256)
        (expr := sub256 (.var "milkHole") (.var "milkDirt"))
        (value := .int (Int.ofNat ilkRoom.toNat)) hsub)
  have hilkExpr :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evmIlks
        (.var "ilkRoom") = .ok (.int (Int.ofNat ilkRoom.toNat)) := by
    simpa [locals1, ilkRoom] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals1)
        (name := "ilkRoom") (value := ilkRoom)
        (barkLocalsIlkRoom_get_ilkRoom evmUrns evmIlks I out outIlks)
  have hHole1 :
      evalExpr? (config v) { contract := contract v, locals := locals1 } evmIlks
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
      evalExpr? (config v) { contract := contract v, locals := locals1 } evmIlks
        (.binary .le (.var "ilkRoom") (.var "milkHole")) = .ok (.bool true) := by
    simp [evalExpr?, EvalResult.bind, bind, hilkExpr, hHole1, evalBinaryOp?]
    exact_mod_cast hilkLe
  simpa [checkedSubUintInto, locals0, locals1] using
    (ExecBlock.consNormal hlet <|
      ExecBlock.consNormal (ExecStmt.requireTrue hreq) ExecBlock.nil)

theorem dogBarkRoomMinCallOk {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray) :
    ExecStmt (config v)
      { contract := contract v, locals := barkLocalsIlkRoom evmUrns evmIlks I out outIlks }
      evmIlks (.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room")
      (.ok { contract := contract v, locals := barkLocalsRoom evmUrns evmIlks I out outIlks }
        evmIlks) := by
  let locals0 := barkLocalsIlkRoom evmUrns evmIlks I out outIlks
  let globalRoom := barkSourceGlobalRoomWord evmIlks
  let ilkRoom := barkSourceIlkRoomWord evmUrns I
  have hglobal :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (.var "globalRoom") = .ok (.int (Int.ofNat globalRoom.toNat)) := by
    simpa [locals0, globalRoom] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "globalRoom") (value := globalRoom)
        (barkLocalsIlkRoom_get_globalRoom evmUrns evmIlks I out outIlks)
  have hilk :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (.var "ilkRoom") = .ok (.int (Int.ofNat ilkRoom.toNat)) := by
    simpa [locals0, ilkRoom] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "ilkRoom") (value := ilkRoom)
        (barkLocalsIlkRoom_get_ilkRoom evmUrns evmIlks I out outIlks)
  have hargs :
      evalExprs? (config v) { contract := contract v, locals := locals0 } evmIlks
        [.var "globalRoom", .var "ilkRoom"] =
          .ok [.int (Int.ofNat globalRoom.toNat), .int (Int.ofNat ilkRoom.toNat)] := by
    simp [evalExprs?, hglobal, hilk, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? minFunction.params
          [.int (Int.ofNat globalRoom.toNat), .int (Int.ofNat ilkRoom.toNat)] =
        some (barkBinaryLocals globalRoom ilkRoom) := by
    simp [minFunction, uint256, bindParams?, barkBinaryLocals]
  have hbody :
      ExecFuncBody (config v)
        { contract := contract v, locals := barkBinaryLocals globalRoom ilkRoom } evmIlks
        minFunction.body
        (.returned { contract := contract v, locals := barkBinaryLocals globalRoom ilkRoom }
          evmIlks (some [.int (Int.ofNat (barkSourceRoomWord evmUrns evmIlks I).toNat)])) := by
    simpa [barkSourceRoomWord, globalRoom, ilkRoom] using
      execBarkMinFunctionReturn (v := v) evmIlks globalRoom ilkRoom
  simpa [locals0, barkLocalsRoom, barkSourceRoomWord, globalRoom, ilkRoom,
    resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config v)
      (caller := { contract := contract v, locals := locals0 })
      (evm := evmIlks) (calleeEvm := evmIlks) (name := "min") (retVar := "room")
      (args := [.var "globalRoom", .var "ilkRoom"])
      (argVals := [.int (Int.ofNat globalRoom.toNat), .int (Int.ofNat ilkRoom.toNat)])
      (callee := minFunction) (locals := barkBinaryLocals globalRoom ilkRoom)
      (calleeSolm := { contract := contract v, locals := barkBinaryLocals globalRoom ilkRoom })
      (value := some [.int (Int.ofNat (barkSourceRoomWord evmUrns evmIlks I).toNat)])
      hargs (by rfl) hbind hbody)

theorem dogBarkRoomWadCheckedMulOverflow {v : DogImmutables}
    (evmUrns evmIlks : EVM.State) (I : ExecutionEnv) (out outIlks : ByteArray)
    (hover :
      UInt256.size ≤ (barkSourceRoomWord evmUrns evmIlks I).toNat * dogWadWord.toNat) :
    ExecBlock (config v)
      { contract := contract v, locals := barkLocalsRoom evmUrns evmIlks I out outIlks }
      evmIlks (checkedMulUintInto "roomWad" (.var "room") (.intLit WAD)) .reverted := by
  let locals0 := barkLocalsRoom evmUrns evmIlks I out outIlks
  let room := barkSourceRoomWord evmUrns evmIlks I
  have hroom :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (.var "room") = .ok (.int (Int.ofNat room.toNat)) := by
    simpa [locals0, room] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals0)
        (name := "room") (value := room)
        (barkLocalsRoom_get_room evmUrns evmIlks I out outIlks)
  have hWad :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (.intLit WAD) = .ok (.int (Int.ofNat dogWadWord.toNat)) := by
    have hWadNat : dogWadWord.toNat = 1000000000000000000 := by
      native_decide
    simp [evalExpr?, pure, WAD, hWadNat]
  have hmul :
      evalExpr? (config v) { contract := contract v, locals := locals0 } evmIlks
        (mul256 (.var "room") (.intLit WAD)) = .revert :=
    evalExpr_bark_mul256_revert hroom hWad (by simpa [room] using hover)
  simp only [checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert hmul)

theorem dogBarkVatIlksRoomWadOverflowSourceBody {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmUrns evmIlks : EVM.State} {out outIlks : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I = ⟨1⟩)
    (hcodePos :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat v.vat.toNat)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallUrns :
      typedCallViaEVM (config v) (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
        [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
        (true, evmUrns, out) false)
    (hdecUrns : (config v).externalABI.decode? "urns" out =
      some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
        .int (Int.ofNat (barkVatUrnsArtWord out).toNat)])
    (hcodePosIlks :
      0 < (UInt256.ofNat
        ((evmUrns.lookupAccount (AccountAddress.ofNat v.vat.toNat)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallIlks :
      typedCallViaEVM (config v) evmUrns
        (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
        [.fixedBytes bytes32Width (barkIlkBytes I)] (true, evmIlks, outIlks) false)
    (hdecIlks : (config v).externalABI.decode? "ilks" outIlks =
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
      (dogSlotWord ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv).toNat <
          (dogSlotWord ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv).toNat ∧
        (dogSlotWord (barkIlksDirtSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat <
          (dogSlotWord (barkIlksHoleSlotFor I) evmUrns.accountMap
            evmUrns.executionEnv).toNat)
    (hoverRoom :
      UInt256.size ≤ (barkSourceRoomWord evmUrns evmIlks I).toNat * dogWadWord.toNat)
    (hsz100 : 100 ≤ I.calldata.size) :
    let locals := barkLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals (barkTransition v).body
      .reverted := by
  intro locals evm0
  have hprefix :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        ((barkTransition v).body.take 15)
        (.ok { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
          evmIlks) := by
    simpa [locals, evm0] using
      dogBarkVatIlksSuccessDustPrefix (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (evmUrns := evmUrns) (evmIlks := evmIlks) (out := out)
        (outIlks := outIlks) hwv hlive hcodePos hcallUrns hdecUrns hcodePosIlks
        hcallIlks hdecIlks hsz100
  have hInkBlock :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot"))
        (.ok { contract := contract v, locals := barkLocalsInkSpot evmUrns I out outIlks }
          evmIlks) :=
    dogBarkInkSpotCheckedMulOk (v := v) evmIlks evmUrns I out outIlks hfitInk
  have hArtBlock :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsInkSpot evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract v, locals := barkLocalsArtRateUnsafe evmUrns I out outIlks }
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
  let hole := dogSlotWord ⟨4⟩ evmIlks.accountMap evmIlks.executionEnv
  let dirt := dogSlotWord ⟨5⟩ evmIlks.accountMap evmIlks.executionEnv
  let milkHole :=
    dogSlotWord (barkIlksHoleSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  let milkDirt :=
    dogSlotWord (barkIlksDirtSlotFor I) evmUrns.accountMap evmUrns.executionEnv
  have hspot :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "spot") = .ok (.int (Int.ofNat spot.toNat)) := by
    simpa [locals2, spot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "spot") (value := barkVatIlksSpotWord outIlks)
        (barkLocalsArtRateUnsafe_get_spot evmUrns I out outIlks)
  have hzero :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.intLit 0) = .ok (.int 0) := by
    simp [evalExpr?, pure]
  have hinkSpot :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "inkSpot") = .ok (.int (Int.ofNat inkSpot.toNat)) := by
    simpa [locals2, inkSpot] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "inkSpot") (value := barkInkSpotWord out outIlks)
        (barkLocalsArtRateUnsafe_get_inkSpot evmUrns I out outIlks)
  have hartRate :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "artRateUnsafe") = .ok (.int (Int.ofNat artRate.toNat)) := by
    simpa [locals2, artRate] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "artRateUnsafe") (value := barkArtRateUnsafeWord out outIlks)
        (barkLocalsArtRateUnsafe_get_artRateUnsafe evmUrns I out outIlks)
  have hunsafeReq :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        unsafeGuard = .ok (.bool true) := by
    have hgt :
        evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
          (.binary .gt (.var "spot") (.intLit 0)) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hspot hzero
      exact Int.ofNat_lt.mpr (by simpa [spot] using hspotPos)
    have hlt :
        evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
          (.binary .lt (.var "inkSpot") (.var "artRateUnsafe")) = .ok (.bool true) := by
      apply evalExpr_bark_lt_int_true hinkSpot hartRate
      exact Int.ofNat_lt.mpr (by simpa [inkSpot, artRate] using hsafeLt)
    simpa [unsafeGuard] using evalExpr_bark_and_true_right hgt hlt
  have hHoleExpr :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.storage HoleRef) = .ok (.int (Int.ofNat hole.toNat)) := by
    simpa [locals2, hole] using
      evalExpr_barkStorageHole (v := v) (evm := evmIlks) (locals := locals2)
        (barkLocalsArtRateUnsafe_get_Hole evmUrns I out outIlks)
  have hDirtExpr :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.storage DirtRef) = .ok (.int (Int.ofNat dirt.toNat)) := by
    simpa [locals2, dirt] using
      evalExpr_barkStorageDirt (v := v) (evm := evmIlks) (locals := locals2)
        (barkLocalsArtRateUnsafe_get_Dirt evmUrns I out outIlks)
  have hmilkHoleExpr :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "milkHole") = .ok (.int (Int.ofNat milkHole.toNat)) := by
    simpa [locals2, milkHole] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "milkHole") (value := milkHole)
        (barkLocalsArtRateUnsafe_get_milkHole evmUrns I out outIlks)
  have hmilkDirtExpr :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        (.var "milkDirt") = .ok (.int (Int.ofNat milkDirt.toNat)) := by
    simpa [locals2, milkDirt] using
      evalExpr_bark_varUInt256 (v := v) (evm := evmIlks) (locals := locals2)
        (name := "milkDirt") (value := milkDirt)
        (barkLocalsArtRateUnsafe_get_milkDirt evmUrns I out outIlks)
  have hlimitReq :
      evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
        limitGuard = .ok (.bool true) := by
    have hgtGlobal :
        evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
          (.binary .gt (.storage HoleRef) (.storage DirtRef)) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hHoleExpr hDirtExpr
      exact Int.ofNat_lt.mpr (by simpa [dirt, hole] using hlimit.1)
    have hgtMilk :
        evalExpr? (config v) { contract := contract v, locals := locals2 } evmIlks
          (.binary .gt (.var "milkHole") (.var "milkDirt")) = .ok (.bool true) := by
      apply evalExpr_bark_gt_int_true hmilkHoleExpr hmilkDirtExpr
      exact Int.ofNat_lt.mpr (by simpa [milkDirt, milkHole] using hlimit.2)
    simpa [limitGuard] using evalExpr_bark_and_true_right hgtGlobal hgtMilk
  have hchecked :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate"))
        (.ok { contract := contract v, locals := locals2 } evmIlks) :=
    by simpa [locals2] using execBlock_append hInkBlock hArtBlock
  have hunsafeBlock :
      ExecBlock (config v) { contract := contract v, locals := locals2 } evmIlks
        [.require unsafeGuard]
        (.ok { contract := contract v, locals := locals2 } evmIlks) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hunsafeReq) ExecBlock.nil
  have hlimitBlock :
      ExecBlock (config v) { contract := contract v, locals := locals2 } evmIlks
        [.require limitGuard]
        (.ok { contract := contract v, locals := locals2 } evmIlks) :=
    ExecBlock.consNormal (ExecStmt.requireTrue hlimitReq) ExecBlock.nil
  have hcheckedUnsafe :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        ((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard])
        (.ok { contract := contract v, locals := locals2 } evmIlks) :=
    execBlock_append hchecked (by simpa [locals2] using hunsafeBlock)
  have hcheckedUnsafeLimit :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (((checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
            checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate")) ++
          [.require unsafeGuard]) ++ [.require limitGuard])
        (.ok { contract := contract v, locals := locals2 } evmIlks) :=
    execBlock_append hcheckedUnsafe (by simpa [locals2] using hlimitBlock)
  have hglobalBlock :=
    dogBarkGlobalRoomCheckedSubOk (v := v) evmUrns evmIlks I out outIlks hlimit.1
  have htoGlobal :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef))
        (.ok { contract := contract v, locals := barkLocalsGlobalRoom evmUrns evmIlks I out outIlks }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append hcheckedUnsafeLimit hglobalBlock
  have hilkBlock :=
    dogBarkIlkRoomCheckedSubOk (v := v) evmUrns evmIlks I out outIlks hlimit.2
  have htoIlk :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt"))
        (.ok { contract := contract v, locals := barkLocalsIlkRoom evmUrns evmIlks I out outIlks }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append htoGlobal hilkBlock
  have hminStmt :=
    dogBarkRoomMinCallOk (v := v) evmUrns evmIlks I out outIlks
  have hminBlock :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsIlkRoom evmUrns evmIlks I out outIlks }
        evmIlks
        [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"]
        (.ok { contract := contract v, locals := barkLocalsRoom evmUrns evmIlks I out outIlks }
          evmIlks) :=
    ExecBlock.consNormal hminStmt ExecBlock.nil
  have htoRoom :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
        evmIlks
        (checkedMulUintInto "inkSpot" (.var "ink") (.var "spot") ++
          checkedMulUintInto "artRateUnsafe" (.var "art") (.var "rate") ++
          [.require unsafeGuard] ++ [.require limitGuard] ++
          checkedSubUintInto "globalRoom" (.storage HoleRef) (.storage DirtRef) ++
          checkedSubUintInto "ilkRoom" (.var "milkHole") (.var "milkDirt") ++
          [.internalCall "min" [.var "globalRoom", .var "ilkRoom"] "room"])
        (.ok { contract := contract v, locals := barkLocalsRoom evmUrns evmIlks I out outIlks }
          evmIlks) := by
    simpa [List.append_assoc] using execBlock_append htoIlk hminBlock
  have hroomWadBlock :=
    dogBarkRoomWadCheckedMulOverflow (v := v) evmUrns evmIlks I out outIlks hoverRoom
  have htoRoomWad :
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
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
    checkedExternalCallStmts (vatExpr v) "grab" (.intLit 0)
      [ .var "ilk", .var "urn", .var "milkClip", vowAddr,
        .unary .neg (asInt256 (.var "dink")),
        .unary .neg (asInt256 (.var "dart")) ] "_grabRet" ++
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
      ExecBlock (config v)
        { contract := contract v, locals := barkLocalsDust evmUrns I out outIlks }
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
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (barkTransition v).body .reverted := by
    have hcombined := execBlock_append hprefix htail
    simpa [unsafeGuard, limitGuard, afterRoomWad, barkTransition, barkBodyRest, nonpayable,
      checkedExternalCallStmts, checkedMulUintInto, checkedSubUintInto, List.append_assoc]
      using hcombined
  simpa [ExecTransitionBody, evm0, locals, barkTransition] using
    ExecFuncBody.execBlockRevert hblock

theorem barkVatUrnsDecode_none_short {v : DogImmutables} {out : ByteArray}
    (hshort : out.size < 64) :
    (config v).externalABI.decode? "urns" out = none := by
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

theorem barkVatUrnsDecode_ok {v : DogImmutables} {out : ByteArray}
    (hlong : 64 ≤ out.size) :
    (config v).externalABI.decode? "urns" out =
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

theorem barkVatIlksDecode_none_short {v : DogImmutables} {out : ByteArray}
    (hshort : out.size < 160) :
    (config v).externalABI.decode? "ilks" out = none := by
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

theorem barkVatIlksDecode_ok {v : DogImmutables} {out : ByteArray}
    (hlong : 160 ≤ out.size) :
    (config v).externalABI.decode? "ilks" out = some (barkVatIlksReturnValues out) := by
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

theorem dogNonpayableLivePrefixRevert {v : DogImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    {locals : Store} {rest : List Stmt}
    (hbase : locals.get? "live" = none)
    (hwv : I.weiValue = ⟨0⟩)
    (hlive : dogSlotWord ⟨3⟩ σ I ≠ ⟨1⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) locals
      (nonpayable ++ [.require (.binary .eq (.storage liveRef) (.intLit 1))] ++ rest)
      .reverted := by
  let evm0 := initState cA gh bl σ σ₀ g A I
  have hcallvalue :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) :=
    evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  have hguard :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    simpa [evm0] using
      dogLiveGuardEval_false (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (locals := locals) hbase hlive
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        (nonpayable ++ [.require (.binary .eq (.storage liveRef) (.intLit 1))] ++ rest)
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue hcallvalue) ?_
    change ExecBlock (config v) { contract := contract v, locals := locals } evm0
      ([.require (.binary .eq (.storage liveRef) (.intLit 1))] ++ rest) .reverted
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, evm0] using ExecFuncBody.execBlockRevert hblock

theorem dogDecodeABIValues_bytes32_address_address_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiAddress, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)], 96) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, hlen32, hlen64]

theorem dogDecodeABIValues_bytes32_address_address_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeABIValues? [abiBytes32, abiAddress, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 = none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hnot : ¬ 32 ≤ bytes.length - 32 := by
        rw [List.length_take, List.length_drop] at htake32n
        omega
      simp [readWord?, readBytes?, hnot]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, htake32]
      have htake64n : ¬ ((bytes.drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hnot : ¬ 32 ≤ bytes.length - 64 := by
        rw [List.length_take, List.length_drop] at htake64n
        omega
      simp [readWord?, readBytes?, hnot]

theorem dogDecodeCalldataWithMode_legacyBytes32_address_address_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
      [abiBytes32, abiAddress, abiAddress] cd =
        some ((((∅ : Solm.Store).insert x
          (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
          (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
          (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress, abiAddress] = some 96 by native_decide]
  simp only [bind, Option.bind]
  rw [dogDecodeABIValues_bytes32_address_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 96)]
  simp [decodeCalldata.insertValues]
  rw [hword36, hword68]

theorem dogDecodeCalldataWithMode_legacyBytes32_address_address_none_short
    {cd : ByteArray} {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size)
    (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
      [abiBytes32, abiAddress, abiAddress] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress, abiAddress] = some 96 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 96
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [dogDecodeABIValues_bytes32_address_address_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem dogDecode_bark_ok {v : DogImmutables} {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode ((barkTransition v).params.map Param.name)
      (transitionSignature (barkTransition v)).paramTypes I.calldata =
        some (barkLocals I) := by
  simpa [config, barkTransition, barkLocals, barkIlkBytes, barkUrn, barkKpr, barkUrnWord,
    barkKprWord, bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width, abiAddress] using
    dogDecodeCalldataWithMode_legacyBytes32_address_address_ok (cd := I.calldata)
      (x := "ilk") (y := "urn") (z := "kpr") hsz100

theorem dogDecode_bark_none_short {v : DogImmutables} {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode (config v).abiDecodeMode ((barkTransition v).params.map Param.name)
      (transitionSignature (barkTransition v)).paramTypes I.calldata = none := by
  simpa [config, barkTransition, bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width,
    abiAddress] using
    dogDecodeCalldataWithMode_legacyBytes32_address_address_none_short
      (cd := I.calldata) (x := "ilk") (y := "urn") (z := "kpr") hsz4 hshort

theorem dogReachBarkBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 2)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨785⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0xed998908⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xed 0x99 0x89 0x08 ⟨0xed998908⟩
      (by native_decide) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootWidth : armTgtWidth code (⟨32⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hhighWidth : armTgtWidth code (⟨43⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h43 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [selArmNextPc, hrootWidth] using
      RD.selectorSplitNotTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot (by simp)
  have hhigh :
      UInt256.gt (armSelNat code (⟨43⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h54 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨54⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [selArmNextPc, hhighWidth] using
      RD.selectorSplitNotTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh (by simp)
  have hchop : UInt256.eq (dogSelectorWord 4) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hilks : UInt256.eq (dogSelectorWord 11) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hfileIlkClip : UInt256.eq (dogSelectorWord 10) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hbark : UInt256.eq (dogSelectorWord 2) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h65 := by
    simpa [selArmNextPc] using
      h54.selectorArmNotTaken (selNat := dogSelectorWord 4) (tgt := (⟨629⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hchop
        (by simp)
  have h76 := by
    simpa [selArmNextPc] using
      h65.selectorArmNotTaken (selNat := dogSelectorWord 11) (tgt := (⟨658⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hilks
        (by simp)
  have h87 := by
    simpa [selArmNextPc] using
      h76.selectorArmNotTaken (selNat := dogSelectorWord 10) (tgt := (⟨735⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hfileIlkClip
        (by simp)
  have h785 := by
    simpa using
      h87.selectorArmTaken (selNat := dogSelectorWord 2) (tgt := (⟨785⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hbark
        (dogPatchedDJumpPrefix1405 ⟨785⟩ hpatch (by native_decide))
        (by simp)
  exact ⟨_, _, h785⟩

theorem RD.dogBarkDecodeToRoutine {v : DogImmutables} {code : ByteArray}
    {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State} {k C : ℕ}
    {decoded ret de : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hdecoded : decoded = ⟨807⟩)
    (hroutine : (D_J code 0).contains ⟨2813⟩ = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2813⟩
      (barkKprKey ee :: barkUrnKey ee :: barkIlkWord ee :: ret :: R)
      mem aw rdata acc k' C' := by
  subst hdecoded
  have rd1 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd2 := rd1.pop
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd3 := rd2.dup1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd4 := rd3.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd5 := rd4.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd7 := rd5.push1 ⟨1⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd9 := rd7.push1 ⟨1⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd11 := rd9.push1 ⟨160⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd12 := rd11.shl
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd13 := rd12.sub
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd15 := rd13.push1 ⟨32⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd16 := rd15.dup3
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd17 := rd16.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd18 := rd17.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd19 := rd18.dup2
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd20 := rd19.and
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd21 := rd20.swap2
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd23 := rd21.push1 ⟨64⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd24 := rd23.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd25 := rd24.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd26 := rd25.and
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd29 := rd26.push2 ⟨2813⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [barkKprKey, barkUrnKey, barkIlkWord, barkKprWord, barkUrnWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      show ((⟨64⟩ : UInt256) + ⟨4⟩).toNat = 68 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd29.jump
        (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
        hroutine (by evm_ov)⟩

theorem RD.dogBarkDecodeToBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hsize : I.calldata.size < UInt256.size) (hsz100 : 100 ≤ I.calldata.size)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨785⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2813⟩
      [barkKprKey I, barkUrnKey I, barkIlkWord I, ⟨448⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize
  have hdecoded := RD.solcExternalStaticArgsLenOk
    (code := code) (sel := sel) (entry := ⟨785⟩) (ret := ⟨448⟩)
    (decoded := ⟨807⟩) (need := ⟨96⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨807⟩ hpatch (by native_decide))
    hlt
  obtain ⟨_, _, hdecoded'⟩ := hdecoded
  obtain ⟨k, C, hbody⟩ := RD.dogBarkDecodeToRoutine hpatch hdecoded' rfl
    (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_singleton]; omega)
  exact ⟨k, C, by simpa using hbody⟩

theorem RD.dogCheckedMulReturns {v : DogImmutables} {code : ByteArray}
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hRlen : R.length ≤ 1010)
    (hret : (D_J code 0).contains ret = true)
    (hfit : x.toNat * y.toNat < UInt256.size)
    (rd4564 : RD code I g s0 ⟨4564⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    ∃ k' C', RD code I g s0 ret (x * y :: R) mem aw rdata acc k' C' := by
  have rd4591prep := evm_run rd4564 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4591⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  by_cases hy0 : y = ⟨0⟩
  · have hcond : UInt256.isZero y ≠ ⟨0⟩ := by
      rw [hy0]
      decide
    have rd4591 := rd4591prep.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hcond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd4558prep := evm_run rd4591 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨4558⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd4558 := rd4558prep.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hcond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd4563 := evm_run rd4558 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap2
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rdret := rd4563.jump
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hret (by evm_ov)
    exact ⟨_, _, by simpa [hy0] using rdret⟩
  · have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hy0
    have rd4574 := rd4591prep.jumpiNT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hcond (by evm_ov)
    have rd4586 := evm_run rd4574 with [
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw dup1
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw dup3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw mul
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw dup3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw dup3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw dup3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw dup2
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨4588⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd4588 := rd4586.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hy0 (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have hyNatNe : y.toNat ≠ 0 := by
      intro hzero
      exact hy0 (uint256_toNat_eq_zero hzero)
    have hdivWord : UInt256.div (x * y) y = x := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : (x * y).toNat = x.toNat * y.toNat := by
        rw [umul_toNat x y hfit]
      rw [hprod]
      simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat
        (Nat.pos_of_ne_zero hyNatNe)
    have rd4558prep := evm_run rd4588 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw div
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw eq
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨4558⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have heqCond : UInt256.eq (UInt256.div (x * y) y) x ≠ ⟨0⟩ := by
      rw [hdivWord, u256_eq_refl]
      exact one_ne_zero_uint
    have rd4558 := rd4558prep.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      heqCond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd4563 := evm_run rd4558 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap2
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rdret := rd4563.jump
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hret (by evm_ov)
    exact ⟨_, _, by simpa using rdret⟩

theorem RD.dogMinReturns {v : DogImmutables} {code : ByteArray}
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hret : (D_J code 0).contains ret = true)
    (rd4600 : RD code I g s0 ⟨4600⟩ (y :: x :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code I g s0 ret
      ((if x.toNat ≤ y.toNat then x else y) :: R) mem aw rdata acc k' C' := by
  have rd4610prep := evm_run rd4600 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4616⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  by_cases hle : x.toNat ≤ y.toNat
  · have hgt : UInt256.gt x y = ⟨0⟩ :=
      Reasoning.Theory.ugt_zero hle
    have rd4610 := rd4610prep
    rw [hgt, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4610
    have rd4616 := rd4610.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      one_ne_zero_uint (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd4624 := evm_run rd4616 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw dup3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap4
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rdret := rd4624.jump
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hret (by evm_ov)
    exact ⟨_, _, by simpa [hle] using rdret⟩
  · have hylt : y.toNat < x.toNat := by omega
    have hgt : UInt256.gt x y = ⟨1⟩ :=
      Reasoning.Theory.ugt_one hylt
    have rd4610 := rd4610prep
    rw [hgt, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4610
    have rd4611 := rd4610.jumpiNT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by rfl) (by evm_ov)
    have rd4615 := evm_run rd4611 with [
      raw dup2
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨4618⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd4618 := rd4615.jump
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd4624 := evm_run rd4618 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap4
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw swap3
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rdret := rd4624.jump
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hret (by evm_ov)
    exact ⟨_, _, by simpa [hle] using rdret⟩

theorem RD.dogCheckedMulOverflowReverts {v : DogImmutables} {code : ByteArray}
    {s0 : EVM.State} {I : ExecutionEnv} {g : Sat256}
    {x y ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {aw : UInt256} {k C : ℕ}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hRlen : R.length ≤ 1010)
    (hover : UInt256.size ≤ x.toNat * y.toNat)
    (rd4564 : RD code I g s0 ⟨4564⟩ (y :: x :: ret :: R)
      mem aw rdata acc k C) :
    RDrev code g s0 := by
  have hyNe : y ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (x * y) y ≠ x := by
    intro hbad
    have h := dog_u256_mul_div_overflow_ne x y hover
    exact h (by
      have hcomm : y * x = x * y := by
        simpa using u256_mul_comm y x
      rw [hcomm]
      exact hbad)
  have rd4591prep := evm_run rd4564 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4591⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hcond : UInt256.isZero y = ⟨0⟩ := isZero_eq_zero_of_ne hyNe
  have rd4574 := rd4591prep.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond (by evm_ov)
  have rd4586 := evm_run rd4574 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mul
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4588⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4588 := rd4586.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hyNe (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd4558prep := evm_run rd4588 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw div
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw eq
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4558⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have heqCond : UInt256.eq (UInt256.div (x * y) y) x = ⟨0⟩ :=
    u256_eq_of_ne hdivNe
  have rdFallthrough := rd4558prep.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    heqCond (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem dogDecodePatchedEqTemplatePrecise {v : DogImmutables} {code : ByteArray}
    {pc : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hwinOp : decide (pc.toNat + 1 ≤ dogBytecode.size) = true)
    (hoffsetsOp : dogPatchOffsets.all
      (fun off => decide (pc.toNat + 1 ≤ off ∨ off + 32 ≤ pc.toNat)) = true)
    (hwinArg : (match dogBytecode.get? pc.toNat >>= parseInstr with
      | none => true
      | some instr =>
          decide (pc.toNat.succ + argOnNBytesOfInstr instr ≤ dogBytecode.size)) = true)
    (hoffsetsArg : (match dogBytecode.get? pc.toNat >>= parseInstr with
      | none => true
      | some instr =>
          dogPatchOffsets.all (fun off =>
        decide (pc.toNat.succ + argOnNBytesOfInstr instr ≤ off ∨
          off + 32 ≤ pc.toNat.succ))) = true) :
    decode code pc = decode dogBytecode pc := by
  unfold decode
  have hsize := dogPatchedSize hpatch
  have hsize64 : dogBytecode.size < 2 ^ 64 := by native_decide
  have hwinOp' : pc.toNat + 1 ≤ dogBytecode.size := by
    exact of_decide_eq_true hwinOp
  have hoffsetsOp' :
      ∀ off ∈ dogPatchOffsets, pc.toNat + 1 ≤ off ∨ off + 32 ≤ pc.toNat := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hoffsetsOp
  have hget : code.get? pc.toNat = dogBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · exact Nat.lt_of_succ_le hwinOp'
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (by omega) (by omega)
        (by
          intro p hp
          rcases hoffsetsOp' p.1 (dogPatchOffsetMem v p hp) with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  rw [hget]
  cases hgetTemplate : dogBytecode.get? pc.toNat with
  | none => simp
  | some b =>
      cases hinstr : parseInstr b with
      | none => simp [hinstr]
      | some instr =>
          simp [hinstr]
          by_cases harg : argOnNBytesOfInstr instr = 0
          · simp [harg]
          · simp [harg]
            have hbind :
                (dogBytecode.get? pc.toNat >>= parseInstr) = some instr := by
              simp [hgetTemplate, hinstr]
            have hwinArg' :
                pc.toNat.succ + argOnNBytesOfInstr instr ≤ dogBytecode.size := by
              have hwinArgBool :
                  decide (pc.toNat.succ + argOnNBytesOfInstr instr ≤ dogBytecode.size) =
                    true := by
                simpa [hgetTemplate, hinstr] using hwinArg
              exact of_decide_eq_true hwinArgBool
            have hextract :
                code.extract' pc.toNat.succ
                    (pc.toNat.succ + argOnNBytesOfInstr instr) =
                  dogBytecode.extract' pc.toNat.succ
                    (pc.toNat.succ + argOnNBytesOfInstr instr) := by
              unfold ByteArray.extract'
              have hstart64 : pc.toNat.succ < 2 ^ 64 := by
                omega
              have hstop64 :
                  pc.toNat.succ + argOnNBytesOfInstr instr < 2 ^ 64 := by
                omega
              have hguard :
                  (decide (pc.toNat.succ < 2 ^ 64) &&
                      decide (pc.toNat.succ + argOnNBytesOfInstr instr < 2 ^ 64)) =
                    true := by
                rw [decide_eq_true hstart64, decide_eq_true hstop64]
                rfl
              rw [if_pos hguard, if_pos hguard]
              exact patchRuntime_extract_eq (start := pc.toNat.succ)
                (stop := pc.toNat.succ + argOnNBytesOfInstr instr)
                (by omega) hwinArg'
                (by
                  have hoffsetsArg' :
                      ∀ off ∈ dogPatchOffsets,
                        pc.toNat.succ + argOnNBytesOfInstr instr ≤ off ∨
                          off + 32 ≤ pc.toNat.succ := by
                    have hoffsetsArgBool :
                        dogPatchOffsets.all (fun off =>
                          decide (pc.toNat.succ + argOnNBytesOfInstr instr ≤ off ∨
                            off + 32 ≤ pc.toNat.succ)) = true := by
                      simpa [hgetTemplate, hinstr] using hoffsetsArg
                    simpa only [List.all_eq_true, decide_eq_true_eq] using hoffsetsArgBool
                  intro p hp
                  rcases hoffsetsArg' p.1 (dogPatchOffsetMem v p hp) with
                    hbefore | hafter
                  · exact Or.inl (by omega)
                  · exact Or.inr (by omega))
                hpatch
            rw [hextract]

theorem dogBarkVatPatchWord2890 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    code.extract 2890 2922 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
  let value := UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
  let pre : List (Nat × ByteArray) := [(1405, value)]
  let post : List (Nat × ByteArray) := [(3170, value), (3965, value)]
  have hpatch' : patchRuntime dogBytecode (pre ++ (2890, value) :: post) = some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 2890 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 2890 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl | rfl <;> omega
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch (template := dogBytecode) (out := code)
    (value := value) (pre := pre) (post := post) (offset := 2890) hsize hpost hpatch'

theorem dogBarkVatConstDecode2889 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    decode code ⟨2889⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32)) := by
  have hsize := dogPatchedSize hpatch
  have hget : code.get? ({ val := 2889 } : UInt256).toNat =
      dogBytecode.get? ({ val := 2889 } : UInt256).toNat := by
    change code.get? 2889 = dogBytecode.get? 2889
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 2889) (stop := 2890)
        (template := dogBytecode) (out := code) (ps := patches v)
        (by omega) (by native_decide)
        (by
          intro p hp
          have hm := dogPatchOffsetMem v p hp
          simp [dogPatchOffsets] at hm
          rcases hm with h | h | h | h
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega)
        hpatch
  have hextract : code.extract' ({ val := 2889 } : UInt256).toNat.succ
      (({ val := 2889 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
    change code.extract' 2890 2922 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
    unfold ByteArray.extract'
    have hguard : (decide (2890 < 2 ^ 64) && decide (2922 < 2 ^ 64)) = true := by
      native_decide
    rw [if_pos hguard]
    exact dogBarkVatPatchWord2890 hpatch
  have hgetSome : code.get? ({ val := 2889 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 2889 } : UInt256).toNat.succ
          (({ val := 2889 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem dogBarkVatPatchWord3170 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    code.extract 3170 3202 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
  let value := UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
  let pre : List (Nat × ByteArray) := [(1405, value), (2890, value)]
  let post : List (Nat × ByteArray) := [(3965, value)]
  have hpatch' : patchRuntime dogBytecode (pre ++ (3170, value) :: post) = some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 3170 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 3170 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
    rcases hp with rfl
    omega
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch (template := dogBytecode) (out := code)
    (value := value) (pre := pre) (post := post) (offset := 3170) hsize hpost hpatch'

theorem dogBarkVatConstDecode3169 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    decode code ⟨3169⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32)) := by
  have hsize := dogPatchedSize hpatch
  have hget : code.get? ({ val := 3169 } : UInt256).toNat =
      dogBytecode.get? ({ val := 3169 } : UInt256).toNat := by
    change code.get? 3169 = dogBytecode.get? 3169
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 3169) (stop := 3170)
        (template := dogBytecode) (out := code) (ps := patches v)
        (by omega) (by native_decide)
        (by
          intro p hp
          have hm := dogPatchOffsetMem v p hp
          simp [dogPatchOffsets] at hm
          rcases hm with h | h | h | h
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega)
        hpatch
  have hextract : code.extract' ({ val := 3169 } : UInt256).toNat.succ
      (({ val := 3169 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
    change code.extract' 3170 3202 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
    unfold ByteArray.extract'
    have hguard : (decide (3170 < 2 ^ 64) && decide (3202 < 2 ^ 64)) = true := by
      native_decide
    rw [if_pos hguard]
    exact dogBarkVatPatchWord3170 hpatch
  have hgetSome : code.get? ({ val := 3169 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 3169 } : UInt256).toNat.succ
          (({ val := 3169 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem dogBarkVatPatchWord3965 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    code.extract 3965 3997 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
  let value := UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
  let pre : List (Nat × ByteArray) := [(1405, value), (2890, value), (3170, value)]
  let post : List (Nat × ByteArray) := []
  have hpatch' : patchRuntime dogBytecode (pre ++ (3965, value) :: post) = some code := by
    dsimp [pre, post, value]
    simpa [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup,
      toByteArray_eq_toBytesBE] using hpatch
  have hpost : ∀ p ∈ post, 3965 + 32 ≤ p.1 ∨ p.1 + 32 ≤ 3965 := by
    intro p hp
    dsimp [post] at hp
    simp at hp
  have hsize : value.size = 32 := by
    dsimp [value]
    exact toByteArray_size _
  exact patchRuntime_extract_patch (template := dogBytecode) (out := code)
    (value := value) (pre := pre) (post := post) (offset := 3965) hsize hpost hpatch'

theorem dogBarkVatConstDecode3964 {v : DogImmutables} {code : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code) :
    decode code ⟨3964⟩ =
      some (.Push .PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32)) := by
  have hsize := dogPatchedSize hpatch
  have hget : code.get? ({ val := 3964 } : UInt256).toNat =
      dogBytecode.get? ({ val := 3964 } : UInt256).toNat := by
    change code.get? 3964 = dogBytecode.get? 3964
    apply get?_eq_of_extract_one
    · rw [hsize]
      native_decide
    · native_decide
    · exact patchRuntime_extract_eq (start := 3964) (stop := 3965)
        (template := dogBytecode) (out := code) (ps := patches v)
        (by omega) (by native_decide)
        (by
          intro p hp
          have hm := dogPatchOffsetMem v p hp
          simp [dogPatchOffsets] at hm
          rcases hm with h | h | h | h
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega
          · rw [h]
            omega)
        hpatch
  have hextract : code.extract' ({ val := 3964 } : UInt256).toNat.succ
      (({ val := 3964 } : UInt256).toNat.succ + 32) =
      UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat) := by
    change code.extract' 3965 3997 = UInt256.toByteArray (EVM.Word.ofNat v.vat.toNat)
    unfold ByteArray.extract'
    have hguard : (decide (3965 < 2 ^ 64) && decide (3997 < 2 ^ 64)) = true := by
      native_decide
    rw [if_pos hguard]
    exact dogBarkVatPatchWord3965 hpatch
  have hgetSome : code.get? ({ val := 3964 } : UInt256).toNat = some 0x7f := by
    rw [hget]
    native_decide
  have hparse : (some (0x7f : UInt8) >>= parseInstr) = some (.Push .PUSH32) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH32,
      some (uInt256OfByteArray
        (code.extract' ({ val := 3964 } : UInt256).toNat.succ
          (({ val := 3964 } : UInt256).toNat.succ + 32)), 32)) =
    some (Operation.Push Operation.POp.PUSH32, some (EVM.Word.ofNat v.vat.toNat, 32))
  rw [hextract, uInt256OfByteArray_eq, fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem RD.dogBarkVatUrnsToCallMload {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2885⟩
      (⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨2941⟩
      (⟨128⟩ :: barkUrnKey I :: barkIlkWord I :: ⟨606387804⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k' C' := by
  have hvatCleanR :
      UInt256.land (barkVatWord v) solcAddrMask = barkVatWord v :=
    solcAddrMask_clean (barkVatWord_canonical v)
  have hvatCleanL :
      UInt256.land solcAddrMask (barkVatWord v) = barkVatWord v :=
    solcAddrMask_clean_left (barkVatWord_canonical v)
  have rd2886 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2889 := evm_run rd2886 with [
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd2922 := rd2889.pushConst (barkVatWord v) (width := 32) (op := .PUSH32)
    (hop := by decide)
    (by simpa [barkVatWord] using dogBarkVatConstDecode2889 hpatch)
    (by evm_ov)
  have rd2940raw := evm_run rd2922 with [
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push4 ⟨606387804⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd2941raw := rd2940raw.mload 0 ⟨128⟩ (UInt256.ofNat 3)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
    (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, hvatCleanR, hvatCleanL] using rd2941raw⟩

theorem RD.dogBarkVatUrnsToExtcodesize {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2941⟩
      (⟨128⟩ :: barkUrnKey I :: barkIlkWord I :: ⟨606387804⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
        ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨2992⟩
      (barkVatWord v :: barkVatWord v :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ ::
        ⟨64⟩ :: ⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
        ret :: sel :: R)
      (barkVatUrnsCallMem I mem) (UInt256.ofNat 7) rdata acc k' C' := by
  have hurnCanon : (barkUrnKey I).toNat < EVM.addressModulus := by
    rw [barkUrnKey, u256_land_comm]
    exact solcAddrMask_result_canonical (barkUrnWord I)
  have hurnCleanR :
      UInt256.land (barkUrnKey I) solcAddrMask = barkUrnKey I :=
    solcAddrMask_clean hurnCanon
  have hurnCleanL :
      UInt256.land solcAddrMask (barkUrnKey I) = barkUrnKey I :=
    solcAddrMask_clean_left hurnCanon
  have rd2951prefix := evm_run h with [
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push4 ⟨4294967295⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨224⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd2953 := rd2951prefix.mstore 6 (barkVatUrnsSelectorMem mem) (UInt256.ofNat 5)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      have hsel :
          UInt256.shiftLeft (UInt256.land (⟨4294967295⟩ : UInt256) ⟨606387804⟩) ⟨224⟩ =
            barkVatUrnsSelectorWord := by
        native_decide
      dsimp [barkVatUrnsSelectorMem, Reasoning.Theory.writeWord]
      rw [hsel]
      rw [show (⟨128⟩ : UInt256).toNat = 128 by native_decide])
    (by native_decide) (by evm_ov)
  have rd2958prefix := evm_run rd2953 with [
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd2960 := rd2958prefix.mstore 3 (barkVatUrnsIlkMem I mem) (UInt256.ofNat 6)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      have h132 : UInt256.add (⟨4⟩ : UInt256) ⟨128⟩ = ⟨132⟩ := by
        native_decide
      dsimp [barkVatUrnsIlkMem, Reasoning.Theory.writeWord]
      rw [show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 by native_decide])
    (by native_decide) (by evm_ov)
  have rd2973raw := evm_run rd2960 with [
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd2974⟩ : ∃ k' C', RD code I g s0 ⟨2974⟩
      (⟨164⟩ :: barkUrnKey I :: ⟨164⟩ :: ⟨132⟩ :: barkUrnKey I ::
        barkIlkWord I :: ⟨606387804⟩ :: barkVatWord v :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsIlkMem I mem) (UInt256.ofNat 6) rdata acc k' C' := by
    exact ⟨_, _, by
      simpa [show UInt256.add (⟨32⟩ : UInt256) ⟨132⟩ = ⟨164⟩ by native_decide,
        show UInt256.add (⟨4⟩ : UInt256) ⟨128⟩ = ⟨132⟩ by native_decide,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide, hurnCleanR, hurnCleanL] using rd2973raw⟩
  have rd2975 := rd2974.mstore 3 (barkVatUrnsCallMem I mem) (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatUrnsCallMem, Reasoning.Theory.writeWord]
      rw [show (⟨164⟩ : UInt256).toNat = 164 by native_decide])
    (by native_decide) (by evm_ov)
  have rd2985prefix := evm_run rd2975 with [
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd2986 := rd2985prefix.mload 0 ⟨128⟩ (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (mloadFreePtrValue
      (by rw [barkVatUrnsCallMem_size hmem]; decide) (by decide)
      (barkVatUrnsCallMem_read64 hmem hread64))
    (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [
      show UInt256.add (⟨32⟩ : UInt256) ⟨164⟩ = ⟨196⟩ from by native_decide,
      show UInt256.sub (⟨196⟩ : UInt256) ⟨128⟩ = ⟨68⟩ from by native_decide] using
      evm_run rd2986 with [
        raw dup1
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov),
        raw dup4
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov),
        raw sub
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov),
        raw dup2
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov),
        raw dup7
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov),
        raw dup1
          (by
            rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
            native_decide)
          (by evm_ov)]⟩

theorem RD.dogBarkVatUrnsNoCodeRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2885⟩
      (⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) = ⟨0⟩)
    (hov : R.length + 24 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd2941⟩ :=
    RD.dogBarkVatUrnsToCallMload hpatch h hmem hread64 (by omega)
  obtain ⟨_, _, rd2992⟩ :=
    RD.dogBarkVatUrnsToExtcodesize hpatch rd2941 hmem hread64 hov
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨2992⟩) (okPc := ⟨3004⟩)
    rd2992 hcodeSize
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatUrnsToStaticcall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g s0 ⟨2885⟩
      (⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hov : R.length + 24 ≤ 1024) :
    ∃ gasWord k' C', RD code I g s0 ⟨3007⟩
      (gasWord :: barkVatWord v :: ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨64⟩ ::
        ⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsCallMem I mem) (UInt256.ofNat 7) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd2941⟩ :=
    RD.dogBarkVatUrnsToCallMload hpatch h hmem hread64 (by omega)
  obtain ⟨_, _, rd2992⟩ :=
    RD.dogBarkVatUrnsToExtcodesize hpatch rd2941 hmem hread64 hov
  obtain ⟨gasWord, k', C', rd3007⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨2992⟩) (okPc := ⟨3004⟩)
      rd2992 hcodeSize
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (dogPatchedJumpDest hpatch (by native_decide))
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega)
  exact ⟨gasWord, k', C', by simpa using rd3007⟩

theorem RD.dogBarkVatUrnsPostStaticcall {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {ret sel : UInt256} {R : List UInt256}
    {k C : ℕ} {mem rdata : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2885⟩
      (⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 24 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I g (initState cA gh bl σ σ₀ g A I) ⟨3008⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
          ret :: sel :: R)
        (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out (cA', σ') k' C'
      ∧ typedCallViaEVM (config v) (initState cA gh bl σ σ₀ g A I)
          (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
          [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
          (z,
            { initState cA gh bl σ σ₀ g A I with
                accountMap := σ', substate := A', createdAccounts := cA' },
            out) false
      ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd3007⟩ :=
    RD.dogBarkVatUrnsToStaticcall hpatch h hmem hread64 hcodeSize hov
  obtain ⟨cA', σ', z, out, A_in, callGas, k', C', hΘpack, rd3008raw, hosz⟩ :=
    RD.uniswapStaticcall rd3007
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k', C', ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat) = UInt256.ofNat 7 := by
      native_decide
    change RD code I g (initState cA gh bl σ σ₀ g A I) ⟨3008⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
        ret :: sel :: R)
      (out.write 0 (barkVatUrnsCallMem I mem) 128
        (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
      (UInt256.ofNat 7) out (cA', σ') k' C'
    exact haw ▸ rd3008raw
  · have hdepthNe : (initState cA gh bl σ σ₀ g A I).executionEnv.depth ≠ 1024 := by
      intro hdepthEq
      exact absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from hdepthEq]; decide)
    have hΘ' :
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (barkVatWord v))
            (toExecute σ (AccountAddress.ofUInt256 (barkVatWord v)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((barkVatUrnsCallMem I mem).readWithPadding 128 68)
            (I.depth + 1) I.header false := by
      simpa [initState] using hΘ
    have htargetNorm :
        AccountAddress.ofUInt256 (barkVatWord v) =
          EVM.address ↑(AccountAddress.ofNat v.vat.toNat) := by
      rw [← barkVat_eq_vatKey v]
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact (Nat.mod_eq_of_lt (AccountAddress.ofNat v.vat.toNat).isLt).symm
    have hΘcall :
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ σ₀ A_in
            I.codeOwner I.sender (EVM.address (AccountAddress.ofNat v.vat.toNat))
            (toExecute σ (EVM.address (AccountAddress.ofNat v.vat.toNat)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((barkVatUrnsCallMem I mem).readWithPadding 128 68)
            (I.depth + 1) I.header false := by
      simpa [accountAddress_roundtrip I.codeOwner, htargetNorm] using hΘ'
    refine ⟨(barkVatUrnsCallMem I mem).readWithPadding 128 68,
      barkVatUrnsEncode_eq (v := v) (I := I) (mem := mem) hsz100 hmem, ?_⟩
    exact callViaEVM.callMade (perm := false) wordOfInt_zero.symm
      ⟨callGas, A_in, by simpa [initState] using hΘcall⟩ rfl
      (by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _)
      hdepthNe

theorem RD.dogBarkVatUrnsCallFailure {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3008⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨3008⟩) (okPc := ⟨3024⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hrdataSize hov

theorem RD.dogBarkVatUrnsCallSuccessToDecode {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3008⟩ (⟨1⟩ :: d0 :: d1 :: d2 :: R)
      mem aw rdata acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3026⟩ (d0 :: d1 :: d2 :: R)
      mem aw rdata acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨3008⟩) (okPc := ⟨3024⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.dogBarkVatUrnsReturnDecodeShortReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3026⟩ (d0 :: d1 :: d2 :: R)
      (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hshort : out.size < 64) (hout : out.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  have rdPop0 := RD.pop rd
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ (UInt256.ofNat 7) rdPush64
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (barkVatUrnsPostCallMem_mload64 hmem hread64 hshort hout)
    (by decide)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush64' := RD.push1 rdReturndatasize ⟨64⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush64'
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hshort
  have rdIszero := RD.iszero rdLt
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨3046⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatUrnsReturnDecodeOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3026⟩
      (⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I ::
        barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3061⟩
      (barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out acc k' C' := by
  have hmload64 := barkVatUrnsPostCallMem_mload64_long (I := I) hmem hread64 hlong hout
  have hmload128 := barkVatUrnsPostCallMem_mload128_long (I := I) hmem hlong hout
  have hmload160 := barkVatUrnsPostCallMem_mload160_long (I := I) hmem hlong hout
  have hlt : UInt256.lt (UInt256.ofNat out.size) (⟨64⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, ulit_toNat' out.size hout]
    exact hlong
  have rd3036 := evm_run rd with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3037raw := RD.lt rd3036
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3037 := by
    simpa [hlt] using rd3037raw
  have rd3043 := evm_run rd3037 with [
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3046⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3046 := rd3043.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    one_ne_zero_uint (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd3054 := evm_run rd3046 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 (barkVatUrnsInkWord out) (UInt256.ofNat 7)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload128 (by decide) (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3055raw := RD.add rd3054
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨k3055, C3055, rd3055⟩ :
      ∃ k3055 C3055, RD code I g s0 ⟨3055⟩
        (⟨160⟩ :: barkVatUrnsInkWord out :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
          barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
        (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out acc k3055 C3055 := by
    exact ⟨_, _, by simpa using rd3055raw⟩
  have rd3061 := evm_run rd3055 with [
    raw mload 0 (barkVatUrnsArtWord out) (UInt256.ofNat 7)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload160 (by decide) (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa using rd3061⟩

theorem RD.dogBarkVatUrnsMaterializeTuple {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3061⟩
      (barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsPostCallMem I mem out) (UInt256.ofNat 7) out acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3070⟩
      (barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsTupleMem I mem out) (UInt256.ofNat 8) out acc k' C' := by
  have hmload64 := barkVatUrnsPostCallMem_mload64_long (I := I) hmem hread64 hlong hout
  have hmask0 :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) ⟨0⟩ =
        ⟨0⟩ := by
    native_decide
  have rd3067 := evm_run rd with [
    raw push2 ⟨3068⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4641⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4641 := rd3067.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd4651prefix := evm_run rd4641 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨128⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4652 := rd4651prefix.mstore 0 (barkVatUrnsTupleFreeMem I mem out)
    (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      rw [show ((⟨128⟩ : UInt256) + ⟨128⟩) = ⟨256⟩ by native_decide]
      dsimp [barkVatUrnsTupleFreeMem, Reasoning.Theory.writeWord]
      rw [show (⟨64⟩ : UInt256).toNat = 64 by native_decide])
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4665prefix := evm_run rd4652 with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4666 := rd4665prefix.mstore 0 (barkVatUrnsTupleWord0Mem I mem out)
    (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatUrnsTupleWord0Mem, barkVatUrnsTupleFreeMem,
        Reasoning.Theory.writeWord]
      rw [hmask0, show (⟨128⟩ : UInt256).toNat = 128 by native_decide])
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4672prefix := evm_run rd4666 with [
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4673 := rd4672prefix.mstore 0 (barkVatUrnsTupleWord1Mem I mem out)
    (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatUrnsTupleWord1Mem, barkVatUrnsTupleWord0Mem,
        barkVatUrnsTupleFreeMem, Reasoning.Theory.writeWord]
      rw [show ((⟨32⟩ : UInt256) + ⟨128⟩).toNat = 160 by native_decide])
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4679prefix := evm_run rd4673 with [
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4680 := rd4679prefix.mstore 0 (barkVatUrnsTupleWord2Mem I mem out)
    (UInt256.ofNat 7)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatUrnsTupleWord2Mem, barkVatUrnsTupleWord1Mem,
        barkVatUrnsTupleWord0Mem, barkVatUrnsTupleFreeMem, Reasoning.Theory.writeWord]
      rw [show ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ⟨128⟩)).toNat = 192 by
        native_decide])
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4686prefix := evm_run rd4680 with [
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4687 := rd4686prefix.mstore 3 (barkVatUrnsTupleMem I mem out)
    (UInt256.ofNat 8)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatUrnsTupleMem, barkVatUrnsTupleWord2Mem, barkVatUrnsTupleWord1Mem,
        barkVatUrnsTupleWord0Mem, barkVatUrnsTupleFreeMem, Reasoning.Theory.writeWord]
      rw [show
        ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ((⟨32⟩ : UInt256) + ⟨128⟩))).toNat =
          224 by native_decide])
    (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4689 := evm_run rd4687 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3068 := rd4689.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd3070 := evm_run rd3068 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa using rd3070⟩

theorem RD.dogBarkLoadIlkFields {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem out : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3070⟩
      (barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatUrnsTupleMem I mem out) (UInt256.ofNat 8) out (cA, σ) k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) out (cA, σ) k' C' := by
  have hslot := barkIlksHashMem_slot (I := I) (mem := mem) (out := out) hmem hlong hout
  have hmload64 := barkIlksHashMem_mload64 (I := I) (mem := mem) (out := out)
    hmem hlong hout
  have hmask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rdMstore0Prefix := evm_run rd with [
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0
    (wordAt0Mem (barkIlkWord I) (barkVatUrnsTupleMem I mem out))
    (UInt256.ofNat 8)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (barkIlksHashMem I mem out)
    (UInt256.ofNat 8)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (barkIlksSlot I) (UInt256.ofNat 8)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost hslot (by native_decide) (by evm_ov)
  have rdAllocPrefix := evm_run rdSlot with [
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨256⟩ (UInt256.ofNat 8)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw push1 ⟨128⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdAfterAlloc := rdAllocPrefix.mstore 0 (barkIlksAllocMem I mem out)
    (UInt256.ofNat 8)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkIlksAllocMem, Reasoning.Theory.writeWord]
      rw [show ((⟨256⟩ : UInt256) + ⟨128⟩) = ⟨384⟩ by native_decide,
        show (⟨64⟩ : UInt256).toNat = 64 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rdBeforeClipLoad := rdAfterAlloc.dup2
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  obtain ⟨_, _, rdAfterClipLoad⟩ := rdBeforeClipLoad.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdClipStorePrefix := evm_run rdAfterClipLoad with [
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  rw [hmask] at rdClipStorePrefix
  have rdAfterClipStore := rdClipStorePrefix.mstore 3 (barkIlksClipMem σ I mem out)
    (UInt256.ofNat 9)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkIlksClipMem, barkIlksClipWord, solcSlotWord, Reasoning.Theory.writeWord]
      rw [show (⟨256⟩ : UInt256).toNat = 256 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rdChopLoadPrefix := evm_run rdAfterClipStore with [
    raw swap5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdAfterChopLoad⟩ := rdChopLoadPrefix.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdChopStorePrefix := evm_run rdAfterChopLoad with [
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdAfterChopStore := rdChopStorePrefix.mstore 3 (barkIlksChopMem σ I mem out)
    (UInt256.ofNat 10)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkIlksChopMem, barkIlksChopWord, solcSlotWord, Reasoning.Theory.writeWord]
      rw [show ((⟨256⟩ : UInt256) + ⟨32⟩).toNat = 288 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rdHoleLoadPrefix := evm_run rdAfterChopStore with [
    raw push1 ⟨2⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdAfterHoleLoad⟩ := rdHoleLoadPrefix.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdHoleStorePrefix := evm_run rdAfterHoleLoad with [
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rdAfterHoleStore := rdHoleStorePrefix.mstore 3 (barkIlksHoleMem σ I mem out)
    (UInt256.ofNat 11)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkIlksHoleMem, barkIlksHoleWord, solcSlotWord, Reasoning.Theory.writeWord]
      rw [show ((⟨64⟩ : UInt256) + ⟨256⟩).toNat = 320 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rdDirtLoadPrefix := evm_run rdAfterHoleStore with [
    raw push1 ⟨3⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdAfterDirtLoad⟩ := rdDirtLoadPrefix.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rdDirtStorePrefix := evm_run rdAfterDirtLoad with [
    raw push1 ⟨96⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdDirtStorePrefix3138⟩ : ∃ kD C_D,
      RD code I g s0 ⟨3138⟩
        (((⟨256⟩ : UInt256) + ⟨96⟩) :: barkIlksDirtWord σ I ::
          ⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
          barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
          barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
        (barkIlksHoleMem σ I mem out) (UInt256.ofNat 11) out (cA, σ) kD C_D := by
    exact ⟨_, _, by simpa [barkIlksDirtWord, solcSlotWord] using rdDirtStorePrefix⟩
  have rdAfterDirtStore := rdDirtStorePrefix3138.mstore 3 (barkIlksMem σ I mem out)
    (UInt256.ofNat 12)
    (by
      exact dogDecodePatchedNoArg (pc := ⟨3138⟩) (byte := 0x52) (op := .MSTORE)
        hpatch (by native_decide)
        (by native_decide)
        (by native_decide) (by native_decide) (by native_decide))
    mem_cost
    (by
      dsimp [barkIlksMem, barkIlksDirtWord, solcSlotWord, Reasoning.Theory.writeWord]
      rw [show ((⟨256⟩ : UInt256) + ⟨96⟩).toNat = 352 by native_decide])
    (by native_decide)
    (by evm_ov)
  exact ⟨_, _, by simpa using rdAfterDirtStore⟩

theorem RD.dogBarkVatIlksToCallMload {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) rdata (cA, σ) k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3160⟩
      (⟨384⟩ :: ⟨384⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatIlksCallMem σ I mem out) (UInt256.ofNat 14) rdata (cA, σ) k' C' := by
  have hmload64 := barkIlksMem_mload64 (σ := σ) (I := I) (mem := mem) (out := out)
    hmem hlong hout
  have hmloadCall := barkVatIlksCallMem_mload64 (σ := σ) (I := I) (mem := mem)
    (out := out) hmem hlong hout
  have rd3150prefix := evm_run rd with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 12)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by native_decide) (by evm_ov),
    raw push4 ⟨1823590043⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨225⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3151 := rd3150prefix.mstore 3 (barkVatIlksSelectorMem σ I mem out)
    (UInt256.ofNat 13)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatIlksSelectorMem, barkVatIlksSelectorWord, Reasoning.Theory.writeWord]
      rw [show (⟨384⟩ : UInt256).toNat = 384 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rd3157prefix := evm_run rd3151 with [
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup12
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3158 := rd3157prefix.mstore 3 (barkVatIlksCallMem σ I mem out)
    (UInt256.ofNat 14)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (by
      dsimp [barkVatIlksCallMem, Reasoning.Theory.writeWord]
      rw [show ((⟨384⟩ : UInt256) + ⟨4⟩).toNat = 388 by native_decide])
    (by native_decide)
    (by evm_ov)
  have rd3160 := evm_run rd3158 with [
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 14)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmloadCall (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd3160⟩

theorem RD.dogBarkVatIlksToGasPrep {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3160⟩
      (⟨384⟩ :: ⟨384⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatIlksCallMem σ I mem out) (UInt256.ofNat 14) rdata (cA, σ) k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3204⟩
      (⟨384⟩ :: ⟨384⟩ :: barkVatWord v :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨256⟩ :: barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatIlksCallMem σ I mem out) (UInt256.ofNat 14) rdata (cA, σ) k' C' := by
  have hvatCleanR :
      UInt256.land (barkVatWord v) solcAddrMask = barkVatWord v :=
    solcAddrMask_clean (barkVatWord_canonical v)
  have rd3169 := evm_run rd with [
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3202 := rd3169.pushConst (barkVatWord v) (width := 32) (op := .PUSH32)
    (hop := by decide)
    (by simpa [barkVatWord] using dogBarkVatConstDecode3169 hpatch)
    (by evm_ov)
  have rd3204 := evm_run rd3202 with [
    raw and
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa [hvatCleanR] using rd3204⟩

theorem RD.dogBarkVatIlksToExtcodesize {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) rdata (cA, σ) k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3229⟩
      (barkVatWord v :: barkVatWord v :: ⟨384⟩ :: ⟨36⟩ :: ⟨384⟩ :: ⟨160⟩ ::
        ⟨420⟩ :: ⟨3647180086⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨256⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatIlksCallMem σ I mem out) (UInt256.ofNat 14) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd3160⟩ :=
    RD.dogBarkVatIlksToCallMload hpatch rd hmem hlong hout hov
  obtain ⟨_, _, rd3204⟩ :=
    RD.dogBarkVatIlksToGasPrep hpatch rd3160 hov
  have rd3229 := evm_run rd3204 with [
    raw push4 ⟨3647180086⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨36⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by
    simpa [show UInt256.sub (⟨384⟩ : UInt256) ⟨384⟩ = ⟨0⟩ by native_decide,
      show ((⟨0⟩ : UInt256) + ⟨36⟩) = ⟨36⟩ by native_decide,
      show ((⟨384⟩ : UInt256) + ⟨36⟩) = ⟨420⟩ by native_decide]
      using rd3229⟩

theorem RD.dogBarkVatIlksToStaticcall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) rdata (cA, σ) k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hov : R.length + 40 ≤ 1024) :
    ∃ gasWord k' C', RD code I g s0 ⟨3244⟩
      (gasWord :: barkVatWord v :: ⟨384⟩ :: ⟨36⟩ :: ⟨384⟩ :: ⟨160⟩ ::
        ⟨420⟩ :: ⟨3647180086⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨256⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatIlksCallMem σ I mem out) (UInt256.ofNat 14) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd3229⟩ :=
    RD.dogBarkVatIlksToExtcodesize hpatch rd hmem hlong hout (by omega)
  obtain ⟨gasWord, k', C', rd3244⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨3229⟩) (okPc := ⟨3241⟩)
      rd3229 hcodeSize
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (dogPatchedJumpDest hpatch (by native_decide))
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega)
  exact ⟨gasWord, k', C', by simpa using rd3244⟩

theorem RD.dogBarkVatIlksPostStaticcall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 evm : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) rdata (cA, σ) k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hevmEnv : evm.executionEnv = I)
    (hevmCreated : evm.createdAccounts = cA)
    (hevmMap : evm.accountMap = σ)
    (hevmGenesis : evm.genesisBlockHeader = s0.genesisBlockHeader)
    (hevmBlocks : evm.blocks = s0.blocks)
    (hevmOrig : evm.σ₀ = s0.σ₀)
    (hdepth : I.depth.val < 1024)
    (hov : R.length + 40 ≤ 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (outIlks : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD code I g s0 ⟨3245⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨420⟩ :: ⟨3647180086⟩ :: barkVatWord v ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨256⟩ ::
          barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
          barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
        (barkVatIlksPostCallMem σ I mem out outIlks) (UInt256.ofNat 17) outIlks
        (cA', σ') k' C'
      ∧ typedCallViaEVM (config v) evm
          (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
          [.fixedBytes bytes32Width (barkIlkBytes I)]
          (z,
            { evm with accountMap := σ', substate := A', createdAccounts := cA' },
            outIlks) false
      ∧ outIlks.size < UInt256.size := by
  obtain ⟨_, _, _, rd3244⟩ :=
    RD.dogBarkVatIlksToStaticcall hpatch rd hmem hlong hout hcodeSize hov
  obtain ⟨cA', σ', z, outIlks, A_in, callGas, k', C', hΘpack, rd3245raw, hosz⟩ :=
    RD.uniswapStaticcall rd3244
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hdepth
      (by simp only [List.length_cons]; omega)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, outIlks, A', k', C', ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 14).toNat
          (⟨384⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat)
          (⟨384⟩ : UInt256).toNat (⟨160⟩ : UInt256).toNat) = UInt256.ofNat 17 := by
      native_decide
    change RD code I g s0 ⟨3245⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨420⟩ :: ⟨3647180086⟩ :: barkVatWord v ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨256⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (outIlks.write 0 (barkVatIlksCallMem σ I mem out) 384
        (min (⟨160⟩ : UInt256) (UInt256.ofNat outIlks.size)).toNat)
      (UInt256.ofNat 17) outIlks (cA', σ') k' C'
    exact haw ▸ rd3245raw
  · have hdepthNe : evm.executionEnv.depth ≠ 1024 := by
      intro hdepthEq
      exact absurd hdepth (by rw [← hevmEnv, hdepthEq]; decide)
    have htargetNorm :
        EVM.address ↑(AccountAddress.ofNat v.vat.toNat) =
          AccountAddress.ofUInt256 (barkVatWord v) := by
      rw [← barkVat_eq_vatKey v]
      apply Fin.ext
      simp [EVM.address, EVM.uintN]
      exact Nat.mod_eq_of_lt (AccountAddress.ofNat v.vat.toNat).isLt
    have hΘ' :
        (cA', σ', g'', A', z, outIlks) =
          Ethereum.EVM.Θ evm.executionEnv.blobVersionedHashes evm.createdAccounts
            evm.genesisBlockHeader evm.blocks evm.accountMap evm.σ₀ A_in
            (AccountAddress.ofUInt256 (UInt256.ofNat evm.executionEnv.codeOwner))
            evm.executionEnv.sender (AccountAddress.ofUInt256 (barkVatWord v))
            (toExecute evm.accountMap (AccountAddress.ofUInt256 (barkVatWord v)))
            callGas (UInt256.ofNat evm.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
            ((barkVatIlksCallMem σ I mem out).readWithPadding 384 36)
            (evm.executionEnv.depth + 1) evm.executionEnv.header false := by
      simpa [hevmEnv, hevmCreated, hevmMap, hevmGenesis, hevmBlocks, hevmOrig] using hΘ
    exact Reasoning.Theory.callCoincides
      (cfg := config v) (evm := evm) (name := "ilks")
      (args := [.fixedBytes bytes32Width (barkIlkBytes I)])
      (tgt := EVM.address (AccountAddress.ofNat v.vat.toNat))
      (targetWord := barkVatWord v) (cA' := cA') (σ' := σ') (A' := A')
      (A_in := A_in) (z := z) (o := outIlks) (g'' := g'') (callGas := callGas)
      (mem := barkVatIlksCallMem σ I mem out) (inOff := ⟨384⟩) (inSize := ⟨36⟩)
      (callPerm := false) hdepthNe htargetNorm
      (barkVatIlksEncode_eq (v := v) (σ := σ) (I := I) (mem := mem) (out := out)
        hsz100 hmem hlong hout)
      hΘ'

theorem RD.dogBarkVatIlksNoCodeRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {mem out rdata : ByteArray} {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3139⟩
      (⟨64⟩ :: ⟨256⟩ :: solcAddrMask :: ⟨0⟩ ::
        barkVatUrnsArtWord out :: barkVatUrnsInkWord out :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkIlksMem σ I mem out) (UInt256.ofNat 12) rdata (cA, σ) k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) = ⟨0⟩)
    (hov : R.length + 40 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, rd3229⟩ :=
    RD.dogBarkVatIlksToExtcodesize hpatch rd hmem hlong hout (by omega)
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨3229⟩) (okPc := ⟨3241⟩)
    rd3229 hcodeSize
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatIlksCallFailure {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3245⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨3245⟩) (okPc := ⟨3261⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hrdataSize hov

theorem RD.dogBarkVatIlksCallSuccessToDecode {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 ret sel : UInt256}
    {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3245⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 ::
        d10 :: d11 :: d12 :: d13 :: ret :: sel :: R)
      mem aw out acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3263⟩
      (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 ::
        d10 :: d11 :: d12 :: d13 :: ret :: sel :: R)
      mem aw out acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨3245⟩) (okPc := ⟨3261⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatIlksReturnDecodeShortReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {σ : AccountMap}
    {mem out outIlks : ByteArray} {k C : ℕ}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 ret sel : UInt256}
    {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3263⟩
      (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 ::
        d10 :: d11 :: d12 :: d13 :: ret :: sel :: R)
      (barkVatIlksPostCallMem σ I mem out outIlks) (UInt256.ofNat 17) outIlks acc k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hshort : outIlks.size < 160) (houtIlks : outIlks.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    RDrev code g s0 := by
  have rdPop0 := RD.pop rd
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdMload64 := RD.mload 0 ⟨384⟩ (UInt256.ofNat 17) rdPush64
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    mem_cost
    (barkVatIlksPostCallMem_mload64 hmem hlong hout hshort houtIlks)
    (by decide)
    (by simp only [List.length_cons]; omega)
  have rdReturndatasize := RD.returndatasize rdMload64
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPush160 := RD.push1 rdReturndatasize ⟨160⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush160
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat outIlks.size) (⟨160⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      ulit_toNat' outIlks.size houtIlks]
    exact hshort
  have rdIszero := RD.iszero rdLt
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero ⟨3283⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat outIlks.size) (⟨160⟩ : UInt256)) =
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatIlksReturnDecodeOkToSpotGuard {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {σ : AccountMap}
    {mem out outIlks : ByteArray} {k C : ℕ}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 ret sel : UInt256}
    {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd : RD code I g s0 ⟨3263⟩
      (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: d6 :: d7 :: d8 :: d9 ::
        d10 :: d11 :: d12 :: d13 :: ret :: sel :: R)
      (barkVatIlksPostCallMem σ I mem out outIlks) (UInt256.ofNat 17) outIlks acc k C)
    (hmem : mem.size = 96) (hlong : 64 ≤ out.size) (hout : out.size < UInt256.size)
    (hlongIlks : 160 ≤ outIlks.size) (houtIlks : outIlks.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3308⟩
      (barkVatIlksSpotWord outIlks :: barkVatIlksDustWord outIlks ::
        barkVatIlksRateWord outIlks :: d6 :: d7 :: d8 :: d9 :: d10 ::
        d11 :: d12 :: d13 :: ret :: sel :: R)
      (barkVatIlksPostCallMem σ I mem out outIlks) (UInt256.ofNat 17) outIlks acc k' C' := by
  have hmload64 := barkVatIlksPostCallMem_mload64_long (σ := σ) (I := I)
    hmem hlong hout hlongIlks houtIlks
  have hmload416 := barkVatIlksPostCallMem_mload416_long (σ := σ) (I := I)
    hmem hlong hout hlongIlks houtIlks
  have hmload448 := barkVatIlksPostCallMem_mload448_long (σ := σ) (I := I)
    hmem hlong hout hlongIlks houtIlks
  have hmload512 := barkVatIlksPostCallMem_mload512_long (σ := σ) (I := I)
    hmem hlong hout hlongIlks houtIlks
  have hlt : UInt256.lt (UInt256.ofNat outIlks.size) (⟨160⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨160⟩ : UInt256).toNat = 160 from by decide,
      ulit_toNat' outIlks.size houtIlks]
    exact hlongIlks
  have rd3272 := evm_run rd with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw returndatasize
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3273raw := RD.lt rd3272
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3273 := by
    simpa [hlt] using rd3273raw
  have rd3275 := evm_run rd3273 with [
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3283⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hcond : UInt256.isZero (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by
    decide
  have rd3283 := RD.jumpiT rd3275
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_cons]; omega)
  have rd3288pre := evm_run rd3283 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3289addrRaw := RD.add rd3288pre
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hadd416 : (⟨384⟩ : UInt256) + ⟨32⟩ = ⟨416⟩ := by
    native_decide
  have rd3289addr := by
    simpa [hadd416] using rd3289addrRaw
  have rd3293pre := evm_run rd3289addr with [
    raw mload 0 (barkVatIlksRateWord outIlks) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload416 (by decide) (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3294addrRaw := RD.add rd3293pre
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hadd448 : (⟨384⟩ : UInt256) + ⟨64⟩ = ⟨448⟩ := by
    native_decide
  have rd3294addr := by
    simpa [hadd448] using rd3294addrRaw
  have rd3299pre := evm_run rd3294addr with [
    raw mload 0 (barkVatIlksSpotWord outIlks) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload448 (by decide) (by evm_ov),
    raw push1 ⟨128⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3300addrRaw := RD.add rd3299pre
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hadd512 : (⟨384⟩ : UInt256) + ⟨128⟩ = ⟨512⟩ := by
    native_decide
  have rd3300addr := by
    simpa [hadd512] using rd3300addrRaw
  have rd3308 := evm_run rd3300addr with [
    raw mload 0 (barkVatIlksDustWord outIlks) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload512 (by decide) (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa using rd3308⟩

theorem RD.dogBarkPostIlksErrorStringRevertTail {code : ByteArray} {g : Sat256}
    {s0 : EVM.State} {I : ExecutionEnv} {k C : ℕ}
    {pc len rawWord shift word : UInt256} {op : Operation.POp} {width : ℕ}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
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
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 17)
      (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by native_decide)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread64)
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

@[reducible] def dogPostIlksErrorStringFullWordTailWf
    (code : ByteArray) (pc len word : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p8 := p4 + UInt256.ofNat 4
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p68 := p27 + UInt256.ofNat 33
  let pDup3 := p68 + UInt256.ofNat 2
  let pAdd := pDup3 + ⟨1⟩
  let pMstore3 := pAdd + ⟨1⟩
  let pSwap := pMstore3 + ⟨1⟩
  let pMload := pSwap + ⟨1⟩
  let pSwap2 := pMload + ⟨1⟩
  let pDup2 := pSwap2 + ⟨1⟩
  let pSwap3 := pDup2 + ⟨1⟩
  let pSub := pSwap3 + ⟨1⟩
  let p100 := pSub + ⟨1⟩
  let pAdd2 := p100 + UInt256.ofNat 2
  let pSwap4 := pAdd2 + ⟨1⟩
  let pRev := pSwap4 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.MLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p17 = some (.DUP3, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (len, 1))
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.MSTORE, .none)
  ∧ decode code p27 = some (.Push .PUSH32, some (word, 32))
  ∧ decode code p68 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode code pDup3 = some (.DUP3, .none)
  ∧ decode code pAdd = some (.ADD, .none)
  ∧ decode code pMstore3 = some (.MSTORE, .none)
  ∧ decode code pSwap = some (.SWAP1, .none)
  ∧ decode code pMload = some (.MLOAD, .none)
  ∧ decode code pSwap2 = some (.SWAP1, .none)
  ∧ decode code pDup2 = some (.DUP2, .none)
  ∧ decode code pSwap3 = some (.SWAP1, .none)
  ∧ decode code pSub = some (.SUB, .none)
  ∧ decode code p100 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode code pAdd2 = some (.ADD, .none)
  ∧ decode code pSwap4 = some (.SWAP1, .none)
  ∧ decode code pRev = some (.REVERT, .none)

theorem RD.dogBarkPostIlksErrorStringRevertTailFullWord {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv} {k C : ℕ}
    {pc len word : UInt256} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code I g s0 pc stk mem (UInt256.ofNat 17) rdata acc k C)
    (hwf : dogPostIlksErrorStringFullWordTailWf code pc len word)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd68, hdDup3, hdAdd,
      hdMstore3, hdSwap, hdMload, hdSwap2, hdDup2, hdSwap3, hdSub, hd100,
      hdAdd2, hdSwap4, hdRev⟩
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ :=
    mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 17)
      (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by native_decide)
      (by
        simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread64)
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
  have rdWord := rdPrefix.pushConst word (width := 32) (op := .PUSH32)
    (by decide) hd27 (by simp only [List.length_cons]; omega)
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

theorem RD.dogBarkSpotZeroReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot = ⟨0⟩)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata acc k C)
    (hov : R.length + 24 ≤ 1024) :
    RDrev code g s0 := by
  have htail : solcErrorStringRevertTailWf code ⟨3344⟩ ⟨14⟩
      dogNotUnsafeRawWord ⟨144⟩ .PUSH14 14 := by
    unfold solcErrorStringRevertTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]; native_decide)
  have rd3316 := evm_run rd3308 with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3339⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hjump : UInt256.isZero spot ≠ ⟨0⟩ := by
    rw [hspot]
    decide
  have rd3339 := rd3316.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hjump (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3343 := evm_run rd3339 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3405⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hfall : UInt256.isZero (UInt256.isZero spot) = ⟨0⟩ := by
    rw [hspot]
    decide
  have rd3344 := rd3343.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hfall (by evm_ov)
  have hpc3344 : (⟨3339⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ = ⟨3344⟩ := by
    native_decide
  have rd3344pc := rd3344
  rw [hpc3344] at rd3344pc
  exact RD.dogBarkPostIlksErrorStringRevertTail
    (pc := ⟨3344⟩) (len := ⟨14⟩) (rawWord := dogNotUnsafeRawWord)
    (shift := ⟨144⟩) (word := UInt256.shiftLeft dogNotUnsafeRawWord ⟨144⟩)
    (op := .PUSH14) (width := 14) rd3344pc htail (by decide) (by rfl) hmem hread64
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkArtRateOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256} {aw : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hoverArt : UInt256.size ≤ art.toNat * rate.toNat)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem aw rdata acc k C)
    (hov : R.length + 27 ≤ 1024) :
    RDrev code g s0 := by
  have rd3316 := evm_run rd3308 with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3339⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hzero : UInt256.isZero spot = ⟨0⟩ := isZero_eq_zero_of_ne hspot
  have rd3317 := rd3316.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hzero (by evm_ov)
  have rd3326 := evm_run rd3317 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3327⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3326.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedMulOverflowReverts (v := v) hpatch
    (R := spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
      kpr :: urn :: ilk :: ret :: sel :: R)
    (x := art) (y := rate) (ret := ⟨3327⟩)
    (by simp only [List.length_cons]; omega) hoverArt rd4564

theorem RD.dogBarkInkSpotOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256} {aw : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hfitArt : art.toNat * rate.toNat < UInt256.size)
    (hoverInk : UInt256.size ≤ ink.toNat * spot.toNat)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem aw rdata acc k C)
    (hov : R.length + 28 ≤ 1024) :
    RDrev code g s0 := by
  have rd3316 := evm_run rd3308 with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3339⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hzero : UInt256.isZero spot = ⟨0⟩ := isZero_eq_zero_of_ne hspot
  have rd3317 := rd3316.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hzero (by evm_ov)
  have rd3326 := evm_run rd3317 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3327⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564art := rd3326.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3327⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (R := spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      (x := art) (y := rate) (ret := ⟨3327⟩)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitArt rd4564art
  have rd3336 := evm_run rd3327 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3337⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564ink := rd3336.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedMulOverflowReverts (v := v) hpatch
    (R := art * rate :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink ::
      ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
    (x := ink) (y := spot) (ret := ⟨3337⟩)
    (by simp only [List.length_cons]; omega) hoverInk rd4564ink

theorem RD.dogBarkNotUnsafeReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hfitArt : art.toNat * rate.toNat < UInt256.size)
    (hfitInk : ink.toNat * spot.toNat < UInt256.size)
    (hnotLt : (art * rate).toNat ≤ (ink * spot).toNat)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata acc k C)
    (hov : R.length + 28 ≤ 1024) :
    RDrev code g s0 := by
  have htail : solcErrorStringRevertTailWf code ⟨3344⟩ ⟨14⟩
      dogNotUnsafeRawWord ⟨144⟩ .PUSH14 14 := by
    unfold solcErrorStringRevertTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
  have rd3316 := evm_run rd3308 with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3339⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hzero : UInt256.isZero spot = ⟨0⟩ := isZero_eq_zero_of_ne hspot
  have rd3317 := rd3316.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hzero (by evm_ov)
  have rd3326 := evm_run rd3317 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3327⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564art := rd3326.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3327⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (R := spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      (x := art) (y := rate) (ret := ⟨3327⟩)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitArt rd4564art
  have rd3336 := evm_run rd3327 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3337⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564ink := rd3336.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3337⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (R := art * rate :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (x := ink) (y := spot) (ret := ⟨3337⟩)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitInk rd4564ink
  have hlt : UInt256.lt (ink * spot) (art * rate) = ⟨0⟩ :=
    Reasoning.Theory.ult_zero hnotLt
  have rd3339raw := evm_run rd3337 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hpc3339 : (⟨3337⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨3339⟩ := by
    native_decide
  have rd3339 := rd3339raw
  rw [hlt, hpc3339] at rd3339
  have rd3343 := evm_run rd3339 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3405⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3344 := rd3343.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by rfl) (by evm_ov)
  have hpc3344 : (⟨3339⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ = ⟨3344⟩ := by
    native_decide
  have rd3344pc := rd3344
  rw [hpc3344] at rd3344pc
  exact RD.dogBarkPostIlksErrorStringRevertTail
    (pc := ⟨3344⟩) (len := ⟨14⟩) (rawWord := dogNotUnsafeRawWord)
    (shift := ⟨144⟩) (word := UInt256.shiftLeft dogNotUnsafeRawWord ⟨144⟩)
    (op := .PUSH14) (width := 14) rd3344pc htail (by decide) (by rfl) hmem hread64
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkSafeToLimitGuard {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hfitArt : art.toNat * rate.toNat < UInt256.size)
    (hfitInk : ink.toNat * spot.toNat < UInt256.size)
    (hsafe : (ink * spot).toNat < (art * rate).toNat)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata acc k C)
    (hov : R.length + 28 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3405⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata acc k' C' := by
  have rd3316 := evm_run rd3308 with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3339⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hzero : UInt256.isZero spot = ⟨0⟩ := isZero_eq_zero_of_ne hspot
  have rd3317 := rd3316.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hzero (by evm_ov)
  have rd3326 := evm_run rd3317 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3327⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564art := rd3326.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3327⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (R := spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      (x := art) (y := rate) (ret := ⟨3327⟩)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitArt rd4564art
  have rd3336 := evm_run rd3327 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3337⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564ink := rd3336.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3337⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (R := art * rate :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (x := ink) (y := spot) (ret := ⟨3337⟩)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitInk rd4564ink
  have hlt : UInt256.lt (ink * spot) (art * rate) = ⟨1⟩ :=
    Reasoning.Theory.ult_one hsafe
  have rd3339raw := evm_run rd3337 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hpc3339 : (⟨3337⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ = ⟨3339⟩ := by
    native_decide
  have rd3339 := rd3339raw
  rw [hlt, hpc3339] at rd3339
  have rd3343 := evm_run rd3339 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3405⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3405 := rd3343.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    one_ne_zero_uint (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, by simpa using rd3405⟩

theorem RD.dogBarkLimitGuardOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ σMem : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hfitArt : art.toNat * rate.toNat < UInt256.size)
    (hfitInk : ink.toNat * spot.toNat < UInt256.size)
    (hsafe : (ink * spot).toNat < (art * rate).toNat)
    (hlimit :
      (dogSlotWord ⟨5⟩ σ I).toNat < (dogSlotWord ⟨4⟩ σ I).toNat ∧
        (barkIlksDirtWord σMem I).toNat < (barkIlksHoleWord σMem I).toNat)
    (hmload320 :
      (if (⟨320⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨320⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨320⟩ : UInt256).toNat 32))) =
        barkIlksHoleWord σMem I)
    (hmload352 :
      (if (⟨352⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨352⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
        barkIlksDirtWord σMem I)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 28 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3512⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd3405⟩ :=
    RD.dogBarkSafeToLimitGuard (v := v) (code := code) (ret := ret) (sel := sel)
      (R := R) hpatch hspot hfitArt hfitInk hsafe rd3308 hov
  have rd3408 := evm_run rd3405 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨5⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3409, C3409, rd3409raw⟩ := rd3408.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd3409 : RD code I g s0 ⟨3409⟩
      (dogSlotWord ⟨5⟩ σ I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k3409 C3409 := by
    simpa [dogSlotWord, solcSlotWord] using rd3409raw
  have rd3411 := evm_run rd3409 with [
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3412, C3412, rd3412raw⟩ := rd3411.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd3412 : RD code I g s0 ⟨3412⟩
      (dogSlotWord ⟨4⟩ σ I :: dogSlotWord ⟨5⟩ σ I :: spot :: dust :: rate ::
        ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k3412 C3412 := by
    simpa [dogSlotWord, solcSlotWord] using rd3412raw
  have hgtGlobal :
      UInt256.gt (dogSlotWord ⟨4⟩ σ I) (dogSlotWord ⟨5⟩ σ I) = ⟨1⟩ :=
    Reasoning.Theory.ugt_one hlimit.1
  have rd3413raw := evm_run rd3412 with [
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3413 := rd3413raw
  rw [hgtGlobal] at rd3413
  have rd3418raw := evm_run rd3413 with [
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3431⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3418 := rd3418raw
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3418
  have rd3419 := rd3418.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by rfl) (by evm_ov)
  have rd3423 := evm_run rd3419 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨96⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3424raw := RD.add rd3423
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd352 : (⟨96⟩ : UInt256) + ⟨256⟩ = ⟨352⟩ := by
    native_decide
  have rd3424 := by
    simpa [hadd352] using rd3424raw
  have rd3425 := evm_run rd3424 with [
    raw mload 0 (barkIlksDirtWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload352 (by decide) (by evm_ov)]
  have rd3428 := evm_run rd3425 with [
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3429raw := RD.add rd3428
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd320 : (⟨64⟩ : UInt256) + ⟨256⟩ = ⟨320⟩ := by
    native_decide
  have rd3429 := by
    simpa [hadd320] using rd3429raw
  have rd3430 := evm_run rd3429 with [
    raw mload 0 (barkIlksHoleWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload320 (by decide) (by evm_ov)]
  have hgtMilk : UInt256.gt (barkIlksHoleWord σMem I) (barkIlksDirtWord σMem I) = ⟨1⟩ :=
    Reasoning.Theory.ugt_one hlimit.2
  have rd3431raw := evm_run rd3430 with [
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3431 := rd3431raw
  rw [hgtMilk] at rd3431
  have rd3435 := evm_run rd3431 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3512⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3512 := rd3435.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    one_ne_zero_uint (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, by simpa using rd3512⟩

theorem RD.dogBarkComputeRoom {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ σMem : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hmload320 :
      (if (⟨320⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨320⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨320⟩ : UInt256).toNat 32))) =
        barkIlksHoleWord σMem I)
    (hmload352 :
      (if (⟨352⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨352⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
        barkIlksDirtWord σMem I)
    (rd3512 : RD code I g s0 ⟨3512⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3543⟩
      (barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k' C' := by
  have rd3519 := evm_run rd3512 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3540⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨5⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3521, C3521, rd3521raw⟩ := rd3519.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd3521 : RD code I g s0 ⟨3521⟩
      (dogSlotWord ⟨5⟩ σ I :: ⟨3540⟩ :: ⟨0⟩ :: spot :: dust :: rate ::
        ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k3521 C3521 := by
    simpa [dogSlotWord, solcSlotWord] using rd3521raw
  have rd3523prep := evm_run rd3521 with [
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3524, C3524, rd3524raw⟩ := rd3523prep.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd3524 : RD code I g s0 ⟨3524⟩
      (dogSlotWord ⟨4⟩ σ I :: dogSlotWord ⟨5⟩ σ I :: ⟨3540⟩ :: ⟨0⟩ ::
        spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k3524 C3524 := by
    simpa [dogSlotWord, solcSlotWord] using rd3524raw
  have rd3525 := evm_run rd3524 with [
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨96⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3528raw := RD.add rd3525
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd352 : (⟨96⟩ : UInt256) + ⟨256⟩ = ⟨352⟩ := by
    native_decide
  have rd3528 := by
    simpa [hadd352, barkGlobalRoomWord] using rd3528raw
  have rd3529 := evm_run rd3528 with [
    raw mload 0 (barkIlksDirtWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload352 (by decide) (by evm_ov)]
  have rd3533 := evm_run rd3529 with [
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3533raw := RD.add rd3533
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd320 : (⟨64⟩ : UInt256) + ⟨256⟩ = ⟨320⟩ := by
    native_decide
  have rd3533add := by
    simpa [hadd320, barkGlobalRoomWord] using rd3533raw
  have rd3534 := evm_run rd3533add with [
    raw mload 0 (barkIlksHoleWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload320 (by decide) (by evm_ov)]
  have rd3536 := evm_run rd3534 with [
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4600⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4600 := rd3536.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3540⟩ :=
    RD.dogMinReturns (v := v) hpatch (dogPatchedJumpDest hpatch (by native_decide))
      (x := barkGlobalRoomWord σ I) (y := barkIlkRoomWord σMem I)
      (ret := ⟨3540⟩)
      (R := ⟨0⟩ :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      rd4600
      (by simp only [List.length_cons]; omega)
  have rd3543 := evm_run rd3540 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa [barkRoomWord] using rd3543⟩

theorem RD.dogBarkComputeDart {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ σMem : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hfitRoom :
      (barkRoomWord σ σMem I).toNat * dogWadWord.toNat < UInt256.size)
    (hrateNe : rate ≠ ⟨0⟩)
    (hchopNe : barkIlksChopWord σMem I ≠ ⟨0⟩)
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨288⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        barkIlksChopWord σMem I)
    (rd3543 : RD code I g s0 ⟨3543⟩
      (barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3594⟩
      (barkRoomWord σ σMem I :: spot :: dust :: rate ::
        barkDartWord σ σMem I art rate (barkIlksChopWord σMem I) :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k' C' := by
  have rd3548 := evm_run rd3543 with [
    raw push2 ⟨3591⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3550raw := RD.add rd3548
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd288 : (⟨32⟩ : UInt256) + ⟨256⟩ = ⟨288⟩ := by
    native_decide
  have rd3551 := by
    simpa [hadd288] using rd3550raw
  have rd3552 := evm_run rd3551 with [
    raw mload 0 (barkIlksChopWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload288 (by decide) (by evm_ov)]
  have rd3557 := evm_run rd3552 with [
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3570⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3566 := rd3557.pushConst dogWadWord (width := 8) (op := .PUSH8)
    (by decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3569 := evm_run rd3566 with [
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3569.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3570raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := barkRoomWord σ σMem I) (y := dogWadWord) (ret := ⟨3570⟩)
      (R := rate :: barkIlksChopWord σMem I :: art :: ⟨3591⟩ ::
        barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitRoom rd4564
  have rd3575 := evm_run rd3570raw with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3577⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3577 := rd3575.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hrateNe (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3579raw := evm_run rd3577 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw div
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3579 := by
    simpa [barkDartByRateWord] using rd3579raw
  have rd3583 := evm_run rd3579 with [
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3585⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3585 := rd3583.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hchopNe (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3587raw := evm_run rd3585 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw div
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4600⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3587 := by
    simpa [barkDartCandidateWord] using rd3587raw
  have rd4600 := rd3587.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd4600' := by
    simpa [barkDartCandidateWord, barkDartByRateWord, barkRoomWadWord] using rd4600
  obtain ⟨_, _, rd3591⟩ :=
    RD.dogMinReturns (v := v) hpatch (dogPatchedJumpDest hpatch (by native_decide))
      (x := art) (y := barkDartCandidateWord σ σMem I rate (barkIlksChopWord σMem I))
      (ret := ⟨3591⟩)
      (R := barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      rd4600'
      (by simp only [List.length_cons]; omega)
  have rd3594 := evm_run rd3591 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa [barkDartWord] using rd3594⟩

theorem RD.dogBarkRoomWadOverflowReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ σMem : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hoverRoom :
      UInt256.size ≤ (barkRoomWord σ σMem I).toNat * dogWadWord.toNat)
    (hmload288 :
      (if (⟨288⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨288⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨288⟩ : UInt256).toNat 32))) =
        barkIlksChopWord σMem I)
    (rd3543 : RD code I g s0 ⟨3543⟩
      (barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 32 ≤ 1024) :
    RDrev code g s0 := by
  have rd3548 := evm_run rd3543 with [
    raw push2 ⟨3591⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3550raw := RD.add rd3548
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have hadd288 : (⟨32⟩ : UInt256) + ⟨256⟩ = ⟨288⟩ := by
    native_decide
  have rd3551 := by
    simpa [hadd288] using rd3550raw
  have rd3552 := evm_run rd3551 with [
    raw mload 0 (barkIlksChopWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload288 (by decide) (by evm_ov)]
  have rd3557 := evm_run rd3552 with [
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3570⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3566 := rd3557.pushConst dogWadWord (width := 8) (op := .PUSH8)
    (by decide)
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3569 := evm_run rd3566 with [
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3569.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact RD.dogCheckedMulOverflowReverts (v := v) hpatch
    (x := barkRoomWord σ σMem I) (y := dogWadWord) (ret := ⟨3570⟩)
    (R := rate :: barkIlksChopWord σMem I :: art :: ⟨3591⟩ ::
      barkRoomWord σ σMem I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
      art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
    (by simp only [List.length_cons]; omega) hoverRoom rd4564

theorem RD.dogBarkNoLeftoverToDinkEntry {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    {room spot dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hnoLeftover : art.toNat ≤ dart.toNat)
    (rd3594 : RD code I g s0 ⟨3594⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3700⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k' C' := by
  have rd3601 := evm_run rd3594 with [
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtZero : UInt256.gt art dart = ⟨0⟩ :=
    Reasoning.Theory.ugt_zero hnoLeftover
  have hcond : UInt256.isZero (UInt256.gt art dart) ≠ ⟨0⟩ := by
    rw [hgtZero]
    decide
  have rd3700 := rd3601.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, rd3700⟩

theorem RD.dogBarkDustyLeftoverToDinkEntry {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    {room spot dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hleftover : dart.toNat < art.toNat)
    (hfitLeftoverDue : (barkLeftoverArtWord art dart).toNat * rate.toNat < UInt256.size)
    (hdusty : (barkLeftoverDueWord art dart rate).toNat < dust.toNat)
    (rd3594 : RD code I g s0 ⟨3594⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3700⟩
      (room :: spot :: dust :: rate :: art :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k' C' := by
  have rd3601 := evm_run rd3594 with [
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtOne : UInt256.gt art dart = ⟨1⟩ :=
    Reasoning.Theory.ugt_one hleftover
  have hcondNoJump : UInt256.isZero (UInt256.gt art dart) = ⟨0⟩ := by
    rw [hgtOne]
    decide
  have rd3602 := rd3601.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcondNoJump (by evm_ov)
  have rd3613 := evm_run rd3602 with [
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3614⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup10
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3613.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3614raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := barkLeftoverArtWord art dart) (y := rate) (ret := ⟨3614⟩)
      (R := dust :: room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitLeftoverDue rd4564
  have rd3614 := by
    simpa [barkLeftoverDueWord, barkLeftoverArtWord] using rd3614raw
  have rd3620 := evm_run rd3614 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3628⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hltOne : UInt256.lt (barkLeftoverDueWord art dart rate) dust = ⟨1⟩ :=
    Reasoning.Theory.ult_one hdusty
  have hcondDusty : UInt256.isZero (UInt256.lt (barkLeftoverDueWord art dart rate) dust) =
      ⟨0⟩ := by
    rw [hltOne]
    decide
  have rd3621 := rd3620.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcondDusty (by evm_ov)
  have rd3627 := evm_run rd3621 with [
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3700 := rd3627.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, rd3700⟩

theorem RD.dogBarkPartialLeftoverToDinkEntry {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    {room spot dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hleftover : dart.toNat < art.toNat)
    (hfitLeftoverDue : (barkLeftoverArtWord art dart).toNat * rate.toNat < UInt256.size)
    (hnotDusty : dust.toNat ≤ (barkLeftoverDueWord art dart rate).toNat)
    (hfitPartialDue : dart.toNat * rate.toNat < UInt256.size)
    (hpartialDueOk : dust.toNat ≤ (barkPartialDueWord dart rate).toNat)
    (rd3594 : RD code I g s0 ⟨3594⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 36 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3700⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k' C' := by
  have rd3601 := evm_run rd3594 with [
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtOne : UInt256.gt art dart = ⟨1⟩ :=
    Reasoning.Theory.ugt_one hleftover
  have hcondNoJump : UInt256.isZero (UInt256.gt art dart) = ⟨0⟩ := by
    rw [hgtOne]
    decide
  have rd3602 := rd3601.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcondNoJump (by evm_ov)
  have rd3613 := evm_run rd3602 with [
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3614⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup10
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564left := rd3613.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3614raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := barkLeftoverArtWord art dart) (y := rate) (ret := ⟨3614⟩)
      (R := dust :: room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitLeftoverDue rd4564left
  have rd3614 := by
    simpa [barkLeftoverDueWord, barkLeftoverArtWord] using rd3614raw
  have rd3620 := evm_run rd3614 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3628⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hltZero : UInt256.lt (barkLeftoverDueWord art dart rate) dust = ⟨0⟩ :=
    Reasoning.Theory.ult_zero hnotDusty
  have hcondContinue :
      UInt256.isZero (UInt256.lt (barkLeftoverDueWord art dart rate) dust) ≠ ⟨0⟩ := by
    rw [hltZero]
    decide
  have rd3628 := rd3620.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcondContinue (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3638 := evm_run rd3628 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3639⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564partial := rd3638.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3639raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := dart) (y := rate) (ret := ⟨3639⟩)
      (R := dust :: room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitPartialDue rd4564partial
  have rd3639 := by
    simpa [barkPartialDueWord] using rd3639raw
  have rd3645 := evm_run rd3639 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw lt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3700⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hpartialLtZero : UInt256.lt (barkPartialDueWord dart rate) dust = ⟨0⟩ :=
    Reasoning.Theory.ult_zero hpartialDueOk
  have hpartialCond :
      UInt256.isZero (UInt256.lt (barkPartialDueWord dart rate) dust) ≠ ⟨0⟩ := by
    rw [hpartialLtZero]
    decide
  have rd3700 := rd3645.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hpartialCond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, rd3700⟩

theorem RD.dogBarkComputeDink {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    {room spot dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hfitInkDart : ink.toNat * dart.toNat < UInt256.size)
    (hartNe : art ≠ ⟨0⟩)
    (rd3700 : RD code I g s0 ⟨3700⟩
      (room :: spot :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 32 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3726⟩
      (barkDinkWord ink dart art :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k' C' := by
  have rd3714 := evm_run rd3700 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup6
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3715⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup9
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup7
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨4564⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd4564 := rd3714.jump
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  obtain ⟨_, _, rd3715raw⟩ :=
    RD.dogCheckedMulReturns (v := v) hpatch
      (x := ink) (y := dart) (ret := ⟨3715⟩)
      (R := art :: ⟨0⟩ :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink ::
        ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      (by simp only [List.length_cons]; omega)
      (dogPatchedJumpDest hpatch (by native_decide)) hfitInkDart rd4564
  have rd3715 := by
    simpa [barkInkDartWord] using rd3715raw
  have rd3720 := evm_run rd3715 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3722⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have rd3722 := rd3720.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hartNe (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  have rd3726 := evm_run rd3722 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw div
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa [barkDinkWord] using rd3726⟩

theorem RD.dogBarkDinkGuardOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    {dink dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hdinkPos : 0 < dink.toNat)
    (rd3726 : RD code I g s0 ⟨3726⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3797⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k' C' := by
  have rd3730 := evm_run rd3726 with [
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3797⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtOne : UInt256.gt dink ⟨0⟩ = ⟨1⟩ :=
    Reasoning.Theory.ugt_one (by simpa using hdinkPos)
  have hcond : UInt256.gt dink ⟨0⟩ ≠ ⟨0⟩ := by
    rw [hgtOne]
    decide
  have rd3797 := rd3730.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, rd3797⟩

theorem RD.dogBarkInt256GuardOk {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    {dink dust rate dart art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hdartBound : dart.toNat ≤ dogInt256LimitWord.toNat)
    (hdinkBound : dink.toNat ≤ dogInt256LimitWord.toNat)
    (rd3797 : RD code I g s0 ⟨3797⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 34 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨3885⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k' C' := by
  have rd3808 := evm_run rd3797 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨255⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3821⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtDartZero :
      UInt256.gt dart (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩) = ⟨0⟩ := by
    simpa [dogInt256LimitWord] using
      (Reasoning.Theory.ugt_zero (a := dart) (b := dogInt256LimitWord) hdartBound)
  have rd3812prep := rd3808
  rw [hgtDartZero,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide,
    show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ by decide] at rd3812prep
  have rd3812 := rd3812prep.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by rfl) (by evm_ov)
  have rd3825 := evm_run rd3812 with [
    raw pop
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨255⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw gt
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw iszero
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push2 ⟨3885⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  have hgtDinkZero :
      UInt256.gt dink (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨255⟩) = ⟨0⟩ := by
    simpa [dogInt256LimitWord] using
      (Reasoning.Theory.ugt_zero (a := dink) (b := dogInt256LimitWord) hdinkBound)
  have rd3825prep := rd3825
  rw [hgtDinkZero,
    show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by decide] at rd3825prep
  have hcond : (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by decide
  have rd3885 := rd3825prep.jumpiT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    hcond (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
  exact ⟨_, _, rd3885⟩

theorem RD.dogBarkVatGrabExtcodesizeGuard {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ σMem : AccountMap}
    {dink dust rate dart art ink : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (hmload256 :
      (if (⟨256⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨256⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨256⟩ : UInt256).toNat 32))) =
        barkIlksClipWord σMem I)
    (rd3885 : RD code I g s0 ⟨3885⟩
      (dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 48 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4023⟩
      (barkVatWord v :: barkVatWord v :: ⟨0⟩ :: barkVatGrabOutPtr ::
        barkVatGrabInSize :: barkVatGrabOutPtr :: barkVatGrabOutSize ::
        barkVatGrabEndPtr :: barkVatGrabSelectorWord :: barkVatWord v ::
        dink :: dust :: rate :: dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      (barkVatGrabCallMem σ σMem I mem dink dart) (UInt256.ofNat 19) rdata
      (cA, σ) k' C' := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨384⟩ := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 17) (v := (⟨384⟩ : UInt256))
      (by rw [hmem]; decide)
      (by native_decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 by native_decide] using hread64)
  have hmload64Call :=
    barkVatGrabCallMem_mload64 (σ := σ) (σMem := σMem) (I := I)
      (mem := mem) (dink := dink) (dart := dart) hmem hread64
  have hvatCleanR :
      UInt256.land (barkVatWord v) solcAddrMask = barkVatWord v :=
    solcAddrMask_clean (barkVatWord_canonical v)
  have hvatCleanL :
      UInt256.land solcAddrMask (barkVatWord v) = barkVatWord v :=
    solcAddrMask_clean_left (barkVatWord_canonical v)
  have hclipCanon : (barkIlksClipWord σMem I).toNat < EVM.addressModulus := by
    simpa [barkIlksClipWord, u256_land_comm] using
      solcAddrMask_result_canonical (solcSlotWord σMem I (barkIlksSlot I))
  have hclipMask :
      UInt256.land solcAddrMask (barkIlksClipWord σMem I) = barkIlksClipWord σMem I :=
    solcAddrMask_clean_left hclipCanon
  have hurnCanon : (barkUrnKey I).toNat < EVM.addressModulus := by
    simpa [barkUrnKey, u256_land_comm] using
      solcAddrMask_result_canonical (barkUrnWord I)
  have hurnMask :
      UInt256.land solcAddrMask (barkUrnKey I) = barkUrnKey I :=
    solcAddrMask_clean_left hurnCanon
  have hvowCanon : (barkVowWord σ I).toNat < EVM.addressModulus := by
    simpa [barkVowWord, u256_land_comm] using
      solcAddrMask_result_canonical (dogSlotWord ⟨2⟩ σ I)
  have hvowMask :
      UInt256.land solcAddrMask (barkVowWord σ I) = barkVowWord σ I :=
    solcAddrMask_clean_left hvowCanon
  have haddrMaskWord :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have hvatCleanLit :
      UInt256.land ({ val := 1461501637330902918203684832716283019655932542975 } :
        UInt256) (barkVatWord v) = barkVatWord v := by
    simpa [solcAddrMask] using hvatCleanL
  have hclipMaskLit :
      UInt256.land ({ val := 1461501637330902918203684832716283019655932542975 } :
        UInt256) (barkIlksClipWord σMem I) = barkIlksClipWord σMem I := by
    simpa [solcAddrMask] using hclipMask
  have hvowWordLit :
      UInt256.land ({ val := 1461501637330902918203684832716283019655932542975 } :
        UInt256) (dogSlotWord ⟨2⟩ σ I) = barkVowWord σ I := by
    simp [barkVowWord, solcAddrMask]
  have rd3890pre := evm_run rd3885 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 (barkIlksClipWord σMem I) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload256 (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨2⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3891, C3891, rd3891raw⟩ := rd3890pre.sload
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd3891 : RD code I g s0 ⟨3891⟩
      (dogSlotWord ⟨2⟩ σ I :: barkIlksClipWord σMem I :: dink :: dust :: rate ::
        dart :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I ::
        barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k3891 C3891 := by
    simpa [dogSlotWord] using rd3891raw
  have rd3964 := evm_run rd3891 with [
    raw push1 ⟨64⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64 (by native_decide) (by simp only [List.length_cons]; omega),
    raw push4 ⟨0x01eeacfd⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨230⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVatGrabSelectorMem mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost (by rfl) (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup16
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVatGrabIlkMem I mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 4 } : UInt256).toNat = 388
          from by native_decide]
        rfl)
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw shl
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup15
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by simp only [List.length_cons]; omega),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨36⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVatGrabUrnMem I mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 36 } : UInt256).toNat = 420
          from by native_decide]
        simp only [barkVatGrabUrnMem, Reasoning.Theory.writeWord]
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide, hurnMask])
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨68⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVatGrabClipMem σMem I mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 68 } : UInt256).toNat = 452
          from by native_decide]
        simp only [barkVatGrabClipMem, Reasoning.Theory.writeWord]
        rw [haddrMaskWord, hclipMask])
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨100⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 0 (barkVatGrabVowMem σ σMem I mem) (UInt256.ofNat 17)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 100 } : UInt256).toNat = 484
          from by native_decide]
        simp only [barkVatGrabVowMem, Reasoning.Theory.writeWord, barkVowWord]
        rw [haddrMaskWord])
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw push1 ⟨0⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨132⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 3 (barkVatGrabDinkMem σ σMem I mem dink) (UInt256.ofNat 18)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 132 } : UInt256).toNat = 516
          from by native_decide]
        rfl)
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨164⟩
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup5
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mstore 3 (barkVatGrabCallMem σ σMem I mem dink dart) (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost
      (by
        rw [show ({ val := 384 } + { val := 164 } : UInt256).toNat = 548
          from by native_decide]
        rfl)
      (by native_decide) (by simp only [List.length_cons]; omega),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw mload 0 ⟨384⟩ (UInt256.ofNat 19)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      mem_cost hmload64Call (by native_decide) (by simp only [List.length_cons]; omega)]
  have rd3997 := rd3964.pushConst (barkVatWord v) (width := 32) (op := .PUSH32)
    (hop := by decide)
    (by simpa [barkVatWord] using dogBarkVatConstDecode3964 hpatch)
    (by simp only [List.length_cons]; omega)
  have rd4023 := evm_run rd3997 with [
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw and
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push4 barkVatGrabSelectorWord
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 barkVatGrabInSize
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup3
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw swap1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw sub
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw add
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup2
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup4
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup8
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw dup1
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  exact ⟨_, _, by
    convert rd4023 using 1 <;>
      simp only [barkVatGrabOutPtr, barkVatGrabInSize, barkVatGrabOutSize,
        barkVatGrabEndPtr, haddrMaskWord, hvatCleanL,
        show UInt256.sub (⟨384⟩ : UInt256) ⟨384⟩ + barkVatGrabInSize =
          barkVatGrabInSize from by native_decide,
        show (⟨384⟩ : UInt256) + barkVatGrabInSize = barkVatGrabEndPtr
          from by native_decide] <;>
      native_decide⟩

theorem RD.dogBarkVatGrabNoCodeRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4023 : RD code I g s0 ⟨4023⟩ (barkVatWord v :: barkVatWord v :: R)
      mem (UInt256.ofNat 19) rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) = ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨4023⟩) (okPc := ⟨4035⟩)
    rd4023 hcodeSize
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    hov

theorem RD.dogBarkVatGrabToCall {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4023 : RD code I g s0 ⟨4023⟩ (barkVatWord v :: barkVatWord v :: R)
      mem (UInt256.ofNat 19) rdata (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ gasWord k' C', RD code I g s0 ⟨4038⟩ (gasWord :: barkVatWord v :: R)
      mem (UInt256.ofNat 19) rdata (cA, σ) k' C' := by
  obtain ⟨gasWord, k', C', rd4038⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨4023⟩) (okPc := ⟨4035⟩)
      rd4023 hcodeSize
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (dogPatchedJumpDest hpatch (by native_decide))
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      (by
        rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]
        native_decide)
      hov
  exact ⟨gasWord, k', C', by simpa using rd4038⟩

theorem RD.dogBarkVatGrabCallFailure {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4039 : RD code I g s0 ⟨4039⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨4039⟩) (okPc := ⟨4055⟩) rd4039
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    hrdataSize hov

theorem RD.dogBarkVatGrabCallSuccess {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (rd4039 : RD code I g s0 ⟨4039⟩ (⟨1⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code I g s0 ⟨4057⟩ R mem aw rdata acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨4039⟩) (okPc := ⟨4055⟩) rd4039
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (dogPatchedJumpDest hpatch (by native_decide))
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    (by
      rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
        (by native_decide) (by native_decide)]
      native_decide)
    hov

theorem RD.dogBarkLiquidationLimitHitReverts {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : EVM.State} {I : ExecutionEnv}
    {k C : ℕ} {ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ σMem : AccountMap}
    {spot dust rate art ink kpr urn ilk : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hspot : spot ≠ ⟨0⟩)
    (hfitArt : art.toNat * rate.toNat < UInt256.size)
    (hfitInk : ink.toNat * spot.toNat < UInt256.size)
    (hsafe : (ink * spot).toNat < (art * rate).toNat)
    (hlimitFalse :
      ¬ ((dogSlotWord ⟨5⟩ σ I).toNat < (dogSlotWord ⟨4⟩ σ I).toNat ∧
        (barkIlksDirtWord σMem I).toNat < (barkIlksHoleWord σMem I).toNat))
    (hmload320 :
      (if (⟨320⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨320⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨320⟩ : UInt256).toNat 32))) =
        barkIlksHoleWord σMem I)
    (hmload352 :
      (if (⟨352⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨352⟩ : UInt256) ≥ UInt256.ofNat 17 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨352⟩ : UInt256).toNat 32))) =
        barkIlksDirtWord σMem I)
    (hmem : mem.size = 544)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨384⟩)
    (rd3308 : RD code I g s0 ⟨3308⟩
      (spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ ::
        kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k C)
    (hov : R.length + 28 ≤ 1024) :
    RDrev code g s0 := by
  have htail : dogPostIlksErrorStringFullWordTailWf code ⟨3436⟩ ⟨25⟩
      (UInt256.shiftLeft dogLiquidationLimitHitRawWord ⟨56⟩) := by
    unfold dogPostIlksErrorStringFullWordTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
  obtain ⟨_, _, rd3405⟩ :=
    RD.dogBarkSafeToLimitGuard (v := v) (code := code) (ret := ret) (sel := sel)
      (R := R) hpatch hspot hfitArt hfitInk hsafe rd3308 hov
  have rd3408 := evm_run rd3405 with [
    raw jumpdest
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov),
    raw push1 ⟨5⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3409, C3409, rd3409raw⟩ := rd3408.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd3409 : RD code I g s0 ⟨3409⟩
      (dogSlotWord ⟨5⟩ σ I :: spot :: dust :: rate :: ⟨0⟩ :: ⟨256⟩ ::
        art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k3409 C3409 := by
    simpa [dogSlotWord, solcSlotWord] using rd3409raw
  have rd3411 := evm_run rd3409 with [
    raw push1 ⟨4⟩
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)]
  obtain ⟨k3412, C3412, rd3412raw⟩ := rd3411.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd3412 : RD code I g s0 ⟨3412⟩
      (dogSlotWord ⟨4⟩ σ I :: dogSlotWord ⟨5⟩ σ I :: spot :: dust :: rate ::
        ⟨0⟩ :: ⟨256⟩ :: art :: ink :: ⟨0⟩ :: kpr :: urn :: ilk :: ret :: sel :: R)
      mem (UInt256.ofNat 17) rdata (cA, σ) k3412 C3412 := by
    simpa [dogSlotWord, solcSlotWord] using rd3412raw
  by_cases hglobal :
      (dogSlotWord ⟨5⟩ σ I).toNat < (dogSlotWord ⟨4⟩ σ I).toNat
  · have hgtGlobal :
        UInt256.gt (dogSlotWord ⟨4⟩ σ I) (dogSlotWord ⟨5⟩ σ I) = ⟨1⟩ :=
      Reasoning.Theory.ugt_one hglobal
    have rd3413raw := evm_run rd3412 with [
      raw gt
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3413 := rd3413raw
    rw [hgtGlobal] at rd3413
    have rd3418raw := evm_run rd3413 with [
      raw dup1
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw iszero
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨3431⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3418 := rd3418raw
    rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3418
    have rd3419 := rd3418.jumpiNT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by rfl) (by evm_ov)
    have rd3423 := evm_run rd3419 with [
      raw pop
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw dup5
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push1 ⟨96⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3424raw := RD.add rd3423
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)
    have hadd352 : (⟨96⟩ : UInt256) + ⟨256⟩ = ⟨352⟩ := by
      native_decide
    have rd3424 := by
      simpa [hadd352] using rd3424raw
    have rd3425 := evm_run rd3424 with [
      raw mload 0 (barkIlksDirtWord σMem I) (UInt256.ofNat 17)
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        mem_cost hmload352 (by decide) (by evm_ov)]
    have rd3428 := evm_run rd3425 with [
      raw dup6
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push1 ⟨64⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3429raw := RD.add rd3428
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by evm_ov)
    have hadd320 : (⟨64⟩ : UInt256) + ⟨256⟩ = ⟨320⟩ := by
      native_decide
    have rd3429 := by
      simpa [hadd320] using rd3429raw
    have rd3430 := evm_run rd3429 with [
      raw mload 0 (barkIlksHoleWord σMem I) (UInt256.ofNat 17)
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        mem_cost hmload320 (by decide) (by evm_ov)]
    have hmilkNot :
        ¬ (barkIlksDirtWord σMem I).toNat < (barkIlksHoleWord σMem I).toNat := by
      intro hmilk
      exact hlimitFalse ⟨hglobal, hmilk⟩
    have hgtMilk : UInt256.gt (barkIlksHoleWord σMem I) (barkIlksDirtWord σMem I) = ⟨0⟩ :=
      Reasoning.Theory.ugt_zero (by omega)
    have rd3431raw := evm_run rd3430 with [
      raw gt
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3431 := rd3431raw
    rw [hgtMilk] at rd3431
    have rd3435 := evm_run rd3431 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨3512⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3436raw := rd3435.jumpiNT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by rfl) (by evm_ov)
    have hpc3436 :
        (⟨3412⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 3 + ⟨1⟩ = ⟨3436⟩ := by
      native_decide
    have rd3436 := rd3436raw
    rw [hpc3436] at rd3436
    exact RD.dogBarkPostIlksErrorStringRevertTailFullWord
      (pc := ⟨3436⟩) (len := ⟨25⟩)
      (word := UInt256.shiftLeft dogLiquidationLimitHitRawWord ⟨56⟩)
      rd3436 htail hmem hread64
      (by simp only [List.length_cons]; omega)
  · have hgtGlobal :
        UInt256.gt (dogSlotWord ⟨4⟩ σ I) (dogSlotWord ⟨5⟩ σ I) = ⟨0⟩ :=
      Reasoning.Theory.ugt_zero (by omega)
    have rd3413raw := evm_run rd3412 with [
      raw gt
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3413 := rd3413raw
    rw [hgtGlobal] at rd3413
    have rd3418raw := evm_run rd3413 with [
      raw dup1
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw iszero
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨3431⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3418 := rd3418raw
    rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3418
    have rd3431 := rd3418.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      one_ne_zero_uint (dogPatchedJumpDest hpatch (by native_decide)) (by evm_ov)
    have rd3435 := evm_run rd3431 with [
      raw jumpdest
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov),
      raw push2 ⟨3512⟩
        (by
          rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
        (by evm_ov)]
    have rd3436raw := rd3435.jumpiNT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      (by rfl) (by evm_ov)
    have hpc3436 : (⟨3431⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ = ⟨3436⟩ := by
      native_decide
    have rd3436 := rd3436raw
    rw [hpc3436] at rd3436
    exact RD.dogBarkPostIlksErrorStringRevertTailFullWord
      (pc := ⟨3436⟩) (len := ⟨25⟩)
      (word := UInt256.shiftLeft dogLiquidationLimitHitRawWord ⟨56⟩)
      rd3436 htail hmem hread64
      (by simp only [List.length_cons]; omega)

theorem RD.dogBarkVatUrnsStaticcallDepthLimitRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {ret sel : UInt256} {R : List UInt256}
    {k C : ℕ} {mem rdata : ByteArray}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2885⟩
      (⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I :: ret :: sel :: R)
      mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (barkVatWord v) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hov : R.length + 24 ≤ 1024) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, _, rd3007⟩ :=
    RD.dogBarkVatUrnsToStaticcall hpatch h hmem hread64 hcodeSize hov
  obtain ⟨_, _, rd3008raw⟩ :=
    RD.uniswapStaticcallDepthLimit rd3007
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      hdepth
      (by simp only [List.length_cons]; omega)
  have hmin : (min (⟨64⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    rfl
  obtain ⟨_, _, rd3008⟩ : ∃ k' C',
      RD code I g (initState cA gh bl σ σ₀ g A I) ⟨3008⟩
        (⟨0⟩ :: ⟨196⟩ :: ⟨606387804⟩ :: barkVatWord v ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: barkKprKey I :: barkUrnKey I :: barkIlkWord I ::
          ret :: sel :: R)
        (barkVatUrnsCallMem I mem) (UInt256.ofNat 7) ByteArray.empty (cA, σ) k' C' := by
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 7).toNat
          (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨64⟩ : UInt256).toNat) = UInt256.ofNat 7 := by
      native_decide
    exact ⟨_, _, by simpa [hmin, byteArray_write_len_zero] using haw ▸ rd3008raw⟩
  exact RD.dogBarkVatUrnsCallFailure hpatch rd3008 (by native_decide)
    (by simp only [List.length_cons]; omega)

theorem RD.dogBarkLiveOk {v : DogImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State} {stk : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g s0 ⟨2813⟩ stk solcFreePtrMem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hlive : solcSlotWord σ I ⟨3⟩ = ⟨1⟩)
    (hov : stk.length + 6 ≤ 1024) :
    ∃ k C, RD code I g s0 ⟨2885⟩ (⟨0⟩ :: stk) solcFreePtrMem
      (UInt256.ofNat 3) rdata (cA, σ) k C := by
  obtain ⟨_, _, h⟩ := hreach
  have rd1 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rd3 := rd1.push1 ⟨0⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rd5 := rd3.push1 ⟨3⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd6⟩ := rd5.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 ⟨1⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd9₀ := rd8.eq
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hraw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨3⟩ ⟨0⟩)) =
        ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  have rd9 := rd9₀
  rw [hraw, uInt256_eq_self] at rd9
  have rd12 := rd9.push2 ⟨2885⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa using rd12.jumpiT
      (by
        rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
        native_decide)
      one_ne_zero_uint
      (dogPatchedJumpDest hpatch (by native_decide))
      (by simp only [List.length_cons]; omega)⟩

theorem RD.dogBarkLiveRevert {v : DogImmutables} {code : ByteArray}
    {I : ExecutionEnv} {g : Sat256} {s0 : EVM.State} {stk : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g s0 ⟨2813⟩ stk solcFreePtrMem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hlive : solcSlotWord σ I ⟨3⟩ ≠ ⟨1⟩)
    (hov : stk.length + 6 ≤ 1024) :
    RDrev code g s0 := by
  obtain ⟨_, _, h⟩ := hreach
  have htail : solcErrorStringRevertTailWf code ⟨2826⟩ ⟨12⟩
      dogNotLiveRawWord ⟨160⟩ .PUSH12 12 := by
    unfold solcErrorStringRevertTailWf
    repeat' first
      | apply And.intro
      | (rw [dogDecodePatchedEqTemplatePrecise hpatch (by native_decide) (by native_decide)
          (by native_decide) (by native_decide)]; native_decide)
  have rd1 := h.jumpdest
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rd3 := rd1.push1 ⟨0⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by omega)
  have rd5 := rd3.push1 ⟨3⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd6⟩ := rd5.sload
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 ⟨1⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd9₀ := rd8.eq
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have hraw :
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨3⟩ ⟨0⟩)) ≠
        ⟨1⟩ := by
    simpa [solcSlotWord] using hlive
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨3⟩ ⟨0⟩)) =
          ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hraw h1.symm)
  have rd9 := rd9₀
  rw [heq0] at rd9
  have rd12 := rd9.push2 ⟨2885⟩
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rdTail := rd12.jumpiNT
    (by
      rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
      native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by simp only [List.length_cons]; omega)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨2826⟩) (len := ⟨12⟩) (rawWord := dogNotLiveRawWord)
    (shift := ⟨160⟩) (word := UInt256.shiftLeft dogNotLiveRawWord ⟨160⟩)
    (op := .PUSH12) (width := 12) rdTail htail
    (by decide) (by rfl) solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons]; omega)

theorem dogBarkBodyCoreDecodeFailed_short
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg (contract v) I.calldata = some (barkTransition v))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨785⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := ⟨785⟩) (ret := ⟨448⟩)
    (decoded := ⟨807⟩) (need := ⟨96⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (dogDecode_bark_none_short (v := v) hsz4 hshort)

theorem dogBarkBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some (barkTransition v) :=
    dogDispatchBark hsel
  have hreach := dogReachBarkBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · have hdecode :
        decodeCalldataWithMode (config v).abiDecodeMode
          ((barkTransition v).params.map Param.name)
          (transitionSignature (barkTransition v)).paramTypes I.calldata =
            some (barkLocals I) :=
      dogDecode_bark_ok (v := v) hsz100
    have hbodyReach := RD.dogBarkDecodeToBody hpatch hsize hsz100 hreach
    by_cases hliveEvm : dogSlotWord ⟨3⟩ σ_evm I = ⟨1⟩
    · have hslotWord :
          dogSlotWord ⟨3⟩ σ_evm I = dogSlotWord ⟨3⟩ σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
      have hliveSolm : dogSlotWord ⟨3⟩ σ_solm I = ⟨1⟩ := by
        rw [← hslotWord]
        exact hliveEvm
      have hliveSolc : solcSlotWord σ_evm I ⟨3⟩ = ⟨1⟩ := by
        simpa [dogSlotWord] using hliveEvm
      obtain ⟨_, _, h2885⟩ := RD.dogBarkLiveOk hpatch hbodyReach hliveSolc
        (by simp only [List.length_cons, List.length_nil]; omega)
      by_cases hvatCodeSize :
          Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (barkVatWord v) = ⟨0⟩
      · have hrev := RD.dogBarkVatUrnsNoCodeRevert
          (v := v) (code := code) (ret := ⟨448⟩) (sel := solcSelectorWord I) (R := [])
          hpatch h2885 solcFreePtrMem_size solcFreePtrMem_read64 hvatCodeSize
          (by simp)
        have hvatCodeSizeSolm :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (barkVatWord v) = ⟨0⟩ :=
          barkVatCodeSize_zero_accountMapEquiv hAccounts hvatCodeSize
        have hvatNoCode :
            (UInt256.ofNat
              (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                (AccountAddress.ofNat v.vat.toNat)).option 0
                  (fun acc => acc.code.size))).toNat = 0 :=
          barkVatCode_zero_of_codeSize_zero (v := v) (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hvatCodeSizeSolm
        let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody (config v) (contract v) evm0 (barkLocals I)
              (barkTransition v).body .reverted := by
          simpa [evm0] using
            (dogBarkVatUrnsNoCodeSourceBody (v := v) (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hliveSolm hvatNoCode)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hvatCodeSizeNe :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (barkVatWord v) ≠ ⟨0⟩ :=
          hvatCodeSize
        have hvatCodeSizeSolmNe :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (barkVatWord v) ≠ ⟨0⟩ :=
          barkVatCodeSize_ne_accountMapEquiv hAccounts hvatCodeSizeNe
        have hvatCode :
            0 < (UInt256.ofNat
              (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                (AccountAddress.ofNat v.vat.toNat)).option 0
                  (fun acc => acc.code.size))).toNat :=
          barkVatCode_pos_of_codeSize_ne (v := v) (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hvatCodeSizeSolmNe
        by_cases hdepthLt : I.depth.val < 1024
        · obtain ⟨cA', σ', z, out, A', _k', _C', rd3008, hcallEvmRaw, hosz⟩ :=
            RD.dogBarkVatUrnsPostStaticcall
              (v := v) (code := code) (ret := ⟨448⟩) (sel := solcSelectorWord I)
              (R := []) hpatch h2885 hsz100 solcFreePtrMem_size solcFreePtrMem_read64
              hvatCodeSizeNe hdepthLt (by simp)
          let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
          let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let evmPostEvm :=
            { evmEvm with accountMap := σ', substate := A', createdAccounts := cA' }
          have hcallEvm :
              typedCallViaEVM (config v) evmEvm
                (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
                [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
                (z, evmPostEvm, out) false := by
            simpa [evmEvm, evmPostEvm] using hcallEvmRaw
          obtain ⟨σSolmPost, ASolmPost, hcallSolmRaw, hStateCallRaw⟩ :=
            typedCallViaEVM_initState_EVMStateEquiv hcallEvm
              (by simp [evmEvm, evmSolm, evmPostEvm, initState]) hAccounts
          let evmPostSolm :=
            { evmSolm with
              accountMap := σSolmPost, substate := ASolmPost, createdAccounts := cA' }
          have hcallSolm :
              typedCallViaEVM (config v) evmSolm
                (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
                [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
                (z, evmPostSolm, out) false := by
            simpa [evmPostSolm] using hcallSolmRaw
          cases z
          · simp only [Bool.false_eq_true, if_false] at rd3008 hcallSolm
            have hrev := RD.dogBarkVatUrnsCallFailure hpatch rd3008 hosz (by simp)
            have hbody :
                ExecTransitionBody (config v) (contract v) evmSolm (barkLocals I)
                  (barkTransition v).body .reverted := by
              simpa [evmSolm] using
                (dogBarkVatUrnsCallFailureSourceBody (v := v) (cA := cA) (gh := gh)
                  (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                  (g := g) (evmCall := evmPostSolm) (out := out)
                  hwv hliveSolm hvatCode hcallSolm)
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · simp only [Bool.true_eq_false, if_true] at rd3008 hcallSolm
            obtain ⟨_, _, rd3026⟩ :=
              RD.dogBarkVatUrnsCallSuccessToDecode hpatch rd3008
                (by simp only [List.length_cons, List.length_nil]; omega)
            by_cases hretLong : 64 ≤ out.size
            · have hdecUrns : (config v).externalABI.decode? "urns" out =
                  some [.int (Int.ofNat (barkVatUrnsInkWord out).toNat),
                    .int (Int.ofNat (barkVatUrnsArtWord out).toNat)] :=
                barkVatUrnsDecode_ok (v := v) hretLong
              obtain ⟨_, _, rd3061⟩ :=
                RD.dogBarkVatUrnsReturnDecodeOk hpatch rd3026
                  solcFreePtrMem_size solcFreePtrMem_read64 hretLong hosz
                  (by simp only [List.length_cons, List.length_nil]; omega)
              obtain ⟨_, _, rd3070⟩ :=
                RD.dogBarkVatUrnsMaterializeTuple hpatch rd3061
                  solcFreePtrMem_size solcFreePtrMem_read64 hretLong hosz
                  (by simp only [List.length_cons, List.length_nil]; omega)
              obtain ⟨_, _, rd3139⟩ :=
                RD.dogBarkLoadIlkFields hpatch rd3070
                  solcFreePtrMem_size hretLong hosz
                  (by simp only [List.length_cons, List.length_nil]; omega)
              have hStateCall : EVMStateEquiv evmPostEvm evmPostSolm := by
                simpa [evmPostEvm, evmPostSolm] using hStateCallRaw
              by_cases hvatIlksCodeSize :
                  Reasoning.Theory.uniswapExtCodeSizeWord σ' (barkVatWord v) = ⟨0⟩
              · have hrev := RD.dogBarkVatIlksNoCodeRevert hpatch rd3139
                  solcFreePtrMem_size hretLong hosz hvatIlksCodeSize
                  (by simp only [List.length_cons, List.length_nil]; omega)
                have hvatIlksCodeSizeEvm :
                    Reasoning.Theory.uniswapExtCodeSizeWord evmPostEvm.accountMap
                      (barkVatWord v) = ⟨0⟩ := by
                  simpa [evmPostEvm] using hvatIlksCodeSize
                have hvatIlksCodeSizeSolm :
                    Reasoning.Theory.uniswapExtCodeSizeWord evmPostSolm.accountMap
                      (barkVatWord v) = ⟨0⟩ :=
                  barkVatCodeSize_zero_accountMapEquiv hStateCall.accountMap
                    hvatIlksCodeSizeEvm
                have hvatNoCode :
                    (UInt256.ofNat
                      ((evmPostSolm.lookupAccount
                        (AccountAddress.ofNat v.vat.toNat)).option 0
                          (fun acc => acc.code.size))).toNat = 0 :=
                  barkVatCode_zero_of_state_codeSize_zero (v := v) (evm := evmPostSolm)
                    hvatIlksCodeSizeSolm
                have hbody :
                    ExecTransitionBody (config v) (contract v) evmSolm (barkLocals I)
                      (barkTransition v).body .reverted := by
                  simpa [evmSolm] using
                    (dogBarkVatIlksNoCodeSourceBody (v := v) (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := g) (evmUrns := evmPostSolm) (out := out)
                      hwv hliveSolm hvatCode hcallSolm hdecUrns hvatNoCode hsz100)
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · obtain ⟨cA'', σ'', zIlks, outIlks, A'', _k'', _C'', rd3245,
                    hcallIlksEvmRaw, hoszIlks⟩ :=
                  RD.dogBarkVatIlksPostStaticcall
                    (v := v) (code := code) (s0 := evmEvm) (evm := evmPostEvm)
                    (ret := ⟨448⟩) (sel := solcSelectorWord I) (R := [])
                    hpatch rd3139 hsz100 solcFreePtrMem_size hretLong hosz
                    hvatIlksCodeSize
                    (by simp [evmPostEvm, evmEvm, initState])
                    (by simp [evmPostEvm, evmEvm])
                    (by simp [evmPostEvm, evmEvm])
                    (by simp [evmPostEvm, evmEvm, initState])
                    (by simp [evmPostEvm, evmEvm, initState])
                    (by simp [evmPostEvm, evmEvm, initState])
                    hdepthLt
                    (by simp only [List.length_nil]; omega)
                let evmIlksPostEvm :=
                  { evmPostEvm with
                    accountMap := σ'', substate := A'', createdAccounts := cA'' }
                have hcallIlksEvm :
                    typedCallViaEVM (config v) evmPostEvm
                      (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
                      [.fixedBytes bytes32Width (barkIlkBytes I)]
                      (zIlks, evmIlksPostEvm, outIlks) false := by
                  simpa [evmIlksPostEvm] using hcallIlksEvmRaw
                obtain ⟨σIlksSolmPost, AIlksSolmPost, hcallIlksSolmRaw,
                    hAccountsIlks⟩ :=
                  dogTypedCallViaEVM_accountMapEquiv_noSubstate
                    (evm_solm := evmPostSolm) hcallIlksEvm
                    hStateCall.accountMap
                    (by simp [evmPostEvm, evmPostSolm, evmEvm, evmSolm, initState])
                    (by simpa [evmPostEvm, evmPostSolm] using hStateCall.createdAccounts.symm)
                    (by simp [evmPostEvm, evmPostSolm, evmEvm, evmSolm, initState])
                    (by simp [evmPostEvm, evmPostSolm, evmEvm, evmSolm, initState])
                    (by simpa [evmPostEvm, evmPostSolm] using hStateCall.executionEnv.symm)
                let evmIlksPostSolm :=
                  { evmPostSolm with
                    accountMap := σIlksSolmPost, substate := AIlksSolmPost,
                    createdAccounts := cA'' }
                have hcallIlksSolm :
                    typedCallViaEVM (config v) evmPostSolm
                      (EVM.address (AccountAddress.ofNat v.vat.toNat)) "ilks" 0
                      [.fixedBytes bytes32Width (barkIlkBytes I)]
                      (zIlks, evmIlksPostSolm, outIlks) false := by
                  simpa [evmIlksPostEvm, evmIlksPostSolm] using hcallIlksSolmRaw
                cases zIlks
                · simp only [Bool.false_eq_true, if_false] at rd3245 hcallIlksEvm
                  simp only [Bool.false_eq_true, if_false] at hcallIlksSolm
                  have hrev := RD.dogBarkVatIlksCallFailure hpatch rd3245 hoszIlks
                    (by simp only [List.length_cons, List.length_nil]; omega)
                  have hvatIlksCodeSizeEvmNe :
                      Reasoning.Theory.uniswapExtCodeSizeWord evmPostEvm.accountMap
                        (barkVatWord v) ≠ ⟨0⟩ := by
                    simpa [evmPostEvm] using hvatIlksCodeSize
                  have hvatIlksCodeSizeSolmNe :
                      Reasoning.Theory.uniswapExtCodeSizeWord evmPostSolm.accountMap
                        (barkVatWord v) ≠ ⟨0⟩ :=
                    barkVatCodeSize_ne_accountMapEquiv hStateCall.accountMap
                      hvatIlksCodeSizeEvmNe
                  have hvatIlksCode :
                      0 < (UInt256.ofNat
                        ((evmPostSolm.lookupAccount
                          (AccountAddress.ofNat v.vat.toNat)).option 0
                            (fun acc => acc.code.size))).toNat :=
                    barkVatCode_pos_of_state_codeSize_ne (v := v) (evm := evmPostSolm)
                      hvatIlksCodeSizeSolmNe
                  have hbody :
                      ExecTransitionBody (config v) (contract v) evmSolm (barkLocals I)
                        (barkTransition v).body .reverted := by
                    simpa [evmSolm] using
                      (dogBarkVatIlksCallFailureSourceBody (v := v) (cA := cA)
                        (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                        (I := I) (g := g) (evmUrns := evmPostSolm)
                        (evmIlks := evmIlksPostSolm) (out := out) (outIlks := outIlks)
                        hwv hliveSolm hvatCode hcallSolm hdecUrns hvatIlksCode
                        hcallIlksSolm hsz100)
                  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · simp only [Bool.true_eq_false, if_true] at rd3245 hcallIlksEvm
                  simp only [Bool.true_eq_false, if_true] at hcallIlksSolm
                  obtain ⟨_, _, rd3263⟩ :=
                    RD.dogBarkVatIlksCallSuccessToDecode hpatch rd3245
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have hvatIlksCodeSizeEvmNe :
                      Reasoning.Theory.uniswapExtCodeSizeWord evmPostEvm.accountMap
                        (barkVatWord v) ≠ ⟨0⟩ := by
                    simpa [evmPostEvm] using hvatIlksCodeSize
                  have hvatIlksCodeSizeSolmNe :
                      Reasoning.Theory.uniswapExtCodeSizeWord evmPostSolm.accountMap
                        (barkVatWord v) ≠ ⟨0⟩ :=
                    barkVatCodeSize_ne_accountMapEquiv hStateCall.accountMap
                      hvatIlksCodeSizeEvmNe
                  have hvatIlksCode :
                      0 < (UInt256.ofNat
                        ((evmPostSolm.lookupAccount
                          (AccountAddress.ofNat v.vat.toNat)).option 0
                            (fun acc => acc.code.size))).toNat :=
                    barkVatCode_pos_of_state_codeSize_ne (v := v) (evm := evmPostSolm)
                      hvatIlksCodeSizeSolmNe
                  by_cases hretIlksLong : 160 ≤ outIlks.size
                  · have hdecIlks :
                        (config v).externalABI.decode? "ilks" outIlks =
                          some (barkVatIlksReturnValues outIlks) :=
                      barkVatIlksDecode_ok (v := v) hretIlksLong
                    obtain ⟨_, _, rd3308⟩ :=
                      RD.dogBarkVatIlksReturnDecodeOkToSpotGuard hpatch rd3263
                        solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                        (by simp only [List.length_cons, List.length_nil]; omega)
                    by_cases hoverInk :
                        UInt256.size ≤
                          (barkVatUrnsInkWord out).toNat *
                            (barkVatIlksSpotWord outIlks).toNat
                    · have hspotNe : barkVatIlksSpotWord outIlks ≠ ⟨0⟩ := by
                        intro hspotZero
                        have hprod0 :
                            (barkVatUrnsInkWord out).toNat *
                                (barkVatIlksSpotWord outIlks).toNat = 0 := by
                          simp [hspotZero]
                        have hsizePos : 0 < UInt256.size := by
                          norm_num [UInt256.size]
                        omega
                      have hbody :
                          ExecTransitionBody (config v) (contract v) evmSolm (barkLocals I)
                            (barkTransition v).body .reverted := by
                        simpa [evmSolm] using
                          (dogBarkVatIlksInkSpotOverflowSourceBody (v := v) (cA := cA)
                            (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                            (I := I) (g := g) (evmUrns := evmPostSolm)
                            (evmIlks := evmIlksPostSolm) (out := out)
                            (outIlks := outIlks) hwv hliveSolm hvatCode hcallSolm
                            hdecUrns hvatIlksCode hcallIlksSolm hdecIlks hoverInk hsz100)
                      by_cases hoverArt :
                          UInt256.size ≤
                            (barkVatUrnsArtWord out).toNat *
                              (barkVatIlksRateWord outIlks).toNat
                      · have hrev := RD.dogBarkArtRateOverflowReverts
                          (v := v) (code := code) (ret := ⟨448⟩)
                          (sel := solcSelectorWord I) (R := []) hpatch hspotNe hoverArt
                          rd3308 (by simp)
                        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have hfitArt :
                            (barkVatUrnsArtWord out).toNat *
                                (barkVatIlksRateWord outIlks).toNat < UInt256.size :=
                          Nat.lt_of_not_ge hoverArt
                        have hrev := RD.dogBarkInkSpotOverflowReverts
                          (v := v) (code := code) (ret := ⟨448⟩)
                          (sel := solcSelectorWord I) (R := []) hpatch hspotNe hfitArt
                          hoverInk rd3308 (by simp)
                        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hfitInk :
                          (barkVatUrnsInkWord out).toNat *
                              (barkVatIlksSpotWord outIlks).toNat < UInt256.size :=
                        Nat.lt_of_not_ge hoverInk
                      by_cases hoverArt :
                          UInt256.size ≤
                            (barkVatUrnsArtWord out).toNat *
                              (barkVatIlksRateWord outIlks).toNat
                      · have hbody :
                            ExecTransitionBody (config v) (contract v) evmSolm (barkLocals I)
                              (barkTransition v).body .reverted := by
                          simpa [evmSolm] using
                            (dogBarkVatIlksArtRateOverflowSourceBody (v := v) (cA := cA)
                              (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                              (I := I) (g := g) (evmUrns := evmPostSolm)
                              (evmIlks := evmIlksPostSolm) (out := out)
                              (outIlks := outIlks) hwv hliveSolm hvatCode hcallSolm
                              hdecUrns hvatIlksCode hcallIlksSolm hdecIlks hfitInk
                              hoverArt hsz100)
                        by_cases hspotZero : barkVatIlksSpotWord outIlks = ⟨0⟩
                        · have hpostMemSize :
                              (barkVatIlksPostCallMem σ' I solcFreePtrMem out outIlks).size =
                                544 :=
                            barkVatIlksPostCallMem_size_long (σ := σ') (I := I)
                              solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                          have hpostMemRead64 :
                              ((barkVatIlksPostCallMem σ' I solcFreePtrMem out outIlks).readWithPadding
                                64 32) =
                                UInt256.toByteArray ⟨384⟩ :=
                            barkVatIlksPostCallMem_read64_long (σ := σ') (I := I)
                              solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                          have hrev := RD.dogBarkSpotZeroReverts
                            (v := v) (code := code) (ret := ⟨448⟩)
                            (sel := solcSelectorWord I) (R := []) hpatch hspotZero
                            hpostMemSize hpostMemRead64 rd3308 (by simp)
                          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · have hrev := RD.dogBarkArtRateOverflowReverts
                            (v := v) (code := code) (ret := ⟨448⟩)
                            (sel := solcSelectorWord I) (R := []) hpatch hspotZero
                            hoverArt rd3308 (by simp)
                          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have hfitArt :
                            (barkVatUrnsArtWord out).toNat *
                                (barkVatIlksRateWord outIlks).toNat < UInt256.size :=
                          Nat.lt_of_not_ge hoverArt
                        have hpostMemSize :
                            (barkVatIlksPostCallMem σ' I solcFreePtrMem out outIlks).size =
                              544 :=
                          barkVatIlksPostCallMem_size_long (σ := σ') (I := I)
                            solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                        have hpostMemRead64 :
                            ((barkVatIlksPostCallMem σ' I solcFreePtrMem out outIlks).readWithPadding
                              64 32) =
                              UInt256.toByteArray ⟨384⟩ :=
                          barkVatIlksPostCallMem_read64_long (σ := σ') (I := I)
                            solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                        by_cases hspotZero : barkVatIlksSpotWord outIlks = ⟨0⟩
                        · have hnotSafe :
                              ¬ (0 < (barkVatIlksSpotWord outIlks).toNat ∧
                                (barkInkSpotWord out outIlks).toNat <
                                  (barkArtRateUnsafeWord out outIlks).toNat) := by
                            intro hsafe
                            have hspotNat : (barkVatIlksSpotWord outIlks).toNat = 0 := by
                              simp [hspotZero]
                            omega
                          have hbody :
                              ExecTransitionBody (config v) (contract v) evmSolm
                                (barkLocals I) (barkTransition v).body .reverted := by
                            simpa [evmSolm] using
                              (dogBarkVatIlksNotUnsafeSourceBody (v := v) (cA := cA)
                                (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                                (A := A) (I := I) (g := g) (evmUrns := evmPostSolm)
                                (evmIlks := evmIlksPostSolm) (out := out)
                                (outIlks := outIlks) hwv hliveSolm hvatCode hcallSolm
                                hdecUrns hvatIlksCode hcallIlksSolm hdecIlks hfitInk
                                hfitArt hnotSafe hsz100)
                          have hrev := RD.dogBarkSpotZeroReverts
                            (v := v) (code := code) (ret := ⟨448⟩)
                            (sel := solcSelectorWord I) (R := []) hpatch hspotZero
                            hpostMemSize hpostMemRead64 rd3308 (by simp)
                          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · by_cases hsafeLt :
                              (barkInkSpotWord out outIlks).toNat <
                                (barkArtRateUnsafeWord out outIlks).toNat
                          · by_cases hlimit :
                              (dogSlotWord ⟨5⟩ σ'' I).toNat <
                                  (dogSlotWord ⟨4⟩ σ'' I).toNat ∧
                                (barkIlksDirtWord σ' I).toNat <
                                  (barkIlksHoleWord σ' I).toNat
                            · have hspotPos :
                                  0 < (barkVatIlksSpotWord outIlks).toNat := by
                                have hnatNe :
                                    (barkVatIlksSpotWord outIlks).toNat ≠ 0 := by
                                  intro hnat
                                  exact hspotZero (uint256_toNat_eq_zero hnat)
                                exact Nat.pos_of_ne_zero hnatNe
                              have hsafeEvm :
                                  ((barkVatUrnsInkWord out) *
                                      (barkVatIlksSpotWord outIlks)).toNat <
                                    ((barkVatUrnsArtWord out) *
                                      (barkVatIlksRateWord outIlks)).toNat := by
                                simpa [barkInkSpotWord, barkArtRateUnsafeWord] using
                                  hsafeLt
                              have hrateNe : barkVatIlksRateWord outIlks ≠ ⟨0⟩ := by
                                intro hrateZero
                                have hartRateZero :
                                    (barkArtRateUnsafeWord out outIlks).toNat = 0 := by
                                  rw [barkArtRateUnsafeWord, hrateZero, u256_mul_op_toNat]
                                  simp
                                have hltZero :
                                    (barkInkSpotWord out outIlks).toNat < 0 := by
                                  simpa [hartRateZero] using hsafeLt
                                omega
                              have hartNe : barkVatUrnsArtWord out ≠ ⟨0⟩ := by
                                intro hartZero
                                have hartRateZero :
                                    (barkArtRateUnsafeWord out outIlks).toNat = 0 := by
                                  rw [barkArtRateUnsafeWord, hartZero, u256_mul_op_toNat]
                                  simp
                                have hltZero :
                                    (barkInkSpotWord out outIlks).toNat < 0 := by
                                  simpa [hartRateZero] using hsafeLt
                                omega
                              have hmload288 :=
                                barkVatIlksPostCallMem_mload288_long (σ := σ') (I := I)
                                  solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                              have hmload320 :=
                                barkVatIlksPostCallMem_mload320_long (σ := σ') (I := I)
                                  solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                              have hmload352 :=
                                barkVatIlksPostCallMem_mload352_long (σ := σ') (I := I)
                                  solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                              obtain ⟨_, _, rd3512⟩ :=
                                RD.dogBarkLimitGuardOk
                                  (v := v) (code := code) (ret := ⟨448⟩)
                                  (sel := solcSelectorWord I) (R := [])
                                  (σ := σ'') (σMem := σ')
                                  hpatch hspotZero hfitArt hfitInk hsafeEvm hlimit
                                  hmload320 hmload352 rd3308 (by simp)
                              obtain ⟨_, _, rd3543⟩ :=
                                RD.dogBarkComputeRoom
                                  (v := v) (code := code) (ret := ⟨448⟩)
                                  (sel := solcSelectorWord I) (R := [])
                                  (σ := σ'') (σMem := σ')
                                  hpatch hmload320 hmload352 rd3512 (by simp)
                              have _traceProgress : True := by
                                by_cases hfitRoom :
                                    (barkRoomWord σ'' σ' I).toNat * dogWadWord.toNat <
                                      UInt256.size
                                · by_cases hchopNe : barkIlksChopWord σ' I ≠ ⟨0⟩
                                  · obtain ⟨_, _, rd3594⟩ :=
                                      RD.dogBarkComputeDart
                                        (v := v) (code := code) (ret := ⟨448⟩)
                                        (sel := solcSelectorWord I) (R := [])
                                        (σ := σ'') (σMem := σ')
                                        hpatch hfitRoom hrateNe hchopNe hmload288 rd3543
                                        (by simp)
                                    by_cases hnoLeftover :
                                        (barkVatUrnsArtWord out).toNat ≤
                                          (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                            (barkVatIlksRateWord outIlks)
                                            (barkIlksChopWord σ' I)).toNat
                                    · obtain ⟨_, _, rd3700⟩ :=
                                        RD.dogBarkNoLeftoverToDinkEntry
                                          (v := v) (code := code) (ret := ⟨448⟩)
                                          (sel := solcSelectorWord I) (R := [])
                                          (σ := σ'') hpatch hnoLeftover rd3594 (by simp)
                                      by_cases hfitInkDart :
                                          (barkVatUrnsInkWord out).toNat *
                                            (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                              (barkVatIlksRateWord outIlks)
                                              (barkIlksChopWord σ' I)).toNat <
                                            UInt256.size
                                      · obtain ⟨_, _, rd3726⟩ :=
                                          RD.dogBarkComputeDink
                                            (v := v) (code := code) (ret := ⟨448⟩)
                                            (sel := solcSelectorWord I) (R := [])
                                            (σ := σ'') hpatch hfitInkDart hartNe rd3700
                                            (by simp)
                                        by_cases hdinkPos :
                                            0 < (barkDinkWord (barkVatUrnsInkWord out)
                                              (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                                (barkVatIlksRateWord outIlks)
                                                (barkIlksChopWord σ' I))
                                              (barkVatUrnsArtWord out)).toNat
                                        · obtain ⟨_, _, rd3797⟩ :=
                                            RD.dogBarkDinkGuardOk
                                              (v := v) (code := code) (ret := ⟨448⟩)
                                              (sel := solcSelectorWord I) (R := [])
                                              hpatch hdinkPos rd3726 (by simp)
                                          by_cases hdartBound :
                                              (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                                (barkVatIlksRateWord outIlks)
                                                (barkIlksChopWord σ' I)).toNat ≤
                                                dogInt256LimitWord.toNat
                                          · by_cases hdinkBound :
                                                (barkDinkWord (barkVatUrnsInkWord out)
                                                  (barkDartWord σ'' σ' I
                                                    (barkVatUrnsArtWord out)
                                                    (barkVatIlksRateWord outIlks)
                                                    (barkIlksChopWord σ' I))
                                                  (barkVatUrnsArtWord out)).toNat ≤
                                                  dogInt256LimitWord.toNat
                                            · obtain ⟨_, _, _rd3885⟩ :=
                                                RD.dogBarkInt256GuardOk
                                                  (v := v) (code := code) (ret := ⟨448⟩)
                                                  (sel := solcSelectorWord I) (R := [])
                                                  hpatch hdartBound hdinkBound rd3797
                                                  (by simp)
                                              exact True.intro
                                            · exact True.intro
                                          · exact True.intro
                                        · exact True.intro
                                      · exact True.intro
                                    · have hleftover :
                                          (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                            (barkVatIlksRateWord outIlks)
                                            (barkIlksChopWord σ' I)).toNat <
                                            (barkVatUrnsArtWord out).toNat := by
                                        omega
                                      by_cases hfitLeftoverDue :
                                          (barkLeftoverArtWord (barkVatUrnsArtWord out)
                                            (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                              (barkVatIlksRateWord outIlks)
                                              (barkIlksChopWord σ' I))).toNat *
                                            (barkVatIlksRateWord outIlks).toNat <
                                            UInt256.size
                                      · by_cases hdusty :
                                            (barkLeftoverDueWord (barkVatUrnsArtWord out)
                                              (barkDartWord σ'' σ' I (barkVatUrnsArtWord out)
                                                (barkVatIlksRateWord outIlks)
                                                (barkIlksChopWord σ' I))
                                              (barkVatIlksRateWord outIlks)).toNat <
                                              (barkVatIlksDustWord outIlks).toNat
                                        · obtain ⟨_, _, rd3700⟩ :=
                                            RD.dogBarkDustyLeftoverToDinkEntry
                                              (v := v) (code := code) (ret := ⟨448⟩)
                                              (sel := solcSelectorWord I) (R := [])
                                              (σ := σ'') hpatch hleftover hfitLeftoverDue
                                              hdusty rd3594 (by simp)
                                          by_cases hfitInkDart :
                                              (barkVatUrnsInkWord out).toNat *
                                                (barkVatUrnsArtWord out).toNat <
                                                UInt256.size
                                          · obtain ⟨_, _, rd3726⟩ :=
                                              RD.dogBarkComputeDink
                                                (v := v) (code := code) (ret := ⟨448⟩)
                                                (sel := solcSelectorWord I) (R := [])
                                                (σ := σ'') hpatch hfitInkDart hartNe rd3700
                                                (by simp)
                                            by_cases hdinkPos :
                                                0 < (barkDinkWord (barkVatUrnsInkWord out)
                                                  (barkVatUrnsArtWord out)
                                                  (barkVatUrnsArtWord out)).toNat
                                            · obtain ⟨_, _, rd3797⟩ :=
                                                RD.dogBarkDinkGuardOk
                                                  (v := v) (code := code) (ret := ⟨448⟩)
                                                  (sel := solcSelectorWord I) (R := [])
                                                  hpatch hdinkPos rd3726 (by simp)
                                              by_cases hdartBound :
                                                  (barkVatUrnsArtWord out).toNat ≤
                                                    dogInt256LimitWord.toNat
                                              · by_cases hdinkBound :
                                                    (barkDinkWord (barkVatUrnsInkWord out)
                                                      (barkVatUrnsArtWord out)
                                                      (barkVatUrnsArtWord out)).toNat ≤
                                                      dogInt256LimitWord.toNat
                                                · obtain ⟨_, _, _rd3885⟩ :=
                                                    RD.dogBarkInt256GuardOk
                                                      (v := v) (code := code) (ret := ⟨448⟩)
                                                      (sel := solcSelectorWord I) (R := [])
                                                      hpatch hdartBound hdinkBound rd3797
                                                      (by simp)
                                                  exact True.intro
                                                · exact True.intro
                                              · exact True.intro
                                            · exact True.intro
                                          · exact True.intro
                                        · have hnotDusty :
                                              (barkVatIlksDustWord outIlks).toNat ≤
                                                (barkLeftoverDueWord (barkVatUrnsArtWord out)
                                                  (barkDartWord σ'' σ' I
                                                    (barkVatUrnsArtWord out)
                                                    (barkVatIlksRateWord outIlks)
                                                    (barkIlksChopWord σ' I))
                                                  (barkVatIlksRateWord outIlks)).toNat := by
                                            omega
                                          by_cases hfitPartialDue :
                                              (barkDartWord σ'' σ' I
                                                (barkVatUrnsArtWord out)
                                                (barkVatIlksRateWord outIlks)
                                                (barkIlksChopWord σ' I)).toNat *
                                                (barkVatIlksRateWord outIlks).toNat <
                                                UInt256.size
                                          · by_cases hpartialDueOk :
                                                (barkVatIlksDustWord outIlks).toNat ≤
                                                  (barkPartialDueWord
                                                    (barkDartWord σ'' σ' I
                                                      (barkVatUrnsArtWord out)
                                                      (barkVatIlksRateWord outIlks)
                                                      (barkIlksChopWord σ' I))
                                                    (barkVatIlksRateWord outIlks)).toNat
                                            · obtain ⟨_, _, rd3700⟩ :=
                                                RD.dogBarkPartialLeftoverToDinkEntry
                                                  (v := v) (code := code) (ret := ⟨448⟩)
                                                  (sel := solcSelectorWord I) (R := [])
                                                  (σ := σ'') hpatch hleftover hfitLeftoverDue
                                                  hnotDusty hfitPartialDue hpartialDueOk
                                                  rd3594 (by simp)
                                              by_cases hfitInkDart :
                                                  (barkVatUrnsInkWord out).toNat *
                                                    (barkDartWord σ'' σ' I
                                                      (barkVatUrnsArtWord out)
                                                      (barkVatIlksRateWord outIlks)
                                                      (barkIlksChopWord σ' I)).toNat <
                                                    UInt256.size
                                              · obtain ⟨_, _, rd3726⟩ :=
                                                  RD.dogBarkComputeDink
                                                    (v := v) (code := code) (ret := ⟨448⟩)
                                                    (sel := solcSelectorWord I) (R := [])
                                                    (σ := σ'') hpatch hfitInkDart hartNe rd3700
                                                    (by simp)
                                                by_cases hdinkPos :
                                                    0 < (barkDinkWord (barkVatUrnsInkWord out)
                                                      (barkDartWord σ'' σ' I
                                                        (barkVatUrnsArtWord out)
                                                        (barkVatIlksRateWord outIlks)
                                                        (barkIlksChopWord σ' I))
                                                      (barkVatUrnsArtWord out)).toNat
                                                · obtain ⟨_, _, rd3797⟩ :=
                                                    RD.dogBarkDinkGuardOk
                                                      (v := v) (code := code) (ret := ⟨448⟩)
                                                      (sel := solcSelectorWord I) (R := [])
                                                      hpatch hdinkPos rd3726 (by simp)
                                                  by_cases hdartBound :
                                                      (barkDartWord σ'' σ' I
                                                        (barkVatUrnsArtWord out)
                                                        (barkVatIlksRateWord outIlks)
                                                        (barkIlksChopWord σ' I)).toNat ≤
                                                        dogInt256LimitWord.toNat
                                                  · by_cases hdinkBound :
                                                        (barkDinkWord (barkVatUrnsInkWord out)
                                                          (barkDartWord σ'' σ' I
                                                            (barkVatUrnsArtWord out)
                                                            (barkVatIlksRateWord outIlks)
                                                            (barkIlksChopWord σ' I))
                                                          (barkVatUrnsArtWord out)).toNat ≤
                                                          dogInt256LimitWord.toNat
                                                    · obtain ⟨_, _, _rd3885⟩ :=
                                                        RD.dogBarkInt256GuardOk
                                                          (v := v) (code := code) (ret := ⟨448⟩)
                                                          (sel := solcSelectorWord I) (R := [])
                                                          hpatch hdartBound hdinkBound rd3797
                                                          (by simp)
                                                      exact True.intro
                                                    · exact True.intro
                                                  · exact True.intro
                                                · exact True.intro
                                              · exact True.intro
                                            · exact True.intro
                                          · exact True.intro
                                      · exact True.intro
                                  · exact True.intro
                                · exact True.intro
                              sorry
                            · have hspotPos :
                                  0 < (barkVatIlksSpotWord outIlks).toNat := by
                                have hnatNe :
                                    (barkVatIlksSpotWord outIlks).toNat ≠ 0 := by
                                  intro hnat
                                  exact hspotZero (uint256_toNat_eq_zero hnat)
                                exact Nat.pos_of_ne_zero hnatNe
                              have hslot5 :
                                  dogSlotWord ⟨5⟩ evmIlksPostSolm.accountMap
                                      evmIlksPostSolm.executionEnv =
                                    dogSlotWord ⟨5⟩ σ'' I := by
                                have h :=
                                  dogSlotWord_eq_of_accountMapEquiv hAccountsIlks I ⟨5⟩
                                simpa [evmIlksPostSolm, evmPostSolm, evmSolm, initState]
                                  using h.symm
                              have hslot4 :
                                  dogSlotWord ⟨4⟩ evmIlksPostSolm.accountMap
                                      evmIlksPostSolm.executionEnv =
                                    dogSlotWord ⟨4⟩ σ'' I := by
                                have h :=
                                  dogSlotWord_eq_of_accountMapEquiv hAccountsIlks I ⟨4⟩
                                simpa [evmIlksPostSolm, evmPostSolm, evmSolm, initState]
                                  using h.symm
                              have hAccountsUrns :
                                  accountMapEquiv σ' evmPostSolm.accountMap := by
                                simpa [evmPostEvm] using hStateCall.accountMap
                              have hmilkDirt :
                                  dogSlotWord (barkIlksDirtSlotFor I)
                                      evmPostSolm.accountMap evmPostSolm.executionEnv =
                                    barkIlksDirtWord σ' I := by
                                have h :=
                                  dogSlotWord_eq_of_accountMapEquiv hAccountsUrns I
                                    (barkIlksDirtSlotFor I)
                                rw [barkIlksDirtWord_eq_slotFor (σ := σ') (I := I)
                                  hsz100]
                                simpa [evmPostSolm, evmSolm, initState] using h.symm
                              have hmilkHole :
                                  dogSlotWord (barkIlksHoleSlotFor I)
                                      evmPostSolm.accountMap evmPostSolm.executionEnv =
                                    barkIlksHoleWord σ' I := by
                                have h :=
                                  dogSlotWord_eq_of_accountMapEquiv hAccountsUrns I
                                    (barkIlksHoleSlotFor I)
                                rw [barkIlksHoleWord_eq_slotFor (σ := σ') (I := I)
                                  hsz100]
                                simpa [evmPostSolm, evmSolm, initState] using h.symm
                              have hlimitSource :
                                  ¬ ((dogSlotWord ⟨5⟩ evmIlksPostSolm.accountMap
                                          evmIlksPostSolm.executionEnv).toNat <
                                        (dogSlotWord ⟨4⟩ evmIlksPostSolm.accountMap
                                          evmIlksPostSolm.executionEnv).toNat ∧
                                      (dogSlotWord (barkIlksDirtSlotFor I)
                                          evmPostSolm.accountMap
                                          evmPostSolm.executionEnv).toNat <
                                        (dogSlotWord (barkIlksHoleSlotFor I)
                                          evmPostSolm.accountMap
                                          evmPostSolm.executionEnv).toNat) := by
                                intro hsrc
                                exact hlimit
                                  ⟨by simpa [hslot5, hslot4] using hsrc.1,
                                    by simpa [hmilkDirt, hmilkHole] using hsrc.2⟩
                              have hbody :
                                  ExecTransitionBody (config v) (contract v) evmSolm
                                    (barkLocals I) (barkTransition v).body .reverted := by
                                simpa [evmSolm] using
                                  (dogBarkVatIlksLiquidationLimitHitSourceBody (v := v)
                                    (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                                    (σ₀ := σ₀) (A := A) (I := I) (g := g)
                                    (evmUrns := evmPostSolm) (evmIlks := evmIlksPostSolm)
                                    (out := out) (outIlks := outIlks) hwv hliveSolm
                                    hvatCode hcallSolm hdecUrns hvatIlksCode hcallIlksSolm
                                    hdecIlks hfitInk hfitArt hspotPos hsafeLt hlimitSource
                                    hsz100)
                              have hsafeEvm :
                                  ((barkVatUrnsInkWord out) *
                                      (barkVatIlksSpotWord outIlks)).toNat <
                                    ((barkVatUrnsArtWord out) *
                                      (barkVatIlksRateWord outIlks)).toNat := by
                                simpa [barkInkSpotWord, barkArtRateUnsafeWord] using
                                  hsafeLt
                              have hmload320 :=
                                barkVatIlksPostCallMem_mload320_long (σ := σ') (I := I)
                                  solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                              have hmload352 :=
                                barkVatIlksPostCallMem_mload352_long (σ := σ') (I := I)
                                  solcFreePtrMem_size hretLong hosz hretIlksLong hoszIlks
                              have hrev := RD.dogBarkLiquidationLimitHitReverts
                                (v := v) (code := code) (ret := ⟨448⟩)
                                (sel := solcSelectorWord I) (R := []) (σMem := σ')
                                hpatch hspotZero hfitArt hfitInk hsafeEvm hlimit
                                hmload320 hmload352 hpostMemSize hpostMemRead64 rd3308
                                (by simp)
                              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                          · have hnotSafe :
                                ¬ (0 < (barkVatIlksSpotWord outIlks).toNat ∧
                                  (barkInkSpotWord out outIlks).toNat <
                                    (barkArtRateUnsafeWord out outIlks).toNat) := by
                              intro hsafe
                              exact hsafeLt hsafe.2
                            have hbody :
                                ExecTransitionBody (config v) (contract v) evmSolm
                                  (barkLocals I) (barkTransition v).body .reverted := by
                              simpa [evmSolm] using
                                (dogBarkVatIlksNotUnsafeSourceBody (v := v) (cA := cA)
                                  (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                                  (A := A) (I := I) (g := g) (evmUrns := evmPostSolm)
                                  (evmIlks := evmIlksPostSolm) (out := out)
                                  (outIlks := outIlks) hwv hliveSolm hvatCode hcallSolm
                                  hdecUrns hvatIlksCode hcallIlksSolm hdecIlks hfitInk
                                  hfitArt hnotSafe hsz100)
                            have hnotLtEvm :
                                ((barkVatUrnsArtWord out) *
                                    (barkVatIlksRateWord outIlks)).toNat ≤
                                  ((barkVatUrnsInkWord out) *
                                    (barkVatIlksSpotWord outIlks)).toNat := by
                              change (barkArtRateUnsafeWord out outIlks).toNat ≤
                                (barkInkSpotWord out outIlks).toNat
                              omega
                            have hrev := RD.dogBarkNotUnsafeReverts
                              (v := v) (code := code) (ret := ⟨448⟩)
                              (sel := solcSelectorWord I) (R := []) hpatch hspotZero
                              hfitArt hfitInk hnotLtEvm hpostMemSize hpostMemRead64 rd3308
                              (by simp)
                            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have hretIlksShort : outIlks.size < 160 :=
                      Nat.lt_of_not_ge hretIlksLong
                    have hrev := RD.dogBarkVatIlksReturnDecodeShortReverts hpatch rd3263
                      solcFreePtrMem_size hretLong hosz hretIlksShort hoszIlks
                      (by simp only [List.length_cons, List.length_nil]; omega)
                    have hdecIlks : (config v).externalABI.decode? "ilks" outIlks = none :=
                      barkVatIlksDecode_none_short (v := v) hretIlksShort
                    have hbody :
                        ExecTransitionBody (config v) (contract v) evmSolm (barkLocals I)
                          (barkTransition v).body .reverted := by
                      simpa [evmSolm] using
                        (dogBarkVatIlksDecodeRevertSourceBody (v := v) (cA := cA)
                          (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                          (I := I) (g := g) (evmUrns := evmPostSolm)
                          (evmIlks := evmIlksPostSolm) (out := out)
                          (outIlks := outIlks) hwv hliveSolm hvatCode hcallSolm
                          hdecUrns hvatIlksCode hcallIlksSolm hdecIlks hsz100)
                    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hretShort : out.size < 64 := Nat.lt_of_not_ge hretLong
              have hrev := RD.dogBarkVatUrnsReturnDecodeShortReverts hpatch rd3026
                solcFreePtrMem_size solcFreePtrMem_read64 hretShort hosz
                (by simp only [List.length_cons, List.length_nil]; omega)
              have hdec : (config v).externalABI.decode? "urns" out = none :=
                barkVatUrnsDecode_none_short (v := v) hretShort
              have hbody :
                  ExecTransitionBody (config v) (contract v) evmSolm (barkLocals I)
                    (barkTransition v).body .reverted := by
                simpa [evmSolm] using
                  (dogBarkVatUrnsDecodeRevertSourceBody (v := v) (cA := cA)
                    (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A)
                    (I := I) (g := g) (evmCall := evmPostSolm) (out := out)
                    hwv hliveSolm hvatCode hcallSolm hdec)
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hdepth1024 : I.depth = 1024 := by
            apply Fin.ext
            have hlt := I.depth.isLt
            rw [not_lt] at hdepthLt
            omega
          have hrev := RD.dogBarkVatUrnsStaticcallDepthLimitRevert
            (v := v) (code := code) (ret := ⟨448⟩) (sel := solcSelectorWord I)
            (R := []) hpatch h2885 solcFreePtrMem_size solcFreePtrMem_read64
            hvatCodeSizeNe hdepth1024 (by simp)
          let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let evmCall :=
            { evm0 with
              substate :=
                (evm0.addAccessedAccount
                  (EVM.address (AccountAddress.ofNat v.vat.toNat))).substate }
          have hcallDepth :
              typedCallViaEVM (config v) evm0
                (EVM.address (AccountAddress.ofNat v.vat.toNat)) "urns" 0
                [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)]
                (false, evmCall, ByteArray.empty) false := by
            simpa [evm0, evmCall, initState] using
              (callNotMade_depthLimit (cfg := config v) (evm := evm0)
                (tgt := EVM.address (AccountAddress.ofNat v.vat.toNat)) (name := "urns")
                (args := [.fixedBytes bytes32Width (barkIlkBytes I), .address (barkUrn I)])
                (callPerm := false)
                (barkVatUrnsEncode_eq (v := v) (I := I) (mem := solcFreePtrMem)
                  hsz100 solcFreePtrMem_size)
                (by simpa [evm0, initState] using hdepth1024))
          have hbody :
              ExecTransitionBody (config v) (contract v) evm0 (barkLocals I)
                (barkTransition v).body .reverted := by
            simpa [evm0] using
              (dogBarkVatUrnsCallFailureSourceBody (v := v) (cA := cA) (gh := gh)
                (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
                (g := g) (evmCall := evmCall) (out := ByteArray.empty)
                hwv hliveSolm hvatCode hcallDepth)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hslotWord :
          dogSlotWord ⟨3⟩ σ_evm I = dogSlotWord ⟨3⟩ σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
      have hliveSolm : dogSlotWord ⟨3⟩ σ_solm I ≠ ⟨1⟩ := by
        intro hsolm
        exact hliveEvm (by rw [hslotWord, hsolm])
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody (config v) (contract v) evm0 (barkLocals I)
            (barkTransition v).body .reverted := by
        simpa [evm0, barkTransition, barkBodyRest] using
          dogNonpayableLivePrefixRevert (v := v) (cA := cA) (gh := gh)
            (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) (locals := barkLocals I)
            (rest := (barkBodyRest v).drop 1)
            (barkLocals_get_live I) hwv hliveSolm
      have hrev := RD.dogBarkLiveRevert hpatch hbodyReach
        (by simpa [dogSlotWord] using hliveEvm)
        (by simp only [List.length_cons, List.length_nil]; omega)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact dogBarkBodyCoreDecodeFailed_short hpatch hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dog
