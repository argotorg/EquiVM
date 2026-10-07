import Reasoning.ABIViews
import Reasoning.Memory
import Benchmarks.Dss.Spot.Ilks
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

theorem pokePeekPostCallWrite_size_gt64 (out base : ByteArray) (L : Nat)
    (hbase : base.size = 160) (hLo : L ≤ out.size) :
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

end Benchmarks.Dss.Spot

end

namespace Benchmarks.Dss.Spot

/-! ## `poke(bytes32)` setup -/

abbrev pokeIlkBytes (I : ExecutionEnv) : List UInt8 :=
  ilksArgBytes I

abbrev pokeIlkWord (I : ExecutionEnv) : UInt256 :=
  ilksArgWord I

abbrev pokeIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (pokeIlkBytes I)

abbrev pokeIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (pokeIlkBytes I)

abbrev pokeLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (pokeIlkValue I)

abbrev pokePipEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (pokeIlkKey I), .field "pip"] }

abbrev pokePipSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (pokeIlkKey I)

abbrev pokeMatSlotFor (I : ExecutionEnv) : UInt256 :=
  pokePipSlotFor I + ⟨1⟩

abbrev pokePipRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWordAt (pokePipSlotFor I) σ I

abbrev pokePipTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (pokePipRawWord σ I) solcAddrMask

abbrev pokePipHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (pokeIlkWord I) ⟨1⟩ solcFreePtrMem

abbrev pokePeekSelectorPlainWord : UInt256 :=
  ⟨1507864023⟩

def pokePeekSelectorWord : UInt256 :=
  UInt256.shiftLeft pokePeekSelectorPlainWord ⟨224⟩

abbrev pokePeekOutPtr : UInt256 :=
  ⟨128⟩

abbrev pokePeekInSize : UInt256 :=
  ⟨4⟩

abbrev pokePeekOutSize : UInt256 :=
  ⟨64⟩

abbrev pokePeekEndPtr : UInt256 :=
  ⟨132⟩

def pokePeekCalldataMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray pokePeekSelectorWord).write 0
    (pokePipHashMem I) 128 32

def pokePeekPostCallMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (pokePeekCalldataMem I) pokePeekOutPtr.toNat
    (min pokePeekOutSize (UInt256.ofNat out.size)).toNat

abbrev pokePeekValBytes (out : ByteArray) : List UInt8 :=
  (out.toList.drop 0).take 32

abbrev pokePeekValWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev pokePeekHasWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

abbrev pokePeekHasBool (out : ByteArray) : Bool :=
  pokePeekHasWord out ≠ ⟨0⟩

abbrev pokePeekReturnValues (out : ByteArray) : List Value :=
  [.fixedBytes bytes32Width (pokePeekValBytes out), .bool (pokePeekHasBool out)]

abbrev pokePipAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (pokePipTargetWord σ I).toNat

abbrev pokeVatTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcAddressSlotWord ⟨2⟩ σ I

abbrev pokeVatAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (pokeVatTargetWord σ I).toNat

abbrev pokeVatFileSelectorPlainWord : UInt256 :=
  ⟨436938878⟩

abbrev pokeVatFileSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨218469439⟩ ⟨225⟩

abbrev pokeSpotParamBytes : List UInt8 :=
  [115, 112, 111, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev pokeSpotParamWord : UInt256 :=
  UInt256.shiftLeft ⟨484187101⟩ ⟨226⟩

abbrev pokeVatFileOutPtr : UInt256 :=
  ⟨128⟩

abbrev pokeVatFileInSize : UInt256 :=
  ⟨100⟩

abbrev pokeVatFileOutSize : UInt256 :=
  ⟨0⟩

abbrev pokeVatFileEndPtr : UInt256 :=
  ⟨228⟩

def pokeVatFileSelectorMem (mem : ByteArray) : ByteArray :=
  pokeVatFileSelectorShifted.toByteArray.write 0 mem pokeVatFileOutPtr.toNat 32

def pokeVatFileIlkMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (pokeIlkWord I).toByteArray.write 0 (pokeVatFileSelectorMem mem)
    (pokeVatFileOutPtr + ⟨4⟩).toNat 32

def pokeVatFileWhatMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  pokeSpotParamWord.toByteArray.write 0 (pokeVatFileIlkMem I mem)
    (pokeVatFileOutPtr + ⟨36⟩).toNat 32

def pokeVatFileCalldataMem
    (I : ExecutionEnv) (spot : UInt256) (mem : ByteArray) : ByteArray :=
  spot.toByteArray.write 0 (pokeVatFileWhatMem I mem)
    (pokeVatFileOutPtr + ⟨68⟩).toNat 32

abbrev pokeEventTopic : UInt256 :=
  ⟨101246123879181155085265228494766967589555279929922161514950944312404277086318⟩

def pokeEventIlkMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (pokeIlkWord I).toByteArray.write 0 mem pokeVatFileOutPtr.toNat 32

def pokeEventValMem (I : ExecutionEnv) (val : UInt256)
    (mem : ByteArray) : ByteArray :=
  val.toByteArray.write 0 (pokeEventIlkMem I mem) (pokeVatFileOutPtr + ⟨32⟩).toNat 32

def pokeEventSpotMem (I : ExecutionEnv) (val spot : UInt256)
    (mem : ByteArray) : ByteArray :=
  spot.toByteArray.write 0 (pokeEventValMem I val mem) (⟨64⟩ + pokeVatFileOutPtr).toNat 32

abbrev pokePeekLocals (I : ExecutionEnv) (out : ByteArray) : Store :=
  (pokeLocals I).insert "peekRet" (collapseReturns (pokePeekReturnValues out))

abbrev pokeValLocals (I : ExecutionEnv) (out : ByteArray) : Store :=
  (pokePeekLocals I out).insert "val" (.fixedBytes bytes32Width (pokePeekValBytes out))

abbrev pokeHasLocals (I : ExecutionEnv) (out : ByteArray) : Store :=
  (pokeValLocals I out).insert "has" (.bool (pokePeekHasBool out))

abbrev pokeSpotLocals (I : ExecutionEnv) (out : ByteArray) (spot : UInt256) : Store :=
  (pokeHasLocals I out).insert "spot" (.int (Int.ofNat spot.toNat))

abbrev pokeBillion : UInt256 :=
  ⟨1000000000⟩

abbrev pokeRay : UInt256 :=
  ⟨1000000000000000000000000000⟩

abbrev pokeValScaledLocals (I : ExecutionEnv) (out : ByteArray)
    (valScaled : UInt256) : Store :=
  (pokeSpotLocals I out ⟨0⟩).insert "valScaled" (.int (Int.ofNat valScaled.toNat))

abbrev pokeSpot1Locals (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 : UInt256) : Store :=
  (pokeValScaledLocals I out valScaled).insert "spot1" (.int (Int.ofNat spot1.toNat))

abbrev pokeSpot2Locals (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 spot2 : UInt256) : Store :=
  (pokeSpot1Locals I out valScaled spot1).insert "spot2" (.int (Int.ofNat spot2.toNat))

abbrev pokeSpotAssignedLocals (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 spot2 : UInt256) : Store :=
  (pokeSpot2Locals I out valScaled spot1 spot2).insert "spot"
    (.int (Int.ofNat spot2.toNat))

abbrev pokeTrueBranchStmts : List Stmt :=
  checkedMulUintInto "valScaled" (.cast (.var "val") uint256St) (.intLit billion) ++
    [ .internalCall "rdiv" [.var "valScaled", .storage parRef] "spot1",
      .internalCall "rdiv" [.var "spot1", .storage (ilksF (.var "ilk") "mat")]
        "spot2",
      .assign .localVar { base := "spot" } (.var "spot2") ]

abbrev pokeAfterSpotStmts : List Stmt :=
  [ .ite (.var "has") pokeTrueBranchStmts [] ] ++
    checkedExternalCallStmts (.storage vatRef) "file" (.intLit 0)
      [.var "ilk", spotParamLit, .var "spot"] "_fileRet" ++
    [.emit "Poke" [.var "ilk", .var "val", .var "spot"]]

abbrev spotUintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev spotUintBinaryLocalsZ (x y z : UInt256) : Store :=
  (spotUintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

abbrev spotUintBinaryLocalsZAssigned (x y old new : UInt256) : Store :=
  (spotUintBinaryLocalsZ x y old).insert "z" (.int (Int.ofNat new.toNat))

theorem pokePeekCalldataMem_size (I : ExecutionEnv) :
    (pokePeekCalldataMem I).size = 160 := by
  unfold pokePeekCalldataMem
  exact toByteArray_write32_size_of_ge
    (base := pokePipHashMem I) (word := pokePeekSelectorWord)
    (off := 128) (baseSize := 96) (finalSize := 160)
    (twoWordHashMem_size_96 (pokeIlkWord I) ⟨1⟩ solcFreePtrMem_size)
    (by norm_num)
    (by exact lt_usize 32 (by norm_num))
    (by norm_num)

theorem pokePeekCalldataMem_read64 (I : ExecutionEnv) :
    (pokePeekCalldataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold pokePeekCalldataMem
  rw [toByteArray_write_read_below_of_gap _ _ 128 64
      (by rw [twoWordHashMem_size_96 (pokeIlkWord I) ⟨1⟩ solcFreePtrMem_size])
      (by norm_num)
      (by
        rw [twoWordHashMem_size_96 (pokeIlkWord I) ⟨1⟩ solcFreePtrMem_size]
        exact lt_usize 32 (by norm_num)),
    twoWordHashMem_read64 (pokeIlkWord I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64]

theorem pokePeekCalldataMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (pokePeekCalldataMem I).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((pokePeekCalldataMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ :=
  mloadFreePtrValue (by rw [pokePeekCalldataMem_size]; decide)
    (pokePeekCalldataMem_read64 I)

theorem pokePipHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (pokePipHashMem I).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((pokePipHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [twoWordHashMem_size_96 (pokeIlkWord I) ⟨1⟩ solcFreePtrMem_size]; decide)
    (twoWordHashMem_read64 (pokeIlkWord I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64)

theorem pokePeekSelectorWord_extract :
    (UInt256.toByteArray pokePeekSelectorWord).extract 0 4 = pipPeekSelector := by
  native_decide

theorem pokePeekCalldataMem_read128_4 (I : ExecutionEnv) :
    (pokePeekCalldataMem I).readWithPadding 128 4 = pipPeekSelector := by
  unfold pokePeekCalldataMem
  rw [toByteArray_write_read_window_of_gap _ _ 128 0 4
    (by norm_num) (by norm_num) (by norm_num)
    (by
      rw [twoWordHashMem_size_96 (pokeIlkWord I) ⟨1⟩ solcFreePtrMem_size]
      exact lt_usize 32 (by norm_num))]
  exact pokePeekSelectorWord_extract

theorem pokePeekEncode_eq (I : ExecutionEnv) :
    config.externalABI.encode? "peek" [] =
      some ((pokePeekCalldataMem I).readWithPadding 128 4) := by
  rw [pokePeekCalldataMem_read128_4]
  simp [config, spotExternalABI, pipPeekSelector]


theorem pokePeekPostCallMem_size_gt64 (I : ExecutionEnv) (out : ByteArray)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    64 < (pokePeekPostCallMem I out).size := by
  unfold pokePeekPostCallMem
  have hlen :
      (min pokePeekOutSize (UInt256.ofNat out.size)).toNat = out.size :=
    umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
  rw [hlen]
  exact pokePeekPostCallWrite_size_gt64 out (pokePeekCalldataMem I) out.size
    (pokePeekCalldataMem_size I) le_rfl

theorem pokePeekPostCallMem_read64 (I : ExecutionEnv) (out : ByteArray)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    (pokePeekPostCallMem I out).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold pokePeekPostCallMem
  have hlen :
      (min pokePeekOutSize (UInt256.ofNat out.size)).toNat = out.size :=
    umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
  rw [hlen]
  change (out.write 0 (pokePeekCalldataMem I) 128 out.size).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact pokePeekCalldataMem_read64 I
  · rw [write_read_below_gen_extend out (pokePeekCalldataMem I)
        128 out.size 64 hzero le_rfl
        (by rw [pokePeekCalldataMem_size I]; omega) (by omega)]
    exact pokePeekCalldataMem_read64 I

theorem pokePeekPostCallMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (pokePeekPostCallMem I out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((pokePeekPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by
      have hgt := pokePeekPostCallMem_size_gt64 I out hshort hout
      omega)
    (pokePeekPostCallMem_read64 I out hshort hout)

theorem pokePeekPostCallMem_size_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (pokePeekPostCallMem I out).size = 192 := by
  unfold pokePeekPostCallMem
  have hlen :
      (min pokePeekOutSize (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  change (out.write 0 (pokePeekCalldataMem I) 128 64).size = 192
  rw [write_eq_gen_extend out (pokePeekCalldataMem I) 128 64
    (by omega) (by omega)
    (by rw [pokePeekCalldataMem_size I]; omega)
    (by rw [pokePeekCalldataMem_size I]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
  rw [pokePeekCalldataMem_size I]
  omega

theorem pokePeekPostCallMem_read64_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (pokePeekPostCallMem I out).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold pokePeekPostCallMem
  have hlen :
      (min pokePeekOutSize (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  change (out.write 0 (pokePeekCalldataMem I) 128 64).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
  rw [write_read_below_gen_extend out (pokePeekCalldataMem I)
    128 64 64 (by omega) (by omega)
    (by rw [pokePeekCalldataMem_size I]; omega) (by omega)]
  exact pokePeekCalldataMem_read64 I

theorem pokePeekPostCallMem_mload64_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (pokePeekPostCallMem I out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((pokePeekPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [pokePeekPostCallMem_size_long I out hlo hout]; decide)
    (pokePeekPostCallMem_read64_long I out hlo hout)

theorem pokePeekPostCallMem_read128_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (pokePeekPostCallMem I out).readWithPadding 128 32 = out.extract 0 32 := by
  unfold pokePeekPostCallMem
  have hlen :
      (min pokePeekOutSize (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  change (out.write 0 (pokePeekCalldataMem I) 128 64).readWithPadding
      128 32 = out.extract 0 32
  rw [write_eq_gen_extend out (pokePeekCalldataMem I) 128 64
    (by omega) (by omega)
    (by rw [pokePeekCalldataMem_size I]; omega)
    (by rw [pokePeekCalldataMem_size I]; omega)]
  have hprefix : ((pokePeekCalldataMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, pokePeekCalldataMem_size I]
    omega
  have hsrc : (out.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((pokePeekCalldataMem I).extract 0 128 ++ out.extract 0 64).size = 192 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      128 + 32 ≤ ((pokePeekCalldataMem I).extract 0 128 ++ out.extract 0 64).size := by
    rw [hmemSize]
    norm_num
  rw [readWithPadding_eq_extract _ 128 hreadIn]
  rw [extract_append_right_window _ _ 128 160 (by rw [hprefix])]
  rw [hprefix, show 128 - 128 = 0 by omega, show 160 - 128 = 32 by omega]
  rw [extract_extract_BA]
  norm_num

theorem pokePeekPostCallMem_mload128_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (pokePeekPostCallMem I out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((pokePeekPostCallMem I out).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      pokePeekValWord out := by
  unfold pokePeekValWord
  have hnot : ¬ (128 ≥ (pokePeekPostCallMem I out).size) := by
    rw [pokePeekPostCallMem_size_long I out hlo hout]
    decide
  change (if 128 ≥ (pokePeekPostCallMem I out).size then ⟨0⟩
    else UInt256.ofNat
      (fromByteArrayBigEndian ((pokePeekPostCallMem I out).readWithPadding 128 32))) =
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  rw [if_neg hnot]
  change UInt256.ofNat
    (fromByteArrayBigEndian ((pokePeekPostCallMem I out).readWithPadding 128 32)) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))
  rw [pokePeekPostCallMem_read128_long I out hlo hout]

theorem pokePeekPostCallMem_read160_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (pokePeekPostCallMem I out).readWithPadding 160 32 = out.extract 32 64 := by
  unfold pokePeekPostCallMem
  have hlen :
      (min pokePeekOutSize (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  change (out.write 0 (pokePeekCalldataMem I) 128 64).readWithPadding
      160 32 = out.extract 32 64
  rw [write_eq_gen_extend out (pokePeekCalldataMem I) 128 64
    (by omega) (by omega)
    (by rw [pokePeekCalldataMem_size I]; omega)
    (by rw [pokePeekCalldataMem_size I]; omega)]
  have hprefix : ((pokePeekCalldataMem I).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, pokePeekCalldataMem_size I]
    omega
  have hsrc : (out.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((pokePeekCalldataMem I).extract 0 128 ++ out.extract 0 64).size = 192 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      160 + 32 ≤ ((pokePeekCalldataMem I).extract 0 128 ++ out.extract 0 64).size := by
    rw [hmemSize]
  rw [readWithPadding_eq_extract _ 160 hreadIn]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem pokePeekPostCallMem_mload160_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (pokePeekPostCallMem I out).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((pokePeekPostCallMem I out).readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      pokePeekHasWord out := by
  unfold pokePeekHasWord
  have hnot : ¬ (160 ≥ (pokePeekPostCallMem I out).size) := by
    rw [pokePeekPostCallMem_size_long I out hlo hout]
    decide
  change (if 160 ≥ (pokePeekPostCallMem I out).size then ⟨0⟩
    else UInt256.ofNat
      (fromByteArrayBigEndian ((pokePeekPostCallMem I out).readWithPadding 160 32))) =
    UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))
  rw [if_neg hnot]
  change UInt256.ofNat
    (fromByteArrayBigEndian ((pokePeekPostCallMem I out).readWithPadding 160 32)) =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))
  rw [pokePeekPostCallMem_read160_long I out hlo hout]

theorem pokePeek_bytesToWord_drop32_eq_extract32_64 (out : ByteArray) :
    ABI.bytesToWord ((out.toList.drop 32).take 32) = pokePeekHasWord out := by
  unfold pokePeekHasWord
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.extract 32 64), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  simp [byteArray_toList_eq]


theorem pokePeekDecode_none_short {out : ByteArray} (hshort : out.size < 64) :
    config.externalABI.decode? "peek" out = none := by
  have h := decode_none_short_aux (out := out) hshort
  simpa [config, spotExternalABI, bytes32, bytes32Width, boolTy, abiBytes32, abiBytes32Width,
    abiBool] using h


theorem pokePeekDecode_ok_aux {out : ByteArray} (hlo : 64 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiBytes32, abiBool] out =
      some (pokePeekReturnValues out) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : (out.toList.take 32).length = 32 := by
    rw [List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword1 := pokePeek_bytesToWord_drop32_eq_extract32_64 out
  unfold ABI.decodeReturnValuesWithMode?
  rw [show abiTupleHeadSize? [abiBytes32, abiBool] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_legacy_ok (bytes := out.toList) htake0 htake32]
  simp [pokePeekReturnValues, pokePeekValBytes, pokePeekHasBool, hword1, bytes32Width,
    abiBytes32Width]

theorem pokePeekDecode_ok {out : ByteArray} (hlo : 64 ≤ out.size) :
    config.externalABI.decode? "peek" out = some (pokePeekReturnValues out) := by
  have h := pokePeekDecode_ok_aux (out := out) hlo
  simpa [config, spotExternalABI, bytes32, bytes32Width, boolTy, abiBytes32, abiBytes32Width,
    abiBool] using h

theorem pokeVatFileSelectorMem_size {mem : ByteArray} (hmem : mem.size = 192) :
    (pokeVatFileSelectorMem mem).size = 192 := by
  unfold pokeVatFileSelectorMem pokeVatFileOutPtr
  exact toByteArray_write32_size_of_le mem pokeVatFileSelectorShifted 128 192 192 hmem
    (by rw [hmem]; omega) (by omega)

theorem pokeVatFileIlkMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 192) :
    (pokeVatFileIlkMem I mem).size = 192 := by
  have hoff : (pokeVatFileOutPtr + ⟨4⟩).toNat = 132 := by native_decide
  unfold pokeVatFileIlkMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (pokeVatFileSelectorMem mem) (pokeIlkWord I)
    132 192 192 (pokeVatFileSelectorMem_size hmem)
    (by rw [pokeVatFileSelectorMem_size hmem]; omega) (by omega)

theorem pokeVatFileWhatMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 192) :
    (pokeVatFileWhatMem I mem).size = 196 := by
  have hoff : (pokeVatFileOutPtr + ⟨36⟩).toNat = 164 := by native_decide
  unfold pokeVatFileWhatMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (pokeVatFileIlkMem I mem) pokeSpotParamWord
    164 192 196 (pokeVatFileIlkMem_size I hmem)
    (by rw [pokeVatFileIlkMem_size I hmem]; omega) (by omega)

theorem pokeVatFileCalldataMem_size (I : ExecutionEnv) (spot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192) :
    (pokeVatFileCalldataMem I spot mem).size = 228 := by
  have hoff : (pokeVatFileOutPtr + ⟨68⟩).toNat = 196 := by native_decide
  unfold pokeVatFileCalldataMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (pokeVatFileWhatMem I mem) spot 196 196 228
    (pokeVatFileWhatMem_size I hmem)
    (by rw [pokeVatFileWhatMem_size I hmem]) (by omega)

theorem pokeVatFileSelectorMem_read64 {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (pokeVatFileSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold pokeVatFileSelectorMem pokeVatFileOutPtr
  change (pokeVatFileSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega)]
  exact hread64

theorem pokeVatFileIlkMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (pokeVatFileIlkMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hoff : (pokeVatFileOutPtr + ⟨4⟩).toNat = 132 := by native_decide
  unfold pokeVatFileIlkMem
  rw [hoff, write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [pokeVatFileSelectorMem_size hmem]; omega) (by omega)]
  exact pokeVatFileSelectorMem_read64 hmem hread64

theorem pokeVatFileWhatMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (pokeVatFileWhatMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hoff : (pokeVatFileOutPtr + ⟨36⟩).toNat = 164 := by native_decide
  unfold pokeVatFileWhatMem
  rw [hoff, write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [pokeVatFileIlkMem_size I hmem]; omega) (by omega)]
  exact pokeVatFileIlkMem_read64 I hmem hread64

theorem pokeVatFileCalldataMem_read64 (I : ExecutionEnv) (spot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (pokeVatFileCalldataMem I spot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hoff : (pokeVatFileOutPtr + ⟨68⟩).toNat = 196 := by native_decide
  unfold pokeVatFileCalldataMem
  rw [hoff, write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [pokeVatFileWhatMem_size I hmem]) (by omega)]
  exact pokeVatFileWhatMem_read64 I hmem hread64

theorem pokeVatFileCalldataMem_mload64 (I : ExecutionEnv) (spot : UInt256)
    {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (pokeVatFileCalldataMem I spot mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((pokeVatFileCalldataMem I spot mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [pokeVatFileCalldataMem_size I spot hmem]; decide) (pokeVatFileCalldataMem_read64 I spot hmem hread64)

theorem pokeEventIlkMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (pokeEventIlkMem I mem).size = 228 := by
  unfold pokeEventIlkMem pokeVatFileOutPtr
  exact toByteArray_write32_size_of_le mem (pokeIlkWord I) 128 228 228 hmem
    (by rw [hmem]; omega) (by omega)

theorem pokeEventValMem_size (I : ExecutionEnv) (val : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (pokeEventValMem I val mem).size = 228 := by
  have hoff : (pokeVatFileOutPtr + ⟨32⟩).toNat = 160 := by native_decide
  unfold pokeEventValMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (pokeEventIlkMem I mem) val 160 228 228
    (pokeEventIlkMem_size I hmem)
    (by rw [pokeEventIlkMem_size I hmem]; omega) (by omega)

theorem pokeEventSpotMem_size (I : ExecutionEnv) (val spot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (pokeEventSpotMem I val spot mem).size = 228 := by
  have hoff : (⟨64⟩ + pokeVatFileOutPtr).toNat = 192 := by native_decide
  unfold pokeEventSpotMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (pokeEventValMem I val mem) spot 192 228 228
    (pokeEventValMem_size I val hmem)
    (by rw [pokeEventValMem_size I val hmem]; omega) (by omega)

theorem pokeEventSpotMem_read64 (I : ExecutionEnv) (val spot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (pokeEventSpotMem I val spot mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hoff2 : (⟨64⟩ + pokeVatFileOutPtr).toNat = 192 := by native_decide
  have hoff1 : (pokeVatFileOutPtr + ⟨32⟩).toNat = 160 := by native_decide
  unfold pokeEventSpotMem pokeEventValMem pokeEventIlkMem
  rw [hoff2, write32_read_below _ _ 192 64 (by rw [toByteArray_size])
    (by
      change 192 ≤ (pokeEventValMem I val mem).size
      rw [pokeEventValMem_size I val hmem]
      omega)
    (by omega)]
  rw [hoff1, write32_read_below _ _ 160 64 (by rw [toByteArray_size])
    (by
      change 160 ≤ (pokeEventIlkMem I mem).size
      rw [pokeEventIlkMem_size I hmem]
      omega)
    (by omega)]
  change ((pokeIlkWord I).toByteArray.write 0 mem 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega)]
  exact hread64

theorem pokeEventSpotMem_mload64 (I : ExecutionEnv) (val spot : UInt256)
    {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (pokeEventSpotMem I val spot mem).size then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((pokeEventSpotMem I val spot mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [pokeEventSpotMem_size I val spot hmem]; decide) (pokeEventSpotMem_read64 I val spot hmem hread64)


theorem pokeVatFileCalldataMem_read128_100
    (I : ExecutionEnv) (spot : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192) :
    (pokeVatFileCalldataMem I spot mem).readWithPadding 128 100 =
      vatFileSelector ++ (pokeIlkWord I).toByteArray ++
        pokeSpotParamWord.toByteArray ++ spot.toByteArray := by
  let final := pokeVatFileCalldataMem I spot mem
  have hfinalSize : final.size = 228 := by
    dsimp [final]
    exact pokeVatFileCalldataMem_size I spot hmem
  have h132 : (pokeVatFileOutPtr + ⟨4⟩).toNat = 132 := by native_decide
  have h164 : (pokeVatFileOutPtr + ⟨36⟩).toNat = 164 := by native_decide
  have h196 : (pokeVatFileOutPtr + ⟨68⟩).toNat = 196 := by native_decide
  have hselectorRead : final.readWithPadding 128 4 = vatFileSelector := by
    dsimp [final]
    unfold pokeVatFileCalldataMem
    rw [h196]
    rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
      (by rw [pokeVatFileWhatMem_size I hmem]) (by omega)
      (by rw [pokeVatFileWhatMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold pokeVatFileWhatMem
    rw [h164]
    rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
      (by rw [pokeVatFileIlkMem_size I hmem]; omega) (by omega)
      (by rw [pokeVatFileIlkMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold pokeVatFileIlkMem
    rw [h132]
    rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [pokeVatFileSelectorMem_size hmem]; omega) (by omega)
      (by rw [pokeVatFileSelectorMem_size hmem]; omega) (by omega) (by norm_num)]
    unfold pokeVatFileSelectorMem pokeVatFileOutPtr
    change
      (pokeVatFileSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
        vatFileSelector
    rw [write32_read_prefix_len _ _ 128 4 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega) (by omega) (by norm_num)]
    unfold pokeVatFileSelectorShifted vatFileSelector selectorBytes
    native_decide
  have hilkRead : final.readWithPadding 132 32 = (pokeIlkWord I).toByteArray := by
    dsimp [final]
    unfold pokeVatFileCalldataMem
    rw [h196]
    rw [write32_read_below_len _ _ 196 132 32 (by rw [toByteArray_size])
      (by rw [pokeVatFileWhatMem_size I hmem]) (by omega)
      (by rw [pokeVatFileWhatMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold pokeVatFileWhatMem
    rw [h164]
    rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
      (by rw [pokeVatFileIlkMem_size I hmem]; omega) (by omega)
      (by rw [pokeVatFileIlkMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold pokeVatFileIlkMem
    rw [h132]
    rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
      (by rw [pokeVatFileSelectorMem_size hmem]; omega) (by omega) (by omega)
      (by norm_num)]
    rw [toByteArray_extract_all]
  have hwhatRead : final.readWithPadding 164 32 = pokeSpotParamWord.toByteArray := by
    dsimp [final]
    unfold pokeVatFileCalldataMem
    rw [h196]
    rw [write32_read_below_len _ _ 196 164 32 (by rw [toByteArray_size])
      (by rw [pokeVatFileWhatMem_size I hmem]) (by omega)
      (by rw [pokeVatFileWhatMem_size I hmem]) (by omega) (by norm_num)]
    unfold pokeVatFileWhatMem
    rw [h164]
    rw [write32_read_prefix_len _ _ 164 32 (by rw [toByteArray_size])
      (by rw [pokeVatFileIlkMem_size I hmem]; omega) (by omega) (by omega)
      (by norm_num)]
    rw [toByteArray_extract_all]
  have hspotRead : final.readWithPadding 196 32 = spot.toByteArray := by
    dsimp [final]
    unfold pokeVatFileCalldataMem
    rw [h196]
    rw [write32_read_back _ _ 196 (by rw [toByteArray_size])
      (by rw [pokeVatFileWhatMem_size I hmem])]
    rw [toByteArray_extract_all]
  rw [readWithPadding_eq_extract' final 128 100 (by norm_num) (by norm_num)
    (by rw [hfinalSize])]
  have hselectorExt : final.extract 128 132 = vatFileSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselectorRead
  have hilkExt : final.extract 132 164 = (pokeIlkWord I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hilkRead
  have hwhatExt : final.extract 164 196 = pokeSpotParamWord.toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hwhatRead
  have hspotExt : final.extract 196 228 = spot.toByteArray := by
    rw [← readWithPadding_eq_extract' final 196 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize])]
    exact hspotRead
  have hsplit : final.extract 128 228 =
      final.extract 128 132 ++ final.extract 132 164 ++ final.extract 164 196 ++
        final.extract 196 228 := by
    rw [show final.extract 128 228 = final.extract 128 132 ++ final.extract 132 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 132 228 = final.extract 132 164 ++ final.extract 164 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 164 228 = final.extract 164 196 ++ final.extract 196 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    simp [ByteArray.append_assoc]
  rw [hsplit, hselectorExt, hilkExt, hwhatExt, hspotExt]
end Benchmarks.Dss.Spot
