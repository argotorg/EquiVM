import Benchmarks.Dss.Jug.Rpow
import Benchmarks.Dss.Jug.FileDuty
import Reasoning.ExternalCall
import Reasoning.Initcode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Jug

abbrev dripLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "ilk" (.fixedBytes bytes32Width (fileDutyIlkBytes I))

noncomputable abbrev dripIlkHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (fileDutyIlkWord I) ⟨1⟩ solcFreePtrMem

theorem dripIlkHashMem_size (I : ExecutionEnv) :
    (dripIlkHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (fileDutyIlkWord I) ⟨1⟩ solcFreePtrMem_size

theorem dripIlkHashMem_read64 (I : ExecutionEnv) :
    (dripIlkHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (fileDutyIlkWord I) ⟨1⟩
    solcFreePtrMem_size solcFreePtrMem_read64

theorem jugDecode_drip_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
      (transitionSignature dripTransition).paramTypes I.calldata =
        some (dripLocals I) := by
  simpa [config, dripTransition, dripLocals, fileDutyIlkBytes, bytes32, bytes32Width] using
    (decodeCalldataWithMode_legacyBytes32_ok (cd := I.calldata) (x := "ilk") hsz36)

theorem jugDecode_drip_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
      (transitionSignature dripTransition).paramTypes I.calldata = none := by
  simpa [config, dripTransition, bytes32, bytes32Width] using
    (decodeCalldataWithMode_legacyBytes32_none_short (cd := I.calldata) (x := "ilk")
      hsz4 hshort)

theorem dripLocals_get_ilk (I : ExecutionEnv) :
    (dripLocals I).get? "ilk" =
      some (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
  rw [dripLocals, store_get_self]

theorem dripLocals_get_ilks (I : ExecutionEnv) :
    (dripLocals I).get? "ilks" = none := by
  rw [dripLocals, store_get_ne _ _ (by decide)]
  simp

theorem dripLocals_get_vat (I : ExecutionEnv) :
    (dripLocals I).get? "vat" = none := by
  rw [dripLocals, store_get_ne _ _ (by decide)]
  simp

abbrev dripVatTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  jugAddressReturnWord ⟨2⟩ σ I

abbrev dripVowTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  jugAddressReturnWord ⟨3⟩ σ I

abbrev dripVatAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (dripVatTargetWord σ I).toNat

abbrev dripVatIlksSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨1823590043⟩ ⟨225⟩

abbrev dripVatIlksSelectorWord : UInt256 :=
  ⟨3647180086⟩

abbrev dripVatFoldSelectorWord : UInt256 :=
  ⟨3058907103⟩

abbrev dripVatFoldSelectorShifted : UInt256 :=
  UInt256.shiftLeft dripVatFoldSelectorWord ⟨224⟩

abbrev dripVatIlksOutPtr : UInt256 :=
  ⟨128⟩

abbrev dripVatIlksInSize : UInt256 :=
  UInt256.add (UInt256.sub dripVatIlksOutPtr dripVatIlksOutPtr) ⟨36⟩

abbrev dripVatIlksEndPtr : UInt256 :=
  UInt256.add dripVatIlksOutPtr ⟨36⟩

abbrev dripVatFoldOutPtr : UInt256 :=
  ⟨128⟩

abbrev dripVatFoldInSize : UInt256 :=
  ⟨100⟩

abbrev dripVatFoldEndPtr : UInt256 :=
  ⟨228⟩

abbrev dripVatIlksArtWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))

abbrev dripVatIlksPrevWord (out : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))

noncomputable def dripVatIlksSelectorMem (mem : ByteArray) : ByteArray :=
  dripVatIlksSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def dripVatIlksCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (fileDutyIlkWord I).toByteArray.write 0 (dripVatIlksSelectorMem mem) 132 32

noncomputable def dripVatIlksPostCallMem (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (dripVatIlksCalldataMem I (dripIlkHashMem I)) dripVatIlksOutPtr.toNat
    (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat

noncomputable def dripVatFoldSelectorMem (mem : ByteArray) : ByteArray :=
  dripVatFoldSelectorShifted.toByteArray.write 0 mem dripVatFoldOutPtr.toNat 32

noncomputable def dripVatFoldIlkMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (fileDutyIlkWord I).toByteArray.write 0 (dripVatFoldSelectorMem mem)
    (dripVatFoldOutPtr + ⟨4⟩).toNat 32

noncomputable def dripVatFoldVowMem (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) : ByteArray :=
  (dripVowTargetWord σ I).toByteArray.write 0 (dripVatFoldIlkMem I mem)
    (dripVatFoldOutPtr + ⟨36⟩).toNat 32

noncomputable def dripVatFoldCalldataMem (σ : AccountMap) (I : ExecutionEnv)
    (delta : UInt256) (mem : ByteArray) : ByteArray :=
  delta.toByteArray.write 0 (dripVatFoldVowMem σ I mem)
    (dripVatFoldOutPtr + ⟨68⟩).toNat 32

theorem dripVatIlksSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (dripVatIlksSelectorMem mem).size = 160 := by
  unfold dripVatIlksSelectorMem
  exact toByteArray_write32_size_of_ge mem dripVatIlksSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem dripVatIlksSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dripVatIlksSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dripVatIlksSelectorMem
  rw [toByteArray_write_read_below_of_gap dripVatIlksSelectorShifted mem 128 64
    (by rw [hmem]) (by omega) (by rw [hmem]; native_decide), hread64]

theorem dripVatIlksCalldataMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dripVatIlksCalldataMem I mem).size = 164 := by
  unfold dripVatIlksCalldataMem
  exact toByteArray_write32_size_of_le (dripVatIlksSelectorMem mem) (fileDutyIlkWord I)
    132 160 164 (dripVatIlksSelectorMem_size hmem)
    (by rw [dripVatIlksSelectorMem_size hmem]; omega) (by omega)

theorem dripVatIlksCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dripVatIlksCalldataMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold dripVatIlksCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [dripVatIlksSelectorMem_size hmem]; omega) (by omega),
    dripVatIlksSelectorMem_read64 hmem hread64]

theorem dripVatIlksPostCallWrite_size_gt64 {base : ByteArray} (out : ByteArray) (L : ℕ)
    (hbase : base.size = 164) (hLo : L ≤ out.size) :
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

theorem dripVatIlksPostCallMem_size_gt64 (I : ExecutionEnv) (out : ByteArray)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    64 < (dripVatIlksPostCallMem I out).size := by
  unfold dripVatIlksPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
    umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
  rw [hlen]
  exact dripVatIlksPostCallWrite_size_gt64 out out.size
    (dripVatIlksCalldataMem_size I (dripIlkHashMem_size I)) le_rfl

theorem dripVatIlksPostCallMem_read64 (I : ExecutionEnv) (out : ByteArray)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    (dripVatIlksPostCallMem I out).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dripVatIlksPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = out.size :=
    umin_ofNat_right_toNat_of_lt (c := 64) (n := out.size) (by decide) hshort hout
  rw [hlen]
  change (out.write 0 (dripVatIlksCalldataMem I (dripIlkHashMem I)) 128 out.size).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
  by_cases hzero : out.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact dripVatIlksCalldataMem_read64 I (dripIlkHashMem_size I) (dripIlkHashMem_read64 I)
  · rw [write_read_below_gen_extend out (dripVatIlksCalldataMem I (dripIlkHashMem I))
        128 out.size 64 hzero le_rfl
        (by rw [dripVatIlksCalldataMem_size I (dripIlkHashMem_size I)]; omega) (by omega)]
    exact dripVatIlksCalldataMem_read64 I (dripIlkHashMem_size I) (dripIlkHashMem_read64 I)

theorem dripVatIlksPostCallMem_mload64 (I : ExecutionEnv) (out : ByteArray)
    (hshort : out.size < 64) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (dripVatIlksPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((dripVatIlksPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by
      have hgt := dripVatIlksPostCallMem_size_gt64 I out hshort hout
      omega)
    (by decide)
    (dripVatIlksPostCallMem_read64 I out hshort hout)

theorem dripVatIlksPostCallMem_size_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (dripVatIlksPostCallMem I out).size = 192 := by
  unfold dripVatIlksPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  change (out.write 0 (dripVatIlksCalldataMem I (dripIlkHashMem I)) 128 64).size = 192
  rw [write_eq_gen_extend out (dripVatIlksCalldataMem I (dripIlkHashMem I)) 128 64
    (by omega) (by omega)
    (by rw [dripVatIlksCalldataMem_size I (dripIlkHashMem_size I)]; omega)
    (by rw [dripVatIlksCalldataMem_size I (dripIlkHashMem_size I)]; omega)]
  rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
  rw [dripVatIlksCalldataMem_size I (dripIlkHashMem_size I)]
  omega

theorem dripVatIlksPostCallMem_read64_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (dripVatIlksPostCallMem I out).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dripVatIlksPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  change (out.write 0 (dripVatIlksCalldataMem I (dripIlkHashMem I)) 128 64).readWithPadding
      64 32 = UInt256.toByteArray ⟨128⟩
  rw [write_read_below_gen_extend out (dripVatIlksCalldataMem I (dripIlkHashMem I))
    128 64 64 (by omega) (by omega)
    (by rw [dripVatIlksCalldataMem_size I (dripIlkHashMem_size I)]; omega) (by omega)]
  exact dripVatIlksCalldataMem_read64 I (dripIlkHashMem_size I) (dripIlkHashMem_read64 I)

theorem dripVatIlksPostCallMem_mload64_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (dripVatIlksPostCallMem I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((dripVatIlksPostCallMem I out).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue
    (by rw [dripVatIlksPostCallMem_size_long I out hlo hout]; decide)
    (by decide)
    (dripVatIlksPostCallMem_read64_long I out hlo hout)

theorem dripVatIlksPostCallMem_read160_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (dripVatIlksPostCallMem I out).readWithPadding 160 32 = out.extract 32 64 := by
  unfold dripVatIlksPostCallMem
  have hlen :
      (min (⟨64⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 64 :=
    umin_ofNat_right_toNat_of_ge (c := 64) (n := out.size) (by decide) hlo hout
  rw [hlen]
  change (out.write 0 (dripVatIlksCalldataMem I (dripIlkHashMem I)) 128 64).readWithPadding
      160 32 = out.extract 32 64
  rw [write_eq_gen_extend out (dripVatIlksCalldataMem I (dripIlkHashMem I)) 128 64
    (by omega) (by omega)
    (by rw [dripVatIlksCalldataMem_size I (dripIlkHashMem_size I)]; omega)
    (by rw [dripVatIlksCalldataMem_size I (dripIlkHashMem_size I)]; omega)]
  have hprefix :
      ((dripVatIlksCalldataMem I (dripIlkHashMem I)).extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, dripVatIlksCalldataMem_size I (dripIlkHashMem_size I)]
    omega
  have hsrc : (out.extract 0 64).size = 64 := by
    rw [ByteArray.size_extract]
    omega
  have hmemSize :
      ((dripVatIlksCalldataMem I (dripIlkHashMem I)).extract 0 128 ++
        out.extract 0 64).size = 192 := by
    rw [ByteArray.size_append, hprefix, hsrc]
  have hreadIn :
      160 + 32 ≤
        ((dripVatIlksCalldataMem I (dripIlkHashMem I)).extract 0 128 ++
          out.extract 0 64).size := by
    rw [hmemSize]
  rw [readWithPadding_eq_extract _ 160 hreadIn]
  rw [extract_append_right_window _ _ 160 192 (by rw [hprefix]; omega), hprefix]
  rw [show 160 - 128 = 32 by omega, show 192 - 128 = 64 by omega]
  rw [extract_extract_BA]
  norm_num

theorem dripVatIlksPostCallMem_mload160_long (I : ExecutionEnv) (out : ByteArray)
    (hlo : 64 ≤ out.size) (hout : out.size < UInt256.size) :
    (if (⟨160⟩ : UInt256).toNat ≥ (dripVatIlksPostCallMem I out).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((dripVatIlksPostCallMem I out).readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      dripVatIlksPrevWord out := by
  unfold dripVatIlksPrevWord
  rw [if_neg]
  · change UInt256.ofNat
      (fromByteArrayBigEndian ((dripVatIlksPostCallMem I out).readWithPadding 160 32)) =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 32 64))
    rw [dripVatIlksPostCallMem_read160_long I out hlo hout]
  · exact not_or.mpr
      ⟨by rw [dripVatIlksPostCallMem_size_long I out hlo hout]; decide, by native_decide⟩

theorem dripVatFoldSelectorMem_size {mem : ByteArray} (hmem : mem.size = 192) :
    (dripVatFoldSelectorMem mem).size = 192 := by
  unfold dripVatFoldSelectorMem dripVatFoldOutPtr
  exact toByteArray_write32_size_of_le mem dripVatFoldSelectorShifted 128 192 192 hmem
    (by rw [hmem]; omega) (by omega)

theorem dripVatFoldIlkMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 192) :
    (dripVatFoldIlkMem I mem).size = 192 := by
  have hoff : (dripVatFoldOutPtr + ⟨4⟩).toNat = 132 := by native_decide
  unfold dripVatFoldIlkMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (dripVatFoldSelectorMem mem) (fileDutyIlkWord I)
    132 192 192 (dripVatFoldSelectorMem_size hmem)
    (by rw [dripVatFoldSelectorMem_size hmem]; omega) (by omega)

theorem dripVatFoldVowMem_size (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 192) :
    (dripVatFoldVowMem σ I mem).size = 196 := by
  have hoff : (dripVatFoldOutPtr + ⟨36⟩).toNat = 164 := by native_decide
  unfold dripVatFoldVowMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (dripVatFoldIlkMem I mem) (dripVowTargetWord σ I)
    164 192 196 (dripVatFoldIlkMem_size I hmem)
    (by rw [dripVatFoldIlkMem_size I hmem]; omega) (by omega)

theorem dripVatFoldCalldataMem_size (σ : AccountMap) (I : ExecutionEnv) (delta : UInt256)
    {mem : ByteArray} (hmem : mem.size = 192) :
    (dripVatFoldCalldataMem σ I delta mem).size = 228 := by
  have hoff : (dripVatFoldOutPtr + ⟨68⟩).toNat = 196 := by native_decide
  unfold dripVatFoldCalldataMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (dripVatFoldVowMem σ I mem) delta 196 196 228
    (dripVatFoldVowMem_size σ I hmem)
    (by rw [dripVatFoldVowMem_size σ I hmem]) (by omega)

theorem dripVatFoldSelectorMem_read64 {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dripVatFoldSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dripVatFoldSelectorMem dripVatFoldOutPtr
  change (dripVatFoldSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega)]
  exact hread64

theorem dripVatFoldIlkMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dripVatFoldIlkMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hoff : (dripVatFoldOutPtr + ⟨4⟩).toNat = 132 := by native_decide
  unfold dripVatFoldIlkMem
  rw [hoff, write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [dripVatFoldSelectorMem_size hmem]; omega) (by omega)]
  exact dripVatFoldSelectorMem_read64 hmem hread64

theorem dripVatFoldVowMem_read64 (σ : AccountMap) (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dripVatFoldVowMem σ I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hoff : (dripVatFoldOutPtr + ⟨36⟩).toNat = 164 := by native_decide
  unfold dripVatFoldVowMem
  rw [hoff, write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [dripVatFoldIlkMem_size I hmem]; omega) (by omega)]
  exact dripVatFoldIlkMem_read64 I hmem hread64

theorem dripVatFoldCalldataMem_read64 (σ : AccountMap) (I : ExecutionEnv)
    (delta : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dripVatFoldCalldataMem σ I delta mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  have hoff : (dripVatFoldOutPtr + ⟨68⟩).toNat = 196 := by native_decide
  unfold dripVatFoldCalldataMem
  rw [hoff, write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [dripVatFoldVowMem_size σ I hmem]) (by omega)]
  exact dripVatFoldVowMem_read64 σ I hmem hread64

theorem dripVatFoldCalldataMem_mload64 (σ : AccountMap) (I : ExecutionEnv)
    (delta : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (dripVatFoldCalldataMem σ I delta mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((dripVatFoldCalldataMem σ I delta mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [dripVatFoldCalldataMem_size σ I delta hmem]; decide)
    (by decide) (dripVatFoldCalldataMem_read64 σ I delta hmem hread64)

noncomputable def dripVatFoldReturnMem (mem : ByteArray) (rate : UInt256) : ByteArray :=
  (UInt256.toByteArray rate).write 0 mem 128 32

theorem dripVatFoldReturnMem_size {mem : ByteArray} (rate : UInt256)
    (hmem : mem.size = 228) :
    (dripVatFoldReturnMem mem rate).size = 228 := by
  unfold dripVatFoldReturnMem
  exact toByteArray_write32_size_of_le mem rate 128 228 228 hmem
    (by rw [hmem]; omega) (by omega)

theorem dripVatFoldReturnMem_read64 {mem : ByteArray} (rate : UInt256)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (dripVatFoldReturnMem mem rate).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold dripVatFoldReturnMem
  rw [toByteArray_write_read_below_of_gap rate mem 128 64
      (by rw [hmem]; omega) (by omega) (by rw [hmem]; native_decide)]
  exact hread64

theorem dripVatFoldReturnMem_read128 {mem : ByteArray} (rate : UInt256)
    (hmem : mem.size = 228) :
    (dripVatFoldReturnMem mem rate).readWithPadding 128 32 = UInt256.toByteArray rate := by
  unfold dripVatFoldReturnMem
  exact toByteArray_write_read_back_of_gap rate mem 128 (by rw [hmem]; native_decide)

theorem drip_wordAt0Mem_size_of_ge32 {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem drip_wordAt32Mem_size_of_ge64 {mem : ByteArray} (word : UInt256)
    (hmem : 64 ≤ mem.size) :
    (wordAt32Mem word mem).size = mem.size := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem drip_twoWordHashMem_size_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  unfold twoWordHashMem
  rw [drip_wordAt32Mem_size_of_ge64 slot (by
    rw [drip_wordAt0Mem_size_of_ge32 key (by omega)]
    exact hmem)]
  exact drip_wordAt0Mem_size_of_ge32 key (by omega)

theorem drip_twoWordHashMem_read0_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 = UInt256.toByteArray key := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
    (by rw [drip_wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)]
  exact wordAt0Mem_read0 key mem

theorem drip_twoWordHashMem_read32_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 = UInt256.toByteArray slot := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
    (by rw [drip_wordAt0Mem_size_of_ge32 key (by omega)]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])

theorem drip_twoWordHashMem_read64_of_ge96 {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (twoWordHashMem key slot mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_above _ _ 32 64 (by rw [toByteArray_size])
      (by rw [drip_wordAt0Mem_size_of_ge32 key (by omega)]; omega) (by omega)
      (by
        rw [drip_wordAt0Mem_size_of_ge32 key (by omega)]
        exact hmem)]
  unfold wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size]) (by omega) (by omega)
      (by omega)]
  exact hread64

theorem drip_twoWordHashMem_read0_64_of_ge64 {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [drip_twoWordHashMem_size_of_ge64 key slot hmem]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0
        (by rw [drip_twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      drip_twoWordHashMem_read0_of_ge64 key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32
        (by rw [drip_twoWordHashMem_size_of_ge64 key slot hmem]; omega),
      drip_twoWordHashMem_read32_of_ge64 key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem drip_twoWordHashMem_solcMappingSlot_of_ge64 (baseSlot key : UInt256)
    {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [drip_twoWordHashMem_read0_64_of_ge64 key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot

theorem dripVatIlksSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 96) :
    (dripVatIlksSelectorMem mem).extract 128 132 = vatIlksSelector := by
  unfold dripVatIlksSelectorMem
  have hgap : 128 - mem.size < USize.size := by
    rw [hmem]
    native_decide
  rw [toByteArray_write_eq dripVatIlksSelectorShifted mem 128 (by omega) hgap]
  have hprefix :
      (mem ++ ffi.ByteArray.zeroes (128 - mem.size)).size = 128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size,
      hmem]
  rw [extract_append_right_window _ _ 128 132 (by rw [hprefix]), hprefix,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    toByteArray_eq_toBytesBE]
  native_decide

theorem dripVatIlksCalldataMem_read128_36 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (dripVatIlksCalldataMem I mem).readWithPadding 128 36 =
      vatIlksSelector ++ (fileDutyIlkWord I).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [dripVatIlksCalldataMem_size I hmem]), dripVatIlksCalldataMem,
    write32_eq _ (dripVatIlksSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [dripVatIlksSelectorMem_size hmem]; omega)]
  have hAsz : ((dripVatIlksSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, dripVatIlksSelectorMem_size hmem]
    omega
  have hBsz : ((fileDutyIlkWord I).toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((dripVatIlksSelectorMem mem).extract 0 132 ++
        (fileDutyIlkWord I).toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull :
      (fileDutyIlkWord I).toByteArray.extract 0 32 = (fileDutyIlkWord I).toByteArray := by
    have h := @ByteArray.extract_zero_size (fileDutyIlkWord I).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), dripVatIlksSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem fileDutyIlkBytes_eq_toBytesBE {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    fileDutyIlkBytes I = EVM.Word.toBytesBE (fileDutyIlkWord I) := by
  have hlen32 : (fileDutyIlkBytes I).length = 32 := fileDutyIlkBytes_length hsz36
  have hword : ABI.bytesToWord (fileDutyIlkBytes I) = fileDutyIlkWord I := by
    simpa [fileDutyIlkBytes, fileDutyIlkWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hto := toBytesBE_bytesToWord_of_length (bs := fileDutyIlkBytes I) hlen32
  rw [hword] at hto
  exact hto.symm

theorem dripVatIlksEncode_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    config.externalABI.encode? "ilks" [.fixedBytes bytes32Width (fileDutyIlkBytes I)] =
      some ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding
        dripVatIlksOutPtr.toNat dripVatIlksInSize.toNat) := by
  change config.externalABI.encode? "ilks" [.fixedBytes bytes32Width (fileDutyIlkBytes I)] =
    some ((dripVatIlksCalldataMem I (dripIlkHashMem I)).readWithPadding 128 36)
  rw [dripVatIlksCalldataMem_read128_36 I (dripIlkHashMem_size I)]
  have hbytes := fileDutyIlkBytes_eq_toBytesBE (I := I) hsz36
  have hlen : (EVM.Word.toBytesBE (fileDutyIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (fileDutyIlkWord I)
  simp [config, jugExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, vatIlksSelector,
    selectorBytes, hbytes, hlen, ABI.zeroBytes, word_toBytesBE_toByteArray_eq_toByteArray]

theorem dripVatFoldCalldataMem_read128_100
    (σ : AccountMap) (I : ExecutionEnv) (delta : UInt256) {mem : ByteArray}
    (hmem : mem.size = 192) :
    (dripVatFoldCalldataMem σ I delta mem).readWithPadding 128 100 =
      vatFoldSelector ++ (fileDutyIlkWord I).toByteArray ++
        (dripVowTargetWord σ I).toByteArray ++ delta.toByteArray := by
  let final := dripVatFoldCalldataMem σ I delta mem
  have hfinalSize : final.size = 228 := by
    dsimp [final]
    exact dripVatFoldCalldataMem_size σ I delta hmem
  have h132 : (dripVatFoldOutPtr + ⟨4⟩).toNat = 132 := by native_decide
  have h164 : (dripVatFoldOutPtr + ⟨36⟩).toNat = 164 := by native_decide
  have h196 : (dripVatFoldOutPtr + ⟨68⟩).toNat = 196 := by native_decide
  have hselectorRead : final.readWithPadding 128 4 = vatFoldSelector := by
    dsimp [final]
    unfold dripVatFoldCalldataMem
    rw [h196]
    rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
      (by rw [dripVatFoldVowMem_size σ I hmem]) (by omega)
      (by rw [dripVatFoldVowMem_size σ I hmem]; omega) (by omega) (by norm_num)]
    unfold dripVatFoldVowMem
    rw [h164]
    rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
      (by rw [dripVatFoldIlkMem_size I hmem]; omega) (by omega)
      (by rw [dripVatFoldIlkMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold dripVatFoldIlkMem
    rw [h132]
    rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [dripVatFoldSelectorMem_size hmem]; omega) (by omega)
      (by rw [dripVatFoldSelectorMem_size hmem]; omega) (by omega) (by norm_num)]
    unfold dripVatFoldSelectorMem dripVatFoldOutPtr
    change
      (dripVatFoldSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
        vatFoldSelector
    rw [write32_read_prefix_len _ _ 128 4 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega) (by omega) (by norm_num)]
    unfold dripVatFoldSelectorShifted dripVatFoldSelectorWord vatFoldSelector selectorBytes
    native_decide
  have hilkRead : final.readWithPadding 132 32 = (fileDutyIlkWord I).toByteArray := by
    dsimp [final]
    unfold dripVatFoldCalldataMem
    rw [h196]
    rw [write32_read_below_len _ _ 196 132 32 (by rw [toByteArray_size])
      (by rw [dripVatFoldVowMem_size σ I hmem]) (by omega)
      (by rw [dripVatFoldVowMem_size σ I hmem]; omega) (by omega) (by norm_num)]
    unfold dripVatFoldVowMem
    rw [h164]
    rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
      (by rw [dripVatFoldIlkMem_size I hmem]; omega) (by omega)
      (by rw [dripVatFoldIlkMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold dripVatFoldIlkMem
    rw [h132]
    rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
      (by rw [dripVatFoldSelectorMem_size hmem]; omega) (by omega) (by omega)
      (by norm_num)]
    rw [toByteArray_extract_all]
  have hvowRead : final.readWithPadding 164 32 = (dripVowTargetWord σ I).toByteArray := by
    dsimp [final]
    unfold dripVatFoldCalldataMem
    rw [h196]
    rw [write32_read_below_len _ _ 196 164 32 (by rw [toByteArray_size])
      (by rw [dripVatFoldVowMem_size σ I hmem]) (by omega)
      (by rw [dripVatFoldVowMem_size σ I hmem]) (by omega) (by norm_num)]
    unfold dripVatFoldVowMem
    rw [h164]
    rw [write32_read_prefix_len _ _ 164 32 (by rw [toByteArray_size])
      (by rw [dripVatFoldIlkMem_size I hmem]; omega) (by omega) (by omega)
      (by norm_num)]
    rw [toByteArray_extract_all]
  have hdeltaRead : final.readWithPadding 196 32 = delta.toByteArray := by
    dsimp [final]
    unfold dripVatFoldCalldataMem
    rw [h196]
    rw [write32_read_back _ _ 196 (by rw [toByteArray_size])
      (by rw [dripVatFoldVowMem_size σ I hmem])]
    rw [toByteArray_extract_all]
  rw [readWithPadding_eq_extract' final 128 100 (by norm_num) (by norm_num)
    (by rw [hfinalSize])]
  have hselectorExt : final.extract 128 132 = vatFoldSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselectorRead
  have hilkExt : final.extract 132 164 = (fileDutyIlkWord I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hilkRead
  have hvowExt : final.extract 164 196 = (dripVowTargetWord σ I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hvowRead
  have hdeltaExt : final.extract 196 228 = delta.toByteArray := by
    rw [← readWithPadding_eq_extract' final 196 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize])]
    exact hdeltaRead
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
  rw [hsplit, hselectorExt, hilkExt, hvowExt, hdeltaExt]

theorem dripVatFoldEncode_eq (σ : AccountMap) (I : ExecutionEnv) (delta : UInt256)
    {mem : ByteArray} (hmem : mem.size = 192) (hsz36 : 36 ≤ I.calldata.size)
    (hdeltaMax : (delta.toNat : Int) ≤ maxInt256) :
    config.externalABI.encode? "fold"
        [.fixedBytes bytes32Width (fileDutyIlkBytes I),
          .address (AccountAddress.ofUInt256 (dripVowTargetWord σ I)),
          .int (Int.ofNat delta.toNat)] =
      some ((dripVatFoldCalldataMem σ I delta mem).readWithPadding
        dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat) := by
  change config.externalABI.encode? "fold"
      [.fixedBytes bytes32Width (fileDutyIlkBytes I),
        .address (AccountAddress.ofUInt256 (dripVowTargetWord σ I)),
        .int (Int.ofNat delta.toNat)] =
    some ((dripVatFoldCalldataMem σ I delta mem).readWithPadding 128 100)
  rw [dripVatFoldCalldataMem_read128_100 σ I delta hmem]
  have hbytes := fileDutyIlkBytes_eq_toBytesBE (I := I) hsz36
  have hlen : (EVM.Word.toBytesBE (fileDutyIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (fileDutyIlkWord I)
  have hdeltaLt : delta.toNat < EVM.twoPow 255 := by
    have hdeltaLtInt : (delta.toNat : Int) < (2 : Int) ^ 255 := by
      have hle : (delta.toNat : Int) ≤ (2 : Int) ^ 255 - 1 := by
        simpa [maxInt256] using hdeltaMax
      omega
    have hdeltaLtNat : delta.toNat < 2 ^ 255 := by
      exact_mod_cast hdeltaLtInt
    simpa [EVM.twoPow] using hdeltaLtNat
  have haddrWord :
      EVM.word ↑(AccountAddress.ofUInt256 (dripVowTargetWord σ I)) =
        dripVowTargetWord σ I := by
    have hvowCanon : (dripVowTargetWord σ I).toNat < EVM.addressModulus := by
      simpa [dripVowTargetWord, jugAddressReturnWord] using
        solcAddrMask_result_canonical (jugSlotWord ⟨3⟩ σ I)
    have hvowCanonVal : ↑(dripVowTargetWord σ I).val < EVM.addressModulus := by
      simpa [UInt256.toNat] using hvowCanon
    apply u256_inj
    simp only [EVM.word, EVM.uintN, UInt256.toNat, AccountAddress.ofUInt256, Fin.ofNat]
    rw [show AccountAddress.size = EVM.addressModulus from by decide]
    rw [Nat.mod_eq_of_lt hvowCanonVal]
    rw [Nat.mod_eq_of_lt hvowCanonVal]
    rw [Nat.mod_eq_of_lt (lt_trans hvowCanonVal (by decide))]
  have hdeltaWord : EVM.wordOfInt (delta.toNat : Int) = delta := by
    simpa [EVM.wordOfInt, EVM.word, EVM.uintN] using u256_ofNat_toNat delta
  simp [config, jugExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, int256,
    int256Int, vatFoldSelector, selectorBytes, hbytes, hlen, hdeltaLt, haddrWord,
    word_toBytesBE_toByteArray_eq_toByteArray]
  rw [hdeltaWord]
  simp [ABI.zeroBytes, ByteArray.append_assoc]

theorem wordOfInt_sub_toUInt256 (x y : UInt256) :
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

theorem dripVatFoldEncode_signed_eq (σ : AccountMap) (I : ExecutionEnv)
    (rate prev delta : UInt256) {mem : ByteArray} (hmem : mem.size = 192)
    (hsz36 : 36 ≤ I.calldata.size)
    (hrateMax : (rate.toNat : Int) ≤ maxInt256)
    (hprevMax : (prev.toNat : Int) ≤ maxInt256)
    (hdelta : delta = UInt256.sub rate prev) :
    config.externalABI.encode? "fold"
        [.fixedBytes bytes32Width (fileDutyIlkBytes I),
          .address (AccountAddress.ofUInt256 (dripVowTargetWord σ I)),
          .int ((rate.toNat : Int) - (prev.toNat : Int))] =
      some ((dripVatFoldCalldataMem σ I delta mem).readWithPadding
        dripVatFoldOutPtr.toNat dripVatFoldInSize.toNat) := by
  change config.externalABI.encode? "fold"
      [.fixedBytes bytes32Width (fileDutyIlkBytes I),
        .address (AccountAddress.ofUInt256 (dripVowTargetWord σ I)),
        .int ((rate.toNat : Int) - (prev.toNat : Int))] =
    some ((dripVatFoldCalldataMem σ I delta mem).readWithPadding 128 100)
  rw [dripVatFoldCalldataMem_read128_100 σ I delta hmem]
  have hbytes := fileDutyIlkBytes_eq_toBytesBE (I := I) hsz36
  have hlen : (EVM.Word.toBytesBE (fileDutyIlkWord I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (fileDutyIlkWord I)
  have hdeltaLo :
      -Int.ofNat (EVM.twoPow 255) ≤ (rate.toNat : Int) - (prev.toNat : Int) := by
    have hprevLe : (prev.toNat : Int) ≤ (2 : Int) ^ 255 - 1 := by
      simpa [maxInt256] using hprevMax
    norm_num [EVM.twoPow]
    omega
  have hdeltaHi :
      (rate.toNat : Int) - (prev.toNat : Int) < Int.ofNat (EVM.twoPow 255) := by
    have hrateLe : (rate.toNat : Int) ≤ (2 : Int) ^ 255 - 1 := by
      simpa [maxInt256] using hrateMax
    norm_num [EVM.twoPow]
    omega
  have hdeltaRange :
      (prev.toNat : Int) ≤ (rate.toNat : Int) + Int.ofNat (EVM.twoPow 255) ∧
        (rate.toNat : Int) - (prev.toNat : Int) < Int.ofNat (EVM.twoPow 255) := by
    constructor
    · omega
    · exact hdeltaHi
  have hdeltaRangeTarget :
      (prev.toNat : Int) ≤ (rate.toNat : Int) + ((EVM.twoPow 255 : Nat) : Int) ∧
        (rate.toNat : Int) - (prev.toNat : Int) < ((EVM.twoPow 255 : Nat) : Int) := by
    exact hdeltaRange
  have haddrWord :
      EVM.word ↑(AccountAddress.ofUInt256 (dripVowTargetWord σ I)) =
        dripVowTargetWord σ I := by
    have hvowCanon : (dripVowTargetWord σ I).toNat < EVM.addressModulus := by
      simpa [dripVowTargetWord, jugAddressReturnWord] using
        solcAddrMask_result_canonical (jugSlotWord ⟨3⟩ σ I)
    have hvowCanonVal : ↑(dripVowTargetWord σ I).val < EVM.addressModulus := by
      simpa [UInt256.toNat] using hvowCanon
    apply u256_inj
    simp only [EVM.word, EVM.uintN, UInt256.toNat, AccountAddress.ofUInt256, Fin.ofNat]
    rw [show AccountAddress.size = EVM.addressModulus from by decide]
    rw [Nat.mod_eq_of_lt hvowCanonVal]
    rw [Nat.mod_eq_of_lt hvowCanonVal]
    rw [Nat.mod_eq_of_lt (lt_trans hvowCanonVal (by decide))]
  have hdeltaWord :
      EVM.wordOfInt ((rate.toNat : Int) - (prev.toNat : Int)) = delta := by
    rw [hdelta]
    exact wordOfInt_sub_toUInt256 rate prev
  simp [config, jugExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, bytes32, bytes32Width, addr, int256,
    int256Int, vatFoldSelector, selectorBytes, hbytes, hlen, hdeltaRangeTarget, haddrWord,
    hdeltaWord, word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ABI.zeroBytes, ByteArray.append_assoc, word_toBytesBE_toByteArray_eq_toByteArray]

theorem dripVatIlksDecode_none_short_aux {out : ByteArray} (hshort : out.size < 64) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiUInt256, abiUInt256] out =
      none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  by_cases hfirst : ((out.toList.drop 0).take 32).length = 32
  · rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) hfirst]
    simp only [Option.bind_eq_bind, Option.bind_some]
    have htake32n : ¬ ((out.toList.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, hlen]
      omega
    rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 32) htake32n]
    simp
  · rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
      (bytes := out.toList) (start := 0) hfirst]
    simp

theorem dripVatIlksDecode_none_short {out : ByteArray} (hshort : out.size < 64) :
    config.externalABI.decode? "ilks" out = none := by
  have h := dripVatIlksDecode_none_short_aux (out := out) hshort
  simpa [config, jugExternalABI, uint256, uint256Int, abiUInt256] using h

theorem dripVatIlks_bytesToWord_drop32_eq_extract32_64 (out : ByteArray) :
    ABI.bytesToWord ((out.toList.drop 32).take 32) = dripVatIlksPrevWord out := by
  unfold dripVatIlksPrevWord
  unfold ABI.bytesToWord fromByteArrayBigEndian
  congr 1
  rw [byteArray_toList_eq (out.extract 32 64), ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, byteArray_toList_eq]
  simp [byteArray_toList_eq]

theorem dripVatIlksDecode_ok_aux {out : ByteArray} (hlo : 64 ≤ out.size) :
    ABI.decodeReturnValuesWithMode? DecodeMode.legacySolc05 [abiUInt256, abiUInt256] out =
      some [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
        .int (Int.ofNat (dripVatIlksPrevWord out).toNat)] := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have htake32 : ((out.toList.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword0 := bytesToWord_take32_eq_extract0_32 (returndata := out)
  have hword1 := dripVatIlks_bytesToWord_drop32_eq_extract32_64 out
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [abiUInt256, abiUInt256]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [abiUInt256, abiUInt256]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [abiUInt256, abiUInt256].length)
    (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 0) htake0]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := out.toList) (start := 32) htake32]
  simp only [Option.bind_some]
  have hword0' :
      ABI.bytesToWord ((out.toList.drop 0).take 32) = dripVatIlksArtWord out := by
    simpa [dripVatIlksArtWord, List.drop_zero] using hword0
  rw [hword0', hword1]

theorem dripVatIlksDecode_ok {out : ByteArray} (hlo : 64 ≤ out.size) :
    config.externalABI.decode? "ilks" out =
      some [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
        .int (Int.ofNat (dripVatIlksPrevWord out).toNat)] := by
  have h := dripVatIlksDecode_ok_aux (out := out) hlo
  simpa [config, jugExternalABI, uint256, uint256Int, abiUInt256] using h

theorem dripVatTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    dripVatTargetWord σ I = dripVatTargetWord τ I := by
  have hslot : jugSlotWord ⟨2⟩ σ I = jugSlotWord ⟨2⟩ τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  simp [dripVatTargetWord, jugAddressReturnWord, hslot]

theorem dripVowTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    dripVowTargetWord σ I = dripVowTargetWord τ I := by
  have hslot : jugSlotWord ⟨3⟩ σ I = jugSlotWord ⟨3⟩ τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  simp [dripVowTargetWord, jugAddressReturnWord, hslot]

theorem dripVatAddress_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    dripVatAddress σ I = dripVatAddress τ I := by
  apply Fin.ext
  simp [dripVatAddress, dripVatTargetWord_accountMapEquiv hAccounts]

theorem dripVatCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (dripVatTargetWord σ I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (dripVatTargetWord τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (dripVatTargetWord σ I)
  have htarget : dripVatTargetWord σ I = dripVatTargetWord τ I :=
    dripVatTargetWord_accountMapEquiv hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem dripVatCodeSize_ne_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (dripVatTargetWord σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (dripVatTargetWord τ I) ≠ ⟨0⟩ := by
  intro hzero
  exact hne (dripVatCodeSize_zero_accountMapEquiv hAccounts.symm hzero)

theorem dripVatAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    dripVatAddress σ I = AccountAddress.ofUInt256 (dripVatTargetWord σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]

theorem evmAddress_accountAddress (a : AccountAddress) :
    EVM.address a.val = a := by
  apply Fin.ext
  show a.val % EVM.addressModulus = a.val
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  exact Nat.mod_eq_of_lt a.isLt

theorem dripVatAddress_eq_evm_target_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    dripVatAddress σ_solm I =
      AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) :=
  calc
    dripVatAddress σ_solm I = dripVatAddress σ_evm I :=
      (dripVatAddress_accountMapEquiv hAccounts).symm
    _ = AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) :=
      dripVatAddress_eq_target σ_evm I

theorem dripVatEvmAddress_eq_target_of_accountMapEquiv {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    EVM.address (dripVatAddress σ_solm I) =
      AccountAddress.ofUInt256 (dripVatTargetWord σ_evm I) := by
  rw [dripVatAddress_eq_evm_target_of_accountMapEquiv hAccounts]
  exact evmAddress_accountAddress _

theorem drip_extCodeSizeWord_zero_lookup_code_zero {σ : AccountMap} {target : UInt256}
    {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hzero : Reasoning.Theory.extCodeSizeWord σ target = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hzero
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      simpa [hacc, Option.option] using
        (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
  | some acc =>
      have hword := congrArg UInt256.toNat hzero
      simpa [hacc] using hword

theorem dripVatCode_zero_of_codeSize_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (dripVatTargetWord σ I) = ⟨0⟩) :
    (UInt256.ofNat
      (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  simpa [initState, State.lookupAccount] using
    drip_extCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := dripVatTargetWord σ I) (addr := dripVatAddress σ I)
      (dripVatAddress_eq_target σ I) hzero

theorem dripVatCode_pos_of_codeSize_ne_zero {cA gh bl σ σ₀ A I} {g : UInt256}
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (dripVatTargetWord σ I) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  by_contra hnot
  have hnat :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (dripVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0 :=
    Nat.eq_zero_of_not_pos hnot
  have hwordZero :
      UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (dripVatAddress σ I)).option 0 (fun acc => acc.code.size)) = ⟨0⟩ :=
    uint256_toNat_eq_zero hnat
  have hword :
      UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (dripVatAddress σ I)).option 0 (fun acc => acc.code.size)) =
        Reasoning.Theory.extCodeSizeWord σ (dripVatTargetWord σ I) := by
    cases hacc : σ.find? (AccountAddress.ofUInt256 (dripVatTargetWord σ I)) <;>
      simp [initState, State.lookupAccount, Reasoning.Theory.extCodeSizeWord,
        dripVatAddress_eq_target σ I, hacc, Option.option] <;>
      native_decide
  exact hne (by rw [← hword, hwordZero])

theorem evalExpr_dripStorageVat (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := dripLocals I } evm
      (.storage vatRef) =
        .ok (.address (dripVatAddress evm.accountMap evm.executionEnv)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := dripLocals I }) (evm := evm)
    (slot := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨2⟩)
    (value := .address (dripVatAddress evm.accountMap evm.executionEnv))
    (dripLocals_get_vat I)
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [vatRef, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [dripVatAddress, dripVatTargetWord, jugAddressReturnWord, jugSlotWord] using
        jugStorageLocLoad_address_offset0 evm ⟨2⟩)

theorem evalExpr_dripStorageVatOfLocals {evm : EVM.State} {locals : Store}
    (hvat : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (dripVatAddress evm.accountMap evm.executionEnv)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨2⟩)
    (value := .address (dripVatAddress evm.accountMap evm.executionEnv))
    hvat
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [vatRef, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [dripVatAddress, dripVatTargetWord, jugAddressReturnWord, jugSlotWord] using
        jugStorageLocLoad_address_offset0 evm ⟨2⟩)

theorem evalExpr_dripStorageVowOfLocals {evm : EVM.State} {locals : Store}
    (hvow : locals.get? "vow" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vowRef) =
      .ok (.address (AccountAddress.ofUInt256
        (dripVowTargetWord evm.accountMap evm.executionEnv))) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := vowRef) (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨3⟩)
    (value := .address (AccountAddress.ofUInt256
      (dripVowTargetWord evm.accountMap evm.executionEnv)))
    hvow
    (by simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [vowRef, storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      simpa [dripVowTargetWord, jugAddressReturnWord, jugSlotWord] using
        jugStorageLocLoad_address_offset0 evm ⟨3⟩)

theorem evalExpr_dripVatCodeGuard_false {evm : EVM.State} {I : ExecutionEnv}
    (hvat :
      evalExpr? config { contract := contract, locals := dripLocals I } evm (.storage vatRef) =
        .ok (.address (dripVatAddress evm.accountMap evm.executionEnv)))
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (dripVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := dripLocals I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem evalExpr_dripVatCodeGuard_true {evm : EVM.State} {I : ExecutionEnv}
    (hvat :
      evalExpr? config { contract := contract, locals := dripLocals I } evm (.storage vatRef) =
        .ok (.address (dripVatAddress evm.accountMap evm.executionEnv)))
    (hcode :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (dripVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := dripLocals I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_dripVatCodeGuard_false_ofLocals {evm : EVM.State} {locals : Store}
    (hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (dripVatAddress evm.accountMap evm.executionEnv)))
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (dripVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem evalExpr_dripVatCodeGuard_true_ofLocals {evm : EVM.State} {locals : Store}
    (hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (dripVatAddress evm.accountMap evm.executionEnv)))
    (hcode :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (dripVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExprs_dripVatIlksArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := dripLocals I } evm [.var "ilk"] =
      .ok [.fixedBytes bytes32Width (fileDutyIlkBytes I)] := by
  have hilkEval :
      evalExpr? config { contract := contract, locals := dripLocals I } evm (.var "ilk") =
        .ok (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((dripLocals I).get? "ilk") =
      .ok (.fixedBytes bytes32Width (fileDutyIlkBytes I))
    rw [dripLocals_get_ilk]
    rfl
  simp [evalExprs?, hilkEval, EvalResult.bind, bind, pure]

abbrev dripVatIlksLocals (I : ExecutionEnv) (out : ByteArray) : Store :=
  (dripLocals I).insert "vatIlk"
    (.tuple [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
      .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])

abbrev dripVatIlksPrevLocals (I : ExecutionEnv) (out : ByteArray) : Store :=
  (dripVatIlksLocals I out).insert "prev"
    (.int (Int.ofNat (dripVatIlksPrevWord out).toNat))

abbrev dripFeeLocals (I : ExecutionEnv) (out : ByteArray) (fee : UInt256) : Store :=
  (dripVatIlksPrevLocals I out).insert "fee" (.int (Int.ofNat fee.toNat))

abbrev dripPowLocals (I : ExecutionEnv) (out : ByteArray) (fee pow : UInt256) : Store :=
  (dripFeeLocals I out fee).insert "pow" (.int (Int.ofNat pow.toNat))

abbrev dripRateLocals (I : ExecutionEnv) (out : ByteArray)
    (fee pow rate : UInt256) : Store :=
  (dripPowLocals I out fee pow).insert "rate" (.int (Int.ofNat rate.toNat))

abbrev dripDeltaLocals (I : ExecutionEnv) (out : ByteArray)
    (fee pow rate delta : UInt256) : Store :=
  (dripRateLocals I out fee pow rate).insert "delta" (.int (Int.ofNat delta.toNat))

abbrev dripDeltaLocalsInt (I : ExecutionEnv) (out : ByteArray)
    (fee pow rate : UInt256) (delta : Int) : Store :=
  (dripRateLocals I out fee pow rate).insert "delta" (.int delta)

theorem dripVatIlksPrevLocals_get_base (I : ExecutionEnv) (out : ByteArray) :
    (dripVatIlksPrevLocals I out).get? "base" = none := by
  rw [dripVatIlksPrevLocals, store_get_ne _ _ (by decide), dripVatIlksLocals,
    store_get_ne _ _ (by decide), dripLocals, store_get_ne _ _ (by decide)]
  simp

theorem dripVatIlksPrevLocals_get_ilks (I : ExecutionEnv) (out : ByteArray) :
    (dripVatIlksPrevLocals I out).get? "ilks" = none := by
  rw [dripVatIlksPrevLocals, store_get_ne _ _ (by decide), dripVatIlksLocals,
    store_get_ne _ _ (by decide), dripLocals, store_get_ne _ _ (by decide)]
  simp

theorem dripVatIlksPrevLocals_get_ilk (I : ExecutionEnv) (out : ByteArray) :
    (dripVatIlksPrevLocals I out).get? "ilk" =
      some (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
  rw [dripVatIlksPrevLocals, store_get_ne _ _ (by decide), dripVatIlksLocals,
    store_get_ne _ _ (by decide), dripLocals_get_ilk]

theorem dripFeeLocals_get_fee (I : ExecutionEnv) (out : ByteArray) (fee : UInt256) :
    (dripFeeLocals I out fee).get? "fee" = some (.int (Int.ofNat fee.toNat)) := by
  rw [dripFeeLocals, store_get_self]

theorem dripFeeLocals_get_ilks (I : ExecutionEnv) (out : ByteArray) (fee : UInt256) :
    (dripFeeLocals I out fee).get? "ilks" = none := by
  rw [dripFeeLocals, store_get_ne _ _ (by decide), dripVatIlksPrevLocals_get_ilks]

theorem dripFeeLocals_get_ilk (I : ExecutionEnv) (out : ByteArray) (fee : UInt256) :
    (dripFeeLocals I out fee).get? "ilk" =
      some (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
  rw [dripFeeLocals, store_get_ne _ _ (by decide), dripVatIlksPrevLocals_get_ilk]

theorem dripPowLocals_get_pow
    (I : ExecutionEnv) (out : ByteArray) (fee pow : UInt256) :
    (dripPowLocals I out fee pow).get? "pow" = some (.int (Int.ofNat pow.toNat)) := by
  rw [dripPowLocals, store_get_self]

theorem dripPowLocals_get_prev
    (I : ExecutionEnv) (out : ByteArray) (fee pow : UInt256) :
    (dripPowLocals I out fee pow).get? "prev" =
      some (.int (Int.ofNat (dripVatIlksPrevWord out).toNat)) := by
  rw [dripPowLocals, store_get_ne _ _ (by decide), dripFeeLocals,
    store_get_ne _ _ (by decide), dripVatIlksPrevLocals, store_get_self]

theorem dripRateLocals_get_rate
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate : UInt256) :
    (dripRateLocals I out fee pow rate).get? "rate" =
      some (.int (Int.ofNat rate.toNat)) := by
  rw [dripRateLocals, store_get_self]

theorem dripRateLocals_get_prev
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate : UInt256) :
    (dripRateLocals I out fee pow rate).get? "prev" =
      some (.int (Int.ofNat (dripVatIlksPrevWord out).toNat)) := by
  rw [dripRateLocals, store_get_ne _ _ (by decide), dripPowLocals_get_prev]

theorem dripDeltaLocals_get_ilk
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate delta : UInt256) :
    (dripDeltaLocals I out fee pow rate delta).get? "ilk" =
      some (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
  rw [dripDeltaLocals, store_get_ne _ _ (by decide), dripRateLocals,
    store_get_ne _ _ (by decide), dripPowLocals, store_get_ne _ _ (by decide),
    dripFeeLocals_get_ilk]

theorem dripDeltaLocals_get_vat
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate delta : UInt256) :
    (dripDeltaLocals I out fee pow rate delta).get? "vat" = none := by
  rw [dripDeltaLocals, store_get_ne _ _ (by decide), dripRateLocals,
    store_get_ne _ _ (by decide), dripPowLocals, store_get_ne _ _ (by decide), dripFeeLocals,
    store_get_ne _ _ (by decide), dripVatIlksPrevLocals, store_get_ne _ _ (by decide),
    dripVatIlksLocals, store_get_ne _ _ (by decide), dripLocals_get_vat]

theorem dripDeltaLocals_get_vow
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate delta : UInt256) :
    (dripDeltaLocals I out fee pow rate delta).get? "vow" = none := by
  rw [dripDeltaLocals, store_get_ne _ _ (by decide), dripRateLocals,
    store_get_ne _ _ (by decide), dripPowLocals, store_get_ne _ _ (by decide), dripFeeLocals,
    store_get_ne _ _ (by decide), dripVatIlksPrevLocals, store_get_ne _ _ (by decide),
    dripVatIlksLocals, store_get_ne _ _ (by decide), dripLocals, store_get_ne _ _ (by decide)]
  simp

theorem dripDeltaLocals_get_delta
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate delta : UInt256) :
    (dripDeltaLocals I out fee pow rate delta).get? "delta" =
      some (.int (Int.ofNat delta.toNat)) := by
  rw [dripDeltaLocals, store_get_self]

theorem dripDeltaLocals_get_ilks
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate delta : UInt256) :
    (dripDeltaLocals I out fee pow rate delta).get? "ilks" = none := by
  rw [dripDeltaLocals, store_get_ne _ _ (by decide), dripRateLocals,
    store_get_ne _ _ (by decide), dripPowLocals, store_get_ne _ _ (by decide),
    dripFeeLocals_get_ilks]

theorem dripDeltaLocals_get_rate
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate delta : UInt256) :
    (dripDeltaLocals I out fee pow rate delta).get? "rate" =
      some (.int (Int.ofNat rate.toNat)) := by
  rw [dripDeltaLocals, store_get_ne _ _ (by decide), dripRateLocals_get_rate]

theorem dripDeltaLocalsInt_get_ilk
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate : UInt256) (delta : Int) :
    (dripDeltaLocalsInt I out fee pow rate delta).get? "ilk" =
      some (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
  rw [dripDeltaLocalsInt, store_get_ne _ _ (by decide), dripRateLocals,
    store_get_ne _ _ (by decide), dripPowLocals, store_get_ne _ _ (by decide),
    dripFeeLocals_get_ilk]

theorem dripDeltaLocalsInt_get_vat
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate : UInt256) (delta : Int) :
    (dripDeltaLocalsInt I out fee pow rate delta).get? "vat" = none := by
  rw [dripDeltaLocalsInt, store_get_ne _ _ (by decide), dripRateLocals,
    store_get_ne _ _ (by decide), dripPowLocals, store_get_ne _ _ (by decide), dripFeeLocals,
    store_get_ne _ _ (by decide), dripVatIlksPrevLocals, store_get_ne _ _ (by decide),
    dripVatIlksLocals, store_get_ne _ _ (by decide), dripLocals_get_vat]

theorem dripDeltaLocalsInt_get_vow
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate : UInt256) (delta : Int) :
    (dripDeltaLocalsInt I out fee pow rate delta).get? "vow" = none := by
  rw [dripDeltaLocalsInt, store_get_ne _ _ (by decide), dripRateLocals,
    store_get_ne _ _ (by decide), dripPowLocals, store_get_ne _ _ (by decide), dripFeeLocals,
    store_get_ne _ _ (by decide), dripVatIlksPrevLocals, store_get_ne _ _ (by decide),
    dripVatIlksLocals, store_get_ne _ _ (by decide), dripLocals, store_get_ne _ _ (by decide)]
  simp

theorem dripDeltaLocalsInt_get_delta
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate : UInt256) (delta : Int) :
    (dripDeltaLocalsInt I out fee pow rate delta).get? "delta" =
      some (.int delta) := by
  rw [dripDeltaLocalsInt, store_get_self]

theorem dripDeltaLocalsInt_get_ilks
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate : UInt256) (delta : Int) :
    (dripDeltaLocalsInt I out fee pow rate delta).get? "ilks" = none := by
  rw [dripDeltaLocalsInt, store_get_ne _ _ (by decide), dripRateLocals,
    store_get_ne _ _ (by decide), dripPowLocals, store_get_ne _ _ (by decide),
    dripFeeLocals_get_ilks]

theorem dripDeltaLocalsInt_get_rate
    (I : ExecutionEnv) (out : ByteArray) (fee pow rate : UInt256) (delta : Int) :
    (dripDeltaLocalsInt I out fee pow rate delta).get? "rate" =
      some (.int (Int.ofNat rate.toNat)) := by
  rw [dripDeltaLocalsInt, store_get_ne _ _ (by decide), dripRateLocals_get_rate]

theorem evalExpr_dripVatIlksPrev (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config { contract := contract, locals := dripVatIlksLocals I out } evm
      (.tupleGet (.var "vatIlk") 1) =
        .ok (.int (Int.ofNat (dripVatIlksPrevWord out).toNat)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := dripVatIlksLocals I out } evm
        (.var "vatIlk") =
          .ok (.tuple [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
            .int (Int.ofNat (dripVatIlksPrevWord out).toNat)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((dripVatIlksLocals I out).get? "vatIlk") =
        .ok (.tuple [.int (Int.ofNat (dripVatIlksArtWord out).toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)])
    rw [dripVatIlksLocals, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind]

theorem evalExpr_dripStorageBase {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "base" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage baseRef) =
      .ok (.int (Int.ofNat (jugSlotWord ⟨4⟩ evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := baseRef) (er := ({ base := "base", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨4⟩)
    (value := .int (Int.ofNat (jugSlotWord ⟨4⟩ evm.accountMap evm.executionEnv).toNat))
    hbase
    (by simp [baseRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by simpa [jugSlotWord] using jugStorageLocLoad_uint256 evm ⟨4⟩)

theorem evalExpr_dripStorageDuty {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (fileDutyIlkBytes I))) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "ilk") "duty")) =
        .ok (.int (Int.ofNat
          (jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "duty") (er := fileDutyDutyEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (fileDutyDutySlotFor I))
    (value := .int (Int.ofNat
      (jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv).toNat))
    hilks
    (by
      have hkeyLen : (fileDutyIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using fileDutyIlkBytes_length (I := I) hsz36
      simp [fileDutyDutyEvaledRef, fileDutyIlkKey, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        ← Std.HashMap.get?_eq_getElem?, hilk, EvalResult.ofOption, EvalResult.bind, pure, bind,
        hkeyLen])
    (by
      simp [fileDutyIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
    (by rfl)
    (by simpa [jugSlotWord] using jugStorageLocLoad_uint256 evm (fileDutyDutySlotFor I))

theorem evalExprs_dripAddArgs (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExprs? config { contract := contract, locals := dripVatIlksPrevLocals I out } evm
      [.storage baseRef, .storage (ilksF (.var "ilk") "duty")] =
        .ok
          [.int (Int.ofNat (jugSlotWord ⟨4⟩ evm.accountMap evm.executionEnv).toNat),
           .int (Int.ofNat
            (jugSlotWord (fileDutyDutySlotFor I) evm.accountMap evm.executionEnv).toNat)] := by
  have hbase := evalExpr_dripStorageBase
    (evm := evm) (locals := dripVatIlksPrevLocals I out)
    (dripVatIlksPrevLocals_get_base I out)
  have hduty := evalExpr_dripStorageDuty
    (evm := evm) (locals := dripVatIlksPrevLocals I out) (I := I) hsz36
    (dripVatIlksPrevLocals_get_ilks I out) (dripVatIlksPrevLocals_get_ilk I out)
  simp [evalExprs?, hbase, hduty, EvalResult.bind, bind, pure]

theorem evalExpr_dripStorageRho (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := dripLocals I } evm
      (.storage (ilksF (.var "ilk") "rho")) =
        .ok (.int (Int.ofNat
          (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := dripLocals I }) (evm := evm)
    (slot := ilksF (.var "ilk") "rho") (er := fileDutyRhoEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (fileDutyRhoSlotFor I))
    (value := .int (Int.ofNat
      (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv).toNat))
    (dripLocals_get_ilks I)
    (by
      have hkeyLen : (fileDutyIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using fileDutyIlkBytes_length (I := I) hsz36
      simp [fileDutyRhoEvaledRef, fileDutyIlkKey, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, dripLocals, evalExpr?, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [fileDutyIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
    (by rfl)
    (by simpa [jugSlotWord] using jugStorageLocLoad_uint256 evm (fileDutyRhoSlotFor I))

theorem evalExpr_dripStorageRhoOfLocals {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (fileDutyIlkBytes I))) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "ilk") "rho")) =
        .ok (.int (Int.ofNat
          (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "rho") (er := fileDutyRhoEvaledRef I)
    (t := .int uint256Int) (loc := wordLoc (fileDutyRhoSlotFor I))
    (value := .int (Int.ofNat
      (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv).toNat))
    hilks
    (by
      have hkeyLen : (fileDutyIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using fileDutyIlkBytes_length (I := I) hsz36
      simp [fileDutyRhoEvaledRef, fileDutyIlkKey, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, evalExpr?, valueToKey?, ← Std.HashMap.get?_eq_getElem?,
        hilk, EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [fileDutyIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
    (by rfl)
    (by simpa [jugSlotWord] using jugStorageLocLoad_uint256 evm (fileDutyRhoSlotFor I))

theorem assign_dripRhoStorageOfLocals {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store} (hsz36 : 36 ≤ I.calldata.size)
    (hilks : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (fileDutyIlkBytes I))) :
    let timestamp := UInt256.ofNat evm.executionEnv.header.timestamp
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (fileDutyRhoSlotFor I)
      timestamp
    assignStorageRef? config { contract := contract, locals := locals } evm
        .storage (ilksF (.var "ilk") "rho") (.int (Int.ofNat timestamp.toNat)) =
      .ok ({ contract := contract, locals := locals }, evm') := by
  intro timestamp evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := fileDutyRhoEvaledRef I)
      (loc := wordLoc (fileDutyRhoSlotFor I))
      (hbase := hilks)
      (her := by
        have hkeyLen : (fileDutyIlkBytes I).length = ↑bytes32Width + 1 := by
          simpa [bytes32Width] using fileDutyIlkBytes_length (I := I) hsz36
        simp [fileDutyRhoEvaledRef, fileDutyIlkKey, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          ← Std.HashMap.get?_eq_getElem?, hilk, EvalResult.ofOption, EvalResult.bind, pure,
          bind, hkeyLen])
      (hty := by
        simp [fileDutyIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (hloc := by rfl)
  simpa [evm', timestamp] using
    jugStorageLocStore_uint256 evm (fileDutyRhoSlotFor I) timestamp

theorem evalExprs_dripRpowNZeroArgs (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (fee : UInt256)
    (hsz36 : 36 ≤ I.calldata.size)
    (hage :
      UInt256.sub (UInt256.ofNat evm.executionEnv.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv) = ⟨0⟩) :
    evalExprs? config { contract := contract, locals := dripFeeLocals I out fee } evm
      [ .var "fee",
        sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
        .intLit one ] =
        .ok [.int (Int.ofNat fee.toNat), .int 0, .int (Int.ofNat jugRay.toNat)] := by
  let rho := jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv
  let nowWord := UInt256.ofNat evm.executionEnv.header.timestamp
  have hnowEqRho : nowWord = rho := by
    rw [← u256_sub_eq_zero_iff_eq]
    simpa [nowWord, rho] using hage
  have hrhoLe : rho.toNat ≤ nowWord.toNat := by
    rw [← hnowEqRho]
  have hfee :
      evalExpr? config { contract := contract, locals := dripFeeLocals I out fee } evm
        (.var "fee") = .ok (.int (Int.ofNat fee.toNat)) := by
    simpa using evalExpr_varUInt256 (evm := evm)
      (locals := dripFeeLocals I out fee) (name := "fee") (value := fee)
      (dripFeeLocals_get_fee I out fee)
  have htimestamp :
      evalExpr? config { contract := contract, locals := dripFeeLocals I out fee } evm
        (.env .timestamp) = .ok (.int (Int.ofNat nowWord.toNat)) := by
    simp [evalExpr?, envValue, pure, nowWord]
  have hrho :
      evalExpr? config { contract := contract, locals := dripFeeLocals I out fee } evm
        (.storage (ilksF (.var "ilk") "rho")) = .ok (.int (Int.ofNat rho.toNat)) := by
    simpa [rho] using
      evalExpr_dripStorageRhoOfLocals (evm := evm) (locals := dripFeeLocals I out fee)
        (I := I) hsz36 (dripFeeLocals_get_ilks I out fee)
        (dripFeeLocals_get_ilk I out fee)
  have hsub :
      evalExpr? config { contract := contract, locals := dripFeeLocals I out fee } evm
        (sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    exact evalExpr_sub256_ok htimestamp hrho (by simpa [nowWord, rho] using hage.symm) hrhoLe
  have hone :
      evalExpr? config { contract := contract, locals := dripFeeLocals I out fee } evm
        (.intLit one) = .ok (.int (Int.ofNat jugRay.toNat)) := by
    simp [evalExpr?, pure, one_eq_jugRay_toNat]
  simp [evalExprs?, hfee, hsub, hone, EvalResult.bind, bind, pure, jugUInt256Zero_toNat]

theorem evalExprs_dripRpowArgs (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (fee age : UInt256)
    (hsz36 : 36 ≤ I.calldata.size)
    (hage :
      age = UInt256.sub (UInt256.ofNat evm.executionEnv.header.timestamp)
        (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv)) :
    evalExprs? config { contract := contract, locals := dripFeeLocals I out fee } evm
      [ .var "fee",
        sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho")),
        .intLit one ] =
        .ok [.int (Int.ofNat fee.toNat), .int (Int.ofNat age.toNat),
          .int (Int.ofNat jugRay.toNat)] := by
  let rho := jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv
  let nowWord := UInt256.ofNat evm.executionEnv.header.timestamp
  have hfee :
      evalExpr? config { contract := contract, locals := dripFeeLocals I out fee } evm
        (.var "fee") = .ok (.int (Int.ofNat fee.toNat)) := by
    simpa using evalExpr_varUInt256 (evm := evm)
      (locals := dripFeeLocals I out fee) (name := "fee") (value := fee)
      (dripFeeLocals_get_fee I out fee)
  have htimestamp :
      evalExpr? config { contract := contract, locals := dripFeeLocals I out fee } evm
        (.env .timestamp) = .ok (.int (Int.ofNat nowWord.toNat)) := by
    simp [evalExpr?, envValue, pure, nowWord]
  have hrho :
      evalExpr? config { contract := contract, locals := dripFeeLocals I out fee } evm
        (.storage (ilksF (.var "ilk") "rho")) = .ok (.int (Int.ofNat rho.toNat)) := by
    simpa [rho] using
      evalExpr_dripStorageRhoOfLocals (evm := evm) (locals := dripFeeLocals I out fee)
        (I := I) hsz36 (dripFeeLocals_get_ilks I out fee)
        (dripFeeLocals_get_ilk I out fee)
  have hsub :
      evalExpr? config { contract := contract, locals := dripFeeLocals I out fee } evm
        (sub256 (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
          .ok (.int (Int.ofNat age.toNat)) := by
    exact evalExpr_sub256_word_ok htimestamp hrho (by simpa [nowWord, rho] using hage)
  have hone :
      evalExpr? config { contract := contract, locals := dripFeeLocals I out fee } evm
        (.intLit one) = .ok (.int (Int.ofNat jugRay.toNat)) := by
    simp [evalExpr?, pure, one_eq_jugRay_toNat]
  simp [evalExprs?, hfee, hsub, hone, EvalResult.bind, bind, pure]

theorem evalExprs_dripRmulArgs (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (fee pow : UInt256) :
    evalExprs? config { contract := contract, locals := dripPowLocals I out fee pow } evm
      [.var "pow", .var "prev"] =
        .ok [.int (Int.ofNat pow.toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)] := by
  have hpow :
      evalExpr? config { contract := contract, locals := dripPowLocals I out fee pow } evm
        (.var "pow") = .ok (.int (Int.ofNat pow.toNat)) := by
    simpa using evalExpr_varUInt256 (evm := evm)
      (locals := dripPowLocals I out fee pow) (name := "pow") (value := pow)
      (dripPowLocals_get_pow I out fee pow)
  have hprev :
      evalExpr? config { contract := contract, locals := dripPowLocals I out fee pow } evm
        (.var "prev") = .ok (.int (Int.ofNat (dripVatIlksPrevWord out).toNat)) := by
    simpa using evalExpr_varUInt256 (evm := evm)
      (locals := dripPowLocals I out fee pow) (name := "prev")
      (value := dripVatIlksPrevWord out) (dripPowLocals_get_prev I out fee pow)
  simp [evalExprs?, hpow, hprev, EvalResult.bind, bind, pure]

theorem evalExprs_dripDiffArgs (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (fee pow rate : UInt256) :
    evalExprs? config { contract := contract, locals := dripRateLocals I out fee pow rate } evm
      [.var "rate", .var "prev"] =
        .ok [.int (Int.ofNat rate.toNat),
          .int (Int.ofNat (dripVatIlksPrevWord out).toNat)] := by
  have hrate :
      evalExpr? config { contract := contract, locals := dripRateLocals I out fee pow rate } evm
        (.var "rate") = .ok (.int (Int.ofNat rate.toNat)) := by
    simpa using evalExpr_varUInt256 (evm := evm)
      (locals := dripRateLocals I out fee pow rate) (name := "rate") (value := rate)
      (dripRateLocals_get_rate I out fee pow rate)
  have hprev :
      evalExpr? config { contract := contract, locals := dripRateLocals I out fee pow rate } evm
        (.var "prev") = .ok (.int (Int.ofNat (dripVatIlksPrevWord out).toNat)) := by
    simpa using evalExpr_varUInt256 (evm := evm)
      (locals := dripRateLocals I out fee pow rate) (name := "prev")
      (value := dripVatIlksPrevWord out) (dripRateLocals_get_prev I out fee pow rate)
  simp [evalExprs?, hrate, hprev, EvalResult.bind, bind, pure]

theorem evalExprs_dripVatFoldArgs (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (fee pow rate delta : UInt256) :
    evalExprs? config
        { contract := contract, locals := dripDeltaLocals I out fee pow rate delta } evm
        [.var "ilk", .storage vowRef, .var "delta"] =
      .ok
        [.fixedBytes bytes32Width (fileDutyIlkBytes I),
          .address (AccountAddress.ofUInt256
            (dripVowTargetWord evm.accountMap evm.executionEnv)),
          .int (Int.ofNat delta.toNat)] := by
  have hilk :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocals I out fee pow rate delta } evm
          (.var "ilk") =
        .ok (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((dripDeltaLocals I out fee pow rate delta).get? "ilk") =
      .ok (.fixedBytes bytes32Width (fileDutyIlkBytes I))
    rw [dripDeltaLocals_get_ilk]
    rfl
  have hvow :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocals I out fee pow rate delta } evm
          (.storage vowRef) =
        .ok (.address (AccountAddress.ofUInt256
          (dripVowTargetWord evm.accountMap evm.executionEnv))) :=
    evalExpr_dripStorageVowOfLocals
      (evm := evm) (locals := dripDeltaLocals I out fee pow rate delta)
      (dripDeltaLocals_get_vow I out fee pow rate delta)
  have hdelta :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocals I out fee pow rate delta } evm
          (.var "delta") = .ok (.int (Int.ofNat delta.toNat)) := by
    simpa using evalExpr_varUInt256 (evm := evm)
      (locals := dripDeltaLocals I out fee pow rate delta) (name := "delta")
      (value := delta) (dripDeltaLocals_get_delta I out fee pow rate delta)
  simp [evalExprs?, hilk, hvow, hdelta, EvalResult.bind, bind, pure]

theorem evalExprs_dripVatFoldArgsInt (evm : EVM.State) (I : ExecutionEnv)
    (out : ByteArray) (fee pow rate : UInt256) (delta : Int) :
    evalExprs? config
        { contract := contract, locals := dripDeltaLocalsInt I out fee pow rate delta } evm
        [.var "ilk", .storage vowRef, .var "delta"] =
      .ok
        [.fixedBytes bytes32Width (fileDutyIlkBytes I),
          .address (AccountAddress.ofUInt256
            (dripVowTargetWord evm.accountMap evm.executionEnv)),
          .int delta] := by
  have hilk :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee pow rate delta } evm
          (.var "ilk") =
        .ok (.fixedBytes bytes32Width (fileDutyIlkBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        ((dripDeltaLocalsInt I out fee pow rate delta).get? "ilk") =
      .ok (.fixedBytes bytes32Width (fileDutyIlkBytes I))
    rw [dripDeltaLocalsInt_get_ilk]
    rfl
  have hvow :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee pow rate delta } evm
          (.storage vowRef) =
        .ok (.address (AccountAddress.ofUInt256
          (dripVowTargetWord evm.accountMap evm.executionEnv))) :=
    evalExpr_dripStorageVowOfLocals
      (evm := evm) (locals := dripDeltaLocalsInt I out fee pow rate delta)
      (dripDeltaLocalsInt_get_vow I out fee pow rate delta)
  have hdelta :
      evalExpr? config
          { contract := contract, locals := dripDeltaLocalsInt I out fee pow rate delta } evm
          (.var "delta") = .ok (.int delta) := by
    exact evalExpr_varInt (evm := evm)
      (locals := dripDeltaLocalsInt I out fee pow rate delta) (name := "delta")
      (value := delta) (dripDeltaLocalsInt_get_delta I out fee pow rate delta)
  simp [evalExprs?, hilk, hvow, hdelta, EvalResult.bind, bind, pure]

theorem evalExpr_dripNowGeRho_true {evm : EVM.State} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hle :
      (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := dripLocals I } evm
      (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
        .ok (.bool true) := by
  have htimestamp :
      evalExpr? config { contract := contract, locals := dripLocals I } evm (.env .timestamp) =
        .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) := by
    simp [evalExpr?, envValue, pure]
  exact evalExpr_ge_uint256_true htimestamp (evalExpr_dripStorageRho evm I hsz36) hle

theorem evalExpr_dripNowGeRho_false {evm : EVM.State} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hlt :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (jugSlotWord (fileDutyRhoSlotFor I) evm.accountMap evm.executionEnv).toNat) :
    evalExpr? config { contract := contract, locals := dripLocals I } evm
      (.binary .ge (.env .timestamp) (.storage (ilksF (.var "ilk") "rho"))) =
        .ok (.bool false) := by
  have htimestamp :
      evalExpr? config { contract := contract, locals := dripLocals I } evm (.env .timestamp) =
        .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) := by
    simp [evalExpr?, envValue, pure]
  exact Benchmarks.Dss.Jug.evalExpr_ge_uint256_false htimestamp
    (evalExpr_dripStorageRho evm I hsz36) hlt

end Benchmarks.Dss.Jug
