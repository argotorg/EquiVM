import Benchmarks.Dss.Vow.Heal
import Benchmarks.Dss.Vow.KissSuccess

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

abbrev healLocalsVatDaiVatSin (I : ExecutionEnv) (vatDai vatSin : UInt256) : Store :=
  (healLocalsVatDai I vatDai).insert "vatSin" (.int (Int.ofNat vatSin.toNat))

abbrev healLocalsVatDaiVatSinFreeSin
    (I : ExecutionEnv) (vatDai vatSin freeSin : UInt256) : Store :=
  (healLocalsVatDaiVatSin I vatDai vatSin).insert "freeSin"
    (.int (Int.ofNat freeSin.toNat))

abbrev healLocalsVatDaiVatSinFreeSinHealDebt
    (I : ExecutionEnv) (vatDai vatSin freeSin healDebt : UInt256) : Store :=
  (healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin).insert "healDebt"
    (.int (Int.ofNat healDebt.toNat))

theorem healLocalsVatDaiVatSin_get_rad (I : ExecutionEnv) (vatDai vatSin : UInt256) :
    (healLocalsVatDaiVatSin I vatDai vatSin).get? "rad" =
      some (.int (Int.ofNat (healRad I).toNat)) := by
  rw [healLocalsVatDaiVatSin, store_get_ne _ _ (by decide),
    healLocalsVatDai_get_rad]

theorem healLocalsVatDaiVatSin_get_vatSin
    (I : ExecutionEnv) (vatDai vatSin : UInt256) :
    (healLocalsVatDaiVatSin I vatDai vatSin).get? "vatSin" =
      some (.int (Int.ofNat vatSin.toNat)) := by
  rw [healLocalsVatDaiVatSin, store_get_self]

theorem healLocalsVatDaiVatSinFreeSin_get_freeSin
    (I : ExecutionEnv) (vatDai vatSin freeSin : UInt256) :
    (healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin).get? "freeSin" =
      some (.int (Int.ofNat freeSin.toNat)) := by
  rw [healLocalsVatDaiVatSinFreeSin, store_get_self]

theorem healLocalsVatDaiVatSinFreeSinHealDebt_get_rad
    (I : ExecutionEnv) (vatDai vatSin freeSin healDebt : UInt256) :
    (healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt).get? "rad" =
      some (.int (Int.ofNat (healRad I).toNat)) := by
  rw [healLocalsVatDaiVatSinFreeSinHealDebt, store_get_ne _ _ (by decide),
    healLocalsVatDaiVatSinFreeSin, store_get_ne _ _ (by decide),
    healLocalsVatDaiVatSin_get_rad]

theorem healLocalsVatDaiVatSinFreeSinHealDebt_get_healDebt
    (I : ExecutionEnv) (vatDai vatSin freeSin healDebt : UInt256) :
    (healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt).get? "healDebt" =
      some (.int (Int.ofNat healDebt.toNat)) := by
  rw [healLocalsVatDaiVatSinFreeSinHealDebt, store_get_self]

abbrev healSinCapitalEvaledRef : EvaledStorageRef :=
  { base := "Sin", steps := [] }

abbrev vowInsufficientDebtRawWord : UInt256 :=
  ⟨31581374176212906047780177930514102119330985105565⟩

abbrev vowInsufficientDebtStringWord : UInt256 :=
  UInt256.shiftLeft vowInsufficientDebtRawWord ⟨90⟩

theorem evalExpr_healSinCapitalStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "Sin" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage SinRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := healSinCapitalEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨5⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ ⟨5⟩)
  · exact hbase
  · simp [healSinCapitalEvaledRef, SinRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
      healSinCapitalEvaledRef]

theorem healSinWrite_size (I : ExecutionEnv) (mem o : ByteArray) (L : ℕ)
    (hmem : mem.size = 164) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (healSinCalldataMem I mem) 128 L).size = 164 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact healSinCalldataMem_size I hmem
  · rw [write_eq_gen o (healSinCalldataMem I mem) 128 L (by omega) hLo
      (by rw [healSinCalldataMem_size I hmem]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, healSinCalldataMem_size I hmem]
    omega

theorem healSinWrite_read64 (I : ExecutionEnv) (mem o : ByteArray) (L : ℕ)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (healSinCalldataMem I mem) 128 L).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact healSinCalldataMem_read64 I hmem hread64
  · rw [write_read_below_gen o (healSinCalldataMem I mem) 128 L 64 (by omega) hLo
      (by rw [healSinCalldataMem_size I hmem]; omega) (by omega),
      healSinCalldataMem_read64 I hmem hread64]

theorem healSinWrite_read128_32 (I : ExecutionEnv) (mem o : ByteArray)
    (hmem : mem.size = 164) (ho32 : 32 ≤ o.size) :
    (o.write 0 (healSinCalldataMem I mem) 128 32).readWithPadding 128 32 =
      o.extract 0 32 :=
  write32_read_back o (healSinCalldataMem I mem) 128 ho32
    (by rw [healSinCalldataMem_size I hmem]; omega)

theorem vatSinDecode_ok {o : ByteArray} (ho32 : 32 ≤ o.size) :
    config.externalABI.decode? "sin" o =
      some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat)] := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_ok (returndata := o) ho32
  have hlt := fromByteArrayBigEndian_extract0_32_lt (returndata := o) ho32
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o =
        some (.int (Int.ofNat (fromByteArrayBigEndian (o.extract 0 32)))) := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 o =
    some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat)]
  unfold decodeReturn?
  rw [hdec']
  simp [UInt256.toNat_ofNat_of_lt hlt, Int.ofNat_eq_natCast]

theorem vatSinDecode_none_short {o : ByteArray} (hshort : o.size < 32) :
    config.externalABI.decode? "sin" o = none := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o) hshort
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o = none := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 o = none
  unfold decodeReturn?
  rw [hdec']
  rfl

theorem RD.vowHealSinCallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1295⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨1277⟩) (okPc := ⟨1293⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowHealSinReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1295⟩
      (d0 :: d1 :: d2 :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨1295⟩) (okPc := ⟨1315⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem RD.vowHealSinReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1295⟩
      (d0 :: d1 :: d2 :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (retWord :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨1295⟩) (okPc := ⟨1315⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.solcCheckedSubEmptyRevertAnyWords {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hwf : solcCheckedSubEmptyRevertWf code pc okPc)
    (hlt : a.toNat < b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hsub, hdRev0, hdRev2, hdRev3⟩
  rcases hsub with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw gt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hgt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  have rdRev := evm_run rdTail with [
    raw push1 ⟨0⟩ hdRev0 (by evm_ov),
    raw dup1 hdRev2 (by evm_ov)]
  exact RD.rev 0 rdRev hdRev3 (fun s _ hstk => memExpRevert0 s hstk) (by evm_ov)

theorem RD.vowHealFreeSinSubUnderflow
    {cA gh bl σ σ₀ A I} {g sel vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (vatSin :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hlt : vatSin.toNat < (vowSlotWord ⟨5⟩ acc.2 I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let SinVal := vowSlotWord ⟨5⟩ acc.2 I
  have rd1320 := rd.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1321, C1321, rd1321Raw⟩ := rd1320.sload (by native_decide) (by evm_ov)
  have rd1321 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1321⟩
      (SinVal :: vatSin :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1321 C1321 := by
    simpa [SinVal, vowSlotWord, solcSlotWord] using rd1321Raw
  have rd1324 := rd1321.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1324.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := vatSin) (b := SinVal) (ret := ⟨1325⟩)
    (R := [⟨4921⟩, healRad I, ⟨412⟩, sel])
    (by simpa [SinVal] using rd5096)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [SinVal] using hlt)
    (by simp)

theorem RD.vowHealFreeSinSubSuccess
    {cA gh bl σ σ₀ A I} {g sel vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (vatSin :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hle : (vowSlotWord ⟨5⟩ acc.2 I).toNat ≤ vatSin.toNat) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (UInt256.sub vatSin (vowSlotWord ⟨5⟩ acc.2 I) ::
        ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  let SinVal := vowSlotWord ⟨5⟩ acc.2 I
  have rd1320 := rd.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1321, C1321, rd1321Raw⟩ := rd1320.sload (by native_decide) (by evm_ov)
  have rd1321 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1321⟩
      (SinVal :: vatSin :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1321 C1321 := by
    simpa [SinVal, vowSlotWord, solcSlotWord] using rd1321Raw
  have rd1324 := rd1321.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1324.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k1325, C1325, rd1325⟩ := RD.solcCheckedSubSuccess
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := vatSin) (b := SinVal) (ret := ⟨1325⟩)
    (R := [⟨4921⟩, healRad I, ⟨412⟩, sel])
    (by simpa [SinVal] using rd5096)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [SinVal] using hle) (by jump_dest) (by jump_dest) (by simp)
  exact ⟨k1325, C1325, by simpa [SinVal] using rd1325⟩

theorem RD.vowHealDebtSubUnderflow
    {cA gh bl σ σ₀ A I} {g sel freeSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (freeSin :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hlt : freeSin.toNat < (vowSlotWord ⟨6⟩ acc.2 I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let AshVal := vowSlotWord ⟨6⟩ acc.2 I
  have rd1326 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1328 := rd1326.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1329, C1329, rd1329Raw⟩ := rd1328.sload (by native_decide) (by evm_ov)
  have rd1329 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1329⟩
      (AshVal :: freeSin :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1329 C1329 := by
    simpa [AshVal, vowSlotWord, solcSlotWord] using rd1329Raw
  have rd1332 := rd1329.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1332.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := freeSin) (b := AshVal) (ret := ⟨4921⟩)
    (R := [healRad I, ⟨412⟩, sel])
    (by simpa [AshVal] using rd5096)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [AshVal] using hlt)
    (by simp)

theorem RD.vowHealDebtSubSuccess
    {cA gh bl σ σ₀ A I} {g sel freeSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (freeSin :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hle : (vowSlotWord ⟨6⟩ acc.2 I).toNat ≤ freeSin.toNat) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4921⟩
      (UInt256.sub freeSin (vowSlotWord ⟨6⟩ acc.2 I) :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  let AshVal := vowSlotWord ⟨6⟩ acc.2 I
  have rd1326 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1328 := rd1326.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1329, C1329, rd1329Raw⟩ := rd1328.sload (by native_decide) (by evm_ov)
  have rd1329 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1329⟩
      (AshVal :: freeSin :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1329 C1329 := by
    simpa [AshVal, vowSlotWord, solcSlotWord] using rd1329Raw
  have rd1332 := rd1329.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1332.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k4921, C4921, rd4921⟩ := RD.solcCheckedSubSuccess
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := freeSin) (b := AshVal) (ret := ⟨4921⟩)
    (R := [healRad I, ⟨412⟩, sel])
    (by simpa [AshVal] using rd5096)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [AshVal] using hle) (by jump_dest) (by jump_dest) (by simp)
  exact ⟨k4921, C4921, by simpa [AshVal] using rd4921⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowHealInsufficientDebt
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel healDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4921⟩
      (healDebt :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hinsuff : healDebt.toNat < (healRad I).toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rd4922 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd4923 := rd4922.dup2 (by native_decide) (by evm_ov)
  have rd4924₀ := rd4923.gt (by native_decide) (by evm_ov)
  have hgt : UInt256.gt (healRad I) healDebt = ⟨1⟩ :=
    ugt_one hinsuff
  have rd4924 := rd4924₀
  rw [hgt] at rd4924
  have rd4925₀ := rd4924.iszero (by native_decide) (by evm_ov)
  have rd4925 := rd4925₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4925
  have rd4928 := rd4925.push2 ⟨4997⟩ (by native_decide) (by evm_ov)
  have rd4929 := rd4928.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd4933 := evm_run rd4929 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd4937 := rd4933.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd4956 := evm_run rd4937 with [
    push1 ⟨229⟩,
    shl,
    dup2,
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨21⟩,
    push1 ⟨36⟩,
    dup3,
    add,
    raw mstore 3 (solcErrorStringMem2 (⟨21⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd4978 := rd4956.pushConst vowInsufficientDebtRawWord
    (width := 21) (op := .PUSH21) (by decide) (by native_decide) (by evm_ov)
  have rd4981₀ := evm_run rd4978 with [
    push1 ⟨90⟩,
    shl]
  have rd4981 := rd4981₀
  rw [show UInt256.shiftLeft vowInsufficientDebtRawWord ⟨90⟩ =
      vowInsufficientDebtStringWord from rfl] at rd4981
  exact evm_run rd4981 with [
    push1 ⟨68⟩,
    dup3,
    add,
    raw mstore 3
      (solcErrorStringMem3 (⟨21⟩ : UInt256) vowInsufficientDebtStringWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 (⟨21⟩ : UInt256)
        vowInsufficientDebtStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1,
    dup2,
    swap1,
    sub,
    push1 ⟨100⟩,
    add,
    swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem RD.vowHealDebtEnough
    {cA gh bl σ σ₀ A I} {g sel healDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4921⟩
      (healDebt :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (henough : (healRad I).toNat ≤ healDebt.toNat) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4997⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o acc k' C' := by
  have rd4922 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd4923 := rd4922.dup2 (by native_decide) (by evm_ov)
  have rd4924₀ := rd4923.gt (by native_decide) (by evm_ov)
  have hgt : UInt256.gt (healRad I) healDebt = ⟨0⟩ :=
    ugt_zero henough
  have rd4924 := rd4924₀
  rw [hgt] at rd4924
  have rd4925₀ := rd4924.iszero (by native_decide) (by evm_ov)
  have rd4925 := rd4925₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4925
  have rd4928 := rd4925.push2 ⟨4997⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4928.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowHealToHealExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4997⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5062⟩
      (kissDaiTargetWord acc.2 I :: kissDaiTargetWord acc.2 I :: kissHealOutSize ::
        kissHealOutPtr :: kissHealInSize :: kissHealOutPtr :: kissHealOutSize ::
        kissHealEndPtr :: kissHealSelector :: kissDaiTargetWord acc.2 I ::
        healRad I :: ⟨412⟩ :: sel :: [])
      (kissHealCalldataMem I mem) (UInt256.ofNat 6) o acc k' C' := by
  let target := kissDaiTargetWord acc.2 I
  have rd4998 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd5000 := rd4998.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k5001, C5001, rd5001Raw⟩ := rd5000.sload (by native_decide) (by evm_ov)
  have rd5001 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5001⟩
      (vowSlotWord ⟨1⟩ acc.2 I :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k5001 C5001 := by
    simpa [vowSlotWord, solcSlotWord] using rd5001Raw
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hHealMem : (kissHealCalldataMem I mem).size = 164 :=
    kissHealCalldataMem_size I hmem
  have hHealRead64 :
      (kissHealCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    kissHealCalldataMem_read64 I hmem hread64
  have hmload64Heal :
      (if (⟨64⟩ : UInt256).toNat ≥ (kissHealCalldataMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((kissHealCalldataMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hHealMem]; decide) (by decide) hHealRead64
  have rd5062 := evm_run rd5001 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨1021227399⟩,
    push1 ⟨226⟩,
    shl,
    dup2,
    raw mstore 0 (kissHealSelectorMem mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    dup5,
    swap1,
    raw mstore 0 (kissHealCalldataMem I mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Heal (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap3,
    and,
    swap2,
    push4 kissHealSelector,
    swap2,
    push1 ⟨36⟩,
    dup1,
    dup3,
    add,
    swap3,
    push1 kissHealOutSize,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup4,
    dup8,
    dup1]
  exact ⟨_, _, by
    simpa [target, kissDaiTargetWord, kissHealSelectorShifted, kissHealSelector,
      kissHealSelectorMem, kissHealCalldataMem, kissHealOutPtr, kissHealOutSize,
      kissHealInSize, kissHealEndPtr, vowSlotWord, solcSlotWord, solcAddrMask,
      healRad, kissRad] using rd5062⟩

theorem RD.vowHealHealNoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4997⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd5062⟩ := RD.vowHealToHealExtcodesizeGuard rd hmem hread64
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5062⟩) (okPc := ⟨1915⟩) rd5062
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowHealToHealCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4997⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1918⟩
      (gasWord :: kissDaiTargetWord acc.2 I :: kissHealOutSize :: kissHealOutPtr ::
        kissHealInSize :: kissHealOutPtr :: kissHealOutSize :: kissHealEndPtr ::
        kissHealSelector :: kissDaiTargetWord acc.2 I :: healRad I :: ⟨412⟩ :: sel :: [])
      (kissHealCalldataMem I mem) (UInt256.ofNat 6) o acc k' C' := by
  obtain ⟨_, _, rd5062⟩ := RD.vowHealToHealExtcodesizeGuard rd hmem hread64
  obtain ⟨gasWord, k1918, C1918, rd1918⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5062⟩) (okPc := ⟨1915⟩) rd5062
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k1918, C1918, by simpa [healRad, kissRad] using rd1918⟩

theorem RD.vowHealHealPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4997⟩
      [healRad I, ⟨412⟩, sel] mem (UInt256.ofNat 6) o acc k C)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: kissHealEndPtr :: kissHealSelector ::
          kissDaiTargetWord acc.2 I :: healRad I :: ⟨412⟩ :: sel :: [])
        (kissHealCalldataMem I mem) (UInt256.ofNat 6) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := acc.2, createdAccounts := acc.1 }
        (EVM.address (kissVatAddress acc.2 I)) "heal" 0
        [.int (Int.ofNat (healRad I).toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd1918⟩ := RD.vowHealToHealCall rd hmem hread64 hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k1919, C1919, hΘpack, rd1919raw, houtsz⟩ :=
    RD.call rd1918 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k1919, C1919, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          kissHealOutPtr.toNat kissHealInSize.toNat)
          kissHealOutPtr.toNat kissHealOutSize.toNat) = UInt256.ofNat 6 := by
      rw [kissHealInSize_eq]
      unfold kissHealOutPtr kissHealOutSize
      native_decide
    have hmin : (min kissHealOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold kissHealOutSize
      rfl
    have rd1919 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1919⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: kissHealEndPtr :: kissHealSelector ::
          kissDaiTargetWord acc.2 I :: healRad I :: ⟨412⟩ :: sel :: [])
        (out.write 0 (kissHealCalldataMem I mem) kissHealOutPtr.toNat
          (min kissHealOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA', σ') k1919 C1919 :=
      haw ▸ rd1919raw
    rw [hmin, byteArray_write_len_zero] at rd1919
    exact rd1919
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := kissDaiTargetWord acc.2 I)
      (mem := kissHealCalldataMem I mem) (inOff := kissHealOutPtr)
      (inSize := kissHealInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (kissVatAddress_eq_daiTarget acc.2 I) ?_ ?_
    · simpa [healRad, kissRad] using kissHealEncode_eq I hmem
    · simpa [initState, hperm, healRad, kissRad] using hΘ

theorem vowHealSourceSinDecodeRevert
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai evmSin : EVM.State}
    {outDai outSin : ByteArray} {vatDai : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin : config.externalABI.decode? "sin" outSin = none) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  let locals1 := healLocalsVatDai I vatDai
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsDai :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, healLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsDai hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "rad") (value := healRad I) (healLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (healLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals1, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals1)
        (by simp [locals1, healLocalsVatDai, healLocals])
  have hguardSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatSin hvatCodeSin
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals1 } evmDai [thisAddr] =
        .ok [.address I.codeOwner] := by
    have henvDai : evmDai.executionEnv = evm0.executionEnv := by
      simpa [evm0] using typedCallViaEVM_executionEnv_eq hcallDai
    simpa [locals1, henvDai, evm0, initState] using evalExprs_kissThis evmDai locals1
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvatSin (by simp [evalExpr?, pure])
      hargsSin hcallSin hdecSin
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin) ?_
    exact ExecBlock.consRevert hcallSinStmt
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealSourceFreeSinUnderflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai evmSin : EVM.State}
    {outDai outSin : ByteArray} {vatDai vatSin SinVal : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hlt : vatSin.toNat < SinVal.toNat) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  let locals1 := healLocalsVatDai I vatDai
  let locals2 := healLocalsVatDaiVatSin I vatDai vatSin
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsDai :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, healLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsDai hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "rad") (value := healRad I) (healLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (healLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals1, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals1)
        (by simp [locals1, healLocalsVatDai, healLocals])
  have hguardSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatSin hvatCodeSin
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals1 } evmDai [thisAddr] =
        .ok [.address I.codeOwner] := by
    have henvDai : evmDai.executionEnv = evm0.executionEnv := by
      simpa [evm0] using typedCallViaEVM_executionEnv_eq hcallDai
    simpa [locals1, henvDai, evm0, initState] using evalExprs_kissThis evmDai locals1
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := locals2 } evmSin) := by
    simpa [locals1, locals2, healLocalsVatDaiVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvatSin (by simp [evalExpr?, pure]) hargsSin
        hcallSin hdecSin
  have hvatSinVar :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSin I vatDai vatSin)
        (name := "vatSin") (value := vatSin)
        (healLocalsVatDaiVatSin_get_vatSin I vatDai vatSin)
  have hSin :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals2, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals2)
        (by simp [locals2, healLocalsVatDaiVatSin, healLocalsVatDai, healLocals])
  have hargsSub :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "vatSin", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSinVar, hSin, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hsubStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin") .reverted := by
    have hbody := execSubFunctionRevert (evm := evmSin) (x := vatSin) (y := SinVal) hlt
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals2 })
      (evm := evmSin) (name := "sub") (retVar := "freeSin")
      (args := [.var "vatSin", .storage SinRef])
      (argVals := [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)])
      (callee := subFunction) (locals := uintBinaryLocals vatSin SinVal)
      hargsSub (by rfl) hbind hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    exact ExecBlock.consRevert hsubStmt
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealSourceHealDebtUnderflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai evmSin : EVM.State}
    {outDai outSin : ByteArray} {vatDai vatSin SinVal freeSin AshVal : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hlt : freeSin.toNat < AshVal.toNat) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  let locals1 := healLocalsVatDai I vatDai
  let locals2 := healLocalsVatDaiVatSin I vatDai vatSin
  let locals3 := healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsDai :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, healLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsDai hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "rad") (value := healRad I) (healLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (healLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals1, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals1)
        (by simp [locals1, healLocalsVatDai, healLocals])
  have hguardSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatSin hvatCodeSin
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals1 } evmDai [thisAddr] =
        .ok [.address I.codeOwner] := by
    have henvDai : evmDai.executionEnv = evm0.executionEnv := by
      simpa [evm0] using typedCallViaEVM_executionEnv_eq hcallDai
    simpa [locals1, henvDai, evm0, initState] using evalExprs_kissThis evmDai locals1
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := locals2 } evmSin) := by
    simpa [locals1, locals2, healLocalsVatDaiVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvatSin (by simp [evalExpr?, pure]) hargsSin
        hcallSin hdecSin
  have hvatSinVar :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSin I vatDai vatSin)
        (name := "vatSin") (value := vatSin)
        (healLocalsVatDaiVatSin_get_vatSin I vatDai vatSin)
  have hSin :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals2, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals2)
        (by simp [locals2, healLocalsVatDaiVatSin, healLocalsVatDai, healLocals])
  have hargsFree :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "vatSin", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSinVar, hSin, EvalResult.bind, bind, pure]
  have hbindFree :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hfreeStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin")
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := vatSin) (y := SinVal)
      (diff := freeSin) hfree hfreeOk
    simpa [locals2, locals3, healLocalsVatDaiVatSinFreeSin, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals2 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "freeSin")
        (args := [.var "vatSin", .storage SinRef])
        (argVals := [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals vatSin SinVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatSin SinVal freeSin })
        (value := some [.int (Int.ofNat freeSin.toNat)]) hargsFree (by rfl) hbindFree hbody)
  have hfreeVar :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.var "freeSin") =
        .ok (.int (Int.ofNat freeSin.toNat)) := by
    simpa [locals3] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin)
        (name := "freeSin") (value := freeSin)
        (healLocalsVatDaiVatSinFreeSin_get_freeSin I vatDai vatSin freeSin)
  have hAsh :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage AshRef) =
        .ok (.int (Int.ofNat AshVal.toNat)) := by
    simpa [locals3, hAshLoad] using
      evalExpr_kissAshStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, healLocalsVatDaiVatSinFreeSin, healLocalsVatDaiVatSin,
          healLocalsVatDai, healLocals])
  have hargsDebt :
      evalExprs? config { contract := contract, locals := locals3 } evmSin
        [.var "freeSin", .storage AshRef] =
          .ok [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] := by
    simp [evalExprs?, hfreeVar, hAsh, EvalResult.bind, bind, pure]
  have hbindDebt :
      bindParams? subFunction.params
          [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] =
        some (uintBinaryLocals freeSin AshVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hdebtStmt :
      ExecStmt config { contract := contract, locals := locals3 } evmSin
        (.internalCall "sub" [.var "freeSin", .storage AshRef] "healDebt") .reverted := by
    have hbody := execSubFunctionRevert (evm := evmSin) (x := freeSin) (y := AshVal) hlt
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals3 })
      (evm := evmSin) (name := "sub") (retVar := "healDebt")
      (args := [.var "freeSin", .storage AshRef])
      (argVals := [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)])
      (callee := subFunction) (locals := uintBinaryLocals freeSin AshVal)
      hargsDebt (by rfl) hbindDebt hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    refine ExecBlock.consNormal hfreeStmt ?_
    exact ExecBlock.consRevert hdebtStmt
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealSourceInsufficientDebt
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai evmSin : EVM.State}
    {outDai outSin : ByteArray}
    {vatDai vatSin SinVal freeSin AshVal healDebt : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : healDebt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hinsuff : healDebt.toNat < (healRad I).toNat) :
    let locals := healLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals healTransition.body .reverted := by
  intro locals evm0
  let locals1 := healLocalsVatDai I vatDai
  let locals2 := healLocalsVatDaiVatSin I vatDai vatSin
  let locals3 := healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin
  let locals4 := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, healLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsDai :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, healLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsDai hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "rad") (value := healRad I) (healLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := healLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (healLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hvatSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [locals1, kissVatAddress, vowAddressReturnWord, hvatLoadDai] using
      evalExpr_kissVatStorage (evm := evmDai) (locals := locals1)
        (by simp [locals1, healLocalsVatDai, healLocals])
  have hguardSin :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatSin hvatCodeSin
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals1 } evmDai [thisAddr] =
        .ok [.address I.codeOwner] := by
    have henvDai : evmDai.executionEnv = evm0.executionEnv := by
      simpa [evm0] using typedCallViaEVM_executionEnv_eq hcallDai
    simpa [locals1, henvDai, evm0, initState] using evalExprs_kissThis evmDai locals1
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := locals2 } evmSin) := by
    simpa [locals1, locals2, healLocalsVatDaiVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvatSin (by simp [evalExpr?, pure]) hargsSin
        hcallSin hdecSin
  have hvatSinVar :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSin I vatDai vatSin)
        (name := "vatSin") (value := vatSin)
        (healLocalsVatDaiVatSin_get_vatSin I vatDai vatSin)
  have hSin :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals2, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals2)
        (by simp [locals2, healLocalsVatDaiVatSin, healLocalsVatDai, healLocals])
  have hargsFree :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "vatSin", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSinVar, hSin, EvalResult.bind, bind, pure]
  have hbindFree :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hfreeStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin")
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := vatSin) (y := SinVal)
      (diff := freeSin) hfree hfreeOk
    simpa [locals2, locals3, healLocalsVatDaiVatSinFreeSin, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals2 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "freeSin")
        (args := [.var "vatSin", .storage SinRef])
        (argVals := [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals vatSin SinVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatSin SinVal freeSin })
        (value := some [.int (Int.ofNat freeSin.toNat)]) hargsFree (by rfl) hbindFree hbody)
  have hfreeVar :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.var "freeSin") =
        .ok (.int (Int.ofNat freeSin.toNat)) := by
    simpa [locals3] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSin I vatDai vatSin freeSin)
        (name := "freeSin") (value := freeSin)
        (healLocalsVatDaiVatSinFreeSin_get_freeSin I vatDai vatSin freeSin)
  have hAsh :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage AshRef) =
        .ok (.int (Int.ofNat AshVal.toNat)) := by
    simpa [locals3, hAshLoad] using
      evalExpr_kissAshStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, healLocalsVatDaiVatSinFreeSin, healLocalsVatDaiVatSin,
          healLocalsVatDai, healLocals])
  have hargsDebt :
      evalExprs? config { contract := contract, locals := locals3 } evmSin
        [.var "freeSin", .storage AshRef] =
          .ok [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] := by
    simp [evalExprs?, hfreeVar, hAsh, EvalResult.bind, bind, pure]
  have hbindDebt :
      bindParams? subFunction.params
          [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] =
        some (uintBinaryLocals freeSin AshVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hdebtStmt :
      ExecStmt config { contract := contract, locals := locals3 } evmSin
        (.internalCall "sub" [.var "freeSin", .storage AshRef] "healDebt")
        (.ok { contract := contract, locals := locals4 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := freeSin) (y := AshVal)
      (diff := healDebt) hdebt hdebtOk
    simpa [locals3, locals4, healLocalsVatDaiVatSinFreeSinHealDebt,
      resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals3 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "healDebt")
        (args := [.var "freeSin", .storage AshRef])
        (argVals := [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals freeSin AshVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ freeSin AshVal healDebt })
        (value := some [.int (Int.ofNat healDebt.toNat)]) hargsDebt (by rfl) hbindDebt hbody)
  have hrad :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.var "rad") =
        .ok (.int (Int.ofNat (healRad I).toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt)
        (name := "rad") (value := healRad I)
        (healLocalsVatDaiVatSinFreeSinHealDebt_get_rad I vatDai vatSin freeSin healDebt)
  have hhealDebt :
      evalExpr? config { contract := contract, locals := locals4 } evmSin (.var "healDebt") =
        .ok (.int (Int.ofNat healDebt.toNat)) := by
    simpa [locals4] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := healLocalsVatDaiVatSinFreeSinHealDebt I vatDai vatSin freeSin healDebt)
        (name := "healDebt") (value := healDebt)
        (healLocalsVatDaiVatSinFreeSinHealDebt_get_healDebt I vatDai vatSin freeSin healDebt)
  have hreqDebt :
      evalExpr? config { contract := contract, locals := locals4 } evmSin
        (.binary .le (.var "rad") (.var "healDebt")) = .ok (.bool false) :=
    evalExpr_le_uint256_false hrad hhealDebt hinsuff
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 healTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardSin) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    refine ExecBlock.consNormal hfreeStmt ?_
    refine ExecBlock.consNormal hdebtStmt ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqDebt)
  simpa [ExecTransitionBody, evm0, locals, healTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowHealSinDecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmSin : EVM.State} {mem outDai outSin : ByteArray}
    {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨1⟩ :: healSinEndPtr :: healSinSelector :: target ::
        ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin acc k C)
    (houtShort : outSin.size < 32)
    (houtSize : outSin.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, rd1295⟩ := RD.vowHealSinCallSuccessToDecode rd1277 (by simp)
  have hrev :=
    RD.vowHealSinReturnDecodeShortReverts rd1295 houtShort houtSize hMload64Value
  have hbody := vowHealSourceSinDecodeRevert (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (evmSin := evmSin) (outDai := outDai) (outSin := outSin)
    (vatDai := vatDai) hwv hvatCode hcallDai hdecDai hvatDaiEnough hvatLoadDai
    hvatCodeSin hcallSin (vatSinDecode_none_short houtShort)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowHealFreeSinUnderflowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatDai vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmSin : EVM.State} {mem outDai outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd1318 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (vatSin :: ⟨1325⟩ :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin acc k C)
    (hunder : vatSin.toNat < (vowSlotWord ⟨5⟩ acc.2 I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ acc.2 I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowHealFreeSinSubUnderflow rd1318 hunder
  have hbody := vowHealSourceFreeSinUnderflow (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (evmSin := evmSin) (outDai := outDai) (outSin := outSin)
    (vatDai := vatDai) (vatSin := vatSin) (SinVal := vowSlotWord ⟨5⟩ acc.2 I)
    hwv hvatCode hcallDai hdecDai hvatDaiEnough hvatLoadDai hvatCodeSin hcallSin
    hdecSin hSinLoad hunder
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowHealDebtUnderflowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatDai vatSin freeSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmSin : EVM.State} {mem outDai outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd1325 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (freeSin :: ⟨4921⟩ :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin acc k C)
    (hunder : freeSin.toNat < (vowSlotWord ⟨6⟩ acc.2 I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ acc.2 I)
    (hfree : freeSin = UInt256.sub vatSin (vowSlotWord ⟨5⟩ acc.2 I))
    (hfreeOk : (vowSlotWord ⟨5⟩ acc.2 I).toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ acc.2 I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowHealDebtSubUnderflow rd1325 hunder
  have hbody := vowHealSourceHealDebtUnderflow (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (evmSin := evmSin) (outDai := outDai) (outSin := outSin)
    (vatDai := vatDai) (vatSin := vatSin) (SinVal := vowSlotWord ⟨5⟩ acc.2 I)
    (freeSin := freeSin) (AshVal := vowSlotWord ⟨6⟩ acc.2 I)
    hwv hvatCode hcallDai hdecDai hvatDaiEnough hvatLoadDai hvatCodeSin hcallSin
    hdecSin hSinLoad hfree hfreeOk hAshLoad hunder
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowHealInsufficientDebtBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatDai vatSin freeSin healDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmDai evmSin : EVM.State} {mem outDai outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some healTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (healTransition.params.map Param.name)
        (transitionSignature healTransition).paramTypes I.calldata = some (healLocals I))
    (rd4921 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨4921⟩
      (healDebt :: healRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin acc k C)
    (hinsuff : healDebt.toNat < (healRad I).toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (healRad I).toNat ≤ vatDai.toNat)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ_solm I)
    (hvatCodeSin :
      0 < (UInt256.ofNat
        ((evmDai.lookupAccount (kissVatAddress σ_solm I)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config evmDai (EVM.address (kissVatAddress σ_solm I)) "sin" 0
        [.address I.codeOwner] (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ acc.2 I)
    (hfree : freeSin = UInt256.sub vatSin (vowSlotWord ⟨5⟩ acc.2 I))
    (hfreeOk : (vowSlotWord ⟨5⟩ acc.2 I).toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ acc.2 I)
    (hdebt : healDebt = UInt256.sub freeSin (vowSlotWord ⟨6⟩ acc.2 I))
    (hdebtOk : (vowSlotWord ⟨6⟩ acc.2 I).toNat ≤ freeSin.toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowHealInsufficientDebt rd4921 hinsuff hmem hread64
  have hbody := vowHealSourceInsufficientDebt (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai := evmDai) (evmSin := evmSin) (outDai := outDai) (outSin := outSin)
    (vatDai := vatDai) (vatSin := vatSin) (SinVal := vowSlotWord ⟨5⟩ acc.2 I)
    (freeSin := freeSin) (AshVal := vowSlotWord ⟨6⟩ acc.2 I) (healDebt := healDebt)
    hwv hvatCode hcallDai hdecDai hvatDaiEnough hvatLoadDai hvatCodeSin hcallSin
    hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk hinsuff
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Vow
