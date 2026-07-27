import Benchmarks.Dss.End.Pack
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.End

set_option maxRecDepth 2000000

noncomputable def packMovePostCallMem (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) : ByteArray :=
  out.write 0 (packMoveCalldataMem σ I solcFreePtrMem) packMoveOutPtr.toNat
    (min packMoveOutSize (UInt256.ofNat out.size)).toNat

theorem packMovePostCallMem_size (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) :
    (packMovePostCallMem σ I out).size = 228 := by
  have hmin : (min packMoveOutSize (UInt256.ofNat out.size)).toNat = 0 := by
    unfold packMoveOutSize
    rw [← u256_ofNat_toNat (UInt256.ofNat out.size)]
    exact umin_ofNat_right_toNat_of_ge (by norm_num [UInt256.size]) (Nat.zero_le _)
      (UInt256.ofNat out.size).val.isLt
  unfold packMovePostCallMem
  rw [hmin, byteArray_write_len_zero]
  exact packMoveCalldataMem_size σ I solcFreePtrMem_size

theorem packMovePostCallMem_read64 (σ : AccountMap) (I : ExecutionEnv) (out : ByteArray) :
    (packMovePostCallMem σ I out).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hmin : (min packMoveOutSize (UInt256.ofNat out.size)).toNat = 0 := by
    unfold packMoveOutSize
    rw [← u256_ofNat_toNat (UInt256.ofNat out.size)]
    exact umin_ofNat_right_toNat_of_ge (by norm_num [UInt256.size]) (Nat.zero_le _)
      (UInt256.ofNat out.size).val.isLt
  unfold packMovePostCallMem
  rw [hmin, byteArray_write_len_zero]
  exact packMoveCalldataMem_read64 σ I solcFreePtrMem_size solcFreePtrMem_read64

theorem RD.endPackMoveCallSuccessReturn
    {cA σStack σCall I} {g : Sat256} {s0 : State} {out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨6552⟩
      (⟨1⟩ :: packMoveEndPtr :: packMoveSelectorWord ::
        packVatMaskedWord σStack I :: packWadWord I :: ⟨562⟩ :: [sel])
      (packMovePostCallMem σStack I out) (UInt256.ofNat 8) out (cA, σCall) k C)
    (hperm : I.perm = true)
    (hfit : (packBagWord σCall I).toNat + (packWadWord I).toNat < UInt256.size) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σCall (packBagStorageSlot I)
        (packBagWord σCall I + packWadWord I))
      ByteArray.empty := by
  have hmem := packMovePostCallMem_size σStack I out
  have hread64 := packMovePostCallMem_read64 σStack I out
  obtain ⟨k6570, C6570, rd6570⟩ :=
    RD.endPackMoveCallSuccessToBag rd (by simp)
  obtain ⟨k10092, C10092, rd10092⟩ :=
    RD.endPackLoadBagToAdd rd6570 hmem
  obtain ⟨k6599, C6599, rd6599⟩ :=
    RD.endPackBagAddSuccess rd10092 hfit
  exact RD.endPackStoreBagAndReturn rd6599 hperm hmem hread64

theorem RD.endPackBagAddOverflow
    {cA σ I} {g : Sat256} {s0 : State} {mem o : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨10092⟩
      (packWadWord I :: packBagWord σ I :: ⟨6599⟩ ::
        packWadWord I :: ⟨562⟩ :: [sel])
      mem (UInt256.ofNat 8) o (cA, σ) k C)
    (hover : UInt256.size ≤ (packBagWord σ I).toNat + (packWadWord I).toNat) :
    RDrev endBytecode g s0 := by
  have hsum_lt2 :
      (packBagWord σ I).toNat + (packWadWord I).toNat < 2 * UInt256.size := by
    have hbag : (packBagWord σ I).toNat < UInt256.size := (packBagWord σ I).val.isLt
    have hwad : (packWadWord I).toNat < UInt256.size := (packWadWord I).val.isLt
    omega
  have hmod :
      ((packBagWord σ I).toNat + (packWadWord I).toNat) % UInt256.size =
        (packBagWord σ I).toNat + (packWadWord I).toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat :
      (packBagWord σ I + packWadWord I).toNat =
        (packBagWord σ I).toNat + (packWadWord I).toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (packBagWord σ I + packWadWord I) (packBagWord σ I) = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hbag : (packBagWord σ I).toNat < UInt256.size := (packBagWord σ I).val.isLt
    have hwad : (packWadWord I).toNat < UInt256.size := (packWadWord I).val.isLt
    omega
  have rd10099pre := evm_run rd with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw lt (by native_decide) (by evm_ov)]
  rw [show packWadWord I + packBagWord σ I = packBagWord σ I + packWadWord I from
    u256_add_comm (packWadWord I) (packBagWord σ I)] at rd10099pre
  rw [hlt] at rd10099pre
  have rd10103pre := evm_run rd10099pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨10108⟩ (by native_decide) (by evm_ov)]
  have rd10104 := rd10103pre.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.uniswapPush1Dup1Revert0 rd10104
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem RD.endPackMoveCallSuccessAddOverflow
    {cA σStack σCall I} {g : Sat256} {s0 : State} {out : ByteArray}
    {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨6552⟩
      (⟨1⟩ :: packMoveEndPtr :: packMoveSelectorWord ::
        packVatMaskedWord σStack I :: packWadWord I :: ⟨562⟩ :: [sel])
      (packMovePostCallMem σStack I out) (UInt256.ofNat 8) out (cA, σCall) k C)
    (hover : UInt256.size ≤ (packBagWord σCall I).toNat + (packWadWord I).toNat) :
    RDrev endBytecode g s0 := by
  have hmem := packMovePostCallMem_size σStack I out
  obtain ⟨k6570, C6570, rd6570⟩ :=
    RD.endPackMoveCallSuccessToBag rd (by simp)
  obtain ⟨k10092, C10092, rd10092⟩ :=
    RD.endPackLoadBagToAdd rd6570 hmem
  exact RD.endPackBagAddOverflow rd10092 hover

theorem packUint256ArgEncoding (v : UInt256) :
    ABI.encodeABIValue? (.elem (.int uint256Int)) (.int (Int.ofNat v.toNat)) =
      some (EVM.Word.toBytesBE v) := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  have hltNat : v.toNat < EVM.twoPow 256 := by
    change v.val.val < EVM.twoPow 256
    exact v.val.isLt
  simp [uint256Int, ABI.encodeABIValue?, ABI.encodeABIWord?, hword, hltNat]

theorem packAddressArgEncoding (a : AccountAddress) :
    ABI.encodeABIValue? (.elem .address) (.address a) =
      some (EVM.Word.toBytesBE (UInt256.ofNat a.val)) := by
  simp [ABI.encodeABIValue?, ABI.encodeABIWord?]
  rw [show EVM.word (↑a : ℕ) = UInt256.ofNat (↑a : ℕ) from rfl]

theorem packMoveEncodeWords (source : AccountAddress) (vow amt : UInt256)
    (hvow : EVM.word ↑(AccountAddress.ofUInt256 vow) = vow) :
    config.externalABI.encode? "move"
      [.address source, .address (AccountAddress.ofUInt256 vow), .int (Int.ofNat amt.toNat)] =
      some (moveSelector ++ (UInt256.ofNat source.val).toByteArray ++ vow.toByteArray ++
        amt.toByteArray) := by
  have hsource := packAddressArgEncoding source
  have hvowEnc : ABI.encodeABIValue? (.elem .address)
      (.address (AccountAddress.ofUInt256 vow)) = some (EVM.Word.toBytesBE vow) := by
    simp [ABI.encodeABIValue?, ABI.encodeABIWord?, hvow]
  have hamtCast : ABI.encodeABIValue? (.elem (.int uint256Int)) (Value.int ↑amt.toNat) =
      some (EVM.Word.toBytesBE amt) := by
    simpa [Int.ofNat_eq_natCast] using packUint256ArgEncoding amt
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    ABI.encodeABIValuesFrom?, hsource, hvowEnc, addr, uint256]
  rw [hamtCast]
  simp only [Option.bind]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc, word_toBytesBE_toByteArray_eq_toByteArray]

theorem packMoveEncode_eq (σ : AccountMap) (I : ExecutionEnv) :
    config.externalABI.encode? "move"
      [.address I.source, .address (AccountAddress.ofUInt256 (packVowMaskedWord σ I)),
        .int (Int.ofNat (packAmtWord I).toNat)] =
      some ((packMoveCalldataMem σ I solcFreePtrMem).readWithPadding
        packMoveOutPtr.toNat packMoveInSize.toNat) := by
  rw [show packMoveOutPtr.toNat = 128 by native_decide,
    show packMoveInSize.toNat = 100 by native_decide]
  rw [packMoveCalldataMem_read128_100 σ I solcFreePtrMem_size]
  simpa [packSourceWord] using
    packMoveEncodeWords I.source (packVowMaskedWord σ I) (packAmtWord I)
      (packVowAddressWord σ I)

theorem evmAddress_ofNat_toNat_eq_ofUInt256 (w : UInt256) :
    EVM.address (↑(AccountAddress.ofNat w.toNat) : ℕ) = AccountAddress.ofUInt256 w := by
  apply Fin.ext
  simp [EVM.address, EVM.uintN, AccountAddress.ofNat, AccountAddress.ofUInt256,
    UInt256.toNat]
  rw [show AccountAddress.size = EVM.twoPow 160 from by decide]
  rw [Nat.mod_mod]

theorem RD.endPackMovePostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {k C : ℕ}
    (rd : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6462⟩
      (packAmtWord I :: packVowMaskedWord σ I :: packSourceWord I ::
        packMoveSelectorWord :: packVatMaskedWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (packVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6552⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: packMoveEndPtr :: packMoveSelectorWord ::
          packVatMaskedWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
        (packMovePostCallMem σ I out) (UInt256.ofNat 8) out (cA', σ') k' C'
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)) "move" 0
        [.address I.source, .address (AccountAddress.ofUInt256 (packVowMaskedWord σ I)),
          .int (Int.ofNat (packAmtWord I).toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) I.perm
    ∧ out.size < UInt256.size := by
  obtain ⟨_, _, _, rd6551⟩ := RD.endPackMoveCall rd hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k6552, C6552, hΘpack, rd6552raw, houtsz⟩ :=
    RD.call rd6551 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k6552, C6552, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          packMoveOutPtr.toNat packMoveInSize.toNat)
          packMoveOutPtr.toNat packMoveOutSize.toNat) = UInt256.ofNat 8 := by
      unfold packMoveOutPtr packMoveInSize packMoveOutSize
      native_decide
    simpa [packMovePostCallMem] using haw ▸ rd6552raw
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := I.perm) (targetWord := packVatMaskedWord σ I)
      (mem := packMoveCalldataMem σ I solcFreePtrMem) (inOff := packMoveOutPtr)
      (inSize := packMoveInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      ?_ (packMoveEncode_eq σ I) ?_
    · exact (evmAddress_ofNat_toNat_eq_ofUInt256 (packVatMaskedWord σ I)).symm
    · simpa [initState] using hΘ

theorem RD.endPackMoveDepthLimitReverts
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (rd : RD endBytecode I g s0 ⟨6462⟩
      (packAmtWord I :: packVowMaskedWord σ I :: packSourceWord I ::
        packMoveSelectorWord :: packVatMaskedWord σ I :: packWadWord I :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (packVatMaskedWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    RDrev endBytecode g s0 := by
  obtain ⟨_, _, _, rd6551⟩ := RD.endPackMoveCall rd hcodeSize
  obtain ⟨k6552, C6552, rd6552raw⟩ :=
    RD.callDepthLimit rd6551 (by native_decide) hdepth (by simp)
  have hmin : (min packMoveOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    unfold packMoveOutSize
    rw [← u256_ofNat_toNat (UInt256.ofNat ByteArray.empty.size)]
    exact umin_ofNat_right_toNat_of_ge (by norm_num [UInt256.size]) (Nat.zero_le _)
      (UInt256.ofNat ByteArray.empty.size).val.isLt
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        packMoveOutPtr.toNat packMoveInSize.toNat)
        packMoveOutPtr.toNat packMoveOutSize.toNat) = UInt256.ofNat 8 := by
    unfold packMoveOutPtr packMoveInSize packMoveOutSize
    native_decide
  have rd6552 : RD endBytecode I g s0 ⟨6552⟩
      (⟨0⟩ :: packMoveEndPtr :: packMoveSelectorWord :: packVatMaskedWord σ I ::
        packWadWord I :: ⟨562⟩ :: [sel])
      (packMovePostCallMem σ I ByteArray.empty) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k6552 C6552 := by
    simpa [packMovePostCallMem, hmin] using haw ▸ rd6552raw
  exact RD.endPackMoveCallFailure rd6552 (by native_decide) (by simp)

theorem evalExpr_packVatCodeGuard_true {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat ≠
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat]
  exact Nat.pos_of_ne_zero hcode

theorem evalExpr_packVowStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "vow" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vowRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
          solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨4⟩)]
  · exact congrArg EvalResult.ok (endStorageLocLoad_address_offset0 _ ⟨4⟩)
  · exact hbase
  · simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]

theorem evalExprs_packMoveArgs {cA gh bl σ σ₀ A I} {g : UInt256} :
    evalExprs? config { contract := contract, locals := packStoreAmt I }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      [sender, vowAddr, .var "amt"] =
      .ok [.address I.source, .address (AccountAddress.ofUInt256 (packVowMaskedWord σ I)),
        .int (Int.ofNat (packAmtWord I).toNat)] := by
  have hvow : evalExpr? config { contract := contract, locals := packStoreAmt I }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) vowAddr =
      .ok (.address (AccountAddress.ofUInt256 (packVowMaskedWord σ I))) := by
    simpa [vowAddr, packVowMaskedWord, packVowWord, endSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount, u256_land_comm,
      accountAddress_ofUInt256_eq_ofNat_toNat] using
      evalExpr_packVowStorage (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (locals := packStoreAmt I) (by simp [packStoreAmt, packStore])
  have hvow' : evalExpr? config
      { contract := contract,
        locals := Std.HashMap.insert (packStore I) "amt" (Value.int ↑(packAmtWord I).toNat) }
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) vowAddr =
      .ok (.address (AccountAddress.ofUInt256 (packVowMaskedWord σ I))) := by
    simpa [packStoreAmt, Int.ofNat_eq_natCast] using hvow
  simp [evalExprs?, evalExpr?, sender, envValue, packStoreAmt, EvalResult.bind, bind, pure,
    EvalResult.ofOption]
  rw [hvow']
  simp [initState]

theorem endPackSourceBodyCallFailure {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmMove : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : packDebtWord σ I ≠ ⟨0⟩)
    (hmul : (packWadWord I).toNat * packRayWord.toNat < UInt256.size)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallMove :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)) "move" 0
        [.address I.source, .address (AccountAddress.ofUInt256 (packVowMaskedWord σ I)),
          .int (Int.ofNat (packAmtWord I).toNat)]
        (false, evmMove, out) true) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (packStore I) packTransition.body .reverted := by
  intro evm0
  have hdebtGuard :
      evalExpr? config { contract := contract, locals := packStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := packStore I } evm0
          (.storage debtRef) =
          .ok (.int (Int.ofNat (packDebtWord σ I).toNat)) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := packStore I })
        (slot := debtRef)
        (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int (Int.ofNat (packDebtWord σ I).toNat))
        (hbase := by simp [packStore, debtRef])
        (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [packDebtWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hne : (Value.int (Int.ofNat (packDebtWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hdebt (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hne,
      Bool.not_false]
  have hargsMul :
      evalExprs? config { contract := contract, locals := packStore I } evm0
        [.var "wad", .intLit RAY] =
        .ok [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)] := by
    change evalExprs? config { contract := contract, locals := packStore I } evm0
        [.var "wad", .intLit RAY] =
        .ok [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat 1000000000000000000000000000)]
    simp [evalExprs?, evalExpr?, packStore, RAY, EvalResult.ofOption, EvalResult.bind, bind,
      pure]
  have hlookup : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbind :
      bindParams? mulFunction.params
        [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)] = some (packMulLocals I) := by
    simp [mulFunction, packMulLocals, bindParams?]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := packStore I } evm0
        (.internalCall "mul" [.var "wad", .intLit RAY] "amt")
        (.ok { contract := contract, locals := packStoreAmt I } evm0) := by
    have hbody := packMulFunctionBodyReturns evm0 I hmul
    simpa [packStoreAmt, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := packStore I })
        (evm := evm0) (calleeEvm := evm0) (name := "mul") (retVar := "amt")
        (args := [.var "wad", .intLit RAY])
        (argVals := [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)])
        (callee := mulFunction) (locals := packMulLocals I)
        (calleeSolm := { contract := contract, locals := packMulLocalsZ I (packAmtWord I) })
        (value := some [.int (Int.ofNat (packAmtWord I).toNat)]) hargsMul hlookup hbind hbody)
  have hvat :
      evalExpr? config { contract := contract, locals := packStoreAmt I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)) := by
    simpa [packVatMaskedWord, packVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_packVatStorage (evm := evm0) (locals := packStoreAmt I)
        (by simp [packStoreAmt, packStore])
  have hguard :
      evalExpr? config { contract := contract, locals := packStoreAmt I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_packVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsMove := evalExprs_packMoveArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hcallStmt :
      ExecStmt config { contract := contract, locals := packStoreAmt I } evm0
        (.externalCall (.storage vatRef) "move" (.intLit 0) [sender, vowAddr, .var "amt"]
          "_move" (perm := true)) .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargsMove hcallMove
  have hblock :
      ExecBlock config { contract := contract, locals := packStore I } evm0 packTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hdebtGuard) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, packTransition, nonpayable, checkedExternalCallStmts]
    using ExecFuncBody.execBlockRevert hblock

set_option maxHeartbeats 2000000 in
theorem endPackSourceBodyCallSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmMove : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : packDebtWord σ I ≠ ⟨0⟩)
    (hmul : (packWadWord I).toNat * packRayWord.toNat < UInt256.size)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallMove :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)) "move" 0
        [.address I.source, .address (AccountAddress.ofUInt256 (packVowMaskedWord σ I)),
          .int (Int.ofNat (packAmtWord I).toNat)]
        (true, evmMove, out) true)
    (hfit :
      (Solm.EVM.storageLoad evmMove evmMove.executionEnv.codeOwner
        (packBagStorageSlot evmMove.executionEnv)).toNat + (packWadWord I).toNat <
          UInt256.size) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let bagOld := Solm.EVM.storageLoad evmMove evmMove.executionEnv.codeOwner
      (packBagStorageSlot evmMove.executionEnv)
    let bagNew := bagOld + packWadWord I
    let localsMove := (packStoreAmt I).insert "_move" .unit
    let finalFrame : Frame :=
      { contract := contract,
        locals := localsMove.insert "bagNew" (.int (Int.ofNat bagNew.toNat)) }
    ExecTransitionBody config contract evm0 (packStore I) packTransition.body
      (.returned finalFrame
        (Solm.EVM.storageStore evmMove evmMove.executionEnv.codeOwner
          (packBagStorageSlot evmMove.executionEnv) bagNew)
        none) := by
  intro evm0 bagOld bagNew localsMove finalFrame
  have hdebtGuard :
      evalExpr? config { contract := contract, locals := packStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := packStore I } evm0
          (.storage debtRef) =
          .ok (.int (Int.ofNat (packDebtWord σ I).toNat)) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := packStore I })
        (slot := debtRef)
        (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int (Int.ofNat (packDebtWord σ I).toNat))
        (hbase := by simp [packStore, debtRef])
        (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [packDebtWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hne : (Value.int (Int.ofNat (packDebtWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hdebt (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hne,
      Bool.not_false]
  have hargsMul :
      evalExprs? config { contract := contract, locals := packStore I } evm0
        [.var "wad", .intLit RAY] =
        .ok [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)] := by
    change evalExprs? config { contract := contract, locals := packStore I } evm0
        [.var "wad", .intLit RAY] =
        .ok [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat 1000000000000000000000000000)]
    simp [evalExprs?, evalExpr?, packStore, RAY, EvalResult.ofOption, EvalResult.bind, bind,
      pure]
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbindMul :
      bindParams? mulFunction.params
        [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)] = some (packMulLocals I) := by
    simp [mulFunction, packMulLocals, bindParams?]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := packStore I } evm0
        (.internalCall "mul" [.var "wad", .intLit RAY] "amt")
        (.ok { contract := contract, locals := packStoreAmt I } evm0) := by
    have hbody := packMulFunctionBodyReturns evm0 I hmul
    simpa [packStoreAmt, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := packStore I })
        (evm := evm0) (calleeEvm := evm0) (name := "mul") (retVar := "amt")
        (args := [.var "wad", .intLit RAY])
        (argVals := [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)])
        (callee := mulFunction) (locals := packMulLocals I)
        (calleeSolm := { contract := contract, locals := packMulLocalsZ I (packAmtWord I) })
        (value := some [.int (Int.ofNat (packAmtWord I).toNat)]) hargsMul hlookupMul
        hbindMul hbody)
  have hvat :
      evalExpr? config { contract := contract, locals := packStoreAmt I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)) := by
    simpa [packVatMaskedWord, packVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_packVatStorage (evm := evm0) (locals := packStoreAmt I)
        (by simp [packStoreAmt, packStore])
  have hguard :
      evalExpr? config { contract := contract, locals := packStoreAmt I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_packVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsMove := evalExprs_packMoveArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hdecode : config.externalABI.decode? "move" out = some ([] : List Value) := by
    simp [config, externalABI, decodeVoid?]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := packStoreAmt I } evm0
        (.externalCall (.storage vatRef) "move" (.intLit 0) [sender, vowAddr, .var "amt"]
          "_move" (perm := true))
        (.ok { contract := contract, locals := localsMove } evmMove) := by
    simpa [localsMove] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsMove hcallMove hdecode
  have hbag :
      evalExpr? config { contract := contract, locals := localsMove } evmMove
        (.storage (bagRef sender)) =
        .ok (.int (Int.ofNat bagOld.toNat)) := by
    simpa [bagOld] using
      evalExpr_packBagStorage (evm := evmMove) (locals := localsMove)
        (by simp [localsMove, packStoreAmt, packStore])
  have hwad :
      evalExpr? config { contract := contract, locals := localsMove } evmMove (.var "wad") =
        .ok (.int (Int.ofNat (packWadWord I).toNat)) := by
    have hget :
        localsMove.get? "wad" = some (.int (Int.ofNat (packWadWord I).toNat)) := by
      unfold localsMove packStoreAmt packStore
      rw [store_get_ne]
      · rw [store_get_ne]
        · simp
        · native_decide
      · native_decide
    exact evalExpr_packVarUInt256 (evm := evmMove) (locals := localsMove)
      (name := "wad") (value := packWadWord I) hget
  have hargsAdd :
      evalExprs? config { contract := contract, locals := localsMove } evmMove
        [.storage (bagRef sender), .var "wad"] =
        .ok [Value.int (Int.ofNat bagOld.toNat),
          Value.int (Int.ofNat (packWadWord I).toNat)] := by
    simp [evalExprs?, hbag, hwad, EvalResult.bind, bind, pure]
  have hlookupAdd : lookupCallable? contract "add" = some addFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbindAdd :
      bindParams? addFunction.params
        [Value.int (Int.ofNat bagOld.toNat), Value.int (Int.ofNat (packWadWord I).toNat)] =
        some (packAddLocals bagOld (packWadWord I)) := by
    simp [addFunction, packAddLocals, bindParams?]
  have haddStmt :
      ExecStmt config { contract := contract, locals := localsMove } evmMove
        (.internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew")
        (.ok finalFrame evmMove) := by
    have hbody := packAddFunctionBodyReturns evmMove (x := bagOld) (y := packWadWord I)
      (sum := bagNew) (by simp [bagNew]) hfit
    change ExecStmt config { contract := contract, locals := localsMove } evmMove
      (.internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew")
      (.ok (resumeAfterInternalCall { contract := contract, locals := localsMove } "bagNew"
        (some [.int (Int.ofNat bagNew.toNat)])) evmMove)
    exact
      internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := localsMove })
        (evm := evmMove) (calleeEvm := evmMove) (name := "add") (retVar := "bagNew")
        (args := [.storage (bagRef sender), .var "wad"])
        (argVals := [Value.int (Int.ofNat bagOld.toNat),
          Value.int (Int.ofNat (packWadWord I).toNat)])
        (callee := addFunction) (locals := packAddLocals bagOld (packWadWord I))
        (value := some [.int (Int.ofNat bagNew.toNat)]) hargsAdd hlookupAdd hbindAdd hbody
  have hbagNewExpr :
      evalExpr? config finalFrame evmMove
        (.var "bagNew") = .ok (.int (Int.ofNat bagNew.toNat)) := by
    have hget :
        finalFrame.locals.get? "bagNew" = some (.int (Int.ofNat bagNew.toNat)) := by
      change (localsMove.insert "bagNew" (.int (Int.ofNat bagNew.toNat))).get? "bagNew" =
        some (.int (Int.ofNat bagNew.toNat))
      exact store_get_self localsMove "bagNew" (.int (Int.ofNat bagNew.toNat))
    simpa [finalFrame] using
      evalExpr_packVarUInt256 (evm := evmMove) (locals := finalFrame.locals)
        (name := "bagNew") (value := bagNew) hget
  have hassign :
      assignStorageRef? config
        finalFrame evmMove
        .storage (bagRef sender) (.int (Int.ofNat bagNew.toNat)) =
        .ok (finalFrame,
          Solm.EVM.storageStore evmMove evmMove.executionEnv.codeOwner
            (packBagStorageSlot evmMove.executionEnv) bagNew) := by
    simpa [finalFrame] using
      assign_packBagStorage evmMove bagNew (by simp [localsMove, packStoreAmt, packStore])
  have hassignStmt :
      ExecStmt config
        finalFrame evmMove
        (.assign .storage (bagRef sender) (.var "bagNew"))
        (.ok finalFrame
          (Solm.EVM.storageStore evmMove evmMove.executionEnv.codeOwner
            (packBagStorageSlot evmMove.executionEnv) bagNew)) :=
    ExecStmt.assign hbagNewExpr hassign
  have hblock :
      ExecBlock config { contract := contract, locals := packStore I } evm0 packTransition.body
        (.ok finalFrame
          (Solm.EVM.storageStore evmMove evmMove.executionEnv.codeOwner
            (packBagStorageSlot evmMove.executionEnv) bagNew)) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hdebtGuard) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallStmt ?_
    refine ExecBlock.consNormal haddStmt ?_
    exact ExecBlock.consNormal hassignStmt ExecBlock.nil
  simpa [ExecTransitionBody, evm0, packTransition, nonpayable, checkedExternalCallStmts,
    localsMove, bagOld, bagNew] using ExecFuncBody.execBlockOK hblock

theorem evalExpr_pack_add_overflow {evm : EVM.State} {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat + y.toNat) :
    evalExpr? config { contract := contract, locals := packAddLocals x y } evm
      (u256 (.binary .add (.var "x") (.var "y"))) = .revert := by
  unfold u256
  have hx :
      (packAddLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) :=
    packAddLocals_get_x x y
  have hy :
      (packAddLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) :=
    packAddLocals_get_y x y
  simp only [evalExpr?, hx, hy, EvalResult.bind, bind, EvalResult.ofOption, pure,
    evalBinaryOp?, uint256Int]
  have hge :
      (2 : Int) ^ (256 : Nat) ≤ Int.ofNat x.toNat + Int.ofNat y.toNat := by
    have hgeNat : 2 ^ (256 : Nat) ≤ x.toNat + y.toNat := by
      simpa [UInt256.size] using hover
    have hgeInt : ((2 ^ (256 : Nat) : Nat) : Int) ≤ (x.toNat + y.toNat : Int) := by
      exact_mod_cast hgeNat
    simpa [Nat.cast_add, Nat.cast_pow] using hgeInt
  have hcond :
      (decide (Int.ofNat x.toNat + Int.ofNat y.toNat < 0) ||
        decide (Int.ofNat x.toNat + Int.ofNat y.toNat ≥ 2 ^ (256 : Nat))) = true := by
    rw [Bool.or_eq_true]
    exact Or.inr (decide_eq_true hge)
  rw [hcond]
  rfl

theorem packAddFunctionBodyReverts (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat + y.toNat) :
    ExecFuncBody config { contract := contract, locals := packAddLocals x y } evm
      addFunction.body .reverted := by
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consRevert <|
      ExecStmt.letDeclRevert (evalExpr_pack_add_overflow (evm := evm) (x := x) (y := y) hover)

set_option maxHeartbeats 2000000 in
theorem endPackSourceBodyCallSuccessAddOverflow {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmMove : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hdebt : packDebtWord σ I ≠ ⟨0⟩)
    (hmul : (packWadWord I).toNat * packRayWord.toNat < UInt256.size)
    (hvatCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)).option 0
          (fun acc => acc.code.size))).toNat ≠ 0)
    (hcallMove :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)) "move" 0
        [.address I.source, .address (AccountAddress.ofUInt256 (packVowMaskedWord σ I)),
          .int (Int.ofNat (packAmtWord I).toNat)]
        (true, evmMove, out) true)
    (hover :
      UInt256.size ≤
        (Solm.EVM.storageLoad evmMove evmMove.executionEnv.codeOwner
          (packBagStorageSlot evmMove.executionEnv)).toNat + (packWadWord I).toNat) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 (packStore I) packTransition.body .reverted := by
  intro evm0
  let bagOld := Solm.EVM.storageLoad evmMove evmMove.executionEnv.codeOwner
    (packBagStorageSlot evmMove.executionEnv)
  let localsMove := (packStoreAmt I).insert "_move" .unit
  have hdebtGuard :
      evalExpr? config { contract := contract, locals := packStore I } evm0
        (.binary .ne (.storage debtRef) (.intLit 0)) = .ok (.bool true) := by
    have hstorage :
        evalExpr? config { contract := contract, locals := packStore I } evm0
          (.storage debtRef) =
          .ok (.int (Int.ofNat (packDebtWord σ I).toNat)) := by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := packStore I })
        (slot := debtRef)
        (er := ({ base := "debt", steps := [] } : EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc ⟨11⟩)
        (value := .int (Int.ofNat (packDebtWord σ I).toNat))
        (hbase := by simp [packStore, debtRef])
        (her := by simp [evalStorageRef, evalStorageRefSteps, debtRef, EvalResult.bind, pure, bind])
        (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [packDebtWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
            State.lookupAccount] using endStorageLocLoad_uint256 evm0 ⟨11⟩)]
    have hne : (Value.int (Int.ofNat (packDebtWord σ I).toNat) == Value.int 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro hbad
      rw [Value.int.injEq] at hbad
      exact hdebt (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
    simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hne,
      Bool.not_false]
  have hargsMul :
      evalExprs? config { contract := contract, locals := packStore I } evm0
        [.var "wad", .intLit RAY] =
        .ok [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)] := by
    change evalExprs? config { contract := contract, locals := packStore I } evm0
        [.var "wad", .intLit RAY] =
        .ok [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat 1000000000000000000000000000)]
    simp [evalExprs?, evalExpr?, packStore, RAY, EvalResult.ofOption, EvalResult.bind, bind,
      pure]
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbindMul :
      bindParams? mulFunction.params
        [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)] = some (packMulLocals I) := by
    simp [mulFunction, packMulLocals, bindParams?]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := packStore I } evm0
        (.internalCall "mul" [.var "wad", .intLit RAY] "amt")
        (.ok { contract := contract, locals := packStoreAmt I } evm0) := by
    have hbody := packMulFunctionBodyReturns evm0 I hmul
    simpa [packStoreAmt, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := packStore I })
        (evm := evm0) (calleeEvm := evm0) (name := "mul") (retVar := "amt")
        (args := [.var "wad", .intLit RAY])
        (argVals := [Value.int (Int.ofNat (packWadWord I).toNat),
          Value.int (Int.ofNat packRayWord.toNat)])
        (callee := mulFunction) (locals := packMulLocals I)
        (calleeSolm := { contract := contract, locals := packMulLocalsZ I (packAmtWord I) })
        (value := some [.int (Int.ofNat (packAmtWord I).toNat)]) hargsMul hlookupMul
        hbindMul hbody)
  have hvat :
      evalExpr? config { contract := contract, locals := packStoreAmt I } evm0 (.storage vatRef) =
        .ok (.address (AccountAddress.ofNat (packVatMaskedWord σ I).toNat)) := by
    simpa [packVatMaskedWord, packVatWord, endSlotWord, evm0, initState, Solm.EVM.storageLoad,
      State.lookupAccount, u256_land_comm] using
      evalExpr_packVatStorage (evm := evm0) (locals := packStoreAmt I)
        (by simp [packStoreAmt, packStore])
  have hguard :
      evalExpr? config { contract := contract, locals := packStoreAmt I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_packVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsMove := evalExprs_packMoveArgs (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hdecode : config.externalABI.decode? "move" out = some ([] : List Value) := by
    simp [config, externalABI, decodeVoid?]
  have hcallStmt :
      ExecStmt config { contract := contract, locals := packStoreAmt I } evm0
        (.externalCall (.storage vatRef) "move" (.intLit 0) [sender, vowAddr, .var "amt"]
          "_move" (perm := true))
        (.ok { contract := contract, locals := localsMove } evmMove) := by
    simpa [localsMove] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsMove hcallMove hdecode
  have hbag :
      evalExpr? config { contract := contract, locals := localsMove } evmMove
        (.storage (bagRef sender)) =
        .ok (.int (Int.ofNat bagOld.toNat)) := by
    simpa [bagOld] using
      evalExpr_packBagStorage (evm := evmMove) (locals := localsMove)
        (by simp [localsMove, packStoreAmt, packStore])
  have hwad :
      evalExpr? config { contract := contract, locals := localsMove } evmMove (.var "wad") =
        .ok (.int (Int.ofNat (packWadWord I).toNat)) := by
    have hget :
        localsMove.get? "wad" = some (.int (Int.ofNat (packWadWord I).toNat)) := by
      unfold localsMove packStoreAmt packStore
      rw [store_get_ne]
      · rw [store_get_ne]
        · simp
        · native_decide
      · native_decide
    exact evalExpr_packVarUInt256 (evm := evmMove) (locals := localsMove)
      (name := "wad") (value := packWadWord I) hget
  have hargsAdd :
      evalExprs? config { contract := contract, locals := localsMove } evmMove
        [.storage (bagRef sender), .var "wad"] =
        .ok [Value.int (Int.ofNat bagOld.toNat),
          Value.int (Int.ofNat (packWadWord I).toNat)] := by
    simp [evalExprs?, hbag, hwad, EvalResult.bind, bind, pure]
  have hlookupAdd : lookupCallable? contract "add" = some addFunction.toCallable := by
    simp [lookupCallable?, lookupFunction?, contract, functions, addFunction, subFunction,
      mulFunction]
  have hbindAdd :
      bindParams? addFunction.params
        [Value.int (Int.ofNat bagOld.toNat), Value.int (Int.ofNat (packWadWord I).toNat)] =
        some (packAddLocals bagOld (packWadWord I)) := by
    simp [addFunction, packAddLocals, bindParams?]
  have haddStmt :
      ExecStmt config { contract := contract, locals := localsMove } evmMove
        (.internalCall "add" [.storage (bagRef sender), .var "wad"] "bagNew") .reverted := by
    exact internalCallFunctionRevert hargsAdd hlookupAdd hbindAdd
      (packAddFunctionBodyReverts evmMove (x := bagOld) (y := packWadWord I) hover)
  have hblock :
      ExecBlock config { contract := contract, locals := packStore I } evm0 packTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hdebtGuard) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallStmt ?_
    exact ExecBlock.consRevert haddStmt
  simpa [ExecTransitionBody, evm0, packTransition, nonpayable, checkedExternalCallStmts,
    localsMove, bagOld] using ExecFuncBody.execBlockRevert hblock

theorem endPackBodyCore : endBodyObligation 30 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 30) rfl hsel
  have hdispatch := endDispatchPackLocal hsel
  have hreach :=
    endReachPackBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := endDecode_pack_ok (I := I) hsz36
    have hroutine :=
      endPackX_decoded (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := endSelWord I)
        hsz36 hsize hreach
    obtain ⟨kRoutine, CRoutine, hroutineRD⟩ := hroutine
    by_cases hdebt : packDebtWord σ_evm I = ⟨0⟩
    · have hdebtSolm : packDebtWord σ_solm I = ⟨0⟩ := by
        have hword : packDebtWord σ_evm I = packDebtWord σ_solm I :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
        rw [← hword]
        exact hdebt
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (packStore I)
            packTransition.body .reverted := by
        simpa using
          endPackSourceBodyDebtZeroReverts (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hdebtSolm
      exact (endPackX_debtZero (g := Sat256.ofUInt256 g) hdebt hroutineRD)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hmulEntry :=
        endPackX_toMul (g := Sat256.ofUInt256 g) hdebt hroutineRD
      by_cases hmulOk : (packWadWord I).toNat * packRayWord.toNat < UInt256.size
      · obtain ⟨kMul, CMul, hmulRD⟩ := hmulEntry
        have hafterMul :=
          endPackX_mulOk (g := Sat256.ofUInt256 g) hmulOk hmulRD
        obtain ⟨kAfterMul, CAfterMul, hafterMulRD⟩ := hafterMul
        by_cases hvatNoCode :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
              (packVatMaskedWord σ_evm I) = ⟨0⟩
        · have hrev :=
            RD.endPackMoveNoCode (g := Sat256.ofUInt256 g) hafterMulRD hvatNoCode
          have hdebtSolm : packDebtWord σ_solm I ≠ ⟨0⟩ := by
            have hword : packDebtWord σ_evm I = packDebtWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
            intro hzero
            exact hdebt (by rw [hword, hzero])
          have hvatWord : packVatMaskedWord σ_evm I = packVatMaskedWord σ_solm I := by
            have hword : packVatWord σ_evm I = packVatWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
            simpa [packVatMaskedWord] using
              congrArg (fun w => UInt256.land solcAddrMask w) hword
          have hvatNoCodeSolm :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                (packVatMaskedWord σ_solm I) = ⟨0⟩ := by
            rw [← hvatWord]
            rw [← uniswapExtCodeSizeWord_accountMapEquiv hAccounts
              (packVatMaskedWord σ_evm I)]
            exact hvatNoCode
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (packStore I)
                packTransition.body .reverted := by
            simpa using
              endPackSourceBodyNoCodeReverts (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hdebtSolm
                hmulOk hvatNoCodeSolm
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · have hdebtSolm : packDebtWord σ_solm I ≠ ⟨0⟩ := by
            have hword : packDebtWord σ_evm I = packDebtWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
            intro hzero
            exact hdebt (by rw [hword, hzero])
          have hvatWord : packVatMaskedWord σ_evm I = packVatMaskedWord σ_solm I := by
            have hword : packVatWord σ_evm I = packVatWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
            simpa [packVatMaskedWord] using
              congrArg (fun w => UInt256.land solcAddrMask w) hword
          have hvowWord : packVowMaskedWord σ_evm I = packVowMaskedWord σ_solm I := by
            have hword : packVowWord σ_evm I = packVowWord σ_solm I :=
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
            simpa [packVowMaskedWord] using
              congrArg (fun w => UInt256.land solcAddrMask w) hword
          have hvatCodeSolm :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                (packVatMaskedWord σ_solm I) ≠ ⟨0⟩ := by
            intro hzero
            apply hvatNoCode
            rw [← hvatWord] at hzero
            rw [← uniswapExtCodeSizeWord_accountMapEquiv hAccounts
              (packVatMaskedWord σ_evm I)] at hzero
            exact hzero
          have hvatCodeNatSolm :
              (UInt256.ofNat
                (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
                  (AccountAddress.ofNat (packVatMaskedWord σ_solm I).toNat)).option 0
                  (fun acc => acc.code.size))).toNat ≠ 0 := by
            intro hnat
            apply hvatCodeSolm
            simp [Reasoning.Theory.uniswapExtCodeSizeWord, initState, State.lookupAccount,
              accountAddress_ofUInt256_eq_ofNat_toNat] at hnat ⊢
            cases hfind : σ_solm.find? (AccountAddress.ofNat (packVatMaskedWord σ_solm I).toNat)
            · native_decide
            · simp [hfind, Option.option, Function.comp] at hnat ⊢
              exact uint256_toNat_eq_zero hnat
          by_cases hdepthMax : I.depth = (1024 : Fin 1025)
          · have hrev :=
              RD.endPackMoveDepthLimitReverts
                (g := Sat256.ofUInt256 g) hafterMulRD hvatNoCode hdepthMax
            have hcallMove :
                typedCallViaEVM config
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (EVM.address (AccountAddress.ofNat (packVatMaskedWord σ_solm I).toNat))
                  "move" 0
                  [.address I.source,
                    .address (AccountAddress.ofUInt256 (packVowMaskedWord σ_solm I)),
                    .int (Int.ofNat (packAmtWord I).toNat)]
                  (false,
                    { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                      substate :=
                        ((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).addAccessedAccount
                          (EVM.address
                            (AccountAddress.ofNat (packVatMaskedWord σ_solm I).toNat))).substate },
                    ByteArray.empty) true := by
              exact callNotMade_depthLimit
                (cfg := config)
                (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                (tgt := EVM.address
                  (AccountAddress.ofNat (packVatMaskedWord σ_solm I).toNat))
                (name := "move")
                (args := [.address I.source,
                  .address (AccountAddress.ofUInt256 (packVowMaskedWord σ_solm I)),
                  .int (Int.ofNat (packAmtWord I).toNat)])
                (calldata :=
                  (packMoveCalldataMem σ_solm I solcFreePtrMem).readWithPadding
                    packMoveOutPtr.toNat packMoveInSize.toNat)
                (callPerm := true)
                (packMoveEncode_eq σ_solm I)
                (by simpa [initState] using hdepthMax)
            have hbody :
                ExecTransitionBody config contract
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (packStore I)
                  packTransition.body .reverted := by
              simpa using
                endPackSourceBodyCallFailure (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hwv hdebtSolm hmulOk hvatCodeNatSolm hcallMove
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have hdepthLt : I.depth.val < 1024 := by
              have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
              have hne : I.depth.val ≠ 1024 := by
                intro hval
                apply hdepthMax
                apply Fin.ext
                exact hval
              omega
            obtain ⟨cA', σ', z, out, A', kCall, CCall, hcallRD, hcallEvm, houtsz⟩ :=
              RD.endPackMovePostCall
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) (sel := endSelWord I)
                hafterMulRD hvatNoCode hdepthLt
            cases z
            · have hrev :=
                RD.endPackMoveCallFailure hcallRD houtsz
                  (by simp only [List.length_cons, List.length_nil]; omega)
              obtain ⟨σ'_solm, A'_solm, hcallSolm, hσ'⟩ :=
                typedCallViaEVM_initState_accountMapEquiv hcallEvm hAccounts
              have hcallMove :
                  typedCallViaEVM config
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (AccountAddress.ofNat (packVatMaskedWord σ_solm I).toNat))
                    "move" 0
                    [.address I.source,
                      .address (AccountAddress.ofUInt256 (packVowMaskedWord σ_solm I)),
                      .int (Int.ofNat (packAmtWord I).toNat)]
                    (false,
                      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' },
                      out) true := by
                simpa [hvatWord, hvowWord, hperm] using hcallSolm
              have hbody :
                  ExecTransitionBody config contract
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (packStore I)
                    packTransition.body .reverted := by
                simpa using
                  endPackSourceBodyCallFailure (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hdebtSolm hmulOk hvatCodeNatSolm hcallMove
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · let evmMoveEvm :=
                { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ', substate := A', createdAccounts := cA' }
              obtain ⟨σ'_solm, A'_solm, hcallSolm, hStateCall⟩ :=
                typedCallViaEVM_initState_EVMStateEquiv hcallEvm (by simp [initState])
                  hAccounts
              let evmMoveSolm :=
                { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                  accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }
              have hcallMove :
                  typedCallViaEVM config
                    (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    (EVM.address (AccountAddress.ofNat (packVatMaskedWord σ_solm I).toNat))
                    "move" 0
                    [.address I.source,
                      .address (AccountAddress.ofUInt256 (packVowMaskedWord σ_solm I)),
                      .int (Int.ofNat (packAmtWord I).toNat)]
                    (true, evmMoveSolm, out) true := by
                simpa [evmMoveSolm, hvatWord, hvowWord, hperm] using hcallSolm
              have hbagEq :
                  packBagWord σ' I =
                    Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                      (packBagStorageSlot evmMoveSolm.executionEnv) := by
                have hload := hStateCall.storageLoad_codeOwner (packBagStorageSlot I)
                simpa [evmMoveEvm, evmMoveSolm, packBagWord, endSlotWord, solcSlotWord, initState,
                  Solm.EVM.storageLoad, State.lookupAccount] using hload
              by_cases hfit :
                  (packBagWord σ' I).toNat + (packWadWord I).toNat < UInt256.size
              · have hret :=
                  RD.endPackMoveCallSuccessReturn hcallRD hperm hfit
                have hfitSolm :
                    (Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                      (packBagStorageSlot evmMoveSolm.executionEnv)).toNat +
                        (packWadWord I).toNat < UInt256.size := by
                  simpa [← hbagEq] using hfit
                have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (packStore I)
                      packTransition.body
                      (.returned
                        { contract := contract,
                          locals :=
                            (((packStoreAmt I).insert "_move" .unit).insert "bagNew"
                              (.int (Int.ofNat
                                ((Solm.EVM.storageLoad evmMoveSolm
                                  evmMoveSolm.executionEnv.codeOwner
                                  (packBagStorageSlot evmMoveSolm.executionEnv)) +
                                  packWadWord I).toNat))) }
                        (Solm.EVM.storageStore evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                          (packBagStorageSlot evmMoveSolm.executionEnv)
                          ((Solm.EVM.storageLoad evmMoveSolm
                            evmMoveSolm.executionEnv.codeOwner
                            (packBagStorageSlot evmMoveSolm.executionEnv)) + packWadWord I))
                        none) := by
                  simpa [evmMoveSolm] using
                    endPackSourceBodyCallSuccess (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (evmMove := evmMoveSolm) (out := out)
                      hwv hdebtSolm hmulOk hvatCodeNatSolm hcallMove hfitSolm
                let evmFinalEvm :=
                  Solm.EVM.storageStore evmMoveEvm evmMoveEvm.executionEnv.codeOwner
                    (packBagStorageSlot evmMoveEvm.executionEnv) (packBagWord σ' I + packWadWord I)
                let evmFinalSolm :=
                  Solm.EVM.storageStore evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                    (packBagStorageSlot evmMoveSolm.executionEnv)
                    ((Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                      (packBagStorageSlot evmMoveSolm.executionEnv)) + packWadWord I)
                have hStateFinal : EVMStateEquiv evmFinalEvm evmFinalSolm := by
                  have hval :
                      packBagWord σ' I + packWadWord I =
                        (Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                          (packBagStorageSlot evmMoveSolm.executionEnv)) + packWadWord I := by
                    rw [hbagEq]
                  simpa [evmFinalEvm, evmFinalSolm, evmMoveEvm, evmMoveSolm, initState] using
                    hStateCall.storageStore_codeOwner (packBagStorageSlot I) hval
                have hcreated :
                    (cA',
                      sstoreAccountMap I.codeOwner σ' (packBagStorageSlot I)
                        (packBagWord σ' I + packWadWord I)).1 =
                      evmFinalEvm.createdAccounts := by
                  simp [evmFinalEvm, evmMoveEvm, storageStore_createdAccounts]
                have haccountsRet :
                    accountMapEquiv
                      (cA',
                        sstoreAccountMap I.codeOwner σ' (packBagStorageSlot I)
                          (packBagWord σ' I + packWadWord I)).2
                      evmFinalEvm.accountMap := by
                  simpa [evmFinalEvm, evmMoveEvm, initState, storageStore_accountMap] using
                    accountMapEquiv_refl
                      (sstoreAccountMap I.codeOwner σ' (packBagStorageSlot I)
                        (packBagWord σ' I + packWadWord I))
                have hretEquiv : returnEquiv ByteArray.empty none packTransition.returnType := by
                  change returnEquiv ByteArray.empty none []
                  exact returnEquiv.fallthrough rfl rfl (by native_decide)
                exact hret.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode
                  (by simpa [evmFinalSolm] using hbody) hcreated haccountsRet hStateFinal
                  hretEquiv
              · have hoverEvm :
                    UInt256.size ≤ (packBagWord σ' I).toNat + (packWadWord I).toNat :=
                  Nat.le_of_not_gt hfit
                have hrev :=
                  RD.endPackMoveCallSuccessAddOverflow hcallRD hoverEvm
                have hoverSolm :
                    UInt256.size ≤
                      (Solm.EVM.storageLoad evmMoveSolm evmMoveSolm.executionEnv.codeOwner
                        (packBagStorageSlot evmMoveSolm.executionEnv)).toNat +
                          (packWadWord I).toNat := by
                  simpa [← hbagEq] using hoverEvm
                have hbody :
                    ExecTransitionBody config contract
                      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (packStore I)
                      packTransition.body .reverted := by
                  simpa [evmMoveSolm] using
                    endPackSourceBodyCallSuccessAddOverflow (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      (evmMove := evmMoveSolm) (out := out)
                      hwv hdebtSolm hmulOk hvatCodeNatSolm hcallMove hoverSolm
                exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · obtain ⟨kMul, CMul, hmulRD⟩ := hmulEntry
        have hover : UInt256.size ≤ (packWadWord I).toNat * packRayWord.toNat :=
          Nat.le_of_not_gt hmulOk
        have hdivne : UInt256.div (packAmtWord I) packRayWord ≠ packWadWord I := by
          simpa [packAmtWord] using
            udiv_mul_wrap_ne_of_overflow (a := packWadWord I) (b := packRayWord) hover
        have hrev :=
          endPackX_mulOverflow (g := Sat256.ofUInt256 g) hdivne hmulRD
        have hdebtSolm : packDebtWord σ_solm I ≠ ⟨0⟩ := by
          have hword : packDebtWord σ_evm I = packDebtWord σ_solm I :=
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
          intro hzero
          exact hdebt (by rw [hword, hzero])
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (packStore I)
              packTransition.body .reverted := by
          simpa using
            endPackSourceBodyMulOverflowReverts (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hdebtSolm
              hover
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hdecode := endDecode_pack_none_short (I := I) (by omega)
    have hrev :=
      endPackX_shortarg (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (sel := endSelWord I)
        hsz4 hsize (by omega) hreach
    exact hrev.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.Dss.End
