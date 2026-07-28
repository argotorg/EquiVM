import Benchmarks.Dss.Cat.FileIlkFlipCalls2
import Benchmarks.Dss.Cat.BiteSource
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace Benchmarks.Dss.Cat

/-! ## `file(bytes32,bytes32,address)` — Solm source body helpers + connect -/

theorem fileIlkFlipIlkKey_word (I : ExecutionEnv) (hsz100 : 100 ≤ I.calldata.size) :
    keyValueToWord (fileIlkFlipIlkKey I) = fileIlkFlipIlkWord I := by
  have hlen32 : (fileIlkFlipIlk I).length = 32 := fileIlkFlipIlk_length (by omega)
  have hword : ABI.bytesToWord (fileIlkFlipIlk I) = fileIlkFlipIlkWord I := by
    simpa [fileIlkFlipIlk, fileIlkFlipIlkWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hbytes : fileIlkFlipIlk I = EVM.Word.toBytesBE (fileIlkFlipIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkFlipIlk I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [fileIlkFlipIlkKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (fileIlkFlipIlkWord I)

theorem fifFlipRead {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size)
    {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (fileIlkFlipIlk I))) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "ilk") "flip")) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (catSlotWord (ilksBase (fileIlkFlipIlkKey I))
          evm.accountMap evm.executionEnv) solcAddrMask).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "flip")
    (er := { base := "ilks", steps := [.mindex (fileIlkFlipIlkKey I), .field "flip"] })
    (t := .address) (loc := addrLoc (ilksBase (fileIlkFlipIlkKey I)))
    (value := .address (AccountAddress.ofNat
      (UInt256.land (catSlotWord (ilksBase (fileIlkFlipIlkKey I))
        evm.accountMap evm.executionEnv) solcAddrMask).toNat))
    hbase
    (by
      have hkeyLen : (fileIlkFlipIlk I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using fileIlkFlipIlk_length (I := I) (by omega)
      have hvar : evalExpr? config { contract := contract, locals := locals } evm (.var "ilk") =
          .ok (.fixedBytes bytes32Width (fileIlkFlipIlk I)) := by
        rw [evalExpr?]
        change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") = _
        rw [hilk]; rfl
      simp [fileIlkFlipIlkKey, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ilksF,
        hvar, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen])
    (by
      simp [fileIlkFlipIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, addrSt, uint256St])
    (by rfl)
    (by simpa [catSlotWord] using catStorageLocLoad_address_offset0 evm (ilksBase (fileIlkFlipIlkKey I)))

theorem fifWhatFlipTrue {I : ExecutionEnv} {evm : EVM.State} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileIlkFlipWhat I)))
    (hwhat : fileIlkFlipWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar : evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
      .ok (.fixedBytes bytes32Width (fileIlkFlipWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") = _
    rw [hget]; rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem fifWhatFlipFalse {I : ExecutionEnv} {evm : EVM.State} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileIlkFlipWhat I)))
    (hwhat : fileIlkFlipWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar : evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
      .ok (.fixedBytes bytes32Width (fileIlkFlipWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") = _
    rw [hget]; rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem fifNopeDecode (out : ByteArray) : config.externalABI.decode? "nope" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem fifHopeDecode (out : ByteArray) : config.externalABI.decode? "hope" out = some [] := by
  simp [config, externalABI, decodeVoid?]

/-! ### `Solm.EVM.storageStore` field-preservation + zero-value substate swap (local copies) -/

theorem storageStore_σ₀ (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem storageStore_genesisBlockHeader (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem storageStore_blocks (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem storageStore_substate (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).substate = evm.substate := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

theorem typedCallViaEVM_zero_setSubstate {cfg : Config} {evm evm' : EVM.State}
    {tgt : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} {perm : Bool}
    (hcall : typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) perm)
    (hdepth : evm.executionEnv.depth ≠ 1024) (A0 : Substate) :
    ∃ A',
      typedCallViaEVM cfg { evm with substate := A0 } tgt name 0 args
        (z,
          { { evm with substate := A0 } with
            accountMap := evm'.accountMap
            substate := A'
            createdAccounts := evm'.createdAccounts },
          out) perm := by
  obtain ⟨calldata, henc, hraw⟩ := hcall
  cases hraw with
  | callMade hvalue hTheta hevm' hvalueLe _hdepth =>
      rename_i valueWord cA' σ' g' A'
      subst evm'
      rcases hTheta with ⟨callGas, A_in, hTheta⟩
      refine ⟨A', ⟨calldata, henc, ?_⟩⟩
      refine callViaEVM.callMade (valueWord := valueWord) (cA' := cA') (σ' := σ')
        (g' := g') (A' := A') (perm := perm) hvalue ⟨callGas, A_in, ?_⟩ ?_ ?_ ?_
      · simpa using hTheta
      · rfl
      · simpa using hvalueLe
      · simpa using hdepth
  | callNotMade _hsubstate _hevm' hfail =>
      exfalso
      exact hfail ⟨(by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _), hdepth⟩

/-! ### `EVM.address` on a canonical address is the identity (call-target bridge) -/

theorem evm_address_ofNat_canonical (n : Nat) (_hc : n < EVM.addressModulus) :
    EVM.address (AccountAddress.ofNat n) = AccountAddress.ofNat n := by
  apply Fin.ext
  simp only [EVM.address, EVM.uintN, AccountAddress.ofNat, Fin.ofNat]
  show n % EVM.addressModulus % EVM.addressModulus = n % EVM.addressModulus
  rw [Nat.mod_mod]

theorem evm_address_ofUInt256_canonical (w : UInt256) (hc : w.toNat < EVM.addressModulus) :
    EVM.address (AccountAddress.ofUInt256 w) = AccountAddress.ofUInt256 w := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  exact evm_address_ofNat_canonical _ hc

/-! ### Address store `ilks[ilk].flip := flip` (RMW offset-0, slot `keccak(ilk,1)`) -/

theorem assign_fileIlkFlipStorage (evm : EVM.State) {I : ExecutionEnv} {locals : Store}
    (hsz100 : 100 ≤ I.calldata.size) (data : UInt256)
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (fileIlkFlipIlk I))) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (ilksBase (fileIlkFlipIlkKey I))
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (ilksBase (fileIlkFlipIlkKey I))) (UInt256.land solcAddrMask data))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (ilksF (.var "ilk") "flip") (.address (AccountAddress.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address (AccountAddress.ofNat data.toNat) : Value) =
        .address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat) := by
    simpa using (solcAddressValue_masked data)
  rw [hvalue]
  have hkeyLen : (fileIlkFlipIlk I).length = ↑bytes32Width + 1 := by
    simpa [bytes32Width] using fileIlkFlipIlk_length (I := I) (by omega)
  have hvar : evalExpr? config { contract := contract, locals := locals } evm (.var "ilk") =
      .ok (.fixedBytes bytes32Width (fileIlkFlipIlk I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") = _
    rw [hilk]; rfl
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
        (ilksF (.var "ilk") "flip") =
        .ok { base := "ilks", steps := [.mindex (fileIlkFlipIlkKey I), .field "flip"] } := by
    simp [fileIlkFlipIlkKey, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ilksF,
      hvar, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen]
  have hstore :
      storageLocStore evm (addrLoc (ilksBase (fileIlkFlipIlkKey I)))
          (.address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat)) =
        some evm' := by
    simpa [addrLoc, evm'] using
      storageLocStore_address_offset0 evm (ilksBase (fileIlkFlipIlkKey I))
        (UInt256.land solcAddrMask data) (by
          rw [u256_land_comm solcAddrMask data]
          exact solcAddrMask_result_canonical data)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc (ilksBase (fileIlkFlipIlkKey I)))
    (hbase := hbase)
    (her := her)
    (hty := by
      simp [fileIlkFlipIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, addrSt, uint256St])
    (hloc := by rfl)
    (hscalar := by trivial)
    (hstore := hstore)

/-! ### vat address / code-guard bridges (Solm side) -/

theorem fifBiteVatAddr_eq {cA gh bl σ σ₀ A I} {g : Sat256} :
    biteVatAddr (initState cA gh bl σ σ₀ g A I) = AccountAddress.ofUInt256 (fifVatM σ I) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]; rfl

theorem fifVatGuardFalse {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "vat" = none)
    (hcode : (UInt256.ofNat ((evm.lookupAccount (biteVatAddr evm)).option 0
      (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, biteVatRead hbase, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem fifExtCodeSizeWord_eq (σ : AccountMap) (target : UInt256) :
    extCodeSizeWord σ target =
      UInt256.ofNat ((σ.find? (AccountAddress.ofUInt256 target)).option 0
        (fun acc => acc.code.size)) := by
  unfold extCodeSizeWord
  cases σ.find? (AccountAddress.ofUInt256 target) <;> rfl

theorem fifVatCodeZero {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : extCodeSizeWord σ (fifVatM σ I) = ⟨0⟩) :
    (UInt256.ofNat (((initState cA gh bl σ σ₀ g A I).lookupAccount
      (biteVatAddr (initState cA gh bl σ σ₀ g A I))).option 0 (fun acc => acc.code.size))).toNat = 0 := by
  rw [show (initState cA gh bl σ σ₀ g A I).lookupAccount
      (biteVatAddr (initState cA gh bl σ σ₀ g A I)) =
      σ.find? (AccountAddress.ofUInt256 (fifVatM σ I)) from by
    rw [fifBiteVatAddr_eq]; simp [initState, State.lookupAccount]]
  rw [← fifExtCodeSizeWord_eq, hzero]; rfl

theorem fifVatCodePos {cA gh bl σ σ₀ A I} {g : Sat256}
    (hne : extCodeSizeWord σ (fifVatM σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat (((initState cA gh bl σ σ₀ g A I).lookupAccount
      (biteVatAddr (initState cA gh bl σ σ₀ g A I))).option 0 (fun acc => acc.code.size))).toNat := by
  rw [show (initState cA gh bl σ σ₀ g A I).lookupAccount
      (biteVatAddr (initState cA gh bl σ σ₀ g A I)) =
      σ.find? (AccountAddress.ofUInt256 (fifVatM σ I)) from by
    rw [fifBiteVatAddr_eq]; simp [initState, State.lookupAccount]]
  rw [← fifExtCodeSizeWord_eq]
  exact Nat.pos_of_ne_zero (fun h => hne (by
    apply u256_inj; simpa using h))

theorem fifVatCodeZeroGen {evm : EVM.State} {target : UInt256}
    (haddr : biteVatAddr evm = AccountAddress.ofUInt256 target)
    (hzero : extCodeSizeWord evm.accountMap target = ⟨0⟩) :
    (UInt256.ofNat ((evm.lookupAccount (biteVatAddr evm)).option 0
      (fun acc => acc.code.size))).toNat = 0 := by
  rw [haddr, show evm.lookupAccount (AccountAddress.ofUInt256 target) =
      evm.accountMap.find? (AccountAddress.ofUInt256 target) from by simp [State.lookupAccount],
    ← fifExtCodeSizeWord_eq, hzero]; rfl

theorem fifVatCodePosGen {evm : EVM.State} {target : UInt256}
    (haddr : biteVatAddr evm = AccountAddress.ofUInt256 target)
    (hne : extCodeSizeWord evm.accountMap target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat ((evm.lookupAccount (biteVatAddr evm)).option 0
      (fun acc => acc.code.size))).toNat := by
  rw [haddr, show evm.lookupAccount (AccountAddress.ofUInt256 target) =
      evm.accountMap.find? (AccountAddress.ofUInt256 target) from by simp [State.lookupAccount],
    ← fifExtCodeSizeWord_eq]
  exact Nat.pos_of_ne_zero (fun h => hne (by apply u256_inj; simpa using h))

/-! ### `twoWordHashMem` size preservation over a 164-byte base -/

theorem fifWordAt0Mem_size_164 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 164) :
    (wordAt0Mem word mem).size = 164 := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem fifWordAt32Mem_size_164 {mem : ByteArray} (word : UInt256) (hmem : mem.size = 164) :
    (wordAt32Mem word mem).size = 164 := by
  unfold wordAt32Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem fifTwoWordHashMem_size_164 {mem : ByteArray} (key slot : UInt256) (hmem : mem.size = 164) :
    (twoWordHashMem key slot mem).size = 164 := by
  unfold twoWordHashMem
  exact fifWordAt32Mem_size_164 slot (fifWordAt0Mem_size_164 key hmem)

/-! ### hope guard/CALL at ⟨3679⟩ over a NON-empty returndata buffer (nope's return bytes)

The library `catFileIlkFlipHope{PostCall,NoCode}` fix the returndata to `ByteArray.empty`; after the
`nope` CALL the returndata buffer holds the (opaque) `nope` output, so we re-prove them over an
arbitrary `rdata` — the underlying guard/CALL steps never inspect it. -/

theorem RD.catFileIlkFlipHopeNoCodeGen {cA gh bl σ σ₀ A I} {g : Sat256} {flip ret sel : UInt256}
    {mem rdata : ByteArray} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3679⟩
      (fifVat2M σ' I :: fifVat2M σ' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ ::
        ⟨2746363844⟩ :: fifVat2M σ' I :: flip :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I ::
        ret :: sel :: [])
      (fifHopeCdMem mem (UInt256.land flip solcAddrMask)) (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ' (fifVat2M σ' I) = ⟨0⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3679⟩) (okPc := ⟨3691⟩) rd hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.catFileIlkFlipHopePostCallGen {cA gh bl σ σ₀ A I} {g : Sat256} {flip ret sel : UInt256}
    {mem rdata : ByteArray} {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap} {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3679⟩
      (fifVat2M σ' I :: fifVat2M σ' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ ::
        ⟨2746363844⟩ :: fifVat2M σ' I :: flip :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I ::
        ret :: sel :: [])
      (fifHopeCdMem mem (UInt256.land flip solcAddrMask)) (UInt256.ofNat 6) rdata (cA', σ') k C)
    (hmem : mem.size = 164)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ' (fifVat2M σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap) (z : Bool)
      (out : ByteArray) (A'' : Substate) (k' C' : ℕ),
      RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3695⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨2746363844⟩ :: fifVat2M σ' I :: flip ::
          fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
        (fifHopeCdMem mem (UInt256.land flip solcAddrMask)) (UInt256.ofNat 6) out (cA'', σ'') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ g A I with accountMap := σ', createdAccounts := cA' }
        (AccountAddress.ofUInt256 (fifVat2M σ' I)) "hope" 0
        [.address (AccountAddress.ofNat (UInt256.land flip solcAddrMask).toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
              accountMap := σ'', substate := A'', createdAccounts := cA'' }, out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, k1, C1, rd3694⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3679⟩) (okPc := ⟨3691⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨cA'', σ'', z, out, A_in, callGas, k', C', hΘpack, rd3695raw, houtsz⟩ :=
    RD.call rd3694 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A'', hΘ⟩ := hΘpack
  refine ⟨cA'', σ'', z, out, A'', k', C', ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (⟨128⟩ : UInt256).toNat (⟨36⟩ : UInt256).toNat) (⟨128⟩ : UInt256).toNat
          (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 6 := by native_decide
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := rfl
    have rd3695 : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3695⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨164⟩ :: ⟨2746363844⟩ :: fifVat2M σ' I :: flip ::
          fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I :: ret :: sel :: [])
        (out.write 0 (fifHopeCdMem mem (UInt256.land flip solcAddrMask)) (⟨128⟩ : UInt256).toNat
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA'', σ'') k' C' :=
      haw ▸ rd3695raw
    rw [hmin, byteArray_write_len_zero] at rd3695
    exact rd3695
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas) (callPerm := true)
      (targetWord := fifVat2M σ' I) (mem := fifHopeCdMem mem (UInt256.land flip solcAddrMask))
      (inOff := ⟨128⟩) (inSize := ⟨36⟩)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      rfl
      (by
        have h := fifHopeEncode_eq hmem (UInt256.land flip solcAddrMask) (fifHopeArg_canonical flip)
        simpa [show (⟨128⟩ : UInt256).toNat = 128 from rfl,
          show (⟨36⟩ : UInt256).toNat = 36 from rfl] using h)
      ?_
    simpa [initState, hperm] using hΘ

/-! ### nope call at the depth limit (`I.depth = 1024`) → CALL returns 0 → revert -/

theorem RD.catFileIlkFlipNopeDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256} {flip ret sel : UInt256}
    {k C : ℕ}
    (rd : RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3546⟩
      (fifVatM σ I :: fifVatM σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨164⟩ ::
        ⟨3696042234⟩ :: fifVatM σ I :: flip :: fileIlkFlipWhatWord I :: fileIlkFlipIlkWord I ::
        ret :: sel :: [])
      (fifNopeCdMem I (fifNopeArg σ I)) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ (fifVatM σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨gasWord, k1, C1, rd3561⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3546⟩) (okPc := ⟨3558⟩) rd hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  obtain ⟨k', C', rd3562⟩ := RD.callDepthLimit rd3561 (by native_decide) hdepth (by evm_ov)
  exact RD.catFileIlkFlipNopeCallFailure (by simpa using rd3562) (by native_decide)

/-! ### Solm body — auth-fail revert -/

theorem fileIlkFlipAuthFailSource {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (fileIlkFlipLocals I) fileIlkFlipTransition.body .reverted := by
  have hguard := catAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := fileIlkFlipLocals I) (by simp [fileIlkFlipLocals]) hauth
  have hblock := nonpayableSecondRequireReverts
    (cfg := config) (solm := { contract := contract, locals := fileIlkFlipLocals I })
    (evm := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
    (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
    (rest := [ .ite (.binary .eq (.var "what") flipParamLit)
      (checkedExternalCallStmts (.storage vatRef) "nope" (.intLit 0)
          [.storage (ilksF (.var "ilk") "flip")] "_nopeRet" ++
        [ .assign .storage (ilksF (.var "ilk") "flip") (.var "flip") ] ++
        checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
          [.var "flip"] "_hopeRet")
      [ .require (.boolLit false) ] ])
    (by simp [initState]; exact hwv) hguard
  simpa [ExecTransitionBody, fileIlkFlipTransition, nonpayable, auth] using
    ExecFuncBody.execBlockRevert hblock

/-! ### Solm body — `what != "flip"` revert -/

theorem fileIlkFlipWhatSkipSource {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkFlipWhat I ≠ fileIlkFlipBytes) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (fileIlkFlipLocals I) fileIlkFlipTransition.body .reverted := by
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := fileIlkFlipLocals I) (by simp [fileIlkFlipLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (.binary .eq (.var "what") flipParamLit) = .ok (.bool false) := by
    simpa [flipParamLit, fileIlkFlipBytes] using
      (fifWhatFlipFalse (I := I) (evm := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (locals := fileIlkFlipLocals I) (bs := fileIlkFlipBytes)
        (fileIlkFlipLocals_get_what I) hwhat)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hblock :
      ExecBlock config { contract := contract, locals := fileIlkFlipLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) fileIlkFlipTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond
      (ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)))
  simpa [ExecTransitionBody, fileIlkFlipTransition, nonpayable, auth,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

/-! ### Solm body — success path (`what == "flip"`, both void calls succeed) -/

theorem fileIlkFlipSourceSuccess {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmNope evmStore evmHope : EVM.State} {outNope outHope : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkFlipWhat I = fileIlkFlipBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (AccountAddress.ofNat (UInt256.land
          (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ I) solcAddrMask).toNat)]
        (true, evmNope, outNope) true)
    (hdecNope : config.externalABI.decode? "nope" outNope = some [])
    (hStore : evmStore = Solm.EVM.storageStore evmNope evmNope.executionEnv.codeOwner
      (ilksBase (fileIlkFlipIlkKey I))
      (setAddressOffset0Word (Solm.EVM.storageLoad evmNope evmNope.executionEnv.codeOwner
        (ilksBase (fileIlkFlipIlkKey I))) (fileIlkFlipFlipKey I)))
    (hvatCodeHope :
      0 < (UInt256.ofNat ((evmStore.lookupAccount (biteVatAddr evmStore)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallHope :
      typedCallViaEVM config evmStore (EVM.address (biteVatAddr evmStore)) "hope" 0
        [.address (fileIlkFlipFlip I)] (true, evmHope, outHope) true)
    (hdecHope : config.externalABI.decode? "hope" outHope = some []) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (fileIlkFlipLocals I) fileIlkFlipTransition.body
      (.returned
        { contract := contract
          locals := ((fileIlkFlipLocals I).insert "_nopeRet" (collapseReturns [])).insert
            "_hopeRet" (collapseReturns []) }
        evmHope none) := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hAM : evm0.accountMap = σ := by rw [hevm0]; rfl
  have hEE : evm0.executionEnv = I := by rw [hevm0]; rfl
  set L1 := (fileIlkFlipLocals I).insert "_nopeRet" (collapseReturns ([] : List Value)) with hL1
  set L2 := L1.insert "_hopeRet" (collapseReturns ([] : List Value)) with hL2
  -- callvalue / auth guards
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := fileIlkFlipLocals I) (by simp [fileIlkFlipLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.binary .eq (.var "what") flipParamLit) = .ok (.bool true) := by
    simpa [flipParamLit, fileIlkFlipBytes] using
      (fifWhatFlipTrue (I := I) (evm := evm0) (locals := fileIlkFlipLocals I) (bs := fileIlkFlipBytes)
        (fileIlkFlipLocals_get_what I) hwhat)
  -- nope call
  have hnopeGuard :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    biteVatGuard_true (fileIlkFlipLocals_get_vat I) hvatCodeNope
  have hnopeArgs :
      evalExprs? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        [.storage (ilksF (.var "ilk") "flip")] =
        .ok [.address (AccountAddress.ofNat
          (UInt256.land (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ I) solcAddrMask).toNat)] := by
    simp only [evalExprs?, fifFlipRead (evm := evm0) hsz100 (fileIlkFlipLocals_get_ilks I)
      (fileIlkFlipLocals_get_ilk I), hAM, hEE, EvalResult.bind, bind, pure]
  have hnopeCallStmt :
      ExecStmt config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.externalCall (.storage vatRef) "nope" (.intLit 0)
          [.storage (ilksF (.var "ilk") "flip")] "_nopeRet")
        (.ok { contract := contract, locals := L1 } evmNope) := by
    simpa [hL1, collapseReturns] using
      ExecStmt.externalCallSuccess (biteVatRead (fileIlkFlipLocals_get_vat I))
        (by simp [evalExpr?, pure]) hnopeArgs hcallNope hdecNope
  -- store `ilks[ilk].flip := flip`
  have hflipL1 : L1.get? "flip" = some (.address (fileIlkFlipFlip I)) := by
    rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_flip I
  have hflipVar :
      evalExpr? config { contract := contract, locals := L1 } evmNope (.var "flip") =
        .ok (.address (fileIlkFlipFlip I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (L1.get? "flip") = _
    rw [hflipL1]; rfl
  have hassign :
      assignStorageRef? config { contract := contract, locals := L1 } evmNope
        .storage (ilksF (.var "ilk") "flip") (.address (fileIlkFlipFlip I)) =
          .ok ({ contract := contract, locals := L1 }, evmStore) := by
    rw [hStore]
    simpa [fileIlkFlipFlip, fileIlkFlipFlipKey] using
      assign_fileIlkFlipStorage evmNope (I := I) (locals := L1) hsz100 (fileIlkFlipFlipRawWord I)
        (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_ilks I)
        (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_ilk I)
  -- hope call
  have hhopeGuard :
      evalExpr? config { contract := contract, locals := L1 } evmStore
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    biteVatGuard_true (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_vat I)
      hvatCodeHope
  have hhopeArgs :
      evalExprs? config { contract := contract, locals := L1 } evmStore [.var "flip"] =
        .ok [.address (fileIlkFlipFlip I)] := by
    have hflipVar' :
        evalExpr? config { contract := contract, locals := L1 } evmStore (.var "flip") =
          .ok (.address (fileIlkFlipFlip I)) := by
      rw [evalExpr?]
      change EvalResult.ofOption EvalError.unboundVariable (L1.get? "flip") = _
      rw [hflipL1]; rfl
    simp only [evalExprs?, hflipVar', EvalResult.bind, bind, pure]
  have hhopeCallStmt :
      ExecStmt config { contract := contract, locals := L1 } evmStore
        (.externalCall (.storage vatRef) "hope" (.intLit 0) [.var "flip"] "_hopeRet")
        (.ok { contract := contract, locals := L2 } evmHope) := by
    simpa [hL2, collapseReturns] using
      ExecStmt.externalCallSuccess
        (biteVatRead (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_vat I))
        (by simp [evalExpr?, pure]) hhopeArgs hcallHope hdecHope
  -- assemble the then-block and the whole body
  have hthen :
      ExecBlock config { contract := contract, locals := fileIlkFlipLocals I } evm0
        [ .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "nope" (.intLit 0)
            [.storage (ilksF (.var "ilk") "flip")] "_nopeRet",
          .assign .storage (ilksF (.var "ilk") "flip") (.var "flip"),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "hope" (.intLit 0) [.var "flip"] "_hopeRet" ]
        (.ok { contract := contract, locals := L2 } evmHope) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue hnopeGuard) ?_
    refine ExecBlock.consNormal hnopeCallStmt ?_
    refine ExecBlock.consNormal (ExecStmt.assign hflipVar hassign) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hhopeGuard) ?_
    exact ExecBlock.consNormal hhopeCallStmt ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := fileIlkFlipLocals I } evm0
        fileIlkFlipTransition.body
        (.ok { contract := contract, locals := L2 } evmHope) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [hevm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, hevm0, fileIlkFlipTransition, nonpayable, auth,
    checkedExternalCallStmts] using ExecFuncBody.execBlockOK hblock

/-! ### Solm body — nope-call reverts (`vat` has no code / nope call fails) -/

theorem fileIlkFlipNopeNoCodeSource {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkFlipWhat I = fileIlkFlipBytes)
    (hvatCodeZero :
      (UInt256.ofNat (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (fileIlkFlipLocals I) fileIlkFlipTransition.body .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := fileIlkFlipLocals I) (by simp [fileIlkFlipLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.binary .eq (.var "what") flipParamLit) = .ok (.bool true) := by
    simpa [flipParamLit, fileIlkFlipBytes] using
      (fifWhatFlipTrue (I := I) (evm := evm0) (locals := fileIlkFlipLocals I) (bs := fileIlkFlipBytes)
        (fileIlkFlipLocals_get_what I) hwhat)
  have hnopeGuardFalse :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    fifVatGuardFalse (fileIlkFlipLocals_get_vat I) hvatCodeZero
  have hblock :
      ExecBlock config { contract := contract, locals := fileIlkFlipLocals I } evm0
        fileIlkFlipTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [hevm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consRevert (ExecStmt.iteTrue hcond ?_)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hnopeGuardFalse)
  simpa [ExecTransitionBody, hevm0, fileIlkFlipTransition, nonpayable, auth,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem fileIlkFlipNopeCallFailSource {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmNope : EVM.State} {outNope : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkFlipWhat I = fileIlkFlipBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (AccountAddress.ofNat (UInt256.land
          (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ I) solcAddrMask).toNat)]
        (false, evmNope, outNope) true) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (fileIlkFlipLocals I) fileIlkFlipTransition.body .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hAM : evm0.accountMap = σ := by rw [hevm0]; rfl
  have hEE : evm0.executionEnv = I := by rw [hevm0]; rfl
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := fileIlkFlipLocals I) (by simp [fileIlkFlipLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.binary .eq (.var "what") flipParamLit) = .ok (.bool true) := by
    simpa [flipParamLit, fileIlkFlipBytes] using
      (fifWhatFlipTrue (I := I) (evm := evm0) (locals := fileIlkFlipLocals I) (bs := fileIlkFlipBytes)
        (fileIlkFlipLocals_get_what I) hwhat)
  have hnopeGuard :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    biteVatGuard_true (fileIlkFlipLocals_get_vat I) hvatCodeNope
  have hnopeArgs :
      evalExprs? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        [.storage (ilksF (.var "ilk") "flip")] =
        .ok [.address (AccountAddress.ofNat
          (UInt256.land (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ I) solcAddrMask).toNat)] := by
    simp only [evalExprs?, fifFlipRead (evm := evm0) hsz100 (fileIlkFlipLocals_get_ilks I)
      (fileIlkFlipLocals_get_ilk I), hAM, hEE, EvalResult.bind, bind, pure]
  have hblock :
      ExecBlock config { contract := contract, locals := fileIlkFlipLocals I } evm0
        fileIlkFlipTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [hevm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consRevert (ExecStmt.iteTrue hcond ?_)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hnopeGuard) ?_
    exact ExecBlock.consRevert
      (ExecStmt.externalCallFailure (biteVatRead (fileIlkFlipLocals_get_vat I))
        (by simp [evalExpr?, pure]) hnopeArgs hcallNope)
  simpa [ExecTransitionBody, hevm0, fileIlkFlipTransition, nonpayable, auth,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

/-! ### Solm body — hope-call reverts (after nope success + store) -/

theorem fileIlkFlipHopeNoCodeSource {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmNope evmStore : EVM.State} {outNope : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkFlipWhat I = fileIlkFlipBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (AccountAddress.ofNat (UInt256.land
          (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ I) solcAddrMask).toNat)]
        (true, evmNope, outNope) true)
    (hdecNope : config.externalABI.decode? "nope" outNope = some [])
    (hStore : evmStore = Solm.EVM.storageStore evmNope evmNope.executionEnv.codeOwner
      (ilksBase (fileIlkFlipIlkKey I))
      (setAddressOffset0Word (Solm.EVM.storageLoad evmNope evmNope.executionEnv.codeOwner
        (ilksBase (fileIlkFlipIlkKey I))) (fileIlkFlipFlipKey I)))
    (hvatCodeHopeZero :
      (UInt256.ofNat ((evmStore.lookupAccount (biteVatAddr evmStore)).option 0
        (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (fileIlkFlipLocals I) fileIlkFlipTransition.body .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hAM : evm0.accountMap = σ := by rw [hevm0]; rfl
  have hEE : evm0.executionEnv = I := by rw [hevm0]; rfl
  set L1 := (fileIlkFlipLocals I).insert "_nopeRet" (collapseReturns ([] : List Value)) with hL1
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := fileIlkFlipLocals I) (by simp [fileIlkFlipLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.binary .eq (.var "what") flipParamLit) = .ok (.bool true) := by
    simpa [flipParamLit, fileIlkFlipBytes] using
      (fifWhatFlipTrue (I := I) (evm := evm0) (locals := fileIlkFlipLocals I) (bs := fileIlkFlipBytes)
        (fileIlkFlipLocals_get_what I) hwhat)
  have hnopeGuard :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    biteVatGuard_true (fileIlkFlipLocals_get_vat I) hvatCodeNope
  have hnopeArgs :
      evalExprs? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        [.storage (ilksF (.var "ilk") "flip")] =
        .ok [.address (AccountAddress.ofNat
          (UInt256.land (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ I) solcAddrMask).toNat)] := by
    simp only [evalExprs?, fifFlipRead (evm := evm0) hsz100 (fileIlkFlipLocals_get_ilks I)
      (fileIlkFlipLocals_get_ilk I), hAM, hEE, EvalResult.bind, bind, pure]
  have hnopeCallStmt :
      ExecStmt config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.externalCall (.storage vatRef) "nope" (.intLit 0)
          [.storage (ilksF (.var "ilk") "flip")] "_nopeRet")
        (.ok { contract := contract, locals := L1 } evmNope) := by
    simpa [hL1, collapseReturns] using
      ExecStmt.externalCallSuccess (biteVatRead (fileIlkFlipLocals_get_vat I))
        (by simp [evalExpr?, pure]) hnopeArgs hcallNope hdecNope
  have hflipL1 : L1.get? "flip" = some (.address (fileIlkFlipFlip I)) := by
    rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_flip I
  have hflipVar :
      evalExpr? config { contract := contract, locals := L1 } evmNope (.var "flip") =
        .ok (.address (fileIlkFlipFlip I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (L1.get? "flip") = _
    rw [hflipL1]; rfl
  have hassign :
      assignStorageRef? config { contract := contract, locals := L1 } evmNope
        .storage (ilksF (.var "ilk") "flip") (.address (fileIlkFlipFlip I)) =
          .ok ({ contract := contract, locals := L1 }, evmStore) := by
    rw [hStore]
    simpa [fileIlkFlipFlip, fileIlkFlipFlipKey] using
      assign_fileIlkFlipStorage evmNope (I := I) (locals := L1) hsz100 (fileIlkFlipFlipRawWord I)
        (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_ilks I)
        (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_ilk I)
  have hhopeGuardFalse :
      evalExpr? config { contract := contract, locals := L1 } evmStore
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) :=
    fifVatGuardFalse (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_vat I)
      hvatCodeHopeZero
  have hblock :
      ExecBlock config { contract := contract, locals := fileIlkFlipLocals I } evm0
        fileIlkFlipTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [hevm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consRevert (ExecStmt.iteTrue hcond ?_)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hnopeGuard) ?_
    refine ExecBlock.consNormal hnopeCallStmt ?_
    refine ExecBlock.consNormal (ExecStmt.assign hflipVar hassign) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hhopeGuardFalse)
  simpa [ExecTransitionBody, hevm0, fileIlkFlipTransition, nonpayable, auth,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem fileIlkFlipHopeCallFailSource {cA gh bl σ σ₀ A I} {g : UInt256}
    {evmNope evmStore evmHope : EVM.State} {outNope outHope : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkFlipWhat I = fileIlkFlipBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
        (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (biteVatAddr (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (AccountAddress.ofNat (UInt256.land
          (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ I) solcAddrMask).toNat)]
        (true, evmNope, outNope) true)
    (hdecNope : config.externalABI.decode? "nope" outNope = some [])
    (hStore : evmStore = Solm.EVM.storageStore evmNope evmNope.executionEnv.codeOwner
      (ilksBase (fileIlkFlipIlkKey I))
      (setAddressOffset0Word (Solm.EVM.storageLoad evmNope evmNope.executionEnv.codeOwner
        (ilksBase (fileIlkFlipIlkKey I))) (fileIlkFlipFlipKey I)))
    (hvatCodeHope :
      0 < (UInt256.ofNat ((evmStore.lookupAccount (biteVatAddr evmStore)).option 0
        (fun acc => acc.code.size))).toNat)
    (hcallHope :
      typedCallViaEVM config evmStore (EVM.address (biteVatAddr evmStore)) "hope" 0
        [.address (fileIlkFlipFlip I)] (false, evmHope, outHope) true) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
      (fileIlkFlipLocals I) fileIlkFlipTransition.body .reverted := by
  set evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with hevm0
  have hAM : evm0.accountMap = σ := by rw [hevm0]; rfl
  have hEE : evm0.executionEnv = I := by rw [hevm0]; rfl
  set L1 := (fileIlkFlipLocals I).insert "_nopeRet" (collapseReturns ([] : List Value)) with hL1
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := fileIlkFlipLocals I) (by simp [fileIlkFlipLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.binary .eq (.var "what") flipParamLit) = .ok (.bool true) := by
    simpa [flipParamLit, fileIlkFlipBytes] using
      (fifWhatFlipTrue (I := I) (evm := evm0) (locals := fileIlkFlipLocals I) (bs := fileIlkFlipBytes)
        (fileIlkFlipLocals_get_what I) hwhat)
  have hnopeGuard :
      evalExpr? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    biteVatGuard_true (fileIlkFlipLocals_get_vat I) hvatCodeNope
  have hnopeArgs :
      evalExprs? config { contract := contract, locals := fileIlkFlipLocals I } evm0
        [.storage (ilksF (.var "ilk") "flip")] =
        .ok [.address (AccountAddress.ofNat
          (UInt256.land (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ I) solcAddrMask).toNat)] := by
    simp only [evalExprs?, fifFlipRead (evm := evm0) hsz100 (fileIlkFlipLocals_get_ilks I)
      (fileIlkFlipLocals_get_ilk I), hAM, hEE, EvalResult.bind, bind, pure]
  have hnopeCallStmt :
      ExecStmt config { contract := contract, locals := fileIlkFlipLocals I } evm0
        (.externalCall (.storage vatRef) "nope" (.intLit 0)
          [.storage (ilksF (.var "ilk") "flip")] "_nopeRet")
        (.ok { contract := contract, locals := L1 } evmNope) := by
    simpa [hL1, collapseReturns] using
      ExecStmt.externalCallSuccess (biteVatRead (fileIlkFlipLocals_get_vat I))
        (by simp [evalExpr?, pure]) hnopeArgs hcallNope hdecNope
  have hflipL1 : L1.get? "flip" = some (.address (fileIlkFlipFlip I)) := by
    rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_flip I
  have hflipVar :
      evalExpr? config { contract := contract, locals := L1 } evmNope (.var "flip") =
        .ok (.address (fileIlkFlipFlip I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (L1.get? "flip") = _
    rw [hflipL1]; rfl
  have hassign :
      assignStorageRef? config { contract := contract, locals := L1 } evmNope
        .storage (ilksF (.var "ilk") "flip") (.address (fileIlkFlipFlip I)) =
          .ok ({ contract := contract, locals := L1 }, evmStore) := by
    rw [hStore]
    simpa [fileIlkFlipFlip, fileIlkFlipFlipKey] using
      assign_fileIlkFlipStorage evmNope (I := I) (locals := L1) hsz100 (fileIlkFlipFlipRawWord I)
        (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_ilks I)
        (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_ilk I)
  have hhopeGuard :
      evalExpr? config { contract := contract, locals := L1 } evmStore
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) :=
    biteVatGuard_true (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_vat I)
      hvatCodeHope
  have hhopeArgs :
      evalExprs? config { contract := contract, locals := L1 } evmStore [.var "flip"] =
        .ok [.address (fileIlkFlipFlip I)] := by
    have hflipVar' :
        evalExpr? config { contract := contract, locals := L1 } evmStore (.var "flip") =
          .ok (.address (fileIlkFlipFlip I)) := by
      rw [evalExpr?]
      change EvalResult.ofOption EvalError.unboundVariable (L1.get? "flip") = _
      rw [hflipL1]; rfl
    simp only [evalExprs?, hflipVar', EvalResult.bind, bind, pure]
  have hblock :
      ExecBlock config { contract := contract, locals := fileIlkFlipLocals I } evm0
        fileIlkFlipTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [hevm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consRevert (ExecStmt.iteTrue hcond ?_)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hnopeGuard) ?_
    refine ExecBlock.consNormal hnopeCallStmt ?_
    refine ExecBlock.consNormal (ExecStmt.assign hflipVar hassign) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hhopeGuard) ?_
    exact ExecBlock.consRevert
      (ExecStmt.externalCallFailure
        (biteVatRead (by rw [hL1, store_get_ne _ _ (by decide)]; exact fileIlkFlipLocals_get_vat I))
        (by simp [evalExpr?, pure]) hhopeArgs hcallHope)
  simpa [ExecTransitionBody, hevm0, fileIlkFlipTransition, nonpayable, auth,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem catFileIlkFlipBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xeb, 0xec, 0xb3, 0x9d]⟩ (by native_decide) hsel
  have hreach := catReachFileIlkFlipBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  by_cases hshort : I.calldata.size < 100
  · -- short calldata → decode fails → both sides revert during decoding
    have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
      apply ult_one
      rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
      change I.calldata.size - 4 < 96
      omega
    have hrev := RD.solcExternalStaticArgsShortReverts
      (code := catBytecode) (sel := catSelWord I) (entry := ⟨733⟩) (ret := ⟨302⟩)
      (decoded := ⟨755⟩) (need := ⟨96⟩) hreach
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) hlt
    exact hrev.reEquivDecodingFailed hcode (catDispatch_fileIlkFlip hsel)
      (catDecode_fileIlkFlip_none_short hsz4 hshort)
  have hsz100 : 100 ≤ I.calldata.size := by omega
  have hdispatch := catDispatch_fileIlkFlip hsel
  have hdecode := catDecode_fileIlkFlip_ok hsz100
  have hcallerWord : catSlotWord (catCallerWardsSlot I) σ_evm I =
      catSlotWord (catCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (catCallerWardsSlot I) ⟨0⟩
  by_cases hauthEvm : catSlotWord (catCallerWardsSlot I) σ_evm I = ⟨1⟩
  · -- authorized
    have hauthSolm : catSlotWord (catCallerWardsSlot I) σ_solm I = ⟨1⟩ := hcallerWord ▸ hauthEvm
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [catCallerWardsSlot, catSlotWord] using hauthEvm
    obtain ⟨_, _, rd3455⟩ := RD.catFileIlkFlipToWhatCheck hreach hsz100 hsize hauthSolc
    by_cases hflip : fileIlkFlipWhat I = fileIlkFlipBytes
    · -- what == "flip": nope / store / hope
      have hmatch : fileIlkFlipWhatWord I = ABI.bytesToWord fileIlkFlipBytes :=
        fileIlkFlipWhatWord_eq_of_bytes_eq (by omega) hflip
      obtain ⟨_, _, rd3471⟩ := RD.catFileIlkFlipWhatFlip rd3455 hmatch (by simp)
      obtain ⟨_, _, rd3546⟩ := RD.catFileIlkFlipNopeEncode rd3471
      have hVat3 : solcSlotWord σ_evm I ⟨3⟩ = solcSlotWord σ_solm I ⟨3⟩ :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
      have hVatM : fifVatM σ_evm I = fifVatM σ_solm I := by unfold fifVatM; rw [hVat3]
      have hcodeEq : extCodeSizeWord σ_evm (fifVatM σ_evm I) =
          extCodeSizeWord σ_solm (fifVatM σ_solm I) :=
        (extCodeSizeWord_accountMapEquiv hAccounts (fifVatM σ_evm I)).trans
          (congrArg (extCodeSizeWord σ_solm) hVatM)
      by_cases hcodeNope : extCodeSizeWord σ_evm (fifVatM σ_evm I) = ⟨0⟩
      · -- vat has no code → both sides revert at the nope guard
        have hcodeSolm : extCodeSizeWord σ_solm (fifVatM σ_solm I) = ⟨0⟩ :=
          hcodeEq.symm.trans hcodeNope
        exact (RD.catFileIlkFlipNopeNoCode rd3546 hcodeNope).reEquivExecutionRevert
          hcode hdispatch hdecode
          (fileIlkFlipNopeNoCodeSource (σ := σ_solm) hwv hauthSolm hflip
            (fifVatCodeZero hcodeSolm))
      · -- vat has code
        have hcodeSolmNe : extCodeSizeWord σ_solm (fifVatM σ_solm I) ≠ ⟨0⟩ :=
          fun h => hcodeNope (hcodeEq.trans h)
        have hIlksAgree :
            solcSlotWord σ_evm I (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I)) =
              solcSlotWord σ_solm I (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I)) :=
          accountMapEquiv_storage_findD hAccounts I.codeOwner
            (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I)) ⟨0⟩
        have hIlksKey :
            ilksBase (fileIlkFlipIlkKey I) = solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I) := by
          show mapSlot (keyValueToWord (fileIlkFlipIlkKey I)) ⟨1⟩ = _
          rw [fileIlkFlipIlkKey_word I hsz100]; rfl
        have hNopeArgCoupling :
            UInt256.land (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ_solm I) solcAddrMask =
              fifNopeArg σ_evm I := by
          show UInt256.land (solcSlotWord σ_solm I (ilksBase (fileIlkFlipIlkKey I))) solcAddrMask = _
          rw [hIlksKey, ← hIlksAgree]
          unfold fifNopeArg
          rw [u256_land_comm]
        have hVatCanon : (fifVatM σ_solm I).toNat < EVM.addressModulus :=
          solcAddrMask_result_canonical (solcSlotWord σ_solm I ⟨3⟩)
        have hVatAddrBridge :
            EVM.address (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
              AccountAddress.ofUInt256 (fifVatM σ_evm I) := by
          rw [fifBiteVatAddr_eq, evm_address_ofUInt256_canonical _ hVatCanon, hVatM]
        by_cases hdepth : I.depth.val < 1024
        · -- depth ok: perform the nope CALL
          obtain ⟨cA', σ', z, out, A', k', C', rd3562, hcallNope_evm, houtsz⟩ :=
            RD.catFileIlkFlipNopePostCall rd3546 hcodeNope hdepth hperm
          cases z
          · -- nope call failed → both sides revert
            obtain ⟨σ'_solm, A'_solm, hcallNope_solm, _hState⟩ :=
              typedCallViaEVM_initState_EVMStateEquiv hcallNope_evm (by simp [initState]) hAccounts
            rw [← hVatAddrBridge, ← hNopeArgCoupling] at hcallNope_solm
            exact (RD.catFileIlkFlipNopeCallFailure rd3562 houtsz).reEquivExecutionRevert
              hcode hdispatch hdecode
              (fileIlkFlipNopeCallFailSource (σ := σ_solm) hwv hsz100 hauthSolm hflip
                (fifVatCodePos hcodeSolmNe) hcallNope_solm)
          · -- nope call succeeded → store `ilks[ilk].flip` then hope
            obtain ⟨_, _, rd3582⟩ := RD.catFileIlkFlipNopeCallSuccessToStore (by simpa using rd3562)
            obtain ⟨_, _, rd3626⟩ :=
              RD.catFileIlkFlipStore rd3582 (fifNopeCdMem_size I (fifNopeArg σ_evm I)) hperm
            set σStore := sstoreAccountMap I.codeOwner σ' (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I))
              (setAddressOffset0Word
                (solcSlotWord σ' I (solcMappingSlot ⟨1⟩ (fileIlkFlipIlkWord I)))
                (fileIlkFlipFlipKey I)) with hσStore
            have hStoreMem164 :
                (twoWordHashMem (fileIlkFlipIlkWord I) ⟨1⟩
                  (fifNopeCdMem I (fifNopeArg σ_evm I))).size = 164 :=
              fifTwoWordHashMem_size_164 _ _ (fifNopeCdMem_size I (fifNopeArg σ_evm I))
            have hStoreRead64 :
                (twoWordHashMem (fileIlkFlipIlkWord I) ⟨1⟩
                  (fifNopeCdMem I (fifNopeArg σ_evm I))).readWithPadding 64 32 =
                  UInt256.toByteArray ⟨128⟩ :=
              twoWordHashMem_read64_preserve (fileIlkFlipIlkWord I) ⟨1⟩
                (by rw [fifNopeCdMem_size]; omega) (fifNopeCdMem_read64 I (fifNopeArg σ_evm I))
            obtain ⟨_, _, rd3679⟩ := RD.catFileIlkFlipHopeEncode rd3626 hStoreMem164 hStoreRead64
            -- transport the nope call to the Solm side, mirror the store
            obtain ⟨σ1_solm, A1_solm, hcallNope_solm, hState1⟩ :=
              typedCallViaEVM_initState_EVMStateEquiv hcallNope_evm (by simp [initState]) hAccounts
            set evmNopeSolm := { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
                accountMap := σ1_solm, substate := A1_solm, createdAccounts := cA' } with hevmNopeSolm
            set evmStoreSolm := Solm.EVM.storageStore evmNopeSolm evmNopeSolm.executionEnv.codeOwner
              (ilksBase (fileIlkFlipIlkKey I))
              (setAddressOffset0Word (Solm.EVM.storageLoad evmNopeSolm
                evmNopeSolm.executionEnv.codeOwner (ilksBase (fileIlkFlipIlkKey I)))
                (fileIlkFlipFlipKey I)) with hevmStoreSolm
            have hStateStore :
                EVMStateEquiv
                  (Solm.EVM.storageStore
                    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ', substate := A', createdAccounts := cA' }
                    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ', substate := A',
                      createdAccounts := cA' }.executionEnv.codeOwner (ilksBase (fileIlkFlipIlkKey I))
                    (setAddressOffset0Word (Solm.EVM.storageLoad
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ', substate := A', createdAccounts := cA' }
                      { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                        accountMap := σ', substate := A',
                        createdAccounts := cA' }.executionEnv.codeOwner
                      (ilksBase (fileIlkFlipIlkKey I))) (fileIlkFlipFlipKey I)))
                  evmStoreSolm :=
              hState1.storageStore_codeOwner (ilksBase (fileIlkFlipIlkKey I))
                (congrArg (setAddressOffset0Word · (fileIlkFlipFlipKey I))
                  (hState1.storageLoad_codeOwner (ilksBase (fileIlkFlipIlkKey I))))
            have hσStoreEq :
                (Solm.EVM.storageStore
                  { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σ', substate := A', createdAccounts := cA' }
                  { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                    accountMap := σ', substate := A',
                    createdAccounts := cA' }.executionEnv.codeOwner (ilksBase (fileIlkFlipIlkKey I))
                  (setAddressOffset0Word (Solm.EVM.storageLoad
                    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ', substate := A', createdAccounts := cA' }
                    { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σ', substate := A',
                      createdAccounts := cA' }.executionEnv.codeOwner
                    (ilksBase (fileIlkFlipIlkKey I))) (fileIlkFlipFlipKey I))).accountMap = σStore := by
              rw [hσStore, hIlksKey]
              simp [storageStore_accountMap, Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage, solcSlotWord, initState]
            have hAccountsStore : accountMapEquiv σStore evmStoreSolm.accountMap := by
              rw [← hσStoreEq]; exact hStateStore.accountMap
            have hEEStore : evmStoreSolm.executionEnv = I := by
              rw [hevmStoreSolm]
              simp [storageStore_executionEnv, hevmNopeSolm, initState]
            have hVat3Store :
                solcSlotWord σStore I ⟨3⟩ = solcSlotWord evmStoreSolm.accountMap I ⟨3⟩ :=
              accountMapEquiv_storage_findD hAccountsStore I.codeOwner ⟨3⟩ ⟨0⟩
            have hHopeCode :
                extCodeSizeWord evmStoreSolm.accountMap (fifVat2M σStore I) =
                  extCodeSizeWord σStore (fifVat2M σStore I) :=
              (extCodeSizeWord_accountMapEquiv hAccountsStore (fifVat2M σStore I)).symm
            have hHopeTarget :
                biteVatAddr evmStoreSolm = AccountAddress.ofUInt256 (fifVat2M σStore I) := by
              have hinner :
                  UInt256.land (catSlotWord ⟨3⟩ evmStoreSolm.accountMap evmStoreSolm.executionEnv)
                    solcAddrMask = fifVat2M σStore I := by
                rw [hEEStore]
                show UInt256.land (solcSlotWord evmStoreSolm.accountMap I ⟨3⟩) solcAddrMask =
                  fifVat2M σStore I
                rw [← hVat3Store]; unfold fifVat2M; rw [u256_land_comm]
              rw [accountAddress_ofUInt256_eq_ofNat_toNat]
              show AccountAddress.ofNat (UInt256.land
                (catSlotWord ⟨3⟩ evmStoreSolm.accountMap evmStoreSolm.executionEnv)
                solcAddrMask).toNat = AccountAddress.ofNat (fifVat2M σStore I).toNat
              rw [hinner]
            rw [← hVatAddrBridge, ← hNopeArgCoupling] at hcallNope_solm
            by_cases hcodeHope : extCodeSizeWord σStore (fifVat2M σStore I) = ⟨0⟩
            · -- vat has no code at the hope call → both sides revert at the hope guard
              exact (RD.catFileIlkFlipHopeNoCodeGen rd3679 hcodeHope).reEquivExecutionRevert
                hcode hdispatch hdecode
                (fileIlkFlipHopeNoCodeSource (σ := σ_solm) hwv hsz100 hauthSolm hflip
                  (fifVatCodePos hcodeSolmNe) hcallNope_solm (fifNopeDecode out) hevmStoreSolm
                  (fifVatCodeZeroGen hHopeTarget (hHopeCode.trans hcodeHope)))
            · obtain ⟨cA'', σ'', z2, out2, A'', k2, C2, rd3695, hcallHope_evm, hout2sz⟩ :=
                RD.catFileIlkFlipHopePostCallGen rd3679 hStoreMem164 hcodeHope hdepth hperm
              have hcodeStoreSolmNe :
                  extCodeSizeWord evmStoreSolm.accountMap (fifVat2M σStore I) ≠ ⟨0⟩ :=
                fun h => hcodeHope (hHopeCode.symm.trans h)
              -- bridge the EVM hope CALL target/arg to the Solm-source forms
              have hcanon2 : (fifVat2M σStore I).toNat < EVM.addressModulus := by
                unfold fifVat2M; rw [u256_land_comm]; exact solcAddrMask_result_canonical _
              have hHopeTargetBridge :
                  EVM.address (biteVatAddr evmStoreSolm) = AccountAddress.ofUInt256 (fifVat2M σStore I) := by
                rw [hHopeTarget]; exact evm_address_ofUInt256_canonical _ hcanon2
              have hHopeArg :
                  (Value.address (fileIlkFlipFlip I)) =
                    .address (AccountAddress.ofNat
                      (UInt256.land (fileIlkFlipFlipKey I) solcAddrMask).toNat) := by
                show (Value.address (AccountAddress.ofNat (fileIlkFlipFlipRawWord I).toNat)) = _
                rw [u256_land_comm (fileIlkFlipFlipKey I) solcAddrMask]
                show (Value.address (AccountAddress.ofNat (fileIlkFlipFlipRawWord I).toNat)) =
                  .address (AccountAddress.ofNat (UInt256.land solcAddrMask
                    (UInt256.land solcAddrMask (fileIlkFlipFlipRawWord I))).toNat)
                rw [solcAddrMask_clean_left (w := UInt256.land solcAddrMask (fileIlkFlipFlipRawWord I))
                  (by rw [u256_land_comm]; exact solcAddrMask_result_canonical _)]
                exact solcAddressValue_masked (fileIlkFlipFlipRawWord I)
              rw [← hHopeTargetBridge, ← hHopeArg] at hcallHope_evm
              -- transport the hope call to the Solm side (value 0 ⇒ substate-agnostic)
              set evmStoreSolmBase := { evmStoreSolm with
                  substate := (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).substate }
                with hevmStoreSolmBase
              have hdepthNeI : I.depth ≠ 1024 := by
                intro h; rw [h] at hdepth; exact absurd hdepth (by decide)
              have hcallCreated :
                  evmStoreSolmBase.createdAccounts =
                    ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σStore, createdAccounts := cA' } : EVM.State).createdAccounts := by
                simp [hevmStoreSolmBase, hevmStoreSolm, hevmNopeSolm, storageStore_createdAccounts,
                  initState]
              have hcallEnv :
                  evmStoreSolmBase.executionEnv =
                    ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
                      accountMap := σStore, createdAccounts := cA' } : EVM.State).executionEnv := by
                simp [hevmStoreSolmBase, hevmStoreSolm, hevmNopeSolm, storageStore_executionEnv,
                  initState]
              obtain ⟨σ_hope_solm, A_hope_solm0, hcallHopeSolmBase, hAccountsHope⟩ :=
                typedCallViaEVM_accountMapEquiv (evm_solm := evmStoreSolmBase) hcallHope_evm
                  hAccountsStore
                  (by simp [hevmStoreSolmBase, hevmStoreSolm, hevmNopeSolm, storageStore_σ₀, initState])
                  hcallCreated
                  (by simp [hevmStoreSolmBase, hevmStoreSolm, hevmNopeSolm,
                    storageStore_genesisBlockHeader, initState])
                  (by simp [hevmStoreSolmBase, hevmStoreSolm, hevmNopeSolm, storageStore_blocks,
                    initState])
                  (by simp [hevmStoreSolmBase])
                  hcallEnv
              have hdepthNeBase : evmStoreSolmBase.executionEnv.depth ≠ 1024 := by
                rw [hcallEnv]; simpa [initState] using hdepthNeI
              obtain ⟨A_hope_solm, hcallHopeSolmRaw⟩ :=
                typedCallViaEVM_zero_setSubstate hcallHopeSolmBase hdepthNeBase evmStoreSolm.substate
              have hcallHopeSolm :
                  typedCallViaEVM config evmStoreSolm (EVM.address (biteVatAddr evmStoreSolm)) "hope" 0
                    [.address (fileIlkFlipFlip I)]
                    (z2,
                      { evmStoreSolm with
                        accountMap := σ_hope_solm
                        substate := A_hope_solm
                        createdAccounts := cA'' },
                      out2) true := by
                simpa [hevmStoreSolmBase] using hcallHopeSolmRaw
              cases z2
              · -- hope call failed → both sides revert at the hope call
                exact (RD.catFileIlkFlipHopeCallFailure rd3695 hout2sz).reEquivExecutionRevert
                  hcode hdispatch hdecode
                  (fileIlkFlipHopeCallFailSource (σ := σ_solm) hwv hsz100 hauthSolm hflip
                    (fifVatCodePos hcodeSolmNe) hcallNope_solm (fifNopeDecode out) hevmStoreSolm
                    (fifVatCodePosGen hHopeTarget hcodeStoreSolmNe) hcallHopeSolm)
              · -- hope call succeeded → refinement holds
                have hbody := fileIlkFlipSourceSuccess (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hwv hsz100 hauthSolm hflip (fifVatCodePos hcodeSolmNe) hcallNope_solm
                  (fifNopeDecode out) hevmStoreSolm
                  (fifVatCodePosGen hHopeTarget hcodeStoreSolmNe) hcallHopeSolm (fifHopeDecode out2)
                have henc : returnEquiv ByteArray.empty none fileIlkFlipTransition.returnType := by
                  rw [show fileIlkFlipTransition.returnType = [] by rfl]
                  exact returnEquiv.fallthrough rfl rfl (by native_decide)
                exact (RD.catFileIlkFlipHopeCallSuccess (by simpa using rd3695)).reEquivExecutionGenAccountMapEquiv
                  hcode hdispatch hdecode hbody rfl hAccountsHope henc
        · -- depth = 1024: nope CALL returns 0 → both sides revert
          have hdepthEq : I.depth = 1024 := by
            apply Fin.ext
            have := Nat.le_of_lt_succ I.depth.isLt
            omega
          have hcallNopeFalse :=
            callNotMade_depthLimit (cfg := config)
              (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (tgt := EVM.address (biteVatAddr (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
              (name := "nope") (callPerm := true)
              (args := [.address (AccountAddress.ofNat
                (UInt256.land (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ_solm I)
                  solcAddrMask).toNat)])
              (fifNopeEncode_eq I
                (UInt256.land (catSlotWord (ilksBase (fileIlkFlipIlkKey I)) σ_solm I) solcAddrMask)
                (solcAddrMask_result_canonical _))
              hdepthEq
          exact (RD.catFileIlkFlipNopeDepthLimit rd3546 hcodeNope hdepthEq).reEquivExecutionRevert
            hcode hdispatch hdecode
            (fileIlkFlipNopeCallFailSource (σ := σ_solm) hwv hsz100 hauthSolm hflip
              (fifVatCodePos hcodeSolmNe) hcallNopeFalse)
    · -- what != "flip": unrecognized-param revert at ⟨953⟩
      have hmatchNe : fileIlkFlipWhatWord I ≠ ABI.bytesToWord fileIlkFlipBytes :=
        fileIlkFlipWhatWord_ne_of_bytes_ne (by omega) hflip (by native_decide)
      obtain ⟨_, _, rd953⟩ := RD.catFileIlkFlipWhatSkip rd3455 hmatchNe (by simp)
      have hmemAuth : (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
        twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      have hread64 :
          (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
            UInt256.toByteArray ⟨128⟩ :=
        twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64
      have hrev := RD.catFileAddressUnrecognizedRevert rd953 hmemAuth hread64 (by simp)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode
        (fileIlkFlipWhatSkipSource (σ := σ_solm) hwv hauthSolm hflip)
  · -- unauthorized → both sides revert at the auth guard
    have hauthSolm : catSlotWord (catCallerWardsSlot I) σ_solm I ≠ ⟨1⟩ :=
      fun h => hauthEvm (hcallerWord.trans h)
    have hauthSolc : solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [catCallerWardsSlot, catSlotWord] using hauthEvm
    have hrev := RD.catFileIlkFlipAuthRevert hreach hsz100 hsize hauthSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode
      (fileIlkFlipAuthFailSource (σ := σ_solm) hwv hauthSolm)

end Benchmarks.Dss.Cat
