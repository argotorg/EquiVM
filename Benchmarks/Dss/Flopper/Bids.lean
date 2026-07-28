import Benchmarks.Dss.Flopper.Dispatch
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flopper

/-! ## `bids(uint256)` struct mapping getter -/

abbrev bidsArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev bidsArgValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (bidsArgWord I).toNat)

abbrev bidsArgKey (I : ExecutionEnv) : KeyValue :=
  .int (Int.ofNat (bidsArgWord I).toNat)

abbrev bidsBidEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (bidsArgKey I), .field "bid"] }

abbrev bidsLotEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (bidsArgKey I), .field "lot"] }

abbrev bidsGuyEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (bidsArgKey I), .field "guy"] }

abbrev bidsTicEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (bidsArgKey I), .field "tic"] }

abbrev bidsEndEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (bidsArgKey I), .field "end"] }

abbrev bidsBaseSlotFor (I : ExecutionEnv) : UInt256 :=
  bidsBase (bidsArgKey I)

abbrev bidsBidSlotFor (I : ExecutionEnv) : UInt256 :=
  bidsBaseSlotFor I

abbrev bidsLotSlotFor (I : ExecutionEnv) : UInt256 :=
  bidsBaseSlotFor I + ⟨1⟩

abbrev bidsPackedSlotFor (I : ExecutionEnv) : UInt256 :=
  bidsBaseSlotFor I + ⟨2⟩

theorem bidsBaseSlotFor_eq (I : ExecutionEnv) :
    bidsBaseSlotFor I = solcMappingSlot ⟨1⟩ (bidsArgWord I) := by
  unfold bidsBaseSlotFor bidsBase bidsArgKey mapSlot solcMappingSlot
  rw [keyValueToWord_uint256]

theorem bidsLotSlotFor_eq (I : ExecutionEnv) :
    bidsLotSlotFor I = solcMappingSlot ⟨1⟩ (bidsArgWord I) + ⟨1⟩ := by
  simp [bidsLotSlotFor, bidsBaseSlotFor_eq]

theorem bidsPackedSlotFor_eq (I : ExecutionEnv) :
    bidsPackedSlotFor I = solcMappingSlot ⟨1⟩ (bidsArgWord I) + ⟨2⟩ := by
  simp [bidsPackedSlotFor, bidsBaseSlotFor_eq]

/-- Legacy solc-0.5 single-`uint256` calldata decode. -/
theorem decodeCalldata_legacyUint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyUint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flopperDecode_bids_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (bidsTransition.params.map Param.name)
      (transitionSignature bidsTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "arg0" (bidsArgValue I)) := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [uint256] I.calldata = _
  simpa [config, bidsArgValue, bidsArgWord, uint256] using
    decodeCalldata_legacyUint256_ok (cd := I.calldata) (x := "arg0") hsz36

theorem flopperDecode_bids_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (bidsTransition.params.map Param.name)
      (transitionSignature bidsTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["arg0"] [uint256] I.calldata = none
  simpa [config, uint256] using
    decodeCalldata_legacyUint256_none_short (cd := I.calldata) (x := "arg0") hsz4 hshort

theorem flopperBidsBodyReturns {I : ExecutionEnv}
    (evm : EVM.State) (locals : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals = (∅ : Store).insert "arg0" (bidsArgValue I)) :
    ExecTransitionBody config contract evm locals bidsTransition.body
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (flopperSlotWord (bidsBidSlotFor I) evm.accountMap evm.executionEnv).toNat)),
          (.int (Int.ofNat
          (flopperSlotWord (bidsLotSlotFor I) evm.accountMap evm.executionEnv).toNat)),
          (.address (AccountAddress.ofNat
          (flopperAddressReturnWord (bidsPackedSlotFor I) evm.accountMap
            evm.executionEnv).toNat)),
          (.int (Int.ofNat
          (flopperUint48Offset20Word (bidsPackedSlotFor I) evm.accountMap
            evm.executionEnv).toNat)),
          (.int (Int.ofNat
          (flopperUint48Offset26Word (bidsPackedSlotFor I) evm.accountMap
            evm.executionEnv).toNat))])) := by
  subst locals
  let frame : Frame := { contract := contract, locals := (∅ : Store).insert "arg0" (bidsArgValue I) }
  have hbid :
      evalExpr? config frame evm (.storage (bidsF (.var "arg0") "bid")) =
        .ok (.int (Int.ofNat
          (flopperSlotWord (bidsBidSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := bidsF (.var "arg0") "bid") (er := bidsBidEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (bidsBidSlotFor I))
      (value := .int (Int.ofNat
        (flopperSlotWord (bidsBidSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, bidsF])
      (by
        simp [frame, bidsBidEvaledRef, bidsArgKey, bidsArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind])
      (by
        simp [frame, bidsArgKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, uint256St])
      (by rfl)
      (by simpa [flopperSlotWord] using flopperStorageLocLoad_uint256 evm (bidsBidSlotFor I))
  have hlot :
      evalExpr? config frame evm (.storage (bidsF (.var "arg0") "lot")) =
        .ok (.int (Int.ofNat
          (flopperSlotWord (bidsLotSlotFor I) evm.accountMap evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := bidsF (.var "arg0") "lot") (er := bidsLotEvaledRef I)
      (t := .int uint256Int) (loc := wordLoc (bidsLotSlotFor I))
      (value := .int (Int.ofNat
        (flopperSlotWord (bidsLotSlotFor I) evm.accountMap evm.executionEnv).toNat))
      (by simp [frame, bidsF])
      (by
        simp [frame, bidsLotEvaledRef, bidsArgKey, bidsArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind])
      (by
        simp [frame, bidsArgKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, uint256St])
      (by rfl)
      (by simpa [flopperSlotWord] using flopperStorageLocLoad_uint256 evm (bidsLotSlotFor I))
  have hguy :
      evalExpr? config frame evm (.storage (bidsF (.var "arg0") "guy")) =
        .ok (.address (AccountAddress.ofNat
          (flopperAddressReturnWord (bidsPackedSlotFor I) evm.accountMap
            evm.executionEnv).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := bidsF (.var "arg0") "guy") (er := bidsGuyEvaledRef I)
      (t := .address) (loc := addrLoc (bidsPackedSlotFor I))
      (value := .address (AccountAddress.ofNat
        (flopperAddressReturnWord (bidsPackedSlotFor I) evm.accountMap
          evm.executionEnv).toNat))
      (by simp [frame, bidsF])
      (by
        simp [frame, bidsGuyEvaledRef, bidsArgKey, bidsArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind])
      (by
        simp [frame, bidsArgKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, addrSt])
      (by rfl)
      (by
        simpa [flopperAddressReturnWord, flopperSlotWord] using
          flopperStorageLocLoad_address_offset0 evm (bidsPackedSlotFor I))
  have htic :
      evalExpr? config frame evm (.storage (bidsF (.var "arg0") "tic")) =
        .ok (.int (Int.ofNat
          (flopperUint48Offset20Word (bidsPackedSlotFor I) evm.accountMap
            evm.executionEnv).toNat)) := by
    have hload :
        storageLocLoad evm (uint48Loc (bidsPackedSlotFor I) ⟨20, by decide⟩ (by decide)) =
          .int (Int.ofNat
            (flopperUint48Offset20Word (bidsPackedSlotFor I) evm.accountMap
              evm.executionEnv).toNat) := by
      rw [flopperStorageLocLoad_uint48_offset20]
      rw [u256_land_comm
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidsPackedSlotFor I))
          (UInt256.ofNat (256 ^ 20)))
        flopperUint48Mask]
      rfl
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := bidsF (.var "arg0") "tic") (er := bidsTicEvaledRef I)
      (t := .int uint48Int) (loc := uint48Loc (bidsPackedSlotFor I) ⟨20, by decide⟩ (by decide))
      (value := .int (Int.ofNat
        (flopperUint48Offset20Word (bidsPackedSlotFor I) evm.accountMap
          evm.executionEnv).toNat))
      (by simp [frame, bidsF])
      (by
        simp [frame, bidsTicEvaledRef, bidsArgKey, bidsArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind])
      (by
        simp [frame, bidsArgKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, uint48St])
      (by rfl)
      hload
  have hend :
      evalExpr? config frame evm (.storage (bidsF (.var "arg0") "end")) =
        .ok (.int (Int.ofNat
          (flopperUint48Offset26Word (bidsPackedSlotFor I) evm.accountMap
            evm.executionEnv).toNat)) := by
    have hload :
        storageLocLoad evm (uint48Loc (bidsPackedSlotFor I) ⟨26, by decide⟩ (by decide)) =
          .int (Int.ofNat
            (flopperUint48Offset26Word (bidsPackedSlotFor I) evm.accountMap
              evm.executionEnv).toNat) := by
      rw [flopperStorageLocLoad_uint48_offset26]
      rw [u256_land_comm
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (bidsPackedSlotFor I))
          (UInt256.ofNat (256 ^ 26)))
        flopperUint48Mask]
      rfl
    exact evalExpr_storage_scalar_value
      (cfg := config) (solm := frame) (evm := evm)
      (slot := bidsF (.var "arg0") "end") (er := bidsEndEvaledRef I)
      (t := .int uint48Int) (loc := uint48Loc (bidsPackedSlotFor I) ⟨26, by decide⟩ (by decide))
      (value := .int (Int.ofNat
        (flopperUint48Offset26Word (bidsPackedSlotFor I) evm.accountMap
          evm.executionEnv).toNat))
      (by simp [frame, bidsF])
      (by
        simp [frame, bidsEndEvaledRef, bidsArgKey, bidsArgValue, evalStorageRef,
          evalStorageRefSteps, evalStorageRefStep, bidsF, evalExpr?, valueToKey?,
          EvalResult.ofOption, EvalResult.bind, pure, bind])
      (by
        simp [frame, bidsArgKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          BidStructTy, uint48St])
      (by rfl)
      hload
  have hreturns :
      evalExprs? config frame evm
        [ .storage (bidsF (.var "arg0") "bid"),
          .storage (bidsF (.var "arg0") "lot"),
          .storage (bidsF (.var "arg0") "guy"),
          .storage (bidsF (.var "arg0") "tic"),
          .storage (bidsF (.var "arg0") "end") ] =
          .ok
            [ .int (Int.ofNat
                (flopperSlotWord (bidsBidSlotFor I) evm.accountMap
                  evm.executionEnv).toNat),
              .int (Int.ofNat
                (flopperSlotWord (bidsLotSlotFor I) evm.accountMap
                  evm.executionEnv).toNat),
              .address (AccountAddress.ofNat
                (flopperAddressReturnWord (bidsPackedSlotFor I) evm.accountMap
                  evm.executionEnv).toNat),
              .int (Int.ofNat
                (flopperUint48Offset20Word (bidsPackedSlotFor I) evm.accountMap
                  evm.executionEnv).toNat),
              .int (Int.ofNat
                (flopperUint48Offset26Word (bidsPackedSlotFor I) evm.accountMap
                  evm.executionEnv).toNat) ] := by
    simp [evalExprs?, hbid, hlot, hguy, htic, hend, EvalResult.bind, bind, pure]
  simpa [bidsTransition, nonpayable, frame] using
    (ExecFuncBody.execBlockRet <|
      ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
        ExecBlock.consReturn (ExecStmt.return hreturns))

@[reducible] def flopperBidsStructGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p32 := p30 + UInt256.ofNat 2
  let p34 := p32 + UInt256.ofNat 2
  let p36 := p34 + UInt256.ofNat 2
  let p37 := p36 + ⟨1⟩
  let p38 := p37 + ⟨1⟩
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p48 := p41 + UInt256.ofNat 7
  let p50 := p48 + UInt256.ofNat 2
  let p52 := p50 + UInt256.ofNat 2
  let p53 := p52 + ⟨1⟩
  let p54 := p53 + ⟨1⟩
  let p55 := p54 + ⟨1⟩
  let p56 := p55 + ⟨1⟩
  let p57 := p56 + ⟨1⟩
  let p58 := p57 + ⟨1⟩
  let p60 := p58 + UInt256.ofNat 2
  let p62 := p60 + UInt256.ofNat 2
  let p63 := p62 + ⟨1⟩
  let p64 := p63 + ⟨1⟩
  let p65 := p64 + ⟨1⟩
  let p66 := p65 + ⟨1⟩
  let p67 := p66 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p10 = some (.SWAP2, .none)
  ∧ decode code p11 = some (.DUP3, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p15 = some (.SWAP1, .none)
  ∧ decode code p16 = some (.SWAP2, .none)
  ∧ decode code p17 = some (.KECCAK256, .none)
  ∧ decode code p18 = some (.DUP1, .none)
  ∧ decode code p19 = some (.SLOAD, .none)
  ∧ decode code p20 = some (.SWAP2, .none)
  ∧ decode code p21 = some (.DUP2, .none)
  ∧ decode code p22 = some (.ADD, .none)
  ∧ decode code p23 = some (.SLOAD, .none)
  ∧ decode code p24 = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code p26 = some (.SWAP1, .none)
  ∧ decode code p27 = some (.SWAP2, .none)
  ∧ decode code p28 = some (.ADD, .none)
  ∧ decode code p29 = some (.SLOAD, .none)
  ∧ decode code p30 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p32 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p34 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p36 = some (.SHL, .none)
  ∧ decode code p37 = some (.SUB, .none)
  ∧ decode code p38 = some (.DUP2, .none)
  ∧ decode code p39 = some (.AND, .none)
  ∧ decode code p40 = some (.SWAP1, .none)
  ∧ decode code p41 = some (.Push .PUSH6, some (flopperUint48Mask, 6))
  ∧ decode code p48 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p50 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p52 = some (.SHL, .none)
  ∧ decode code p53 = some (.DUP3, .none)
  ∧ decode code p54 = some (.DIV, .none)
  ∧ decode code p55 = some (.DUP2, .none)
  ∧ decode code p56 = some (.AND, .none)
  ∧ decode code p57 = some (.SWAP2, .none)
  ∧ decode code p58 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p60 = some (.Push .PUSH1, some (⟨208⟩, 1))
  ∧ decode code p62 = some (.SHL, .none)
  ∧ decode code p63 = some (.SWAP1, .none)
  ∧ decode code p64 = some (.DIV, .none)
  ∧ decode code p65 = some (.AND, .none)
  ∧ decode code p66 = some (.DUP6, .none)
  ∧ decode code p67 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem RD.flopperBidsStructGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : flopperBidsStructGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land
        (UInt256.div (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨2⟩))
          (UInt256.ofNat (256 ^ 26)))
        flopperUint48Mask ::
        UInt256.land flopperUint48Mask
          (UInt256.div (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨2⟩))
            (UInt256.ofNat (256 ^ 20))) ::
        UInt256.land (solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨2⟩))
          solcAddrMask ::
        solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key + ⟨1⟩) ::
        solcSlotWord σ ee (solcMappingSlot ⟨1⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨1⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd15, hd16,
      hd17, hd18, hd19, hd20, hd21, hd22, hd23, hd24, hd26, hd27, hd28, hd29,
      hd30, hd32, hd34, hd36, hd37, hd38, hd39, hd40, hd41, hd48, hd50, hd52,
      hd53, hd54, hd55, hd56, hd57, hd58, hd60, hd62, hd63, hd64, hd65, hd66,
      hd67⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨1⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.swap1 hd6 (by evm_ov)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨1⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd10 := rd8.push1 ⟨0⟩ hd8 (by evm_ov)
  have rd11 := rd10.swap2 hd10 (by evm_ov)
  have rd12 := rd11.dup3 hd11 (by evm_ov)
  have rd13 := rd12.mstore 0 (solcMappingHashMem ⟨1⟩ key)
    (UInt256.ofNat 3) hd12 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd15 := rd13.push1 ⟨64⟩ hd13 (by evm_ov)
  have rd16 := rd15.swap1 hd15 (by evm_ov)
  have rd17 := rd16.swap2 hd16 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨1⟩ key
  have rd18 := rd17.keccak256 0 (solcMappingSlot ⟨1⟩ key)
    (UInt256.ofNat 3) hd17 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  have rd19 := rd18.dup1 hd18 (by evm_ov)
  obtain ⟨_, _, rd20⟩ := rd19.sload hd19 (by evm_ov)
  have rd21 := rd20.swap2 hd20 (by evm_ov)
  have rd22 := rd21.dup2 hd21 (by evm_ov)
  have rd23 := rd22.add hd22 (by evm_ov)
  obtain ⟨_, _, rd24⟩ := rd23.sload hd23 (by evm_ov)
  have rd26 := rd24.push1 ⟨2⟩ hd24 (by evm_ov)
  have rd27 := rd26.swap1 hd26 (by evm_ov)
  have rd28 := rd27.swap2 hd27 (by evm_ov)
  have rd29 := rd28.add hd28 (by evm_ov)
  obtain ⟨_, _, rd30⟩ := rd29.sload hd29 (by evm_ov)
  have rd32 := rd30.push1 ⟨1⟩ hd30 (by evm_ov)
  have rd34 := rd32.push1 ⟨1⟩ hd32 (by evm_ov)
  have rd36 := rd34.push1 ⟨160⟩ hd34 (by evm_ov)
  have rd37 := rd36.shl hd36 (by evm_ov)
  have rd38 := rd37.sub hd37 (by evm_ov)
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd38
  have rd39 := rd38.dup2 hd38 (by evm_ov)
  have rd40 := rd39.and hd39 (by evm_ov)
  have rd41 := rd40.swap1 hd40 (by evm_ov)
  have rd48 := rd41.pushConst flopperUint48Mask (width := 6) (op := .PUSH6)
    (by decide) hd41 (by evm_ov)
  have rd50 := rd48.push1 ⟨1⟩ hd48 (by evm_ov)
  have rd52 := rd50.push1 ⟨160⟩ hd50 (by evm_ov)
  have rd53 := rd52.shl hd52 (by evm_ov)
  have rd54 := rd53.dup3 hd53 (by evm_ov)
  have rd55 := rd54.div hd54 (by evm_ov)
  have rd56 := rd55.dup2 hd55 (by evm_ov)
  have rd57 := rd56.and hd56 (by evm_ov)
  have rd58 := rd57.swap2 hd57 (by evm_ov)
  have rd60 := rd58.push1 ⟨1⟩ hd58 (by evm_ov)
  have rd62 := rd60.push1 ⟨208⟩ hd60 (by evm_ov)
  have rd63 := rd62.shl hd62 (by evm_ov)
  have rd64 := rd63.swap1 hd63 (by evm_ov)
  have rd65 := rd64.div hd64 (by evm_ov)
  have rd66 := rd65.and hd65 (by evm_ov)
  have rd67 := rd66.dup6 hd66 (by evm_ov)
  have hshift160 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = UInt256.ofNat (256 ^ 20) := by
    native_decide
  have hshift208 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ = UInt256.ofNat (256 ^ 26) := by
    native_decide
  exact ⟨_, _, by
    simpa [solcSlotWord, hshift160, hshift208, u256_add_comm] using
      rd67.jump hd67 hret (by evm_ov)⟩

noncomputable abbrev flopperBidsReturnBytes
    (bid lot guy tic endw : UInt256) : ByteArray :=
  UInt256.toByteArray bid ++ UInt256.toByteArray lot ++
    UInt256.toByteArray (UInt256.land guy solcAddrMask) ++
    UInt256.toByteArray (UInt256.land tic flopperUint48Mask) ++
    UInt256.toByteArray (UInt256.land endw flopperUint48Mask)

noncomputable abbrev flopperBidsReturnMem
    (scratch : ByteArray) (bid lot guy tic endw : UInt256) : ByteArray :=
  writeCascade scratch
    [ (128, bid),
      (160, lot),
      (192, UInt256.land guy solcAddrMask),
      (224, UInt256.land tic flopperUint48Mask),
      (256, UInt256.land endw flopperUint48Mask) ]

theorem flopperBidsReturnBytes_size (bid lot guy tic endw : UInt256) :
    (flopperBidsReturnBytes bid lot guy tic endw).size = 160 := by
  simp [flopperBidsReturnBytes, ByteArray.size_append]

theorem flopperBidsReturnMem_eq {scratch : ByteArray}
    (bid lot guy tic endw : UInt256) (hscratch : scratch.size = 96) :
    flopperBidsReturnMem scratch bid lot guy tic endw =
      (scratch ++ ffi.ByteArray.zeroes 32) ++
        flopperBidsReturnBytes bid lot guy tic endw := by
  unfold flopperBidsReturnMem flopperBidsReturnBytes
  simp only [writeCascade_cons, writeCascade_nil]
  unfold Reasoning.Theory.writeWord
  rw [toByteArray_write_eq bid scratch 128 (by rw [hscratch]; omega)
    (by rw [hscratch]; exact lt_usize _ (by norm_num))]
  rw [show (160 : Nat) =
      (scratch ++ ffi.ByteArray.zeroes (128 - scratch.size) ++ UInt256.toByteArray bid).size by
        simp [ByteArray.size_append, ByteArray_zeroes_size, hscratch]]
  rw [write_at_end_eq (UInt256.toByteArray lot)
    (scratch ++ ffi.ByteArray.zeroes (128 - scratch.size) ++ UInt256.toByteArray bid) 32
    (by decide) (by rw [toByteArray_size])]
  rw [toByteArray_extract_all lot]
  rw [show (192 : Nat) =
      ((scratch ++ ffi.ByteArray.zeroes (128 - scratch.size) ++ UInt256.toByteArray bid) ++
        UInt256.toByteArray lot).size by
        simp [ByteArray.size_append, ByteArray_zeroes_size, hscratch]]
  rw [write_at_end_eq (UInt256.toByteArray (UInt256.land guy solcAddrMask))
    ((scratch ++ ffi.ByteArray.zeroes (128 - scratch.size) ++ UInt256.toByteArray bid) ++
      UInt256.toByteArray lot) 32 (by decide) (by rw [toByteArray_size])]
  rw [toByteArray_extract_all (UInt256.land guy solcAddrMask)]
  rw [show (224 : Nat) =
      (((scratch ++ ffi.ByteArray.zeroes (128 - scratch.size) ++ UInt256.toByteArray bid) ++
        UInt256.toByteArray lot) ++
        UInt256.toByteArray (UInt256.land guy solcAddrMask)).size by
        simp [ByteArray.size_append, ByteArray_zeroes_size, hscratch]]
  rw [write_at_end_eq (UInt256.toByteArray (UInt256.land tic flopperUint48Mask))
    (((scratch ++ ffi.ByteArray.zeroes (128 - scratch.size) ++ UInt256.toByteArray bid) ++
      UInt256.toByteArray lot) ++
      UInt256.toByteArray (UInt256.land guy solcAddrMask)) 32
    (by decide) (by rw [toByteArray_size])]
  rw [toByteArray_extract_all (UInt256.land tic flopperUint48Mask)]
  rw [show (256 : Nat) =
      ((((scratch ++ ffi.ByteArray.zeroes (128 - scratch.size) ++ UInt256.toByteArray bid) ++
        UInt256.toByteArray lot) ++ UInt256.toByteArray (UInt256.land guy solcAddrMask)) ++
        UInt256.toByteArray (UInt256.land tic flopperUint48Mask)).size by
        simp [ByteArray.size_append, ByteArray_zeroes_size, hscratch]]
  rw [write_at_end_eq (UInt256.toByteArray (UInt256.land endw flopperUint48Mask))
    ((((scratch ++ ffi.ByteArray.zeroes (128 - scratch.size) ++ UInt256.toByteArray bid) ++
      UInt256.toByteArray lot) ++ UInt256.toByteArray (UInt256.land guy solcAddrMask)) ++
      UInt256.toByteArray (UInt256.land tic flopperUint48Mask)) 32
    (by decide) (by rw [toByteArray_size])]
  rw [toByteArray_extract_all (UInt256.land endw flopperUint48Mask)]
  rw [hscratch]
  apply ByteArray.ext
  simp [ByteArray.data_append]

theorem flopperBidsReturnMem_size {scratch : ByteArray}
    (bid lot guy tic endw : UInt256) (hscratch : scratch.size = 96) :
    (flopperBidsReturnMem scratch bid lot guy tic endw).size = 288 := by
  rw [flopperBidsReturnMem_eq bid lot guy tic endw hscratch]
  simp [ByteArray.size_append, ByteArray_zeroes_size, hscratch]

theorem flopperBidsReturnMem_read64 {scratch : ByteArray}
    (bid lot guy tic endw : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (flopperBidsReturnMem scratch bid lot guy tic endw).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold flopperBidsReturnMem
  rw [writeCascade_read_preserved_of_base scratch _ hscratch
    (by simp [WindowDisjointFromWrites]; all_goals exact lt_usize _ (by norm_num))]
  exact hread64

theorem flopperBidsReturnMem_mload64 {scratch : ByteArray}
    (bid lot guy tic endw : UInt256)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (flopperBidsReturnMem scratch bid lot guy tic endw).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 9 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((flopperBidsReturnMem scratch bid lot guy tic endw).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [flopperBidsReturnMem_size bid lot guy tic endw hscratch]; decide)
    (by decide)
    (flopperBidsReturnMem_read64 bid lot guy tic endw hscratch hread64)

theorem flopperBidsReturnMem_read128_160 {scratch : ByteArray}
    (bid lot guy tic endw : UInt256) (hscratch : scratch.size = 96) :
    (flopperBidsReturnMem scratch bid lot guy tic endw).readWithPadding 128 160 =
      flopperBidsReturnBytes bid lot guy tic endw := by
  rw [flopperBidsReturnMem_eq bid lot guy tic endw hscratch]
  rw [readWithPadding_eq_extract' _ 128 160 (by norm_num) (by norm_num) (by
    simp [ByteArray.size_append, ByteArray_zeroes_size, hscratch])]
  exact extract_append_right' (scratch ++ ffi.ByteArray.zeroes 32)
    (flopperBidsReturnBytes bid lot guy tic endw) 128 288
    (by simp [ByteArray.size_append, ByteArray_zeroes_size, hscratch])
    (by simp [ByteArray.size_append, ByteArray_zeroes_size, hscratch])

theorem flopperBidsReturnEncoding (bid lot guy tic endw : UInt256) :
    encodeReturnValues? [uint256, uint256, addr, uint48, uint48]
      [ .int (Int.ofNat bid.toNat),
        .int (Int.ofNat lot.toNat),
        .address (AccountAddress.ofNat (UInt256.land guy solcAddrMask).toNat),
        .int (Int.ofNat (UInt256.land tic flopperUint48Mask).toNat),
        .int (Int.ofNat (UInt256.land endw flopperUint48Mask).toNat) ] =
        some (flopperBidsReturnBytes bid lot guy tic endw) := by
  have hencBid :
      encodeABIValue? uint256 (.int (Int.ofNat bid.toNat)) =
        some (EVM.Word.toBytesBE bid) := by
    have hword : EVM.word bid.toNat = bid := by
      show UInt256.ofNat bid.toNat = bid
      exact u256_ofNat_toNat bid
    have hlt : bid.toNat < EVM.twoPow 256 := by
      change bid.val.val < EVM.twoPow 256
      exact bid.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hencLot :
      encodeABIValue? uint256 (.int (Int.ofNat lot.toNat)) =
        some (EVM.Word.toBytesBE lot) := by
    have hword : EVM.word lot.toNat = lot := by
      show UInt256.ofNat lot.toNat = lot
      exact u256_ofNat_toNat lot
    have hlt : lot.toNat < EVM.twoPow 256 := by
      change lot.val.val < EVM.twoPow 256
      exact lot.val.isLt
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hencGuy :
      encodeABIValue? addr
          (.address (AccountAddress.ofNat (UInt256.land guy solcAddrMask).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land guy solcAddrMask)) := by
    have hcanon := solcAddrMask_result_canonical guy
    have haddrMod : (UInt256.land guy solcAddrMask).toNat % AccountAddress.size =
        (UInt256.land guy solcAddrMask).toNat := by
      apply Nat.mod_eq_of_lt
      simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
    have hword :
        EVM.word (UInt256.land guy solcAddrMask).toNat =
          UInt256.land guy solcAddrMask :=
      u256_ofNat_toNat _
    simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]
  have hencTic :
      encodeABIValue? uint48
          (.int (Int.ofNat (UInt256.land tic flopperUint48Mask).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land tic flopperUint48Mask)) := by
    have hword :
        EVM.word (UInt256.land tic flopperUint48Mask).toNat =
          UInt256.land tic flopperUint48Mask := by
      show UInt256.ofNat (UInt256.land tic flopperUint48Mask).toNat = _
      exact u256_ofNat_toNat _
    have hlt := flopperUint48Masked_lt tic
    simp [uint48, uint48Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  have hencEnd :
      encodeABIValue? uint48
          (.int (Int.ofNat (UInt256.land endw flopperUint48Mask).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land endw flopperUint48Mask)) := by
    have hword :
        EVM.word (UInt256.land endw flopperUint48Mask).toNat =
          UInt256.land endw flopperUint48Mask := by
      show UInt256.ofNat (UInt256.land endw flopperUint48Mask).toNat = _
      exact u256_ofNat_toNat _
    have hlt := flopperUint48Masked_lt endw
    simp [uint48, uint48Int, encodeABIValue?, encodeABIWord?, hword, hlt]
  unfold flopperBidsReturnBytes
  rw [show UInt256.toByteArray bid = (EVM.Word.toBytesBE bid).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray bid).symm]
  rw [show UInt256.toByteArray lot = (EVM.Word.toBytesBE lot).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray lot).symm]
  rw [show UInt256.toByteArray (UInt256.land guy solcAddrMask) =
      (EVM.Word.toBytesBE (UInt256.land guy solcAddrMask)).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray
      (UInt256.land guy solcAddrMask)).symm]
  rw [show UInt256.toByteArray (UInt256.land tic flopperUint48Mask) =
      (EVM.Word.toBytesBE (UInt256.land tic flopperUint48Mask)).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray
      (UInt256.land tic flopperUint48Mask)).symm]
  rw [show UInt256.toByteArray (UInt256.land endw flopperUint48Mask) =
      (EVM.Word.toBytesBE (UInt256.land endw flopperUint48Mask)).toByteArray by
    exact (word_toBytesBE_toByteArray_eq_toByteArray
      (UInt256.land endw flopperUint48Mask)).symm]
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? [uint256, uint256, addr, uint48, uint48] = some 160
    by native_decide]
  simp only [bind, Option.bind]
  unfold encodeABIValuesFrom?
  rw [hencBid]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [hencLot]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint256 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [hencGuy]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType addr = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [hencTic]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint48 = false by native_decide]
  unfold encodeABIValuesFrom?
  rw [hencEnd]
  simp only [bind, Option.bind]
  rw [show isDynamicABIType uint48 = false by native_decide]
  unfold encodeABIValuesFrom?
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append]

@[reducible] def flopperBidsReturnFromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p18 := p16 + UInt256.ofNat 2
  let p20 := p18 + UInt256.ofNat 2
  let p22 := p20 + UInt256.ofNat 2
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p30 := p29 + ⟨1⟩
  let p31 := p30 + ⟨1⟩
  let p38 := p31 + UInt256.ofNat 7
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p43 := p41 + UInt256.ofNat 2
  let p44 := p43 + ⟨1⟩
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p47 := p46 + ⟨1⟩
  let p49 := p47 + UInt256.ofNat 2
  let p50 := p49 + ⟨1⟩
  let p51 := p50 + ⟨1⟩
  let p52 := p51 + ⟨1⟩
  let p53 := p52 + ⟨1⟩
  let p54 := p53 + ⟨1⟩
  let p55 := p54 + ⟨1⟩
  let p56 := p55 + ⟨1⟩
  let p57 := p56 + ⟨1⟩
  let p59 := p57 + UInt256.ofNat 2
  let p60 := p59 + ⟨1⟩
  let p61 := p60 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p3 = some (.DUP1, .none)
  ∧ decode code p4 = some (.MLOAD, .none)
  ∧ decode code p5 = some (.SWAP6, .none)
  ∧ decode code p6 = some (.DUP7, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p10 = some (.DUP7, .none)
  ∧ decode code p11 = some (.ADD, .none)
  ∧ decode code p12 = some (.SWAP5, .none)
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.SWAP5, .none)
  ∧ decode code p15 = some (.MSTORE, .none)
  ∧ decode code p16 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p20 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p22 = some (.SHL, .none)
  ∧ decode code p23 = some (.SUB, .none)
  ∧ decode code p24 = some (.SWAP1, .none)
  ∧ decode code p25 = some (.SWAP3, .none)
  ∧ decode code p26 = some (.AND, .none)
  ∧ decode code p27 = some (.DUP5, .none)
  ∧ decode code p28 = some (.DUP5, .none)
  ∧ decode code p29 = some (.ADD, .none)
  ∧ decode code p30 = some (.MSTORE, .none)
  ∧ decode code p31 = some (.Push .PUSH6, some (flopperUint48Mask, 6))
  ∧ decode code p38 = some (.SWAP1, .none)
  ∧ decode code p39 = some (.DUP2, .none)
  ∧ decode code p40 = some (.AND, .none)
  ∧ decode code p41 = some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode code p43 = some (.DUP6, .none)
  ∧ decode code p44 = some (.ADD, .none)
  ∧ decode code p45 = some (.MSTORE, .none)
  ∧ decode code p46 = some (.AND, .none)
  ∧ decode code p47 = some (.Push .PUSH1, some (⟨128⟩, 1))
  ∧ decode code p49 = some (.DUP4, .none)
  ∧ decode code p50 = some (.ADD, .none)
  ∧ decode code p51 = some (.MSTORE, .none)
  ∧ decode code p52 = some (.MLOAD, .none)
  ∧ decode code p53 = some (.SWAP1, .none)
  ∧ decode code p54 = some (.DUP2, .none)
  ∧ decode code p55 = some (.SWAP1, .none)
  ∧ decode code p56 = some (.SUB, .none)
  ∧ decode code p57 = some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode code p59 = some (.ADD, .none)
  ∧ decode code p60 = some (.SWAP1, .none)
  ∧ decode code p61 = some (.RETURN, .none)

theorem RD.flopperBidsReturnFromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc bid lot guy tic endw ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (endw :: tic :: guy :: lot :: bid :: ret :: R)
        mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : flopperBidsReturnFromMemWf code pc)
    (hscratch : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 20 ≤ 1024) :
    RDret code g s0 acc (flopperBidsReturnBytes bid lot guy tic endw) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd6, hd7, hd8, hd10, hd11, hd12, hd13, hd14,
      hd15, hd16, hd18, hd20, hd22, hd23, hd24, hd25, hd26, hd27, hd28, hd29,
      hd30, hd31, hd38, hd39, hd40, hd41, hd43, hd44, hd45, hd46, hd47, hd49,
      hd50, hd51, hd52, hd53, hd54, hd55, hd56, hd57, hd59, hd60, hd61⟩
  let guyMasked := UInt256.land guy solcAddrMask
  let ticMasked := UInt256.land tic flopperUint48Mask
  let endMasked := UInt256.land endw flopperUint48Mask
  let mem1 := Reasoning.Theory.writeWord mem 128 bid
  let mem2 := Reasoning.Theory.writeWord mem1 160 lot
  let mem3 := Reasoning.Theory.writeWord mem2 192 guyMasked
  let mem4 := Reasoning.Theory.writeWord mem3 224 ticMasked
  let mem5 := Reasoning.Theory.writeWord mem4 256 endMasked
  have hload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hscratch]; decide) (by decide) hread64
  have rd4 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hload64 (by decide)
      (by evm_ov)]
  have rd7 := evm_run rd4 with [
    raw swap6 hd5 (by evm_ov),
    raw dup7 hd6 (by evm_ov),
    raw mstore 6 mem1 (UInt256.ofNat 5) hd7 mem_cost
      (by dsimp [mem1, Reasoning.Theory.writeWord]; rfl) (by decide) (by evm_ov)]
  have rd15 := evm_run rd7 with [
    raw push1 ⟨32⟩ hd8 (by evm_ov),
    raw dup7 hd10 (by evm_ov),
    raw add hd11 (by evm_ov),
    raw swap5 hd12 (by evm_ov),
    raw swap1 hd13 (by evm_ov),
    raw swap5 hd14 (by evm_ov),
    raw mstore 3 mem2 (UInt256.ofNat 6) hd15 mem_cost
      (by dsimp [mem2, Reasoning.Theory.writeWord]; rfl) (by decide) (by evm_ov)]
  have rd26 := evm_run rd15 with [
    raw push1 ⟨1⟩ hd16 (by evm_ov),
    raw push1 ⟨1⟩ hd18 (by evm_ov),
    raw push1 ⟨160⟩ hd20 (by evm_ov),
    raw shl hd22 (by evm_ov),
    raw sub hd23 (by evm_ov),
    raw swap1 hd24 (by evm_ov),
    raw swap3 hd25 (by evm_ov),
    raw and hd26 (by evm_ov)]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd26
  have rd30 := evm_run rd26 with [
    raw dup5 hd27 (by evm_ov),
    raw dup5 hd28 (by evm_ov),
    raw add hd29 (by evm_ov),
    raw mstore 3 mem3 (UInt256.ofNat 7) hd30 mem_cost
      (by dsimp [mem3, mem2, mem1, guyMasked, Reasoning.Theory.writeWord]; rfl) (by decide)
      (by evm_ov)]
  have rd40 := evm_run rd30 with [
    raw pushConst flopperUint48Mask (by decide) hd31 (by evm_ov),
    raw swap1 hd38 (by evm_ov),
    raw dup2 hd39 (by evm_ov),
    raw and hd40 (by evm_ov)]
  have rd45 := evm_run rd40 with [
    raw push1 ⟨96⟩ hd41 (by evm_ov),
    raw dup6 hd43 (by evm_ov),
    raw add hd44 (by evm_ov),
    raw mstore 3 mem4 (UInt256.ofNat 8) hd45 mem_cost
      (by
        dsimp [mem4, mem3, mem2, mem1, ticMasked, guyMasked,
          Reasoning.Theory.writeWord]
        rw [show (((⟨128⟩ : UInt256) + ⟨96⟩).toNat = 224) from by decide]
        rw [u256_land_comm flopperUint48Mask tic])
      (by decide) (by evm_ov)]
  have rd51 := evm_run rd45 with [
    raw and hd46 (by evm_ov),
    raw push1 ⟨128⟩ hd47 (by evm_ov),
    raw dup4 hd49 (by evm_ov),
    raw add hd50 (by evm_ov),
    raw mstore 3 mem5 (UInt256.ofNat 9) hd51 mem_cost
      (by
        dsimp [mem5, mem4, mem3, mem2, mem1, endMasked, ticMasked, guyMasked,
          Reasoning.Theory.writeWord]
        rw [show (((⟨128⟩ : UInt256) + ⟨128⟩).toNat = 256) from by decide]
        rw [u256_land_comm flopperUint48Mask endw])
      (by decide) (by evm_ov)]
  have hmem5 : mem5 = flopperBidsReturnMem mem bid lot guy tic endw := by
    dsimp [mem5, mem4, mem3, mem2, mem1, endMasked, ticMasked, guyMasked,
      flopperBidsReturnMem, writeCascade, Reasoning.Theory.writeWord]
  have rd52 := rd51.mload 0 ⟨128⟩ (UInt256.ofNat 9) hd52 mem_cost
    (by
      rw [hmem5]
      exact flopperBidsReturnMem_mload64 bid lot guy tic endw hscratch hread64)
    (by decide) (by evm_ov)
  have rd60 := evm_run rd52 with [
    raw swap1 hd53 (by evm_ov),
    raw dup2 hd54 (by evm_ov),
    raw swap1 hd55 (by evm_ov),
    raw sub hd56 (by evm_ov),
    raw push1 ⟨160⟩ hd57 (by evm_ov),
    raw add hd59 (by evm_ov),
    raw swap1 hd60 (by evm_ov)]
  have hretBytes :
      mem5.readWithPadding (⟨128⟩ : UInt256).toNat
          (UInt256.add (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩) ⟨160⟩).toNat =
        flopperBidsReturnBytes bid lot guy tic endw := by
    rw [hmem5]
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
    rw [show (UInt256.add (UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩) ⟨160⟩).toNat =
        160 from by decide]
    exact flopperBidsReturnMem_read128_160 bid lot guy tic endw hscratch
  exact rd60.ret 0 (flopperBidsReturnBytes bid lot guy tic endw) hd61 mem_cost
    hretBytes (by evm_ov)

theorem flopperReachBidsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flopperSelBytes 1)) :
    ∃ k C, RD flopperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨407⟩ [flopperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flopperSelWord I = ⟨0x4423c5f1⟩ := by
    simpa [flopperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x44 0x23 0xc5 0xf1 ⟨0x4423c5f1⟩
        (by native_decide) (by simpa [flopperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flopperBytecode flopperRootSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flopperBytecode flopperLowSplitPc)
      (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flopperReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  have heq0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowLowFirstArmPc j))
        (flopperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flopperBytecode (nthArmPc flopperBytecode flopperLowLowFirstArmPc 3))
        (flopperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨407⟩ 3 hfirst
    (fun j hj => flopperLowLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem flopperBidsBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some bidsTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (bidsTransition.params.map Param.name)
        (transitionSignature bidsTransition).paramTypes I.calldata =
          some ((∅ : Store).insert "arg0" (bidsArgValue I)))
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨407⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let key := bidsArgWord I
  let baseSlot := solcMappingSlot ⟨1⟩ key
  let bidSlot := baseSlot
  let lotSlot := baseSlot + ⟨1⟩
  let packedSlot := baseSlot + ⟨2⟩
  let bidWord := flopperSlotWord bidSlot σ_evm I
  let lotWord := flopperSlotWord lotSlot σ_evm I
  let packedWord := flopperSlotWord packedSlot σ_evm I
  let ticRaw := UInt256.div packedWord (UInt256.ofNat (256 ^ 20))
  let endRaw := UInt256.div packedWord (UInt256.ofNat (256 ^ 26))
  let locals : Store := (∅ : Store).insert "arg0" (bidsArgValue I)
  have hbidSlot : bidsBidSlotFor I = bidSlot := by
    simp [bidSlot, baseSlot, key, bidsBidSlotFor, bidsBaseSlotFor_eq]
  have hlotSlot : bidsLotSlotFor I = lotSlot := by
    simp [lotSlot, baseSlot, key, bidsLotSlotFor_eq]
  have hpackedSlot : bidsPackedSlotFor I = packedSlot := by
    simp [packedSlot, baseSlot, key, bidsPackedSlotFor_eq]
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals bidsTransition.body
        (.returned { contract := contract, locals := locals }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat
            (flopperSlotWord (bidsBidSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat
            (flopperSlotWord (bidsLotSlotFor I) σ_solm I).toNat)),
            (.address (AccountAddress.ofNat
            (flopperAddressReturnWord (bidsPackedSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat
            (flopperUint48Offset20Word (bidsPackedSlotFor I) σ_solm I).toNat)),
            (.int (Int.ofNat
            (flopperUint48Offset26Word (bidsPackedSlotFor I) σ_solm I).toNat))])) := by
    simpa [locals, initState] using
      flopperBidsBodyReturns (I := I)
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) locals
        (by simp only [initState]; exact hwv) rfl
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flopperBytecode) (sel := sel) (entry := ⟨407⟩) (ret := ⟨436⟩)
    (decoded := ⟨429⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  have htoRoutine : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1552⟩
      (bidsArgWord I :: ⟨436⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    have rd430 := hdecoded.jumpdest (by native_decide) (by evm_ov)
    have rd431 := rd430.pop (by native_decide) (by evm_ov)
    have rd432 := rd431.calldataload (by native_decide) (by evm_ov)
    have rd435 := rd432.push2 ⟨1552⟩ (by native_decide) (by evm_ov)
    exact ⟨_, _, by
      simpa [bidsArgWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
        using rd435.jump (by native_decide) (by jump_dest) (by evm_ov)⟩
  obtain ⟨_, _, htoRoutineRd⟩ := htoRoutine
  obtain ⟨_, _, hretPc⟩ := RD.flopperBidsStructGetter
    (code := flopperBytecode) (pc := ⟨1552⟩) (key := bidsArgWord I) (ret := ⟨436⟩)
    (R := [sel]) (by simpa using htoRoutineRd)
    (by
      unfold flopperBidsStructGetterWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  have hret :
      RDret flopperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (flopperBidsReturnBytes bidWord lotWord packedWord ticRaw endRaw) := by
    have hret' := RD.flopperBidsReturnFromMem
      (pc := ⟨436⟩) (bid := bidWord) (lot := lotWord)
      (guy := UInt256.land packedWord solcAddrMask)
      (tic := UInt256.land flopperUint48Mask ticRaw)
      (endw := UInt256.land endRaw flopperUint48Mask) (ret := ⟨436⟩) (R := [sel])
      (mem := solcMappingHashMem ⟨1⟩ (bidsArgWord I))
      (by
        simpa [bidWord, lotWord, packedWord, ticRaw, endRaw, bidSlot, lotSlot,
          packedSlot, baseSlot, key, flopperSlotWord] using hretPc)
      (by
        unfold flopperBidsReturnFromMemWf
        repeat' first | apply And.intro | native_decide)
      (solcMappingHashMem_size ⟨1⟩ (bidsArgWord I))
      (solcMappingHashMem_read64 ⟨1⟩ (bidsArgWord I))
      (by simp)
    have hcleanGuy :
        UInt256.land (UInt256.land packedWord solcAddrMask) solcAddrMask =
          UInt256.land packedWord solcAddrMask :=
      solcAddrMask_clean (solcAddrMask_result_canonical packedWord)
    have hcleanTic :
        UInt256.land (UInt256.land flopperUint48Mask ticRaw) flopperUint48Mask =
          UInt256.land ticRaw flopperUint48Mask := by
      rw [u256_land_comm flopperUint48Mask ticRaw]
      exact flopperUint48Mask_clean ticRaw
    have hcleanEnd :
        UInt256.land (UInt256.land endRaw flopperUint48Mask) flopperUint48Mask =
          UInt256.land endRaw flopperUint48Mask :=
      flopperUint48Mask_clean endRaw
    simpa [flopperBidsReturnBytes, hcleanGuy, hcleanTic, hcleanEnd] using hret'
  have hbidWord : flopperSlotWord bidSlot σ_evm I = flopperSlotWord bidSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner bidSlot ⟨0⟩
  have hlotWord : flopperSlotWord lotSlot σ_evm I = flopperSlotWord lotSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner lotSlot ⟨0⟩
  have hpackedWord :
      flopperSlotWord packedSlot σ_evm I = flopperSlotWord packedSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner packedSlot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (flopperSlotWord (bidsBidSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat (flopperSlotWord (bidsLotSlotFor I) σ_solm I).toNat),
        Value.address (AccountAddress.ofNat
          (flopperAddressReturnWord (bidsPackedSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat
          (flopperUint48Offset20Word (bidsPackedSlotFor I) σ_solm I).toNat),
        Value.int (Int.ofNat
          (flopperUint48Offset26Word (bidsPackedSlotFor I) σ_solm I).toNat)] =
      some [Value.int (Int.ofNat bidWord.toNat),
        Value.int (Int.ofNat lotWord.toNat),
        Value.address (AccountAddress.ofNat (UInt256.land packedWord solcAddrMask).toNat),
        Value.int (Int.ofNat (UInt256.land ticRaw flopperUint48Mask).toNat),
        Value.int (Int.ofNat (UInt256.land endRaw flopperUint48Mask).toNat)] := by
    rw [hbidSlot, hlotSlot, hpackedSlot]
    simp [flopperAddressReturnWord, flopperUint48Offset20Word, flopperUint48Offset26Word,
      bidWord, lotWord, packedWord, ticRaw, endRaw, hbidWord, hlotWord, hpackedWord,
      u256_land_comm]
  have henc :
      returnEquiv (flopperBidsReturnBytes bidWord lotWord packedWord ticRaw endRaw)
        (some [(.int (Int.ofNat bidWord.toNat)),
          (.int (Int.ofNat lotWord.toNat)),
          (.address (AccountAddress.ofNat (UInt256.land packedWord solcAddrMask).toNat)),
          (.int (Int.ofNat (UInt256.land ticRaw flopperUint48Mask).toNat)),
          (.int (Int.ofNat (UInt256.land endRaw flopperUint48Mask).toNat))])
        bidsTransition.returnType := by
    rw [show bidsTransition.returnType = [uint256, uint256, addr, uint48, uint48] by rfl]
    exact returnEquiv.returned rfl
      (flopperBidsReturnEncoding bidWord lotWord packedWord ticRaw endRaw)
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem flopperBidsBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flopperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some bidsTransition)
    (hreach : ∃ k C, RD flopperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨407⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := flopperBytecode) (sel := sel) (entry := ⟨407⟩) (ret := ⟨436⟩)
    (decoded := ⟨429⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (flopperDecode_bids_none_short hsz4 hshort)

theorem flopperBidsBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flopperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flopperSelBytes 1))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flopperSelBytes 1) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some bidsTransition :=
    flopperDispatchBids hsel
  have hreach := flopperReachBidsBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · exact flopperBidsBodyCoreOk hcode hwv hsz36 hsize hdispatch
      (flopperDecode_bids_ok hsz36) hreach hAccounts
  · exact flopperBidsBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Flopper
