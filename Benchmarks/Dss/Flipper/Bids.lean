import Benchmarks.Dss.Flipper.Dispatch
import Benchmarks.Dss.Flipper.BidStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 800000

namespace Reasoning.Reach

theorem swap9_xstep {s : State} {code : ByteArray}
    {pcv a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.SWAP9, .none))
    (hstk : s.machineState.stack = a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
    (hov : t.length + 10 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 3 then .error .OutOfGass
         else .ok (stSwap s (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t),
          .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.SWAP9, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_swap9 s hd, hstk]
  have hov' :
      ¬ ((a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t).length - 10 + 10 >
          1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Gverylow, stSwap]

theorem RD.swap9 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d e f gg hh ii jj : UInt256} {t : List UInt256}
    (rd : RD code ee g s0 pc (a :: b :: c :: d :: e :: f :: gg :: hh :: ii :: jj :: t)
      mem aw rdata acc k C)
    (hdec : decode code pc = some (.SWAP9, .none)) (hov : t.length + 10 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩)
      (jj :: b :: c :: d :: e :: f :: gg :: hh :: ii :: a :: t)
      mem aw rdata acc (k + 1) (C + 3) :=
  rd.stepSwap (fun _ hc hp hs => swap9_xstep hc hp hdec hs hov)

end Reasoning.Reach

namespace Benchmarks.Dss.Flipper

/-! ## `bids(uint256)` getter -/

abbrev bidsId (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev bidsLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (.int (Int.ofNat (bidsId I).toNat))

abbrev bidsBaseWord (I : ExecutionEnv) : UInt256 :=
  bidBaseOfWord (bidsId I)

abbrev bidsPackedSlot (I : ExecutionEnv) : UInt256 :=
  bidPackedSlotOfWord (bidsId I)

abbrev bidsEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "bids", steps := [.mindex (.int (Int.ofNat (bidsId I).toNat)), .field field] }

abbrev bidsBidWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord (bidsBaseWord I) σ I

abbrev bidsLotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord (bidsBaseWord I + ⟨1⟩) σ I

abbrev bidsPackedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord (bidsPackedSlot I) σ I

abbrev bidsGuyWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (bidsPackedWord σ I) solcAddrMask

abbrev bidsTicWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset20Word (bidsPackedSlot I) σ I

abbrev bidsEndWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperUint48Offset26Word (bidsPackedSlot I) σ I

abbrev bidsUsrWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (flipperSlotWord (bidsBaseWord I + ⟨3⟩) σ I) solcAddrMask

abbrev bidsGalWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (flipperSlotWord (bidsBaseWord I + ⟨4⟩) σ I) solcAddrMask

abbrev bidsTabWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  flipperSlotWord (bidsBaseWord I + ⟨5⟩) σ I

def bidsReturnValues (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  [ .int (Int.ofNat (bidsBidWord σ I).toNat),
    .int (Int.ofNat (bidsLotWord σ I).toNat),
    .address (AccountAddress.ofNat (bidsGuyWord σ I).toNat),
    .int (Int.ofNat (bidsTicWord σ I).toNat),
    .int (Int.ofNat (bidsEndWord σ I).toNat),
    .address (AccountAddress.ofNat (bidsUsrWord σ I).toNat),
    .address (AccountAddress.ofNat (bidsGalWord σ I).toNat),
    .int (Int.ofNat (bidsTabWord σ I).toNat) ]

def bidsReturnData (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  UInt256.toByteArray (bidsBidWord σ I) ++
  UInt256.toByteArray (bidsLotWord σ I) ++
  UInt256.toByteArray (bidsGuyWord σ I) ++
  UInt256.toByteArray (bidsTicWord σ I) ++
  UInt256.toByteArray (bidsEndWord σ I) ++
  UInt256.toByteArray (bidsUsrWord σ I) ++
  UInt256.toByteArray (bidsGalWord σ I) ++
  UInt256.toByteArray (bidsTabWord σ I)

noncomputable abbrev bidsHashMem (I : ExecutionEnv) : ByteArray :=
  solcMappingHashMem ⟨1⟩ (bidsId I)

noncomputable abbrev bidsReturnPrefix (I : ExecutionEnv) : ByteArray :=
  bidsHashMem I ++ ffi.ByteArray.zeroes 32

noncomputable abbrev bidsReturnMem1 (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  bidsReturnPrefix I ++ UInt256.toByteArray (bidsBidWord σ I)

noncomputable abbrev bidsReturnMem2 (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  bidsReturnMem1 σ I ++ UInt256.toByteArray (bidsLotWord σ I)

noncomputable abbrev bidsReturnMem3 (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  bidsReturnMem2 σ I ++ UInt256.toByteArray (bidsGuyWord σ I)

noncomputable abbrev bidsReturnMem4 (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  bidsReturnMem3 σ I ++ UInt256.toByteArray (bidsTicWord σ I)

noncomputable abbrev bidsReturnMem5 (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  bidsReturnMem4 σ I ++ UInt256.toByteArray (bidsEndWord σ I)

noncomputable abbrev bidsReturnMem6 (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  bidsReturnMem5 σ I ++ UInt256.toByteArray (bidsUsrWord σ I)

noncomputable abbrev bidsReturnMem7 (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  bidsReturnMem6 σ I ++ UInt256.toByteArray (bidsGalWord σ I)

noncomputable abbrev bidsReturnMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  bidsReturnPrefix I ++ bidsReturnData σ I

theorem bidsBase_eq_bidsBase (I : ExecutionEnv) :
    bidsBase (.int (Int.ofNat (bidsId I).toNat)) = bidsBaseWord I := by
  simpa [bidsBaseWord] using bidsBase_intOfNatWord (bidsId I)

theorem bidsLocals_get_arg0 (I : ExecutionEnv) :
    (bidsLocals I).get? "arg0" =
      some (.int (Int.ofNat (bidsId I).toNat)) := by
  rw [bidsLocals, store_get_self]

theorem bidsLocals_get_bids (I : ExecutionEnv) :
    (bidsLocals I).get? "bids" = none := by
  rw [bidsLocals, store_get_ne _ _ (by decide)]
  simp

theorem evalStorageRef_bidsField {evm : EVM.State} {I : ExecutionEnv} {field : Ident} :
    evalStorageRef config { contract := contract, locals := bidsLocals I } evm
      (bidsF (.var "arg0") field) = .ok (bidsEvaledRef I field) := by
  simp [bidsEvaledRef, bidsLocals, bidsF, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, valueToKey?, EvalResult.ofOption, EvalResult.bind,
    pure, bind]

theorem evalExpr_bidsBid {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := bidsLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "arg0") "bid")) =
        .ok (.int (Int.ofNat (bidsBidWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (loc := wordLoc (bidsBaseWord I))
    (hbase := bidsLocals_get_bids I)
    (her := evalStorageRef_bidsField (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (field := "bid"))
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidsEvaledRef, contract, storageDecls,
        BidStructTy, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, bidsEvaledRef,
        bidsBaseWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  simpa [initState, bidsBidWord, flipperSlotWord] using
    congrArg EvalResult.ok
      (flipperStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) (bidsBaseWord I))

theorem evalExpr_bidsLot {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := bidsLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "arg0") "lot")) =
        .ok (.int (Int.ofNat (bidsLotWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (loc := wordLoc (bidsBaseWord I + ⟨1⟩))
    (hbase := bidsLocals_get_bids I)
    (her := evalStorageRef_bidsField (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (field := "lot"))
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidsEvaledRef, contract, storageDecls,
        BidStructTy, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, bidsEvaledRef,
        bidsBaseWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  simpa [initState, bidsLotWord, flipperSlotWord] using
    congrArg EvalResult.ok
      (flipperStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I)
        (bidsBaseWord I + ⟨1⟩))

theorem evalExpr_bidsGuy {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := bidsLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "arg0") "guy")) =
        .ok (.address (AccountAddress.ofNat (bidsGuyWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .address)
    (loc := addrLoc (bidsPackedSlot I))
    (hbase := bidsLocals_get_bids I)
    (her := evalStorageRef_bidsField (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (field := "guy"))
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidsEvaledRef, contract, storageDecls,
        BidStructTy, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, bidsEvaledRef,
        bidsPackedSlot, bidPackedSlotOfWord, bidsBaseWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  simpa [initState, bidsGuyWord, bidsPackedWord, flipperSlotWord] using
    congrArg EvalResult.ok
      (flipperStorageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
        (bidsPackedSlot I))

theorem evalExpr_bidsTic {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := bidsLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "arg0") "tic")) =
        .ok (.int (Int.ofNat (bidsTicWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint48Int)
    (loc := uint48Loc (bidsPackedSlot I) ⟨20, by decide⟩ (by decide))
    (hbase := bidsLocals_get_bids I)
    (her := evalStorageRef_bidsField (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (field := "tic"))
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidsEvaledRef, contract, storageDecls,
        BidStructTy, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, bidsEvaledRef,
        bidsPackedSlot, bidPackedSlotOfWord, bidsBaseWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  simpa [initState, bidsTicWord, flipperUint48Offset20Word, bidsPackedWord,
    flipperSlotWord] using
    congrArg EvalResult.ok
      (flipperStorageLocLoad_uint48_offset20 (initState cA gh bl σ σ₀ g A I)
        (bidsPackedSlot I))

theorem evalExpr_bidsEnd {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := bidsLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "arg0") "end")) =
        .ok (.int (Int.ofNat (bidsEndWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint48Int)
    (loc := uint48Loc (bidsPackedSlot I) ⟨26, by decide⟩ (by decide))
    (hbase := bidsLocals_get_bids I)
    (her := evalStorageRef_bidsField (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (field := "end"))
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidsEvaledRef, contract, storageDecls,
        BidStructTy, uint48St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, bidsEvaledRef,
        bidsPackedSlot, bidPackedSlotOfWord, bidsBaseWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  simpa [initState, bidsEndWord, flipperUint48Offset26Word, bidsPackedWord,
    flipperSlotWord] using
    congrArg EvalResult.ok
      (flipperStorageLocLoad_uint48_offset26 (initState cA gh bl σ σ₀ g A I)
        (bidsPackedSlot I))

theorem evalExpr_bidsUsr {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := bidsLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "arg0") "usr")) =
        .ok (.address (AccountAddress.ofNat (bidsUsrWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .address)
    (loc := addrLoc (bidsBaseWord I + ⟨3⟩))
    (hbase := bidsLocals_get_bids I)
    (her := evalStorageRef_bidsField (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (field := "usr"))
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidsEvaledRef, contract, storageDecls,
        BidStructTy, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, bidsEvaledRef,
        bidsBaseWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  simpa [initState, bidsUsrWord, flipperSlotWord] using
    congrArg EvalResult.ok
      (flipperStorageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
        (bidsBaseWord I + ⟨3⟩))

theorem evalExpr_bidsGal {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := bidsLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "arg0") "gal")) =
        .ok (.address (AccountAddress.ofNat (bidsGalWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .address)
    (loc := addrLoc (bidsBaseWord I + ⟨4⟩))
    (hbase := bidsLocals_get_bids I)
    (her := evalStorageRef_bidsField (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (field := "gal"))
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidsEvaledRef, contract, storageDecls,
        BidStructTy, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, bidsEvaledRef,
        bidsBaseWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  simpa [initState, bidsGalWord, flipperSlotWord] using
    congrArg EvalResult.ok
      (flipperStorageLocLoad_address_offset0 (initState cA gh bl σ σ₀ g A I)
        (bidsBaseWord I + ⟨4⟩))

theorem evalExpr_bidsTab {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := bidsLocals I }
      (initState cA gh bl σ σ₀ g A I) (.storage (bidsF (.var "arg0") "tab")) =
        .ok (.int (Int.ofNat (bidsTabWord σ I).toNat)) := by
  rw [evalExpr_storage_scalar
    (t := .int uint256Int)
    (loc := wordLoc (bidsBaseWord I + ⟨5⟩))
    (hbase := bidsLocals_get_bids I)
    (her := evalStorageRef_bidsField (evm := initState cA gh bl σ σ₀ g A I)
      (I := I) (field := "tab"))
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, bidsEvaledRef, contract, storageDecls,
        BidStructTy, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, bidsEvaledRef,
        bidsBaseWord, bidBaseOfWord]
      unfold bidsBase mapSlot solcMappingSlot
      rw [keyValueToWord_uint256_natCast])]
  simpa [initState, bidsTabWord, flipperSlotWord] using
    congrArg EvalResult.ok
      (flipperStorageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I)
        (bidsBaseWord I + ⟨5⟩))

theorem evalExprs_bidsReturn {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExprs? config { contract := contract, locals := bidsLocals I }
      (initState cA gh bl σ σ₀ g A I)
      [ .storage (bidsF (.var "arg0") "bid"),
        .storage (bidsF (.var "arg0") "lot"),
        .storage (bidsF (.var "arg0") "guy"),
        .storage (bidsF (.var "arg0") "tic"),
        .storage (bidsF (.var "arg0") "end"),
        .storage (bidsF (.var "arg0") "usr"),
        .storage (bidsF (.var "arg0") "gal"),
        .storage (bidsF (.var "arg0") "tab") ] =
      .ok (bidsReturnValues σ I) := by
  simp [evalExprs?, bidsReturnValues, evalExpr_bidsBid, evalExpr_bidsLot,
    evalExpr_bidsGuy, evalExpr_bidsTic, evalExpr_bidsEnd, evalExpr_bidsUsr,
    evalExpr_bidsGal, evalExpr_bidsTab, EvalResult.bind, bind, pure]

theorem flipperBidsSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (bidsLocals I)
      bidsTransition.body
      (.returned { contract := contract, locals := bidsLocals I }
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (some (bidsReturnValues σ I))) := by
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by
      simp only [initState]
      exact hwv))) <|
      ExecBlock.consReturn (ExecStmt.return (by
        simpa [bidsTransition, nonpayable] using
          (evalExprs_bidsReturn (cA := cA) (gh := gh) (bl := bl) (σ := σ)
            (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g))))

theorem encodeABIValue_uint256_word (w : UInt256) :
    encodeABIValue? uint256 (.int (Int.ofNat w.toNat)) =
      some (UInt256.toByteArray w).toList := by
  have hlt : w.toNat < EVM.twoPow 256 := w.val.isLt
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hlt, hword,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem encodeABIValue_uint48_word (w : UInt256) :
    encodeABIValue? uint48 (.int (Int.ofNat (UInt256.land w uint48Mask).toNat)) =
      some (UInt256.toByteArray (UInt256.land w uint48Mask)).toList := by
  have hlt := uint48Mask_bound w
  have hword : EVM.word (UInt256.land w uint48Mask).toNat = UInt256.land w uint48Mask :=
    u256_ofNat_toNat _
  simp [uint48, uint48Int, encodeABIValue?, encodeABIWord?, hlt, hword,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem encodeABIValue_address_word (w : UInt256) :
    encodeABIValue? addr
        (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (UInt256.toByteArray (UInt256.land w solcAddrMask)).toList := by
  have hcanon := solcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat =
      UInt256.land w solcAddrMask := u256_ofNat_toNat _
  simp [addr, encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword,
    toByteArray_eq_toBytesBE, byteArray_toList_eq]

theorem bidsReturnEncoding (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValues? bidsTransition.returnType (bidsReturnValues σ I) =
      some (bidsReturnData σ I) := by
  have hdu : isDynamicABIType uint256 = false := by native_decide
  have hda : isDynamicABIType addr = false := by native_decide
  have hd48 : isDynamicABIType uint48 = false := by native_decide
  unfold encodeReturnValues? encodeABIValues?
  rw [show abiTupleHeadSize? bidsTransition.returnType = some 256 by native_decide]
  simp only [bidsTransition, bidsReturnValues, bidsReturnData, bind]
  simp only [encodeABIValuesFrom?, encodeABIValue_uint256_word, encodeABIValue_uint48_word,
    encodeABIValue_address_word, hdu, hda, hd48, Bool.false_eq_true, if_false,
    bind, Option.bind, List.nil_append]
  apply congrArg some
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.toList_append, byteArray_toList_eq, bidsGuyWord,
    bidsTicWord, bidsEndWord, bidsUsrWord, bidsGalWord]

theorem flipperDecodeCalldata_legacyUInt256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  simp [decodeCalldata.insertValues, hword4]

theorem flipperDecodeCalldata_legacyUInt256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have hlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [hlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem flipperDecode_bids_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (bidsTransition.params.map Param.name)
      (transitionSignature bidsTransition).paramTypes I.calldata =
        some (bidsLocals I) := by
  simpa [config, bidsTransition, transitionSignature, bidsLocals, bidsId]
    using (flipperDecodeCalldata_legacyUInt256_ok (cd := I.calldata) (x := "arg0") hsz36)

theorem flipperDecode_bids_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (bidsTransition.params.map Param.name)
      (transitionSignature bidsTransition).paramTypes I.calldata = none := by
  simpa [config, bidsTransition, transitionSignature]
    using (flipperDecodeCalldata_legacyUInt256_none_short (cd := I.calldata)
      (x := "arg0") hsz4 hshort)

theorem flipperDispatchBids {I : ExecutionEnv}
    (hsel : selIs I (flipperSelBytes 1)) :
    dispatchMsg contract I.calldata = some bidsTransition := by
  have hcd : I.calldata.extract 0 4 = flipperSelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some bidsTransition
  unfold transitions
  have hbeg : (flipperSelBytes 0 == flipperSelBytes 1) = false := by native_decide
  have hbids : (flipperSelBytes 1 == flipperSelBytes 1) = true := by native_decide
  simp [dispatchList, selectorOf, hcd, begSelectorBytes, bidsSelectorBytes, hbeg, hbids]

theorem flipperReachBidsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 1)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨480⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0x4423c5f1⟩ :=
    flipperSelWord_eq_of_beq I hsz 0x44 0x23 0xc5 0xf1 ⟨0x4423c5f1⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat flipperBytecode flipperHighSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperHighHighFirstArmPc 0))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachHighHighBody 0 (by omega) ⟨480⟩ hcode hwv hsz hsize hroot hhigh
    heq0 htake (by jump_dest) (by native_decide)

theorem RD.flipperBidsDecodeToRoutine {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨502⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = flipperBytecode)
    (hroutine : (D_J code 0).contains ⟨2568⟩ = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2568⟩
      (calldataWord ee.calldata 4 :: ret :: sel :: R) mem aw rdata acc k' C' := by
  subst hwf
  have rd2568 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨2568⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) hroutine (by evm_ov)]
  exact ⟨_, _, by simpa [calldataWord] using rd2568⟩

theorem flipperBidsX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨480⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2568⟩
        [bidsId I, ⟨509⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flipperBytecode) (sel := sel) (entry := ⟨480⟩) (ret := ⟨509⟩)
    (decoded := ⟨502⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.flipperBidsDecodeToRoutine
    (code := flipperBytecode) (ret := ⟨509⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [bidsId] using hroutine⟩

theorem flipperBidsX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨480⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flipperBytecode) (sel := sel) (entry := ⟨480⟩) (ret := ⟨509⟩)
    (decoded := ⟨502⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem bidsReturnPrefix_size (I : ExecutionEnv) :
    (bidsReturnPrefix I).size = 128 := by
  simp [bidsReturnPrefix, bidsHashMem, solcMappingHashMem_size, ByteArray.size_append,
    ByteArray_zeroes_size]

theorem bidsReturnMem1_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnMem1 σ I).size = 160 := by
  rw [bidsReturnMem1, ByteArray.size_append, bidsReturnPrefix_size, toByteArray_size]

theorem bidsReturnMem2_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnMem2 σ I).size = 192 := by
  rw [bidsReturnMem2, ByteArray.size_append, bidsReturnMem1_size, toByteArray_size]

theorem bidsReturnMem3_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnMem3 σ I).size = 224 := by
  rw [bidsReturnMem3, ByteArray.size_append, bidsReturnMem2_size, toByteArray_size]

theorem bidsReturnMem4_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnMem4 σ I).size = 256 := by
  rw [bidsReturnMem4, ByteArray.size_append, bidsReturnMem3_size, toByteArray_size]

theorem bidsReturnMem5_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnMem5 σ I).size = 288 := by
  rw [bidsReturnMem5, ByteArray.size_append, bidsReturnMem4_size, toByteArray_size]

theorem bidsReturnMem6_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnMem6 σ I).size = 320 := by
  rw [bidsReturnMem6, ByteArray.size_append, bidsReturnMem5_size, toByteArray_size]

theorem bidsReturnMem7_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnMem7 σ I).size = 352 := by
  rw [bidsReturnMem7, ByteArray.size_append, bidsReturnMem6_size, toByteArray_size]

theorem bidsReturnData_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnData σ I).size = 256 := by
  simp [bidsReturnData, ByteArray.size_append, toByteArray_size]

theorem bidsReturnMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnMem σ I).size = 384 := by
  rw [bidsReturnMem, ByteArray.size_append, bidsReturnPrefix_size, bidsReturnData_size]

theorem bidsReturnMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rw [readWithPadding_eq_extract _ 64 (by rw [bidsReturnMem_size]; omega)]
  rw [bidsReturnMem]
  rw [extract_append_left _ _ 64 96 (by rw [bidsReturnPrefix_size]; omega)]
  rw [bidsReturnPrefix]
  rw [extract_append_left _ _ 64 96 (by
    simp [bidsHashMem, solcMappingHashMem_size])]
  rw [← readWithPadding_eq_extract _ 64 (by
    simp [bidsHashMem, solcMappingHashMem_size])]
  exact solcMappingHashMem_read64 ⟨1⟩ (bidsId I)

theorem bidsReturnMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (bidsReturnMem σ I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 12 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((bidsReturnMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [bidsReturnMem_size]; decide) (by decide)
    (bidsReturnMem_read64 σ I)

theorem bidsReturnMem_read128_256 (σ : AccountMap) (I : ExecutionEnv) :
    (bidsReturnMem σ I).readWithPadding 128 256 = bidsReturnData σ I := by
  rw [readWithPadding_eq_extract' _ 128 256 (by norm_num) (by norm_num)
    (by rw [bidsReturnMem_size])]
  rw [bidsReturnMem]
  rw [extract_append_right_window (bidsReturnPrefix I) (bidsReturnData σ I)
    128 (128 + 256) (by rw [bidsReturnPrefix_size])]
  rw [bidsReturnPrefix_size]
  norm_num
  simpa [bidsReturnData_size] using byteArray_extract_self (bidsReturnData σ I)

theorem flipperBidsDecodePushMask2627 :
    decode flipperBytecode (⟨2627⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperBidsDecodePushMask540 :
    decode flipperBytecode (⟨540⟩ : UInt256) =
      some (.Push .PUSH6, some (uint48Mask, 6)) := by
  native_decide

theorem flipperBidsX_loadStruct {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2568⟩
      [bidsId I, ⟨509⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨509⟩
      [bidsTabWord σ I, bidsGalWord σ I, bidsUsrWord σ I, bidsEndWord σ I,
        bidsTicWord σ I, bidsGuyWord σ I, bidsLotWord σ I, bidsBidWord σ I,
        ⟨509⟩, sel]
      (bidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let base := bidsBaseWord I
  let packed := bidsPackedWord σ I
  have hbaseComm2 : ⟨2⟩ + base = base + ⟨2⟩ := u256_add_comm _ _
  have hbaseComm3 : ⟨3⟩ + base = base + ⟨3⟩ := u256_add_comm _ _
  have hbaseComm4 : ⟨4⟩ + base = base + ⟨4⟩ := u256_add_comm _ _
  have hbaseComm5 : ⟨5⟩ + base = base + ⟨5⟩ := u256_add_comm _ _
  have hdiv160 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = uint48Divisor20 := by
    rfl
  have hmask160 : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    native_decide
  have hmask160' : UInt256.sub uint48Divisor20 ⟨1⟩ = solcAddrMask := by
    rw [← hdiv160]
    exact hmask160
  have hdiv208 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨208⟩ = uint48Divisor26 := by
    rfl
  have hhash : UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((bidsHashMem I).readWithPadding 0 64))) = base := by
    simpa [bidsHashMem, bidsBaseWord, bidBaseOfWord] using
      (solcMappingKeccakSlot ⟨1⟩ (bidsId I))
  have rd2586 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (solcMappingBaseSlotMem ⟨1⟩) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw mstore 0 (bidsHashMem I) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw keccak256 0 base (UInt256.ofNat 3) (by native_decide) mem_cost hhash
      (by native_decide) (by evm_ov)]
  have rd2587 := evm_run rd2586 with [
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2588⟩ := rd2587.sload (by native_decide) (by evm_ov)
  have rd2591 := evm_run rd2588 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2592⟩ := rd2591.sload (by native_decide) (by evm_ov)
  have rd2596 := evm_run rd2592 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2597⟩ := rd2596.sload (by native_decide) (by evm_ov)
  have rd2601 := evm_run rd2597 with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2602⟩ := rd2601.sload (by native_decide) (by evm_ov)
  have rd2606 := evm_run rd2602 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2607⟩ := rd2606.sload (by native_decide) (by evm_ov)
  have rd2612 := evm_run rd2607 with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd2613⟩ := rd2612.sload (by native_decide) (by evm_ov)
  have rd2661 := evm_run rd2613 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperBidsDecodePushMask2627
      (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨208⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov)]
  have haddrMaskClean :
      UInt256.land (UInt256.land packed solcAddrMask) solcAddrMask =
        UInt256.land packed solcAddrMask := by
    exact solcAddrMask_clean (solcAddrMask_result_canonical packed)
  have hticClean :
      UInt256.land
          (UInt256.land (UInt256.div packed uint48Divisor20) uint48Mask) uint48Mask =
        UInt256.land (UInt256.div packed uint48Divisor20) uint48Mask := by
    exact uint48Mask_clean (uint48Mask_bound (UInt256.div packed uint48Divisor20))
  have hendClean :
      UInt256.land
          (UInt256.land (UInt256.div packed uint48Divisor26) uint48Mask) uint48Mask =
        UInt256.land (UInt256.div packed uint48Divisor26) uint48Mask := by
    exact uint48Mask_clean (uint48Mask_bound (UInt256.div packed uint48Divisor26))
  have hticComm :
      UInt256.land uint48Mask (UInt256.div packed uint48Divisor20) =
        UInt256.land (UInt256.div packed uint48Divisor20) uint48Mask := by
    exact u256_land_comm _ _
  have rd509 := rd2661.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by
    simpa [base, packed, bidsBaseWord, bidsPackedSlot, bidPackedSlotOfWord, bidsBidWord,
      bidsLotWord, bidsPackedWord, bidsGuyWord, bidsTicWord, bidsEndWord, bidsUsrWord,
      bidsGalWord, bidsTabWord, flipperUint48Offset20Word, flipperUint48Offset26Word,
      hmask160, hmask160', hdiv160, hdiv208, haddrMaskClean, hticClean, hendClean,
      hticComm, u256_land_comm, flipperSlotWord]
      using rd509⟩

theorem flipperBidsX_return {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {k C : ℕ}
    (h : RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨509⟩
      [bidsTabWord σ I, bidsGalWord σ I, bidsUsrWord σ I, bidsEndWord σ I,
        bidsTicWord σ I, bidsGuyWord σ I, bidsLotWord σ I, bidsBidWord σ I,
        ⟨509⟩, sel]
      (bidsHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flipperBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (bidsReturnData σ I) := by
  have hprefixStore :
      (UInt256.toByteArray (bidsBidWord σ I)).write 0 (bidsHashMem I) 128 32 =
        bidsReturnMem1 σ I := by
    unfold bidsReturnMem1 bidsReturnPrefix bidsHashMem
    rw [toByteArray_write_eq _ _ _ (by rw [solcMappingHashMem_size]; omega)
      (by rw [solcMappingHashMem_size]; exact lt_usize _ (by norm_num))]
    rw [show 128 - (solcMappingHashMem (baseSlot := ⟨1⟩) (bidsId I)).size = 32 by
      rw [solcMappingHashMem_size]]
  have hstore2 :
      (UInt256.toByteArray (bidsLotWord σ I)).write 0 (bidsReturnMem1 σ I) 160 32 =
        bidsReturnMem2 σ I := by
    unfold bidsReturnMem2
    rw [toByteArray_write_eq _ _ _ (by rw [bidsReturnMem1_size])
      (by rw [bidsReturnMem1_size]; exact lt_usize _ (by norm_num))]
    rw [zeroes_zero (n := 160 - (bidsReturnMem1 σ I).size) (by
      rw [bidsReturnMem1_size])]
    simp [ByteArray.empty_append]
  have hstore3 :
      (UInt256.toByteArray (bidsGuyWord σ I)).write 0 (bidsReturnMem2 σ I) 192 32 =
        bidsReturnMem3 σ I := by
    unfold bidsReturnMem3
    rw [toByteArray_write_eq _ _ _ (by rw [bidsReturnMem2_size])
      (by rw [bidsReturnMem2_size]; exact lt_usize _ (by norm_num))]
    rw [zeroes_zero (n := 192 - (bidsReturnMem2 σ I).size) (by
      rw [bidsReturnMem2_size])]
    simp [ByteArray.empty_append]
  have hstore4 :
      (UInt256.toByteArray (bidsTicWord σ I)).write 0 (bidsReturnMem3 σ I) 224 32 =
        bidsReturnMem4 σ I := by
    unfold bidsReturnMem4
    rw [toByteArray_write_eq _ _ _ (by rw [bidsReturnMem3_size])
      (by rw [bidsReturnMem3_size]; exact lt_usize _ (by norm_num))]
    rw [zeroes_zero (n := 224 - (bidsReturnMem3 σ I).size) (by
      rw [bidsReturnMem3_size])]
    simp [ByteArray.empty_append]
  have hstore5 :
      (UInt256.toByteArray (bidsEndWord σ I)).write 0 (bidsReturnMem4 σ I) 256 32 =
        bidsReturnMem5 σ I := by
    unfold bidsReturnMem5
    rw [toByteArray_write_eq _ _ _ (by rw [bidsReturnMem4_size])
      (by rw [bidsReturnMem4_size]; exact lt_usize _ (by norm_num))]
    rw [zeroes_zero (n := 256 - (bidsReturnMem4 σ I).size) (by
      rw [bidsReturnMem4_size])]
    simp [ByteArray.empty_append]
  have hstore6 :
      (UInt256.toByteArray (bidsUsrWord σ I)).write 0 (bidsReturnMem5 σ I) 288 32 =
        bidsReturnMem6 σ I := by
    unfold bidsReturnMem6
    rw [toByteArray_write_eq _ _ _ (by rw [bidsReturnMem5_size])
      (by rw [bidsReturnMem5_size]; exact lt_usize _ (by norm_num))]
    rw [zeroes_zero (n := 288 - (bidsReturnMem5 σ I).size) (by
      rw [bidsReturnMem5_size])]
    simp [ByteArray.empty_append]
  have hstore7 :
      (UInt256.toByteArray (bidsGalWord σ I)).write 0 (bidsReturnMem6 σ I) 320 32 =
        bidsReturnMem7 σ I := by
    unfold bidsReturnMem7
    rw [toByteArray_write_eq _ _ _ (by rw [bidsReturnMem6_size])
      (by rw [bidsReturnMem6_size]; exact lt_usize _ (by norm_num))]
    rw [zeroes_zero (n := 320 - (bidsReturnMem6 σ I).size) (by
      rw [bidsReturnMem6_size])]
    simp [ByteArray.empty_append]
  have hstore8 :
      (UInt256.toByteArray (bidsTabWord σ I)).write 0 (bidsReturnMem7 σ I) 352 32 =
        bidsReturnMem σ I := by
    rw [toByteArray_write_eq _ _ _ (by rw [bidsReturnMem7_size])
      (by rw [bidsReturnMem7_size]; exact lt_usize _ (by norm_num))]
    rw [zeroes_zero (n := 352 - (bidsReturnMem7 σ I).size) (by
      rw [bidsReturnMem7_size])]
    simp
    rw [bidsReturnMem, bidsReturnMem7, bidsReturnMem6, bidsReturnMem5, bidsReturnMem4,
      bidsReturnMem3, bidsReturnMem2, bidsReturnMem1, bidsReturnData]
    simp only [ByteArray.append_assoc]
  have haddrClean :
      UInt256.land solcAddrMask (bidsGuyWord σ I) = bidsGuyWord σ I := by
    rw [u256_land_comm]
    exact solcAddrMask_clean (solcAddrMask_result_canonical (bidsPackedWord σ I))
  have hticClean : UInt256.land uint48Mask (bidsTicWord σ I) = bidsTicWord σ I := by
    rw [u256_land_comm]
    exact uint48Mask_clean
      (uint48Mask_bound (UInt256.div (bidsPackedWord σ I) uint48Divisor20))
  have hendClean : UInt256.land uint48Mask (bidsEndWord σ I) = bidsEndWord σ I := by
    rw [u256_land_comm]
    exact uint48Mask_clean
      (uint48Mask_bound (UInt256.div (bidsPackedWord σ I) uint48Divisor26))
  have husrClean :
      UInt256.land solcAddrMask (bidsUsrWord σ I) = bidsUsrWord σ I := by
    rw [u256_land_comm]
    exact solcAddrMask_clean
      (solcAddrMask_result_canonical
        (flipperSlotWord (bidsBaseWord I + (⟨3⟩ : UInt256)) σ I))
  have hgalClean :
      UInt256.land solcAddrMask (bidsGalWord σ I) = bidsGalWord σ I := by
    rw [u256_land_comm]
    exact solcAddrMask_clean
      (solcAddrMask_result_canonical
        (flipperSlotWord (bidsBaseWord I + (⟨4⟩ : UInt256)) σ I))
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd510 := h.jumpdest (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd513 := evm_run rd510 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have rd514 := rd513.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
    (solcMappingHashMem_mload64 ⟨1⟩ (bidsId I)) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd515 := rd514.swap9 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd516 := rd515.dup10 (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd517 := rd516.mstore 6 (bidsReturnMem1 σ I) (UInt256.ofNat 5)
    (by native_decide) mem_cost hprefixStore (by native_decide) (by evm_ov)
  have rd524 := evm_run rd517 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup10 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap8 (by native_decide) (by evm_ov)]
  have rd525 := rd524.mstore 3 (bidsReturnMem2 σ I) (UInt256.ofNat 6)
    (by native_decide) mem_cost hstore2 (by native_decide) (by evm_ov)
  have rd539 := evm_run rd525 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap6 (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw dup9 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [hmask160] at rd539
  rw [haddrClean] at rd539
  have rd540 := rd539.mstore 3 (bidsReturnMem3 σ I) (UInt256.ofNat 7)
    (by native_decide) mem_cost hstore3 (by native_decide) (by evm_ov)
  have rd554 := evm_run rd540 with [
    raw pushConst uint48Mask
      (show Operation.POp.PUSH6 ≠ Operation.POp.PUSH0 by native_decide)
      flipperBidsDecodePushMask540
      (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by native_decide) (by evm_ov),
    raw dup10 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [hticClean] at rd554
  have rd555 := rd554.mstore 3 (bidsReturnMem4 σ I) (UInt256.ofNat 8)
    (by native_decide) mem_cost hstore4 (by native_decide) (by evm_ov)
  have rd563 := evm_run rd555 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [hendClean] at rd563
  have rd564 := rd563.mstore 3 (bidsReturnMem5 σ I) (UInt256.ofNat 9)
    (by native_decide) mem_cost hstore5 (by native_decide) (by evm_ov)
  have rd570 := evm_run rd564 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [husrClean] at rd570
  have rd571 := rd570.mstore 3 (bidsReturnMem6 σ I) (UInt256.ofNat 10)
    (by native_decide) mem_cost hstore6 (by native_decide) (by evm_ov)
  have rd577 := evm_run rd571 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨192⟩ (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  rw [hgalClean] at rd577
  have rd578 := rd577.mstore 3 (bidsReturnMem7 σ I) (UInt256.ofNat 11)
    (by native_decide) mem_cost hstore7 (by native_decide) (by evm_ov)
  have rd582 := evm_run rd578 with [
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov)]
  have rd583 := rd582.mstore 3 (bidsReturnMem σ I) (UInt256.ofNat 12)
    (by native_decide) mem_cost hstore8 (by native_decide) (by evm_ov)
  have rd592 := evm_run rd583 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by native_decide) mem_cost
      (bidsReturnMem_mload64 σ I) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push2 ⟨256⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  exact rd592.ret 0 (bidsReturnData σ I) (by native_decide) mem_cost
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show (((⟨256⟩ : UInt256) + (⟨128⟩ : UInt256).sub ⟨128⟩).toNat) = 256 from by
          native_decide]
      exact bidsReturnMem_read128_256 σ I)
    (by evm_ov)

theorem flipperBidsBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 1))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 1) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some bidsTransition :=
    flipperDispatchBids hsel
  have hreach := flipperReachBidsBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := flipperDecode_bids_ok (I := I) hsz36
    obtain ⟨_, _, hdecoded⟩ := flipperBidsX_decoded (g := Sat256.ofUInt256 g)
      hsz36 hsize hreach
    obtain ⟨_, _, hloaded⟩ := flipperBidsX_loadStruct hdecoded
    have hret := flipperBidsX_return hloaded
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (bidsLocals I)
          bidsTransition.body
          (.returned { contract := contract, locals := bidsLocals I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some (bidsReturnValues σ_solm I))) := by
      exact flipperBidsSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv
    have hslot0 :
        flipperSlotWord (bidsBaseWord I) σ_evm I =
          flipperSlotWord (bidsBaseWord I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (bidsBaseWord I) ⟨0⟩
    have hslot1 :
        flipperSlotWord (bidsBaseWord I + ⟨1⟩) σ_evm I =
          flipperSlotWord (bidsBaseWord I + ⟨1⟩) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (bidsBaseWord I + (⟨1⟩ : UInt256)) ⟨0⟩
    have hslot2 :
        flipperSlotWord (bidsPackedSlot I) σ_evm I =
          flipperSlotWord (bidsPackedSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (bidsPackedSlot I) ⟨0⟩
    have hslot3 :
        flipperSlotWord (bidsBaseWord I + ⟨3⟩) σ_evm I =
          flipperSlotWord (bidsBaseWord I + ⟨3⟩) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (bidsBaseWord I + (⟨3⟩ : UInt256)) ⟨0⟩
    have hslot4 :
        flipperSlotWord (bidsBaseWord I + ⟨4⟩) σ_evm I =
          flipperSlotWord (bidsBaseWord I + ⟨4⟩) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (bidsBaseWord I + (⟨4⟩ : UInt256)) ⟨0⟩
    have hslot5 :
        flipperSlotWord (bidsBaseWord I + ⟨5⟩) σ_evm I =
          flipperSlotWord (bidsBaseWord I + ⟨5⟩) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner
        (bidsBaseWord I + (⟨5⟩ : UInt256)) ⟨0⟩
    have hval :
        some (bidsReturnValues σ_solm I) = some (bidsReturnValues σ_evm I) := by
      simp [bidsReturnValues, bidsBidWord, bidsLotWord, bidsGuyWord, bidsTicWord,
        bidsEndWord, bidsUsrWord, bidsGalWord, bidsTabWord, bidsPackedWord,
        flipperUint48Offset20Word, flipperUint48Offset26Word, hslot0, hslot1,
        hslot2, hslot3, hslot4, hslot5]
    have henc :
        returnEquiv (bidsReturnData σ_evm I) (some (bidsReturnValues σ_evm I))
          bidsTransition.returnType := by
      exact returnEquiv.returned rfl (bidsReturnEncoding σ_evm I)
    exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc
  · have hshort : I.calldata.size < 36 := by
      omega
    exact (flipperBidsX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (flipperDecode_bids_none_short hsz4 hshort)

end Benchmarks.Dss.Flipper
