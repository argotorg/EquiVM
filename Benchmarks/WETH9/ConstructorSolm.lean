import Benchmarks.WETH9.ConstructorClear
import Reasoning.SolmBody
import Reasoning.Constructor
import Solm.Equiv

/-!
# WETH9 constructor — Solm side

The Solm constructor body is `nonpayable ++ [assign name, assign symbol, assign decimals]`.  On a
zero-value call it stores the two compact short strings (`name`/`symbol`) and the `decimals` byte;
on a nonzero-value call the leading `require(msg.value == 0)` reverts the whole body.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.WETH9

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! ## The `decimals` byte-0 store word -/

theorem weth9DecimalsStoreWord (w : UInt256) :
    UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨18⟩ =
      UInt256.ofNat (18 + 256 * (w.toNat / 256)) := by
  apply u256_inj
  unfold UInt256.lor UInt256.land UInt256.toNat Fin.lor Fin.land
  change (Nat.lor ((Nat.land w.val.val (UInt256.lnot (⟨255⟩ : UInt256)).toNat) % UInt256.size) 18) %
      UInt256.size = (18 + 256 * (w.toNat / 256)) % UInt256.size
  have hlnot : (UInt256.lnot (⟨255⟩ : UInt256)).toNat = 2 ^ 256 - 2 ^ 8 := by native_decide
  rw [hlnot]
  change (Nat.lor ((Nat.land w.toNat (2 ^ 256 - 2 ^ 8)) % UInt256.size) 18) % UInt256.size =
      (18 + 256 * (w.toNat / 256)) % UInt256.size
  have hwlt : w.toNat < 2 ^ 256 := w.val.isLt
  have hland_lt : Nat.land w.toNat (2 ^ 256 - 2 ^ 8) < UInt256.size := by
    rw [natLandClearLow8 w.toNat hwlt]
    exact lt_of_le_of_lt (Nat.div_mul_le_self _ _) w.val.isLt
  rw [Nat.mod_eq_of_lt hland_lt, natLandClearLow8 w.toNat hwlt, show (256 : Nat) = 2 ^ 8 by norm_num,
    nat_lor_comm, nat_lor_shift_add 18 (w.toNat / 2 ^ 8) 8 (by norm_num),
    Nat.mul_comm (w.toNat / 2 ^ 8) (2 ^ 8)]

theorem weth9DecimalsStoreWord_toNat (w : UInt256) :
    (UInt256.lor (UInt256.land w (UInt256.lnot ⟨255⟩)) ⟨18⟩).toNat = 18 + 256 * (w.toNat / 256) := by
  rw [weth9DecimalsStoreWord]
  refine ulit_toNat' _ ?_
  have hlt : w.toNat < 2 ^ 256 := w.val.isLt
  have hsz : UInt256.size = 2 ^ 256 := rfl
  have hdiv : w.toNat / 256 < 2 ^ 248 := by
    apply Nat.div_lt_of_lt_mul; rw [show 256 * 2 ^ 248 = 2 ^ 256 by norm_num]; omega
  omega

theorem weth9DecimalsStore (evm : EVM.State) :
    storageLocStore evm (uint8Loc ⟨2⟩) (.int 18) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
        (UInt256.lor (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
          (UInt256.lnot ⟨255⟩)) ⟨18⟩)) := by
  unfold storageLocStore storageLocWriteWord uint8Loc
  simp only [valueToWord, wordOfInt_nonneg 18 (by norm_num), bind, Option.bind, pure]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (1 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (1 : Fin 33).val) _) =
        (UInt256.lor
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
            (UInt256.lnot ⟨255⟩)) ⟨18⟩).toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (1 : Fin 33).val = 1 from rfl,
    List.take_zero, List.nil_append]
  rw [show List.take 1 (EVM.Word.toBytesLEWithSizeProof (EVM.word (18 : Int).toNat)).1 = [18] by
    native_decide]
  rw [fromBytes'_append, fromBytes'_drop_wordLE]
  simp only [fromBytes']
  rw [weth9DecimalsStoreWord_toNat]
  simp only [List.length_cons, List.length_nil, Nat.zero_add, pow_one, Nat.mul_zero, Nat.add_zero,
    show (8 * 1 : Nat) = 8 from rfl, show (↑(UInt8.toFin 18) : Nat) = 18 from rfl,
    show (2 : Nat) ^ 8 = 256 from rfl]

/-! ## The compact-string (`bytes`/`string`) assignment -/

/-- A `bytes`/`string` storage assignment at a top-level slot resolves through the WETH9 write hook
    to the 0.5.16 clear-then-store on `slotIdx`. -/
theorem weth9SolmAssignBytes (evm : EVM.State) (frame : Frame) (slotRef : StorageRef)
    (slotIdx : UInt256) (bs : ByteArray)
    (hbase : frame.locals.get? slotRef.base = none)
    (her : evalStorageRef config frame evm slotRef = .ok { base := slotRef.base, steps := [] })
    (hty : storageTypeAt? frame.contract.storage { base := slotRef.base, steps := [] } = some .string)
    (hlen : storageLayoutRaw { base := slotRef.base, steps := [.length] } evm =
      some (bytesLikeLengthLoc slotIdx evm))
    (hsize : bs.size < 32) :
    assignStorageRef? config frame evm .storage slotRef (.bytes bs) =
      .ok (frame,
        Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom evm slotIdx 0
            (solidityBytesDataWordCount
              (weth9DecodeLenWord
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slotIdx)).toNat))
          evm.executionEnv.codeOwner slotIdx (solidityShortBytesWord bs)) := by
  have hbsl : weth9BytesBaseSlotAndLength? storageLayoutRaw { base := slotRef.base, steps := [] } evm =
      .ok (slotIdx,
        (weth9DecodeLenWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slotIdx)).toNat) := by
    rw [weth9BytesBaseSlotAndLength?]
    simp only [List.nil_append, hlen, weth9DecodeBytesLengthHeader_eq,
      show (bytesLikeLengthLoc slotIdx evm).slot = slotIdx from by
        unfold bytesLikeLengthLoc; split <;> rfl]
  have hbytes : weth9WriteBytesValue? storageLayoutRaw { base := slotRef.base, steps := [] } bs evm =
      .ok (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom evm slotIdx 0
          (solidityBytesDataWordCount
            (weth9DecodeLenWord
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slotIdx)).toNat))
        evm.executionEnv.codeOwner slotIdx (solidityShortBytesWord bs)) := by
    rw [weth9WriteBytesValue?, hbsl]
    simp only [hsize, ↓reduceIte, clearSolidityBytesDataWordsFrom_executionEnv]
  have hwrite : writeStorage? config evm { base := slotRef.base, steps := [] } .string (.bytes bs) =
      .ok (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom evm slotIdx 0
          (solidityBytesDataWordCount
            (weth9DecodeLenWord
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slotIdx)).toNat))
        evm.executionEnv.codeOwner slotIdx (solidityShortBytesWord bs)) := by
    simp only [writeStorage?,
      show config.storage.writeValue? { base := slotRef.base, steps := [] } .string (.bytes bs) evm =
        some (weth9WriteBytesValue? storageLayoutRaw { base := slotRef.base, steps := [] } bs evm)
        from rfl, hbytes, storagePrepareResultToEval]
  rw [assignStorageRef?]
  simp only [resolveStorageRef?_ok hbase her hty, bind, EvalResult.bind, pure, hwrite]

/-! ## The Solm constructor final state -/

noncomputable def weth9SolmNameState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evm ⟨0⟩ 0
      (solidityBytesDataWordCount
        (weth9DecodeLenWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)).toNat))
    evm.executionEnv.codeOwner ⟨0⟩ (solidityShortBytesWord (String.toByteArray "Wrapped Ether"))

noncomputable def weth9SolmSymbolState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom (weth9SolmNameState evm) ⟨1⟩ 0
      (solidityBytesDataWordCount
        (weth9DecodeLenWord (Solm.EVM.storageLoad (weth9SolmNameState evm)
          (weth9SolmNameState evm).executionEnv.codeOwner ⟨1⟩)).toNat))
    (weth9SolmNameState evm).executionEnv.codeOwner ⟨1⟩
    (solidityShortBytesWord (String.toByteArray "WETH"))

noncomputable def weth9SolmFinalState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore (weth9SolmSymbolState evm)
    (weth9SolmSymbolState evm).executionEnv.codeOwner ⟨2⟩
    (UInt256.lor (UInt256.land (Solm.EVM.storageLoad (weth9SolmSymbolState evm)
      (weth9SolmSymbolState evm).executionEnv.codeOwner ⟨2⟩) (UInt256.lnot ⟨255⟩)) ⟨18⟩)

/-! ## The constructor body executes / reverts -/

theorem weth9SolmCtorBodyReturns (evm : EVM.State) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (∅ : Store) contract.ctor.body
      (.returned { contract := contract, locals := ∅ } (weth9SolmFinalState evm) none) := by
  refine ExecFuncBody.execBlockOK ?_
  change ExecBlock config { contract := contract, locals := ∅ } evm
    (Stmt.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
      Stmt.assign .storage nameRef (.bytesLit (String.toByteArray "Wrapped Ether")) ::
      Stmt.assign .storage symbolRef (.bytesLit (String.toByteArray "WETH")) ::
      Stmt.assign .storage decimalsRef (.intLit 18) :: []) _
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (value := .bytes (String.toByteArray "Wrapped Ether")) (by unfold evalExpr?; rfl)
      (weth9SolmAssignBytes evm { contract := contract, locals := ∅ } nameRef ⟨0⟩
        (String.toByteArray "Wrapped Ether")
        (by simp) (by simp [evalStorageRef, nameRef, EvalResult.bind, bind, pure])
        (by simp [storageTypeAt?, contract, storageDecls, nameRef]) rfl (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (value := .bytes (String.toByteArray "WETH")) (by unfold evalExpr?; rfl)
      (weth9SolmAssignBytes (weth9SolmNameState evm) { contract := contract, locals := ∅ }
        symbolRef ⟨1⟩ (String.toByteArray "WETH")
        (by simp) (by simp [evalStorageRef, symbolRef, EvalResult.bind, bind, pure])
        (by simp [storageTypeAt?, contract, storageDecls, symbolRef]) rfl (by native_decide))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (value := .int 18) (by unfold evalExpr?; rfl)
      (assignStorageRef_storage_scalar (er := { base := "decimals", steps := [] })
        (ty := uint8St) (loc := uint8Loc ⟨2⟩)
        (by simp) (by simp [evalStorageRef, decimalsRef, EvalResult.bind, bind, pure])
        (by simp [storageTypeAt?, contract, storageDecls, uint8St]) rfl
        (weth9DecimalsStore (weth9SolmSymbolState evm)))) ?_
  exact ExecBlock.nil

theorem weth9SolmCtorExecSuccess
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [] cA gh bl σ σ₀ g A I
      (.returned { contract := contract, locals := ∅ }
        (weth9SolmFinalState (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) none) := by
  refine solmCtorExec.intro
    (evmState := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (argsStore := ∅)
    rfl rfl ?_ ?_
  · simp [contract, constructorDecl]
  · exact weth9SolmCtorBodyReturns _ (by simp only [initState]; exact hwv)

theorem weth9SolmCtorExecReverts
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [] cA gh bl σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (argsStore := ∅)
    rfl rfl ?_ ?_
  · simp [contract, constructorDecl]
  · exact bodyReverts_nonPayable (by simp only [initState]; exact hwv)

end Benchmarks.WETH9
