import Benchmarks.WETH9.Opcodes
import Benchmarks.WETH9.Storage

/-!
# WETH9 `deposit()` / fallback refinement (scaffold — trace pending)

`deposit` (and the payable fallback, and any calldata that does not select a named function) credits
`balanceOf[msg.sender] += msg.value` and emits `Deposit` (`LOG2`).  It is dispatched three ways, all
converging on the runtime body at pc 760:
* the `deposit()` selector (`weth9DepositBodyCore`, via selector dispatch),
* calldata ≥ 4 that matches no selector (`weth9FallbackBodyCore`, via fallback dispatch),
* calldata < 4 (`weth9ShortFallbackBodyCore`, via fallback dispatch; the prologue short-circuits).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.WETH9

/-- The Solm `deposit()` body credits `balanceOf[msg.sender] += msg.value` and falls through
    (no explicit return).  The unchecked `+=` truncates on store to the wrapping word. -/
theorem weth9DepositBodyReturnsSplit {σ σ₀ A I} {g : Sat256} :
    (ExecTransitionBody config contract (initState σ σ₀ g A I) ∅
      depositTransition.body
      (.returned { contract := contract, locals := ∅ }
        (Solm.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner (callerBalSlot I)
          (UInt256.add (Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
            (callerBalSlot I)) I.weiValue)) none)) ∧
      (I.perm = false → ExecTransitionBody config contract (initState σ σ₀ g A I) ∅
        depositTransition.body .staticViolation) := by
  have hsrc : (initState σ σ₀ g A I).executionEnv = I := by simp [initState]
  have hco : (initState σ σ₀ g A I).executionEnv.codeOwner = I.codeOwner := by rw [hsrc]
  have hcv : (initState σ σ₀ g A I).executionEnv.weiValue = I.weiValue := by rw [hsrc]
  set evm := initState σ σ₀ g A I with hevm
  have heval : evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .add (.storage (balanceOfRef sender)) (.env .callvalue)) =
        .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm I.codeOwner (callerBalSlot I)).toNat
          + Int.ofNat I.weiValue.toNat)) := by
    show evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .add (.storage (balanceOfRef sender)) (.env .callvalue)) = _
    have hlhs := evalCallerBal evm I ∅ hsrc (by simp)
    rw [hco] at hlhs
    simp only [evalExpr?, hlhs, envValue, hcv, EvalResult.bind, bind, pure, evalBinaryOp?]
    rfl
  have hassign : assignStorageRef? config { contract := contract, locals := ∅ } evm
      .storage (balanceOfRef sender)
      (.int (Int.ofNat (Solm.EVM.storageLoad evm I.codeOwner (callerBalSlot I)).toNat
        + Int.ofNat I.weiValue.toNat)) =
      .ok ({ contract := contract, locals := ∅ },
        Solm.EVM.storageStore evm I.codeOwner (callerBalSlot I)
          (UInt256.add (Solm.EVM.storageLoad evm I.codeOwner (callerBalSlot I)) I.weiValue)) := by
    refine assignStorageRef_storage_scalar_value
      (er := callerBalRef I) (ty := uint256St) (loc := wordLoc (callerBalSlot I))
      (hbase := by simp [balanceOfRef]) ?_ ?_ (by rfl) (by trivial) ?_
    · simp only [balanceOfRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
        evalExpr?, envValue, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
    · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]
    · rw [show wordLoc (callerBalSlot I) = uint256Loc (callerBalSlot I) from rfl,
        storageLocStore_uint256_int, hco, wordOfInt_add_words]
  constructor
  · exact ExecFuncBody.execBlockOK (assignStorageBlock heval hassign)
  · intro hperm
    exact ExecFuncBody.execBlockStatic (ExecBlock.consStatic
      (ExecStmt.assignStatic heval hassign (by simpa [evm, initState] using hperm)))

theorem weth9DepositBodyReturns {σ σ₀ A I} {g : Sat256} :
    ExecTransitionBody config contract (initState σ σ₀ g A I) ∅
      depositTransition.body
      (.returned { contract := contract, locals := ∅ }
        (Solm.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner (callerBalSlot I)
          (UInt256.add (Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
            (callerBalSlot I)) I.weiValue)) none) :=
  weth9DepositBodyReturnsSplit.1

/-! ## EVM trace (store portion — the caller-keyed keccak + load-add-store) -/

theorem callerBalSlot_eq (I : ExecutionEnv) :
    callerBalSlot I = solcMappingSlot ⟨3⟩ (solcSourceWord I) := by
  unfold callerBalSlot balanceOfSlot solcMappingSlot mapSlot solcSourceWord
  rw [keyValueToWord_address]

/-- Reach the deposit body entry (pc 760) from the shared handler (pc 156). -/
theorem weth9DepositReachBody {σ σ₀ A I} {R : List UInt256} {g : Sat256} {k C : ℕ}
    (hR : R.length ≤ 1)
    (h : RD weth9Bytecode I g (initState σ σ₀ g A I) ⟨156⟩ R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD weth9Bytecode I g (initState σ σ₀ g A I) ⟨760⟩ (⟨164⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have h760 := h.jumpdest (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.push2 ⟨164⟩ (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.push2 ⟨760⟩ (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.jump (by native_decide) (by jump_dest) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
  exact ⟨_, _, h760⟩

/-- Deposit store: from pc 760 with `[164, w]`, run the caller-keyed keccak + load-add-store,
    reaching pc 789 with `balanceOf[msg.sender]` credited by `msg.value` (wrapping). -/
theorem weth9DepositStoreSplit {σ σ₀ A I} {R : List UInt256} {g : Sat256} {k C : ℕ}
    (hR : R.length ≤ 1)
    (h : RD weth9Bytecode I g (initState σ σ₀ g A I) ⟨760⟩ (⟨164⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
      ∃ k' C', RD weth9Bytecode I g (initState σ σ₀ g A I) ⟨789⟩
        (I.weiValue :: ⟨32⟩ :: ⟨64⟩ :: solcSourceWord I :: ⟨164⟩ :: R)
        (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
        (sstoreAccountMap I.codeOwner σ (callerBalSlot I)
          (I.weiValue + solcSlotWord σ I (callerBalSlot I))) k' C') ∨
      (I.perm = false ∧ RDstatic weth9Bytecode g (initState σ σ₀ g A I)) := by
  have h779 := h.jumpdest (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.caller (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.push1 ⟨0⟩ (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.dup2 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.dup2 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.mstore 0 (wordAt0Mem (solcSourceWord I) solcFreePtrMem) (UInt256.ofNat 3)
        (by native_decide) mem_cost (by rfl) (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.push1 ⟨3⟩ (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.push1 ⟨32⟩ (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap1 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.dup2 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.mstore 0 (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem) (UInt256.ofNat 3)
        (by native_decide) mem_cost
        (by rw [show (⟨32⟩ : UInt256).toNat = 32 from rfl]; rfl) (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.push1 ⟨64⟩ (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap2 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.dup3 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap1 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
  have hkecval : UInt256.ofNat (fromByteArrayBigEndian
      (KEC ((twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem).readWithPadding 0 64)))
        = callerBalSlot I := by
    rw [twoWordHashMem_solcMappingSlot ⟨3⟩ (solcSourceWord I) solcFreePtrMem_size]
    exact (callerBalSlot_eq I).symm
  have h780 := h779.keccak256 0 (callerBalSlot I) (UInt256.ofNat 3)
      (by native_decide) mem_cost hkecval (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.dup1 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
  obtain ⟨_, _, h782⟩ := h780.sload (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
  have h788 := h782.callvalue (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap1 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.dup2 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.add (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap1 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap2 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
  have hstoreDec : decode weth9Bytecode ⟨788⟩ = some (.SSTORE, none) := by
    native_decide
  by_cases hperm : I.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      h788.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, h789⟩ := h788.sstore hperm hstoreDec (by evm_ov)
  exact ⟨_, _, h789⟩

/-- The Deposit LOG2 tail (789→STOP): terminates with empty output (the log is invisible to `RD`). -/
theorem weth9DepositLog {σ σ₀ A I acc} {R : List UInt256} {g : Sat256} {k C : ℕ}
    (hperm : I.perm = true) (hR : R.length ≤ 1)
    (h : RD weth9Bytecode I g (initState σ σ₀ g A I) ⟨789⟩
      (I.weiValue :: ⟨32⟩ :: ⟨64⟩ :: solcSourceWord I :: ⟨164⟩ :: R)
      (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      acc k C) :
    RDret weth9Bytecode g (initState σ σ₀ g A I) acc ByteArray.empty := by
  have hpermI : (initState σ σ₀ g A I).executionEnv.perm = true := by
    simp [initState]; exact hperm
  have hread64 : (twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem).readWithPadding 64 32
      = UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64
  set thm := twoWordHashMem (solcSourceWord I) ⟨3⟩ solcFreePtrMem with hthm
  have hthmsize : thm.size = 96 := by rw [hthm, twoWordHashMem_size_96 _ _ solcFreePtrMem_size]
  have hmload64 : (if (⟨64⟩ : UInt256).toNat ≥ thm.size
      then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian (thm.readWithPadding
        (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    rw [if_neg (by rw [hthmsize]; decide), show (⟨64⟩ : UInt256).toNat = 64 from rfl, hthm, hread64]
    native_decide
  have hgap32 : (128 : ℕ) - thm.size = 32 := by rw [hthmsize]
  set dlm := (UInt256.toByteArray I.weiValue).write 0 thm 128 32 with hdlm
  have hgapeq : dlm = thm ++ ByteArray.zeroes 32
      ++ UInt256.toByteArray I.weiValue := by
    rw [hdlm, toByteArray_write_eq _ _ _ (by rw [hthmsize]; omega)
      (by rw [hgap32]; exact lt_usize 32 (by norm_num)), hgap32]
  have hcvsize : (UInt256.toByteArray I.weiValue).size = 32 :=
    (UInt256.toByteArrayWithSizeProof I.weiValue).2
  have hzsize : (ByteArray.zeroes 32).size = 32 := by
    rw [ByteArray_zeroes_size]
  have hdlmsize : dlm.size = 160 := by
    rw [hgapeq, ByteArray.size_append, ByteArray.size_append, hthmsize, hzsize, hcvsize]
  have hdlmread64 : dlm.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    have h1 : dlm.readWithPadding 64 32 = dlm.extract 64 (64 + 32) :=
      readWithPadding_eq_extract _ 64 (by rw [hdlmsize]; omega)
    have h2 : (64 : ℕ) + 32 ≤ (thm ++ ByteArray.zeroes 32).size := by
      rw [ByteArray.size_append, hthmsize, hzsize]; omega
    have h3 : (64 : ℕ) + 32 ≤ thm.size := by rw [hthmsize]
    rw [h1, hgapeq, extract_append_left _ _ 64 (64 + 32) h2,
      extract_append_left _ _ 64 (64 + 32) h3,
      ← readWithPadding_eq_extract thm 64 h3, hthm, hread64]
  have hdlm_mload64 : (if (⟨64⟩ : UInt256).toNat ≥ dlm.size
      then ⟨0⟩ else UInt256.ofNat (fromByteArrayBigEndian (dlm.readWithPadding
        (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    rw [if_neg (by rw [hdlmsize]; decide), show (⟨64⟩ : UInt256).toNat = 64 from rfl, hdlmread64]
    native_decide
  have h837 := h.dup3 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost hmload64 (by native_decide)
        (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap1 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.dup2 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.mstore 6 dlm (UInt256.ofNat 5) (by native_decide) mem_cost
        (by rw [hdlm, show (⟨128⟩ : UInt256).toNat = 128 from rfl]) (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap2 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost hdlm_mload64 (by native_decide)
        (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.pushConst (⟨102222681472383059465863322013072701928378550215632170212813623808969952268444⟩ : UInt256)
        (op := .PUSH32) (width := 32) (by decide) (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap3 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.dup2 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap1 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.sub (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap1 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap2 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.add (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.swap1 (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
  have h838 := RD.log2 0 (UInt256.ofNat 5) h837 (by native_decide) hpermI mem_cost (by native_decide)
    (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
  exact (h838.jump (by native_decide) (by jump_dest) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)).jumpdest (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)
    |>.stop (by native_decide) (by (try simp only [List.length_cons, List.length_singleton, List.length_nil]); omega)

/-- The full deposit body EVM run (shared handler pc 156 → `STOP`): credits `balanceOf[msg.sender]`
    by `msg.value` and halts with empty output. -/
theorem weth9DepositXSplit {σ σ₀ A I} {R : List UInt256} {g : Sat256} {k C : ℕ}
    (hR : R.length ≤ 1)
    (h : RD weth9Bytecode I g (initState σ σ₀ g A I) ⟨156⟩ R
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    (I.perm = true ∧
      RDret weth9Bytecode g (initState σ σ₀ g A I)
        (sstoreAccountMap I.codeOwner σ (callerBalSlot I)
          (I.weiValue + solcSlotWord σ I (callerBalSlot I))) ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic weth9Bytecode g (initState σ σ₀ g A I)) := by
  obtain ⟨_, _, h760⟩ := weth9DepositReachBody hR h
  rcases weth9DepositStoreSplit hR h760 with
    ⟨hperm, _, _, h789⟩ | ⟨hperm, hstatic⟩
  · exact Or.inl ⟨hperm, weth9DepositLog hperm hR h789⟩
  · exact Or.inr ⟨hperm, hstatic⟩

theorem weth9SelectorDispatchDeposit {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 9)) :
    selectorDispatchMsg contract I.calldata = some depositTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 9 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes, weth9TotalSupplySelectorBytes,
    weth9TransferFromSelectorBytes, weth9WithdrawSelectorBytes, weth9DecimalsSelectorBytes,
    weth9BalanceOfSelectorBytes, weth9SymbolSelectorBytes, weth9TransferSelectorBytes,
    weth9DepositSelectorBytes]
  native_decide

/-- The deposit source body's post-state accountMap is the caller-keyed store (commuted). -/
theorem weth9DepositBody_accountMap {σ σ₀ A I} {g : Sat256} :
    (Solm.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner (callerBalSlot I)
        (UInt256.add (Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
          (callerBalSlot I)) I.weiValue)).accountMap
      = sstoreAccountMap I.codeOwner σ (callerBalSlot I)
          (UInt256.add (solcSlotWord σ I (callerBalSlot I)) I.weiValue) := by
  have h : Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner (callerBalSlot I)
      = solcSlotWord σ I (callerBalSlot I) := by
    simp [solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, initState,
      Ethereum.Account.lookupStorage]
  rw [storageStore_accountMap, show (initState σ σ₀ g A I).accountMap = σ from rfl, h]

/-- The `deposit()` selector dispatches (payable — any callvalue) to the deposit body. -/
theorem weth9DepositBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 9)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 9) (by native_decide) hsel
  obtain ⟨_, _, h156⟩ := weth9ReachDepositEntry (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  rcases weth9DepositXSplit (g := Sat256.ofUInt256 g) (by simp) h156 with
    ⟨_hperm, hX⟩ | ⟨hperm, hstatic⟩
  swap
  · exact weth9ReEquivExecStatic hcode hstatic (weth9SelectorDispatchDeposit hsel)
      (decodeCalldataWithMode_empty_ok hsz4) (weth9DepositBodyReturnsSplit.2 hperm)
  have hbody := weth9DepositBodyReturns (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g)
  have hvaleq : I.weiValue + solcSlotWord σ I (callerBalSlot I)
      = UInt256.add (solcSlotWord σ I (callerBalSlot I)) I.weiValue := by
    exact u256_add_comm _ _
  refine weth9ReEquivExecGen (t := depositTransition) hcode hX
    (weth9SelectorDispatchDeposit hsel) ?_ hbody ?_ ?_
  · show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
    exact decodeCalldataWithMode_empty_ok hsz4
  · rw [hvaleq, weth9DepositBody_accountMap]
  · exact returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide)

/-! ## Fallback dispatch (no selector / receive) -/

/-- `RDret ⇒ fallback execution`: the payable fallback runs (no selector/receive dispatch). -/
theorem weth9ReEquivFallbackGen {cfg : Config} {contract : ContractDecl} {t : TransitionDecl}
    {σ σ₀ A I} {g : Sat256}
    {o : ByteArray} {callargs cs retVal returnConv}
    {acc : AccountMap} {evm'' : EVM.State}
    (hcode : I.code = weth9Bytecode)
    (h : RDret weth9Bytecode g (initState σ σ₀ g A I) acc o)
    (hnosel : selectorDispatchMsg contract I.calldata = none)
    (hnorecv : receiveDispatchMsg contract I.calldata = none)
    (hfb : contract.fallback = some t)
    (hargs : fallbackCallargs I.calldata t.params = some callargs)
    (hret : fallbackReturnConvention t = some returnConv)
    (hbody : ExecTransitionBody cfg contract
              (initState σ σ₀ g A I) callargs t.body
              (.returned cs evm'' retVal))
    (hAccountMap : acc = evm''.accountMap)
    (hRetData : returnDataEquiv o retVal returnConv) :
    runtimeEquivalenceFor cfg contract σ σ₀ g.toUInt256 A I := by
  rcases h with hoog | ⟨s, hX, hsacc⟩
  · exact reEquiv_outOfGas (Xi_error_of_X (g := g.toUInt256) (by
      rw [← hcode] at hoog
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
  · have hxi := Xi_success_of_X (g := g.toUInt256) (by
      rw [← hcode] at hX
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
    have hbody' :
        ExecTransitionBody cfg contract
          (initState σ σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
          callargs t.body (.returned cs evm'' retVal) := by
      simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
    refine runtimeEquivalenceFor.execution rfl
      (solmExec.fallback hnosel hnorecv hfb hargs hret rfl hbody') ?_
    rw [hxi]
    have haccounts : s.accountMap = evm''.accountMap := hsacc.trans hAccountMap
    exact execResultsEquiv.success rfl rfl haccounts hRetData

theorem weth9ReEquivFallbackStatic {cfg : Config} {contract : ContractDecl}
    {t : TransitionDecl} {σ σ₀ A I} {g : Sat256} {callargs returnConv}
    (hcode : I.code = weth9Bytecode)
    (h : RDstatic weth9Bytecode g (initState σ σ₀ g A I))
    (hnosel : selectorDispatchMsg contract I.calldata = none)
    (hnorecv : receiveDispatchMsg contract I.calldata = none)
    (hfb : contract.fallback = some t)
    (hargs : fallbackCallargs I.calldata t.params = some callargs)
    (hret : fallbackReturnConvention t = some returnConv)
    (hbody : ExecTransitionBody cfg contract
      (initState σ σ₀ g A I) callargs t.body .staticViolation) :
    runtimeEquivalenceFor cfg contract σ σ₀ g.toUInt256 A I := by
  apply h.reEquivElim hcode
  intro hstatic
  have hbody' : ExecTransitionBody cfg contract
      (initState σ σ₀ (Sat256.ofUInt256 g.toUInt256) A I)
      callargs t.body .staticViolation := by
    simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hbody
  refine runtimeEquivalenceFor.execution rfl
    (solmExec.fallback hnosel hnorecv hfb hargs hret rfl hbody') ?_
  rw [hstatic]
  exact execResultsEquiv.staticHalt rfl rfl

/-- Short calldata (`< 4` bytes): the prologue's `calldatasize < 4` guard jumps directly to the
    shared fallback handler (pc 156) with an empty stack. -/
theorem weth9ReachShort156 {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hshort : I.calldata.size < 4) :
    ∃ k C, RD weth9Bytecode I g (initState σ σ₀ g A I) ⟨156⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have h5 := (RD.initState (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    |>.push1 ⟨128⟩ (by native_decide) (by decide)
    |>.push1 ⟨64⟩ (by native_decide) (by decide)
    |>.mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide)
        mem_cost (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
        (by decide) (by decide)
  have h156 := h5
    |>.push1 ⟨4⟩ (by native_decide) (by simp)
    |>.calldatasize (by native_decide) (by simp)
    |>.lt (by native_decide) (by simp)
    |>.pushConst (⟨156⟩ : UInt256) (width := 2) (op := .PUSH2) (by native_decide)
        (by native_decide) (by simp)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hshort) (by jump_dest) (by simp)
  exact ⟨_, _, h156⟩

theorem weth9SelDispatch_none_short {cd : ByteArray} (hshort : cd.size < 4) :
    selectorDispatchMsg contract cd = none := by
  rw [selectorDispatchMsg_eq_dispatchList contract cd]
  exact dispatchList_none_short contract.transitions
    (fun t _ => by rw [selectorOf, ByteArray.size_extract, keccak_size]; decide) hshort

theorem weth9_receive_none {cd : ByteArray} : receiveDispatchMsg contract cd = none := by
  simp [receiveDispatchMsg, contract]

/-- The deposit source body, transported to the fallback: `fallbackTransition.body` is defeq to
    `depositTransition.body`, and `∅` callargs. -/
theorem weth9FallbackBody {σ σ₀ A I} {g : Sat256} :
    ExecTransitionBody config contract (initState σ σ₀ g A I) ∅
      fallbackTransition.body
      (.returned { contract := contract, locals := ∅ }
        (Solm.EVM.storageStore (initState σ σ₀ g A I) I.codeOwner (callerBalSlot I)
          (UInt256.add (Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
            (callerBalSlot I)) I.weiValue)) none) :=
  weth9DepositBodyReturns

/-- The shared connect for a fallback-dispatched deposit run (no-match or short). -/
theorem weth9FallbackConnect {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode)
    (hnosel : selectorDispatchMsg contract I.calldata = none)
    (hX : RDret weth9Bytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (sstoreAccountMap I.codeOwner σ (callerBalSlot I)
        (I.weiValue + solcSlotWord σ I (callerBalSlot I))) ByteArray.empty) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hvaleq : I.weiValue + solcSlotWord σ I (callerBalSlot I)
      = UInt256.add (solcSlotWord σ I (callerBalSlot I)) I.weiValue := by
    exact u256_add_comm _ _
  refine weth9ReEquivFallbackGen (t := fallbackTransition) hcode hX
    hnosel weth9_receive_none rfl rfl rfl weth9FallbackBody ?_ ?_
  · rw [hvaleq, weth9DepositBody_accountMap]
  · exact returnDataEquiv.abi (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide))

theorem weth9FallbackConnectSplit {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode)
    (hnosel : selectorDispatchMsg contract I.calldata = none)
    (hX : (I.perm = true ∧ RDret weth9Bytecode (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (sstoreAccountMap I.codeOwner σ (callerBalSlot I)
        (I.weiValue + solcSlotWord σ I (callerBalSlot I))) ByteArray.empty) ∨
      (I.perm = false ∧ RDstatic weth9Bytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I))) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  rcases hX with ⟨_hperm, hret⟩ | ⟨hperm, hstatic⟩
  · exact weth9FallbackConnect hcode hnosel hret
  · exact weth9ReEquivFallbackStatic hcode hstatic hnosel weth9_receive_none rfl rfl rfl
      (weth9DepositBodyReturnsSplit.2 hperm)

/-- No named selector matches (`calldata ≥ 4`): the binary-search dispatch walks every arm and
    falls through to the shared fallback handler (pc 156) with the selector word on the stack. -/
theorem weth9ReachNoMatch156 {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hsz4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 11 → (weth9SelBytes i == I.calldata.extract 0 4) = false) :
    ∃ k C, RD weth9Bytecode I g (initState σ σ₀ g A I) ⟨156⟩ [weth9SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hmiss (i : ℕ) (hi : i < 11) (c0 c1 c2 c3 : UInt8) (sel : UInt256)
      (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
      (hbytes : weth9SelBytes i = (⟨#[c0, c1, c2, c3]⟩ : ByteArray)) :
      UInt256.eq sel (weth9SelWord I) = ⟨0⟩ := by
    dsimp [weth9SelWord]
    rw [evmSelectorDecode hsz4 c0 c1 c2 c3 sel hsel]
    have hno := hnm i hi
    rw [hbytes] at hno
    simp [hno]
  have hUpper : ∀ j, j < 6 →
      UInt256.eq (armSelNat weth9Bytecode (nthArmPc weth9Bytecode ⟨30⟩ j)) (weth9SelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hmiss 5 (by omega) 0x31 0x3c 0xe5 0x67 _ (by native_decide) rfl
    · exact hmiss 6 (by omega) 0x70 0xa0 0x82 0x31 _ (by native_decide) rfl
    · exact hmiss 7 (by omega) 0x95 0xd8 0x9b 0x41 _ (by native_decide) rfl
    · exact hmiss 8 (by omega) 0xa9 0x05 0x9c 0xbb _ (by native_decide) rfl
    · exact hmiss 9 (by omega) 0xd0 0xe3 0x0d 0xb0 _ (by native_decide) rfl
    · exact hmiss 10 (by omega) 0xdd 0x62 0xed 0x3e _ (by native_decide) rfl
  have hLower : ∀ j, j < 5 →
      UInt256.eq (armSelNat weth9Bytecode (nthArmPc weth9Bytecode ⟨101⟩ j)) (weth9SelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hmiss 0 (by omega) 0x06 0xfd 0xde 0x03 _ (by native_decide) rfl
    · exact hmiss 1 (by omega) 0x09 0x5e 0xa7 0xb3 _ (by native_decide) rfl
    · exact hmiss 2 (by omega) 0x18 0x16 0x0d 0xdd _ (by native_decide) rfl
    · exact hmiss 3 (by omega) 0x23 0xb8 0x72 0xdd _ (by native_decide) rfl
    · exact hmiss 4 (by omega) 0x2e 0x1a 0x7d 0x4d _ (by native_decide) rfl
  obtain ⟨_, _, h19⟩ := weth9ReachSplit (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz4 hsize
  by_cases hroot : UInt256.gt (armSelNat weth9Bytecode ⟨19⟩) (weth9SelWord I) = ⟨0⟩
  · have h30 := RD.selectorSplitNotTakenAuto h19 weth9RootSplitWellFormed hroot (by simp)
    have h96 := h30
      |>.selectorArmNotTakenAuto (weth9UpperArmsWellFormed 0 (by omega)) (hUpper 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (weth9UpperArmsWellFormed 1 (by omega)) (hUpper 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (weth9UpperArmsWellFormed 2 (by omega)) (hUpper 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (weth9UpperArmsWellFormed 3 (by omega)) (hUpper 3 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (weth9UpperArmsWellFormed 4 (by omega)) (hUpper 4 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (weth9UpperArmsWellFormed 5 (by omega)) (hUpper 5 (by omega)) (by simp)
    have h156 := h96.push2 ⟨156⟩ (by native_decide) (by simp)
      |>.jump (by native_decide) (by jump_dest) (by simp)
    exact ⟨_, _, h156⟩
  · have h100 := RD.selectorSplitTakenAuto h19 weth9RootSplitWellFormed hroot (by jump_dest) (by simp)
    have h156 := h100.jumpdest (by native_decide) (by simp)
      |>.selectorArmNotTakenAuto (weth9LowerArmsWellFormed 0 (by omega)) (hLower 0 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (weth9LowerArmsWellFormed 1 (by omega)) (hLower 1 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (weth9LowerArmsWellFormed 2 (by omega)) (hLower 2 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (weth9LowerArmsWellFormed 3 (by omega)) (hLower 3 (by omega)) (by simp)
      |>.selectorArmNotTakenAuto (weth9LowerArmsWellFormed 4 (by omega)) (hLower 4 (by omega)) (by simp)
    exact ⟨_, _, h156⟩

theorem weth9SelDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 11 → (weth9SelBytes i == cd.extract 0 4) = false) :
    selectorDispatchMsg contract cd = none := by
  rw [selectorDispatchMsg_eq_dispatchList contract cd]
  apply dispatchList_none_of_all_ne
  intro t ht
  simp only [contract] at ht
  fin_cases ht
  · rw [selectorOf, weth9NameSelectorBytes]; exact hnm 0 (by decide)
  · rw [selectorOf, weth9ApproveSelectorBytes]; exact hnm 1 (by decide)
  · rw [selectorOf, weth9TotalSupplySelectorBytes]; exact hnm 2 (by decide)
  · rw [selectorOf, weth9TransferFromSelectorBytes]; exact hnm 3 (by decide)
  · rw [selectorOf, weth9WithdrawSelectorBytes]; exact hnm 4 (by decide)
  · rw [selectorOf, weth9DecimalsSelectorBytes]; exact hnm 5 (by decide)
  · rw [selectorOf, weth9BalanceOfSelectorBytes]; exact hnm 6 (by decide)
  · rw [selectorOf, weth9SymbolSelectorBytes]; exact hnm 7 (by decide)
  · rw [selectorOf, weth9TransferSelectorBytes]; exact hnm 8 (by decide)
  · rw [selectorOf, weth9DepositSelectorBytes]; exact hnm 9 (by decide)
  · rw [selectorOf, weth9AllowanceSelectorBytes]; exact hnm 10 (by decide)

/-- Calldata ≥ 4 that matches no named selector runs the payable fallback (the deposit body). -/
theorem weth9FallbackBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 11 → (weth9SelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  obtain ⟨_, _, h156⟩ := weth9ReachNoMatch156 (g := Sat256.ofUInt256 g) hcode hsz4 hsize hnm
  exact weth9FallbackConnectSplit hcode (weth9SelDispatch_none_nomatch hnm)
    (weth9DepositXSplit (g := Sat256.ofUInt256 g) (by simp) h156)

/-- Calldata shorter than a selector runs the payable fallback (the deposit body). -/
theorem weth9ShortFallbackBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 4) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  obtain ⟨_, _, h156⟩ := weth9ReachShort156 (g := Sat256.ofUInt256 g) hcode hshort
  exact weth9FallbackConnectSplit hcode (weth9SelDispatch_none_short hshort)
    (weth9DepositXSplit (g := Sat256.ofUInt256 g) (by simp) h156)

end Benchmarks.WETH9
