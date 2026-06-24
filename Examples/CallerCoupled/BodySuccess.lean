import Examples.Caller.Bytecode
import Reasoning.ABI
import Reasoning.EVMWord
import Reasoning.Dispatch
import Reasoning.SolmBody
import Reasoning.Stepping
import Reasoning.Memory
import Reasoning.Solc
import Reasoning.Reach
import Reasoning.ExternalCall
import Reasoning.Refinement

/-!
# Caller coupled-state experiment

This mirrors the Pow coupled proof for the body suffix of `Caller.run`: start after calldata decode
at pc 66 with the Solm non-payable guard already accounted for, then couple the opaque external
call and the storage assignment.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace CallerCoupled

noncomputable section

set_option maxRecDepth 10000

/-- All `callerBytecode` jump targets validated by one tactic. -/
macro "caller_jd" : term => `(by jump_dest)

private abbrev callerContract := Caller.callerContract
private abbrev runTransition := Caller.runTransition
private abbrev addr := Caller.addr
private abbrev uint256 := Caller.uint256
private abbrev callerExternalABI := Caller.callerExternalABI
private abbrev pow2Selector := Caller.pow2Selector

theorem callerDispatch_eq (cd : ByteArray) :
    dispatchMsg callerContract cd
      = if ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == cd.extract 0 4)
        then some runTransition else none :=
  dispatch_eq rfl callerSelectorBytes cd

theorem callerDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg callerContract cd = none :=
  dispatch_none_short rfl callerSelectorBytes rfl h

theorem callerDispatch_none_nomatch {cd : ByteArray}
    (h : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == cd.extract 0 4) = false) :
    dispatchMsg callerContract cd = none :=
  dispatch_none_nomatch rfl callerSelectorBytes h

theorem callerBodyReverts (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody callerConfig callerContract evm locals runTransition.body .reverted :=
  bodyReverts_nonPayable h

theorem callerBodyExtFail (evm : EVM.State) (locals : Solm.Store) {tval : EVM.Address} {nval : ℤ}
    {evm' : EVM.State} {out : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (ht : locals.get? "t" = some (.address tval))
    (hn : locals.get? "n" = some (.int nval))
    (hcall : typedCallViaEVM callerConfig evm (EVM.address tval) "pow2" 0 [.int nval]
              (false, evm', out)) :
    ExecTransitionBody callerConfig callerContract evm locals runTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert
    (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
      (ExecBlock.consRevert (ExecStmt.externalCallFailure ?_ ?_ ?_ hcall)))
  · show evalExpr? callerConfig _ evm (.var "t") = .ok (.address tval)
    simp only [evalExpr?, EvalResult.ofOption, ht]
  · show evalExpr? callerConfig _ evm (.intLit 0) = .ok (.int 0)
    simp only [evalExpr?]; rfl
  · show evalExprs? callerConfig _ evm [.var "n"] = .ok [.int nval]
    simp only [evalExprs?, evalExpr?, EvalResult.ofOption, hn, EvalResult.bind, bind, pure]

theorem callerContains15 : (D_J callerBytecode 0).contains ⟨15⟩ = true := by
  jump_dest
theorem callerContains41 : (D_J callerBytecode 0).contains ⟨41⟩ = true := by
  jump_dest
theorem callerContains45 : (D_J callerBytecode 0).contains ⟨45⟩ = true := by
  jump_dest
theorem callerContains348 : (D_J callerBytecode 0).contains ⟨348⟩ = true := by
  jump_dest
theorem callerContains491 : (D_J callerBytecode 0).contains ⟨491⟩ = true := by
  jump_dest
theorem callerContains203 : (D_J callerBytecode 0).contains ⟨203⟩ = true := by
  jump_dest
theorem callerContains71 : (D_J callerBytecode 0).contains ⟨71⟩ = true := by
  jump_dest
theorem callerContains194 : (D_J callerBytecode 0).contains ⟨194⟩ = true := by
  jump_dest
theorem callerContains297 : (D_J callerBytecode 0).contains ⟨297⟩ = true := by
  jump_dest
theorem callerContains306 : (D_J callerBytecode 0).contains ⟨306⟩ = true := by
  jump_dest
theorem callerContains315 : (D_J callerBytecode 0).contains ⟨315⟩ = true := by
  jump_dest
theorem callerContains325 : (D_J callerBytecode 0).contains ⟨325⟩ = true := by
  jump_dest
theorem callerContains450 : (D_J callerBytecode 0).contains ⟨450⟩ = true := by
  jump_dest
theorem callerContains464 : (D_J callerBytecode 0).contains ⟨464⟩ = true := by
  jump_dest
theorem callerContains504 : (D_J callerBytecode 0).contains ⟨504⟩ = true := by
  jump_dest
theorem callerContains158 : (D_J callerBytecode 0).contains ⟨158⟩ = true := by
  jump_dest
theorem callerContains470 : (D_J callerBytecode 0).contains ⟨470⟩ = true := by
  jump_dest

/-- Address-mask literal (`PUSH20 0xff…ff`). -/
def addrMask : UInt256 := ⟨1461501637330902918203684832716283019655932542975⟩

/-- The decoded calldata address word at offset 4. -/
abbrev callerArg0 (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)

/-- The decoded calldata uint256 word at offset 36. -/
abbrev callerArg1 (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨32⟩ : UInt256).toNat 32)

theorem ueq_self (a : UInt256) : UInt256.eq a a = ⟨1⟩ := by
  have h : UInt256.eq a a = UInt256.ofNat 1 := by simp [UInt256.eq, UInt256.fromBool]
  rw [h]; rfl

noncomputable def callerSelMem : ByteArray :=
  (UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ ⟨1143701499⟩) ⟨224⟩).toByteArray.write 0
    solcFreePtrMem 128 32

noncomputable def callerCalldataMem (I : ExecutionEnv) : ByteArray :=
  (callerArg1 I).toByteArray.write 0 callerSelMem 132 32

noncomputable def callerOutPtr (I : ExecutionEnv) : UInt256 :=
  if (⟨64⟩ : UInt256).toNat ≥ (callerCalldataMem I).size ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩
  then ⟨0⟩
  else UInt256.ofNat (fromByteArrayBigEndian ((callerCalldataMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))

theorem callerSelMem_size : callerSelMem.size = 160 := solcReturnMem_size _

theorem callerSelMem_read64 : callerSelMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  solcReturnMem_read64 _

theorem callerCalldataMem_size (I : ExecutionEnv) : (callerCalldataMem I).size = 164 := by
  unfold callerCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [callerSelMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, callerSelMem_size, toByteArray_size]
  omega

theorem callerCalldataMem_read64 (I : ExecutionEnv) :
    (callerCalldataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold callerCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size]) (by rw [callerSelMem_size]; omega)
        (by omega), callerSelMem_read64]

theorem callerOutPtr_eq (I : ExecutionEnv) : callerOutPtr I = ⟨128⟩ := by
  unfold callerOutPtr
  exact mloadFreePtrValue (by rw [callerCalldataMem_size]; decide) (by decide)
    (callerCalldataMem_read64 I)

theorem callerSelMem_selector : callerSelMem.extract 128 132 = Caller.pow2Selector := by
  rw [show callerSelMem
        = solcReturnMem (UInt256.shiftLeft (UInt256.land ⟨4294967295⟩ ⟨1143701499⟩) ⟨224⟩) from rfl,
      solcReturnMem_eq,
      extract_append_right_window _ _ _ _ (by rw [solcFreePtrMem_pad_size]),
      solcFreePtrMem_pad_size, show (128:ℕ) - 128 = 0 from rfl, show (132:ℕ) - 128 = 4 from rfl,
      toByteArray_eq_toBytesBE]
  native_decide

theorem callerCalldataMem_read128_36 (I : ExecutionEnv) :
    (callerCalldataMem I).readWithPadding 128 36 = Caller.pow2Selector ++ (callerArg1 I).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
        (by rw [callerCalldataMem_size]), callerCalldataMem,
      write32_eq _ callerSelMem 132 (by rw [toByteArray_size]) (by rw [callerSelMem_size]; omega)]
  have hAsz : (callerSelMem.extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, callerSelMem_size]; omega
  have hBsz : ((callerArg1 I).toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]; omega
  have hPsz : (callerSelMem.extract 0 132 ++ (callerArg1 I).toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : (callerArg1 I).toByteArray.extract 0 32 = (callerArg1 I).toByteArray := by
    have h := @ByteArray.extract_zero_size (callerArg1 I).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
      extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega), hAsz,
      extract_prefix _ 132 128 132 (by omega), callerSelMem_selector,
      extract_extract_BA, show (0:ℕ) + 0 = 0 from rfl,
      show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem wordOfInt_ofNat_toNat (a : UInt256) : EVM.wordOfInt (Int.ofNat a.toNat) = a := by
  rw [EVM.wordOfInt, if_neg (by simp)]
  apply u256_inj
  rw [show (Int.ofNat a.toNat).toNat = a.toNat from rfl]
  show a.toNat % EVM.twoPow 256 = a.toNat
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le a.val.isLt (by decide))

theorem callerEncode_eq (I : ExecutionEnv) :
    Caller.callerExternalABI.encode? "pow2" [.int (Int.ofNat (callerArg1 I).toNat)]
      = some ((callerCalldataMem I).readWithPadding 128 36) := by
  rw [callerCalldataMem_read128_36]
  show some (Caller.pow2Selector ++ UInt256.toByteArray (EVM.wordOfInt (Int.ofNat (callerArg1 I).toNat)))
      = some (Caller.pow2Selector ++ (callerArg1 I).toByteArray)
  rw [wordOfInt_ofNat_toNat]

theorem natLandComm (a b : ℕ) : Nat.land a b = Nat.land b a := by
  apply Nat.eq_of_testBit_eq; intro i
  show (a &&& b).testBit i = (b &&& a).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_comm]

theorem uland_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply u256_inj
  show (Fin.land a.val b.val).val = (Fin.land b.val a.val).val
  simp only [Fin.land]; rw [natLandComm]

theorem callerLand_target {I : ExecutionEnv}
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    UInt256.land addrMask (callerArg0 I) = callerArg0 I := by
  have heq : callerArg0 I = UInt256.land (callerArg0 I) addrMask := by
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false, Bool.false_eq_true,
      ↓reduceIte] at hclean
    exact absurd hclean (by decide)
  rw [uland_comm, ← heq]

theorem callerTarget_eq {I : ExecutionEnv}
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    EVM.address (AccountAddress.ofNat (callerArg0 I).toNat)
      = AccountAddress.ofUInt256 (UInt256.land addrMask (callerArg0 I)) := by
  rw [callerLand_target hclean]
  apply Fin.ext
  show (callerArg0 I).toNat % EVM.addressModulus % AccountAddress.size
      = (callerArg0 I).val % AccountAddress.size % AccountAddress.size
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  rfl

theorem wordOfInt_ofNat_eq (k : ℕ) : EVM.wordOfInt (Int.ofNat k) = UInt256.ofNat k := by
  rw [EVM.wordOfInt, if_neg (by simp)]; apply u256_inj
  show (Int.ofNat k).toNat % EVM.twoPow 256 = (UInt256.ofNat k).toNat
  rw [show (Int.ofNat k).toNat = k from rfl, show (UInt256.ofNat k).toNat = k % UInt256.size from rfl,
      show EVM.twoPow 256 = UInt256.size from by decide]

theorem fromBytesLE_roundtrip (w : UInt256) :
    fromBytes' (EVM.Word.toBytesLEWithSizeProof w).1 = w.toNat := by
  show fromBytes' (toBytes' w.val ++ List.replicate (32 - (toBytes' w.val).length) 0) = w.toNat
  rw [fromBytes'_append_zeros, fromBytes'_toBytes']; rfl

theorem callerLocStore (evm' : EVM.State) (k : ℕ) :
    storageLocStore evm'
        { slot := ⟨0⟩, offset := 0, size := 32, hbound := by decide,
          bitOffset := .none,
          type := .int (.uint ⟨256, by decide⟩) } (.int (Int.ofNat k))
      = some (EVM.storageStore evm' evm'.executionEnv.codeOwner ⟨0⟩ (UInt256.ofNat k)) := by
  unfold storageLocStore
  simp only [valueToWord, wordOfInt_ofNat_eq, bind, Option.bind, pure, storageLocWriteWord]
  have hslen := (EVM.Word.toBytesLEWithSizeProof (EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨0⟩)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat k)).2
  congr 2; apply u256_inj
  show fromBytes' (List.take (0:Fin 32).val _ ++ List.take (32:Fin 33).val _
        ++ List.drop ((0:Fin 32).val + (32:Fin 33).val) _) = (UInt256.ofNat k).toNat
  rw [show (0:Fin 32).val = 0 from rfl, show (32:Fin 33).val = 32 from rfl,
      List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by omega), List.append_nil,
      List.take_of_length_le (by omega), fromBytesLE_roundtrip]

theorem callerAssign (evm' : EVM.State) (L : Solm.Store) (k : ℕ) (hbase : L.get? "stored" = none) :
    assignStorageRef? callerConfig { contract := Caller.callerContract, locals := L } evm' .storage
        { base := "stored", steps := [] } (.int (Int.ofNat k))
      = .ok ({ contract := Caller.callerContract, locals := L },
             EVM.storageStore evm' evm'.executionEnv.codeOwner ⟨0⟩ (UInt256.ofNat k)) := by
  have her : evalStorageRef callerConfig { contract := Caller.callerContract, locals := L } evm'
      { base := "stored", steps := [] } = .ok { base := "stored", steps := [] } := by
    simp [evalStorageRef, bind, EvalResult.bind, pure]
  have hty : storageTypeAt? Caller.callerContract.storage { base := "stored", steps := [] } =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := by
    simp [storageTypeAt?, Caller.callerContract]
  have hloc : callerConfig.storage.layout { base := "stored", steps := [] } =
      fun _ => some { slot := ⟨0⟩, offset := 0, size := 32, hbound := (by decide),
                      bitOffset := .none, type := .int (.uint ⟨256, (by decide)⟩) } := rfl
  exact assignStorageRef_storage_scalar hbase her hty hloc (callerLocStore evm' k)

theorem storageStore_accountMap (evm' : EVM.State) (a : AccountAddress) (s v : UInt256) :
    (EVM.storageStore evm' a s v).accountMap = sstoreAccountMap a evm'.accountMap s v := by
  simp only [EVM.storageStore, sstoreAccountMap, State.lookupAccount]
  cases evm'.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount, Account.updateStorage]

theorem storageStore_createdAccounts (evm' : EVM.State) (a : AccountAddress) (s v : UInt256) :
    (EVM.storageStore evm' a s v).createdAccounts = evm'.createdAccounts := by
  simp only [EVM.storageStore, State.lookupAccount]
  cases evm'.accountMap.find? a with
  | none => rfl
  | some acc => simp only [Option.option, State.setAccount]

theorem ofNat_toNat_lt_size (n : ℕ) (h : n < UInt256.size) : (UInt256.ofNat n).toNat = n :=
  ulit_toNat' n h

theorem ofNat_toNat_lt (n : ℕ) (h : n < 2^255) : (UInt256.ofNat n).toNat = n :=
  ofNat_toNat_lt_size n (by simpa [UInt256.size] using (by omega : n < 2^256))

theorem callerL_succ (n : ℕ) (h1 : 32 ≤ n) (h2 : n < UInt256.size) :
    (min (⟨32⟩:UInt256) (UInt256.ofNat n)).toNat = 32 := by
  show (if (⟨32⟩:UInt256) ≤ UInt256.ofNat n then (⟨32⟩:UInt256) else UInt256.ofNat n).toNat = 32
  rw [if_pos (show (⟨32⟩:UInt256) ≤ UInt256.ofNat n from ?_)]
  · rfl
  · show (32:ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl,
      ofNat_toNat_lt_size n h2]
    omega

theorem callerL_rev (n : ℕ) (h : n < 32) :
    (min (⟨32⟩:UInt256) (UInt256.ofNat n)).toNat = n := by
  show (if (⟨32⟩:UInt256) ≤ UInt256.ofNat n then (⟨32⟩:UInt256) else UInt256.ofNat n).toNat = n
  rw [if_neg (show ¬ (⟨32⟩:UInt256) ≤ UInt256.ofNat n from ?_), ofNat_toNat_lt n (by omega)]
  · show ¬ (32:ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl, ofNat_toNat_lt n (by omega)]; omega

theorem write_len_zero (src base : ByteArray) (sa da : ℕ) : src.write sa base da 0 = base := by
  rw [ByteArray.write]; rfl

theorem callerWrite_size (I : ExecutionEnv) (o : ByteArray) (L : ℕ) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (callerCalldataMem I) 128 L).size = 164 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h; rw [write_len_zero]; exact callerCalldataMem_size I
  · rw [write_eq_gen o (callerCalldataMem I) 128 L (by omega) hLo (by rw [callerCalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, callerCalldataMem_size]; omega

theorem callerWrite_read64 (I : ExecutionEnv) (o : ByteArray) (L : ℕ) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (callerCalldataMem I) 128 L).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h; rw [write_len_zero]; exact callerCalldataMem_read64 I
  · rw [write_read_below_gen o (callerCalldataMem I) 128 L 64 (by omega) hLo
      (by rw [callerCalldataMem_size]; omega) (by omega), callerCalldataMem_read64]

theorem callerEvmSelector {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    UInt256.eq ⟨941609360⟩
        (UInt256.shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) ⟨224⟩)
      = if ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == cd.extract 0 4) then ⟨1⟩ else ⟨0⟩ :=
  evmSelectorDecode hsz 0x38 0x1f 0xd1 0x90 ⟨941609360⟩ (by decide)

theorem callerX_callvalue_ne
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push2 ⟨15⟩,
      jumpiNT (isZero_eq_zero_of_ne hwv),
      raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem callerX_cvz_prefix
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩) :
    RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨24⟩
        [⟨41⟩, UInt256.lt (UInt256.ofNat I.calldata.size) ⟨4⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) 14 53 := by
  exact evm_run (solcGuardPrologueRD hcode (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) with [
      push2 ⟨15⟩,
      jumpiT (by rw [hwv]; decide) callerContains15,
      jumpdest, pop, push1 ⟨4⟩, calldatasize, lt, push2 ⟨41⟩ ]

abbrev callerSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

abbrev callerFirstArmPc : UInt256 := ⟨30⟩

theorem callerArmWellFormed : armWellFormed callerBytecode callerFirstArmPc :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem callerArmSelNat : armSelNat callerBytecode callerFirstArmPc = ⟨941609360⟩ := by decide

theorem callerMatch_eq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) :
    UInt256.eq (armSelNat callerBytecode callerFirstArmPc) (callerSelWord I)
      = if ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  rw [callerArmSelNat]; exact callerEvmSelector hsz

theorem callerReachBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨45⟩
        [callerSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact solcDispatchReachBody
    (firstArmPc := callerFirstArmPc) (bodyPC := ⟨45⟩) (i := 0)
    hcode hwv hsz hsize (by solc_dispatch_prefix) (by jump_dest)
    (fun j hj => by rw [Nat.le_zero.mp hj]; exact callerArmWellFormed)
    (fun j hj => absurd hj (by omega))
    (by show UInt256.eq (armSelNat callerBytecode callerFirstArmPc) (callerSelWord I) ≠ ⟨0⟩
        rw [callerMatch_eq I hsz, if_pos hmatch]; decide)
    (by jump_dest) (by decide)

theorem callerX_cvz_short
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩) (hsz : I.calldata.size < 4) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (callerX_cvz_prefix hcode hwv) with [
    jumpiT (lt_four_ne_zero_of_lt hsz) callerContains41,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem callerX_cvz_revertB
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = false) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run (callerX_cvz_prefix hcode hwv) with [
    jumpiNT (lt_four_eq_zero_of_ge hsz hsize),
    push0, calldataload, push1 ⟨224⟩, shr, dup1, push4 ⟨941609360⟩, eq, push2 ⟨45⟩,
    jumpiNT (by rw [show ((⟨0⟩ : UInt256).toNat) = 0 from by decide, callerEvmSelector hsz];
                simp [hmatch]),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem callerX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨348⟩
        [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k0, C0, rd0⟩ := callerReachBody (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hmatch
  have rd := evm_run rd0 with [
    jumpdest, push2 ⟨71⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1, push2 ⟨66⟩,
    swap2, swap1, push2 ⟨348⟩,
    jump callerContains348 ]
  rw [uadd_word_usub_ofNat_word (c := (⟨4⟩ : UInt256))
    (by rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]; exact hsz) hsize] at rd
  exact ⟨_, _, rd⟩

theorem callerX_dec277 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨277⟩
        [⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨383⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hszhi hsize
  obtain ⟨k0, C0, rd0⟩ := callerX_toDecoder (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hmatch
  exact ⟨_, _, evm_run rd0 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero, push2 ⟨370⟩,
    jumpiT (by rw [hslt]; decide) caller_jd,
    jumpdest, push0, push2 ⟨383⟩, dup6, dup3, dup7, add, push2 ⟨277⟩,
    jump caller_jd ]⟩

theorem callerX_dec264 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨264⟩
        [UInt256.land (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32)) addrMask,
          uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32),
          ⟨291⟩, uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ + ⟨0⟩ : UInt256).toNat 32),
          ⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨383⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_dec277 hcode hwv hsz hsize hsz68 hszhi hmatch
  exact ⟨_, _, evm_run rd with [
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨291⟩, dup2, push2 ⟨255⟩, jump caller_jd,
    jumpdest, push2 ⟨264⟩, dup2, push2 ⟨238⟩, jump caller_jd,
    jumpdest, push0, push2 ⟨248⟩, dup3, push2 ⟨207⟩, jump caller_jd,
    jumpdest, push0, push20 addrMask, dup3, and, swap1, pop, swap2, swap1, pop, jump caller_jd,
    jumpdest, swap1, pop, swap2, swap1, pop, jump caller_jd ]⟩

theorem callerX_dec291 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨291⟩
        [callerArg0 I, ⟨4⟩ + ⟨0⟩, UInt256.ofNat I.calldata.size, ⟨383⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨4⟩,
          UInt256.ofNat I.calldata.size, ⟨66⟩, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_dec264 hcode hwv hsz hsize hsz68 hszhi hmatch
  exact ⟨_, _, evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨274⟩, jumpiT (by rw [hclean]; decide) caller_jd,
    jumpdest, pop, jump caller_jd ]⟩

theorem callerDecode_n {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (callerArg0 I).toNat < EVM.addressModulus) :
    decodeCalldata (runTransition.params.map Param.name)
        (transitionSignature runTransition).paramTypes I.calldata
      = some (((∅ : Solm.Store).insert "t"
          (.address (Ethereum.AccountAddress.ofNat (callerArg0 I).toNat))).insert "n"
          (.int (Int.ofNat (callerArg1 I).toNat))) := by
  show decodeCalldata ["t", "n"] [addr, uint256] I.calldata = _
  simpa [addr, uint256, Pow.uint256, abiUInt256, calldataWord, callerArg0, callerArg1]
    using decodeCalldata_addr_uint256_ok
      (cd := I.calldata) (x := "t") (y := "n") hsz68 hbig hcanon

theorem callerDecode_none_short {I : ExecutionEnv} (hsz4 : 4 ≤ I.calldata.size)
    (hshort : I.calldata.size < 68) :
    decodeCalldata (runTransition.params.map Param.name)
        (transitionSignature runTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["t", "n"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, Pow.uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_short
      (cd := I.calldata) (x := "t") (y := "n") hsz4 hshort

theorem callerDecode_none_noncanon {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size)
    (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (callerArg0 I).toNat < EVM.addressModulus) :
    decodeCalldata (runTransition.params.map Param.name)
        (transitionSignature runTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["t", "n"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, Pow.uint256, abiUInt256, calldataWord, callerArg0]
    using decodeCalldata_addr_uint256_none_noncanon
      (cd := I.calldata) (x := "t") (y := "n") hsz68 hbig hnc

theorem callerDecode_none_huge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (runTransition.params.map Param.name)
        (transitionSignature runTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["t", "n"] [addr, uint256] I.calldata = none
  simpa [addr, uint256, Pow.uint256, abiUInt256]
    using decodeCalldata_addr_uint256_none_huge
      (cd := I.calldata) (x := "t") (y := "n") hbig

theorem callerX_decoded {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∃ k C, RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨66⟩
        [callerArg1 I, callerArg0 I, ⟨71⟩,
          UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, rd⟩ := callerX_dec291 hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  exact ⟨_, _, evm_run rd with [
    jumpdest, swap3, swap2, pop, pop, jump caller_jd,
    jumpdest, swap3, pop, pop, push1 ⟨32⟩, push2 ⟨400⟩, dup6, dup3, dup7, add, push2 ⟨328⟩, jump caller_jd,
    jumpdest, push0, dup2, calldataload, swap1, pop, push2 ⟨342⟩, dup2, push2 ⟨306⟩, jump caller_jd,
    jumpdest, push2 ⟨315⟩, dup2, push2 ⟨297⟩, jump caller_jd,
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump caller_jd,
    jumpdest, dup2, eq, push2 ⟨325⟩, jumpiT (by rw [ueq_self]; decide) caller_jd,
    jumpdest, pop, jump caller_jd,
    jumpdest, swap3, swap2, pop, pop, jump caller_jd,
    jumpdest, swap2, pop, pop, swap3, pop, swap3, swap1, pop, jump caller_jd ]⟩

theorem callerArg0_canonical {I : ExecutionEnv}
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    (callerArg0 I).toNat < EVM.addressModulus := by
  have heq : callerArg0 I = UInt256.land (callerArg0 I) addrMask := by
    by_contra hne
    simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false, Bool.false_eq_true,
      ↓reduceIte] at hclean
    exact absurd hclean (by decide)
  have hlandle : ∀ a b : ℕ, Nat.land a b ≤ b := by
    intro a b
    refine Nat.le_of_testBit fun i hi => ?_
    change (a &&& b).testBit i = true at hi
    rw [Nat.testBit_and] at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.2
  have hland : (callerArg0 I).toNat
      = Nat.land (callerArg0 I).toNat addrMask.toNat % EVM.twoPow 256 := by
    conv_lhs => rw [heq]
    rfl
  have hmod : Nat.land (callerArg0 I).toNat addrMask.toNat % EVM.twoPow 256
      = Nat.land (callerArg0 I).toNat addrMask.toNat :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (hlandle _ _) (by decide))
  have hmask : addrMask.toNat < EVM.addressModulus := by decide
  rw [hland, hmod]; exact lt_of_le_of_lt (hlandle _ _) hmask

theorem land_mask160 (n : ℕ) (h : n < 2^160) : Nat.land n (2^160 - 1) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  show (n &&& (2^160-1)).testBit i = n.testBit i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 160
  · rw [decide_eq_true hi, Bool.and_true]
  · rw [decide_eq_false hi, Bool.and_false]
    have : n < 2^i := lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact (Nat.testBit_lt_two_pow this).symm

theorem callerCanon_eq {I : ExecutionEnv} (hcanon : (callerArg0 I).toNat < EVM.addressModulus) :
    UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩ := by
  have hland : UInt256.land (callerArg0 I) addrMask = callerArg0 I := by
    apply u256_inj
    show Nat.land (callerArg0 I).toNat addrMask.toNat % EVM.twoPow 256 = (callerArg0 I).toNat
    rw [show addrMask.toNat = 2 ^ 160 - 1 from by decide,
        land_mask160 _ (by rw [show EVM.addressModulus = 2^160 from by decide] at hcanon; exact hcanon)]
    exact Nat.mod_eq_of_lt (by
      change (callerArg0 I).val.val < UInt256.size
      exact (callerArg0 I).val.isLt)
  rw [hland]; exact ueq_self (callerArg0 I)

theorem callerX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz hshort hsize
  obtain ⟨k0, C0, rd0⟩ := callerX_toDecoder (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hmatch
  exact evm_run rd0 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero, push2 ⟨370⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨369⟩, push2 ⟨203⟩, jump callerContains203,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem callerX_hugearg {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  obtain ⟨k0, C0, rd0⟩ := callerX_toDecoder (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hmatch
  exact evm_run rd0 with [
    jumpdest, push0, push0, push1 ⟨64⟩, dup4, dup6, sub, slt, iszero, push2 ⟨370⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨369⟩, push2 ⟨203⟩, jump callerContains203,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem ueq_zero_of_ne {a b : UInt256} (h : ¬ UInt256.eq a b = ⟨1⟩) : UInt256.eq a b = ⟨0⟩ := by
  by_cases hab : a = b
  · subst hab; exact absurd (ueq_self a) h
  · show UInt256.fromBool (decide (a = b)) = ⟨0⟩
    rw [decide_eq_false hab]; rfl

theorem callerX_noncanon {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hnc : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨0⟩) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := callerX_dec264 hcode hwv hsz hsize hsz68 hszhi hmatch
  exact (evm_run rd with [
    jumpdest, dup2, eq, push2 ⟨274⟩, jumpiNT (by rw [hnc]),
    raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ] :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I))

theorem store_get_empty (k : Ident) : (∅ : Solm.Store).get? k = none := by simp

abbrev callerDecStore (I : ExecutionEnv) : Solm.Store :=
  ((∅:Solm.Store).insert "t" (.address (AccountAddress.ofNat (callerArg0 I).toNat))).insert "n"
    (.int (Int.ofNat (callerArg1 I).toNat))

theorem callerStore_t (I : ExecutionEnv) :
    (callerDecStore I).get? "t" = some (.address (AccountAddress.ofNat (callerArg0 I).toNat)) := by
  rw [callerDecStore, store_get_ne _ _ (by decide), store_get_self]

theorem callerStore_n (I : ExecutionEnv) :
    (callerDecStore I).get? "n" = some (.int (Int.ofNat (callerArg1 I).toNat)) := by
  rw [callerDecStore, store_get_self]

theorem callerStore_stored_none (I : ExecutionEnv) :
    (callerDecStore I).get? "stored" = none := by
  rw [callerDecStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_empty]

theorem callerStore_stored (I : ExecutionEnv) (v : Value) :
    ((callerDecStore I).insert "tmp" v).get? "stored" = none := by
  rw [store_get_ne _ _ (by decide), callerDecStore, store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), store_get_empty]

private abbrev u3 : UInt256 := UInt256.ofNat 3
private abbrev u6 : UInt256 := UInt256.ofNat 6
private abbrev u66 : UInt256 := ⟨66⟩
private abbrev u143 : UInt256 := ⟨142⟩ + ⟨1⟩
private abbrev u144 : UInt256 := ⟨142⟩ + ⟨1⟩ + ⟨1⟩

private abbrev decodedStack (I : ExecutionEnv) (sel : UInt256) : List UInt256 :=
  [callerArg1 I, callerArg0 I, ⟨71⟩, sel]

private abbrev postCallStack (I : ExecutionEnv) (sel : UInt256) (z : Bool) : List UInt256 :=
  (if z then ⟨1⟩ else ⟨0⟩) ::
    ⟨164⟩ :: ⟨1143701499⟩ :: UInt256.land addrMask (callerArg0 I) ::
    callerArg1 I :: callerArg0 I :: ⟨71⟩ :: sel :: []

private def cursorAt (pc : UInt256) (stack : List UInt256) (mem : ByteArray) (aw : UInt256)
    (rdata : ByteArray) (world : Batteries.RBSet AccountAddress compare × AccountMap) : Cursor :=
  { pc := pc, stack := stack, mem := mem, aw := aw, rdata := rdata, world := world }

def CallerEntryRel {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} (I : ExecutionEnv) (g : Sat256)
    (sel : UInt256) : StateRel :=
  fun cur frame evm =>
    evm = initState cA gh bl σ σ₀ g A I ∧
    cur.stack = decodedStack I sel ∧
    cur.mem = solcFreePtrMem ∧ cur.aw = u3 ∧ cur.rdata = ByteArray.empty ∧
    frame.contract = Caller.callerContract ∧
    frame.locals.get? "t" =
      some (.address (AccountAddress.ofNat (callerArg0 I).toNat)) ∧
    frame.locals.get? "n" = some (.int (Int.ofNat (callerArg1 I).toNat)) ∧
    frame.locals.get? "stored" = none

def CallerPostCallRel {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} (I : ExecutionEnv) (g : Sat256)
    (sel : UInt256) (z : Bool) (o : ByteArray) : StateRel :=
  fun cur frame evm =>
    ∃ cA' σ' A',
      evm = { initState cA gh bl σ σ₀ g A I with
        accountMap := σ', substate := A', createdAccounts := cA' } ∧
      cur.stack = postCallStack I sel z ∧
      cur.mem = (o.write 0 (callerCalldataMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat) ∧
      cur.aw = u6 ∧ cur.rdata = o ∧ cur.world = worldOf evm ∧
      typedCallViaEVM callerConfig (initState cA gh bl σ σ₀ g A I)
        (EVM.address (AccountAddress.ofNat (callerArg0 I).toNat)) "pow2" 0
        [.int (Int.ofNat (callerArg1 I).toNat)] (z, evm, o) ∧
      frame.contract = Caller.callerContract ∧
      frame.locals.get? "t" =
        some (.address (AccountAddress.ofNat (callerArg0 I).toNat)) ∧
      frame.locals.get? "n" = some (.int (Int.ofNat (callerArg1 I).toNat))

def CallerAssignRel {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    (I : ExecutionEnv) (g : Sat256) (sel : UInt256) (o : ByteArray) : StateRel :=
  fun cur frame evm =>
    ∃ cA' σ' A' kw,
      32 ≤ o.size ∧ o.size < 2 ^ 255 ∧
      kw = fromByteArrayBigEndian (o.extract 0 32) ∧
      evm = { initState cA gh bl σ σ₀ g A I with
        accountMap := σ', substate := A', createdAccounts := cA' } ∧
      cur.stack = postCallStack I sel true ∧
      cur.mem = (o.write 0 (callerCalldataMem I) 128 32) ∧
      cur.aw = u6 ∧ cur.rdata = o ∧ cur.world = worldOf evm ∧
      frame.contract = Caller.callerContract ∧
      frame.locals.get? "tmp" = some (.int (Int.ofNat kw)) ∧
      frame.locals.get? "stored" = none

def CallerBodyPost (code : ByteArray) (g : Sat256) (s0 : State) : StmtPost
  | .ok _ evm' =>
      ∃ o, RDret code g s0 (worldOf evm') o ∧ returnEquiv o none none
  | .reverted =>
      RDrev code g s0
  | .returned _ _ _ | .break _ _ | .continue _ _ =>
      False

/-- Body code from decoded arguments at pc 66 to the `GAS` opcode immediately before `CALL`. -/
theorem callerX_toCall142_from66 {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ} {sel : UInt256}
    (rd : RD callerBytecode I g s0 u66 (decodedStack I sel) solcFreePtrMem u3 ByteArray.empty acc k C) :
    ∃ k' C', RD callerBytecode I g s0 ⟨142⟩
      [UInt256.land addrMask (callerArg0 I), ⟨0⟩, callerOutPtr I,
        UInt256.sub ⟨164⟩ (callerOutPtr I), callerOutPtr I, ⟨32⟩, ⟨164⟩,
        ⟨1143701499⟩, UInt256.land addrMask (callerArg0 I),
        callerArg1 I, callerArg0 I, ⟨71⟩, sel]
      (callerCalldataMem I) u6 ByteArray.empty acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    jumpdest, push2 ⟨73⟩, jump caller_jd,
    jumpdest, dup2, push20 addrMask, and, push4 ⟨1143701499⟩, dup3, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ u3 (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    dup3, push4 ⟨4294967295⟩, and, push1 ⟨224⟩, shl, dup2,
    raw mstore 6 callerSelMem (UInt256.ofNat 5) (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨4⟩, add, push2 ⟨130⟩, swap2, swap1, push2 ⟨425⟩, jump caller_jd,
    jumpdest, push0, push1 ⟨32⟩, dup3, add, swap1, pop, push2 ⟨444⟩, push0, dup4, add, dup5,
    push2 ⟨410⟩, jump caller_jd,
    jumpdest, push2 ⟨419⟩, dup2, push2 ⟨297⟩, jump caller_jd,
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump caller_jd,
    jumpdest, dup3,
    raw mstore 3 (callerCalldataMem I) u6 (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    pop, pop, jump caller_jd,
    jumpdest, swap3, swap2, pop, pop, jump caller_jd,
    jumpdest, push1 ⟨32⟩, push1 ⟨64⟩,
    raw mload 0 (callerOutPtr I) u6 (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    dup1, dup4, sub, dup2, push0, dup8 ]⟩

/-- Extract the concrete initial world from a coupled decoded-entry state. -/
theorem callerEntryWorld {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256}
    (st : CoupledState callerBytecode I g (initState cA gh bl σ σ₀ g A I)
      (CallerEntryRel (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        I g sel) u66) :
    st.cur.world = (cA, σ) := by
  rcases st.hrel with ⟨hevm, _⟩
  rw [st.hworld, hevm]
  rfl

/- The opaque `CALL` package from the decoded body entry.

   This is the compositional boundary for Caller: all setup before the `CALL`, the `CALL` itself,
   the `RD.call` active-word/memory normalization, the `typedCallViaEVM` coincidence, and the
   return-data size bound are hidden behind one lemma.  Post-call proof chunks can consume the
   returned cursor without redoing the call bridge. -/
set_option maxHeartbeats 4000000 in
theorem callerX_postCall_from66 {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {k C : ℕ}
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hclean : UInt256.eq (callerArg0 I)
      (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩)
    (rd66 : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) u66
      (decodedStack I sel) solcFreePtrMem u3 ByteArray.empty (cA, σ) k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) u144
        (postCallStack I sel z)
        (o.write 0 (callerCalldataMem I) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        u6 o (cA', σ') k' C'
    ∧ typedCallViaEVM callerConfig (initState cA gh bl σ σ₀ g A I)
        (EVM.address (AccountAddress.ofNat (callerArg0 I).toNat)) "pow2" 0
        [.int (Int.ofNat (callerArg1 I).toNat)]
        (z, { initState cA gh bl σ σ₀ g A I with
                accountMap := σ', substate := A', createdAccounts := cA' }, o)
    ∧ o.size < UInt256.size := by
  obtain ⟨k142, C142, rd142⟩ := callerX_toCall142_from66 rd66
  obtain ⟨gv, rd143⟩ := rd142.gas (by decide) (by evm_ov)
  obtain ⟨cA', σ', z, o, A_in, callGas, k144, C144, hΘpack, rd144raw, hosz⟩ :=
    rd143.call (by decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k144, C144, ?_, ?_, ?_⟩
  · have haw : UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
        (callerOutPtr I).toNat (UInt256.sub ⟨164⟩ (callerOutPtr I)).toNat)
        (callerOutPtr I).toNat (⟨32⟩ : UInt256).toNat) = u6 := by
      rw [callerOutPtr_eq]
      decide
    have hoff : (callerOutPtr I).toNat = 128 := by
      rw [callerOutPtr_eq]
      decide
    have rd144aw : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) u144
        (postCallStack I sel z)
        (o.write 0 (callerCalldataMem I) (callerOutPtr I).toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        u6 o (cA', σ') k144 C144 :=
      haw ▸ rd144raw
    rw [hoff] at rd144aw
    exact rd144aw
  · refine callCoincides (targetWord := UInt256.land addrMask (callerArg0 I))
      (mem := callerCalldataMem I) (inOff := callerOutPtr I)
      (inSize := UInt256.sub ⟨164⟩ (callerOutPtr I)) hperm
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (callerTarget_eq hclean) ?_ hΘ
    rw [show (callerOutPtr I).toNat = 128 from by rw [callerOutPtr_eq]; decide,
        show (UInt256.sub ⟨164⟩ (callerOutPtr I)).toNat = 36 from by
          rw [callerOutPtr_eq]; decide]
    exact callerEncode_eq I
  · exact hosz

theorem callerX_postRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ} {rest : List UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
            (⟨0⟩ :: rest) mem aw rdata acc k C)
    (hov : rest.length + 4 ≤ 1024) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have rd151 : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I)
      (⟨142⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩)
      (UInt256.isZero ⟨0⟩ :: rest) mem aw rdata acc _ _ :=
    evm_run rd with [iszero, dup1, iszero, push2 ⟨158⟩, jumpiNT (by decide)]
  obtain ⟨mem2, aw2, k2, C2, rd155⟩ :=
    RD.returndatacopyFull rd151 (by decide) (by decide) (by decide) (by decide)
      (by simp only [List.length_cons]; omega)
  have rd156 := RD.returndatasize rd155 (by decide) (by simp only [List.length_cons]; omega)
  have rd157 := RD.push0 rd156 (by decide) (by simp only [List.length_cons]; omega)
  exact RD.rev _ rd157 (by decide)
    (fun s haws hstks => by rw [memExpRevertZeroOff s hstks, haws])
    (by simp only [List.length_cons]; omega)

theorem callerX_succ_to165 {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : ℕ}
    {d0 d1 d2 : UInt256} {tl : List UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
            (⟨1⟩ :: d0 :: d1 :: d2 :: tl) mem aw rdata acc k C)
    (hov : tl.length + 7 ≤ 1024) :
    ∃ k' C', RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨165⟩
        (⟨64⟩ :: tl) mem aw rdata acc k' C' := by
  refine ⟨_, _, evm_run rd with [iszero, dup1, iszero, push2 ⟨158⟩,
    jumpiT (by decide) callerContains158, jumpdest, pop, pop, pop, pop, push1 ⟨64⟩]⟩

noncomputable def callerMem2 (o mem : ByteArray) : ByteArray :=
  (UInt256.add ⟨128⟩ (UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)
    (UInt256.lnot ⟨31⟩))).toByteArray.write 0 mem 64 32

theorem callerX_succ_to470 {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨165⟩
            [⟨64⟩, arg1, arg0, ⟨71⟩, sel] mem ⟨6⟩ o acc k C)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
           else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
          = ⟨128⟩) :
    ∃ k' C', RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
      [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
      (callerMem2 o mem) ⟨6⟩ o acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    raw mload 0 ⟨128⟩ ⟨6⟩ (by decide)
      mem_cost
      hfp (by decide) (by evm_ov),
    returndatasize,
    push1 ⟨31⟩, not, push1 ⟨31⟩, dup3, add, and, dup3, add, dup1, push1 ⟨64⟩,
    raw mstore 0 ((UInt256.add ⟨128⟩ (UInt256.land (UInt256.add (UInt256.ofNat o.size) ⟨31⟩)
        (UInt256.lnot ⟨31⟩))).toByteArray.write 0 mem 64 32) ⟨6⟩ (by decide)
      mem_cost
      (by rfl) (by decide) (by evm_ov),
    pop, dup2, add, swap1, push2 ⟨194⟩, swap2, swap1, push2 ⟨470⟩, jump callerContains470 ]⟩

theorem callerX_succ_to491 {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem2 : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
            [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
            mem2 ⟨6⟩ o acc k C)
    (ho32 : 32 ≤ o.size) (ho : o.size < 2 ^ 255) :
    ∃ k' C', RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨491⟩
      [⟨0⟩, ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
      mem2 ⟨6⟩ o acc k' C' := by
  refine ⟨_, _, evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨491⟩,
    jumpiT (by rw [solcDecodeEndLenCheckOk_128_32 ho32 ho]; decide) callerContains491 ]⟩

theorem callerX_succ_revert {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem2 : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
            [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
            mem2 ⟨6⟩ o acc k C)
    (ho : o.size < 32) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨491⟩,
    jumpiNT (by rw [solcDecodeEndLenCheckShort_128_32 ho]; decide),
    push2 ⟨490⟩, push2 ⟨203⟩, jump callerContains203,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem callerX_succ_revert_huge {cA gh bl σ σ₀ A I} {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem2 : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨470⟩
            [⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
            mem2 ⟨6⟩ o acc k C)
    (hhi : 2 ^ 255 ≤ o.size) (hlo : o.size < UInt256.size) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run rd with [
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨491⟩,
    jumpiNT (by rw [solcDecodeEndLenCheckHuge_128_32 hhi hlo]; decide),
    push2 ⟨490⟩, push2 ⟨203⟩, jump callerContains203,
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem callerX_succ_tail {cA gh bl σ σ₀ A I} {g : Sat256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {mem2 : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel : UInt256}
    (rd : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨491⟩
            [⟨0⟩, ⟨128⟩, UInt256.add ⟨128⟩ (UInt256.ofNat o.size), ⟨194⟩, arg1, arg0, ⟨71⟩, sel]
            mem2 ⟨6⟩ o (cAx, σx) k C)
    (hperm : I.perm = true)
    (hword : mem2.readWithPadding 128 32 = o.extract 0 32)
    (hsize2 : 128 < mem2.size) :
    RDret callerBytecode g (initState cA gh bl σ σ₀ g A I)
      (cAx, sstoreAccountMap I.codeOwner σx ⟨0⟩
              (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))))
      ByteArray.empty := by
  have rd198 := evm_run rd with [
    jumpdest, push0, push2 ⟨504⟩, dup5, dup3, dup6, add, push2 ⟨450⟩, jump callerContains450,
    jumpdest, push0, dup2,
    raw mload 0 (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))) ⟨6⟩ (by decide)
      mem_cost
      (by
        have h128 : ((⟨128⟩ : UInt256) + ⟨0⟩).toNat = 128 := by decide
        split_ifs with h
        · exfalso; rcases h with h | h
          · rw [h128] at h; omega
          · exact absurd h (by decide)
        · rw [h128, hword])
      (by decide) (by evm_ov),
    swap1, pop, push2 ⟨464⟩, dup2, push2 ⟨306⟩, jump callerContains306,
    jumpdest, push2 ⟨315⟩, dup2, push2 ⟨297⟩, jump callerContains297,
    jumpdest, push0, dup2, swap1, pop, swap2, swap1, pop, jump callerContains315,
    jumpdest, dup2, eq, push2 ⟨325⟩, jumpiT (by rw [ueq_self]; decide) callerContains325,
    jumpdest, pop, jump callerContains464,
    jumpdest, swap3, swap2, pop, pop, jump callerContains504,
    jumpdest, swap2, pop, pop, swap3, swap2, pop, pop, jump callerContains194,
    jumpdest, push0, dup2, swap1 ]
  obtain ⟨k', C', rd199⟩ := rd198.sstore hperm (by decide) (by evm_ov)
  exact RD.stop (evm_run rd199 with [pop, pop, pop, jump callerContains71, jumpdest])
    (by decide) (by evm_ov)

theorem callerX_successChain {cA gh bl σ σ₀ A I} {g : Sat256}
    {cAx : Batteries.RBSet AccountAddress compare} {σx : AccountMap}
    {mem : ByteArray} {o : ByteArray} {k C : ℕ} {arg1 arg0 sel d0 d1 d2 : UInt256}
    (rd144 : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) (⟨142⟩ + ⟨1⟩ + ⟨1⟩)
            (⟨1⟩ :: d0 :: d1 :: d2 :: arg1 :: arg0 :: ⟨71⟩ :: sel :: []) mem ⟨6⟩ o (cAx, σx) k C)
    (hperm : I.perm = true) (ho32 : 32 ≤ o.size) (ho : o.size < 2 ^ 255)
    (hfp : (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
           else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
          = ⟨128⟩)
    (hword : mem.readWithPadding 128 32 = o.extract 0 32) (hmsz : 160 ≤ mem.size) :
    RDret callerBytecode g (initState cA gh bl σ σ₀ g A I)
      (cAx, sstoreAccountMap I.codeOwner σx ⟨0⟩
              (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))))
      ByteArray.empty := by
  obtain ⟨k1, C1, rd165⟩ := callerX_succ_to165 rd144 (by simp)
  obtain ⟨k2, C2, rd470⟩ := callerX_succ_to470 rd165 hfp
  obtain ⟨k3, C3, rd491⟩ := callerX_succ_to491 rd470 ho32 ho
  have hword2 : (callerMem2 o mem).readWithPadding 128 32 = o.extract 0 32 := by
    rw [callerMem2, write32_read_above _ _ 64 128 (by rw [toByteArray_size]) (by omega)
      (by omega) (by omega), hword]
  have hmsz2 : 128 < (callerMem2 o mem).size := by
    rw [callerMem2, write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
      ByteArray.size_extract, toByteArray_size]
    omega
  exact callerX_succ_tail rd491 hperm hword2 hmsz2

def CallerExternalPost {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader}
    {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    (I : ExecutionEnv) (g : Sat256) (s0 : State) (sel : UInt256) : StmtPost
  | .ok frame' evm' =>
      ∃ o cur' k' C',
        cur'.pc = u144 ∧ RDc callerBytecode I g s0 cur' k' C' ∧
        cur'.world = worldOf evm' ∧ CallerAssignRel (cA := cA) (gh := gh) (bl := bl)
          (σ := σ) (σ₀ := σ₀) (A := A) I g sel o cur' frame' evm'
  | .reverted =>
      RDrev callerBytecode g s0
  | .returned _ _ _ | .break _ _ | .continue _ _ =>
      False

set_option maxHeartbeats 3000000 in
/-- Coupled proof chunk for the opaque external call in `Caller.run`.

    The pre-call bytecode prefix and `RD.call` bridge are factored through
    `callerX_postCall_from66`.  On call failure or ABI-decode failure the statement reverts and the
    matching EVM path is discharged immediately; on decode success the postcondition exposes the
    reached post-call cursor with `tmp` bound, ready for the storage-assignment chunk. -/
theorem callerCoupled_externalCall {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hclean : UInt256.eq (callerArg0 I)
      (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∀ st : CoupledState callerBytecode I g (initState cA gh bl σ σ₀ g A I)
      (CallerEntryRel (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        I g sel) u66,
      CoupledState.refines st callerConfig
        [.externalCall (.var "t") "pow2" (.intLit 0) [.var "n"] "tmp"]
        (CallerExternalPost (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) I g (initState cA gh bl σ σ₀ g A I) sel) := by
  intro st
  rcases st.hrel with ⟨hevm, hstack, hmem, haw, hrdata, hcontract, ht, hn, hstored⟩
  have hworld0 : st.cur.world = (cA, σ) := callerEntryWorld st
  have rd66cur := st.toRD hstack hmem haw hrdata
  have rd66 : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) u66
      (decodedStack I sel) solcFreePtrMem u3 ByteArray.empty (cA, σ) st.k st.C := by
    rw [hworld0] at rd66cur
    exact rd66cur
  obtain ⟨cA', σ', z, o, A', k144, C144, rd144, hcoin, ho255⟩ :=
    callerX_postCall_from66 (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) hperm hdepth hclean rd66
  have hrec : evalExpr? callerConfig st.frame st.evm (.var "t")
      = .ok (.address (AccountAddress.ofNat (callerArg0 I).toNat)) := by
    simp only [evalExpr?, EvalResult.ofOption, ht]
  have heth : evalExpr? callerConfig st.frame st.evm (.intLit 0) = .ok (.int 0) := by
    simp only [evalExpr?]
    rfl
  have hargs : evalExprs? callerConfig st.frame st.evm [.var "n"]
      = .ok [.int (Int.ofNat (callerArg1 I).toNat)] := by
    simp only [evalExprs?, evalExpr?, EvalResult.ofOption, hn, EvalResult.bind, bind, pure]
  cases z
  · refine CoupledState.refines.externalCallFailure st ?_ ?_
    · refine ⟨AccountAddress.ofNat (callerArg0 I).toNat, 0,
        [.int (Int.ofNat (callerArg1 I).toNat)],
        { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' },
        o, hrec, heth, hargs, ?_⟩
      rw [hevm]
      exact hcoin
    · exact callerX_postRevert rd144 (by simp)
  · by_cases ho32 : 32 ≤ o.size
    · by_cases hoSmall : o.size < 2 ^ 255
      · set kw := fromByteArrayBigEndian (o.extract 0 32) with hkw
        have hdec : callerConfig.externalABI.decode? "pow2" o =
            some (.int (Int.ofNat kw)) := by
          show defaultDecodeReturn? "pow2" o = _
          simpa [defaultDecodeReturn?, ← hkw, Int.ofNat_eq_natCast] using
            decodeReturnValue_uint256_ok (returndata := o) ho32 hoSmall
        have hmem32 : o.write 0 (callerCalldataMem I) 128
            (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat =
            o.write 0 (callerCalldataMem I) 128 32 := by
          rw [callerL_succ o.size ho32 ho255]
        rw [hmem32] at rd144
        set evmP : State := { initState cA gh bl σ σ₀ g A I with
          accountMap := σ', substate := A', createdAccounts := cA' } with hevmP
        set frameP : Frame := { st.frame with
          locals := st.frame.locals.insert "tmp" (.int (Int.ofNat kw)) } with hframeP
        have hcallSt : typedCallViaEVM callerConfig st.evm
            (EVM.address (AccountAddress.ofNat (callerArg0 I).toNat)) "pow2" 0
            [.int (Int.ofNat (callerArg1 I).toNat)] (true, evmP, o) := by
          rw [hevm, hevmP]
          exact hcoin
        have hstmt : ExecStmt callerConfig st.frame st.evm
            (.externalCall (.var "t") "pow2" (.intLit 0) [.var "n"] "tmp")
            (.ok frameP evmP) := by
          rw [hframeP]
          exact ExecStmt.externalCallSuccess hrec heth hargs hcallSt hdec
        let cur144 : Cursor := cursorAt u144 (postCallStack I sel true)
          (o.write 0 (callerCalldataMem I) 128 32) u6 o (cA', σ')
        have hrdc : RDc callerBytecode I g (initState cA gh bl σ σ₀ g A I) cur144 k144 C144 := by
          change RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) cur144.pc
            cur144.stack cur144.mem cur144.aw cur144.rdata cur144.world k144 C144
          exact rd144
        have hwcur : cur144.world = worldOf evmP := by
          rw [hevmP]
          rfl
        have hrel : CallerAssignRel (cA := cA) (gh := gh) (bl := bl) (σ := σ)
            (σ₀ := σ₀) (A := A) I g sel o cur144 frameP evmP := by
          refine ⟨cA', σ', A', kw, ho32, hoSmall, hkw, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
          · rw [hevmP]
          · rw [hevmP]
            rfl
          · rw [hframeP]
            exact hcontract
          · rw [hframeP, store_get_self]
          · rw [hframeP, store_get_ne _ _ (by decide), hstored]
        exact ⟨.ok frameP evmP, ExecBlock.consNormal hstmt ExecBlock.nil,
          o, cur144, k144, C144, rfl, hrdc, hwcur, hrel⟩
      · rw [not_lt] at hoSmall
        have hdecn : callerConfig.externalABI.decode? "pow2" o = none := by
          show defaultDecodeReturn? "pow2" o = none
          simpa [defaultDecodeReturn?] using
            decodeReturnValue_uint256_none_huge (returndata := o) hoSmall
        have hmem32 : o.write 0 (callerCalldataMem I) 128
            (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat =
            o.write 0 (callerCalldataMem I) 128 32 := by
          rw [callerL_succ o.size ho32 ho255]
        rw [hmem32] at rd144
        have hfp : (if (⟨64⟩ : UInt256).toNat ≥
                (o.write 0 (callerCalldataMem I) 128 32).size
              ∨ (⟨64⟩ : UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
            else UInt256.ofNat (fromByteArrayBigEndian
              ((o.write 0 (callerCalldataMem I) 128 32).readWithPadding
                (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
          exact mloadFreePtrValue
            (by rw [callerWrite_size I o 32 (by omega) ho32]; decide)
            (by decide) (callerWrite_read64 I o 32 (by omega) ho32)
        obtain ⟨k165, C165, rd165⟩ := callerX_succ_to165 rd144 (by simp)
        obtain ⟨k470, C470, rd470⟩ := callerX_succ_to470 rd165 hfp
        refine CoupledState.refines.externalCallDecodeRevert st ?_ ?_
        · refine ⟨AccountAddress.ofNat (callerArg0 I).toNat, 0,
            [.int (Int.ofNat (callerArg1 I).toNat)],
            { initState cA gh bl σ σ₀ g A I with
              accountMap := σ', substate := A', createdAccounts := cA' },
            o, hrec, heth, hargs, ?_, hdecn⟩
          rw [hevm]
          exact hcoin
        · exact callerX_succ_revert_huge rd470 hoSmall ho255
    · rw [not_le] at ho32
      have hdecn : callerConfig.externalABI.decode? "pow2" o = none := by
        show defaultDecodeReturn? "pow2" o = none
        simpa [defaultDecodeReturn?] using
          decodeReturnValue_uint256_none_short (returndata := o) ho32
      rw [callerL_rev o.size ho32] at rd144
      have hfp : (if (⟨64⟩ : UInt256).toNat ≥
              (o.write 0 (callerCalldataMem I) 128 o.size).size
            ∨ (⟨64⟩ : UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
          else UInt256.ofNat (fromByteArrayBigEndian
            ((o.write 0 (callerCalldataMem I) 128 o.size).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
        exact mloadFreePtrValue
          (by rw [callerWrite_size I o o.size (by omega) (by omega)]; decide)
          (by decide) (callerWrite_read64 I o o.size (by omega) (by omega))
      obtain ⟨k165, C165, rd165⟩ := callerX_succ_to165 rd144 (by simp)
      obtain ⟨k470, C470, rd470⟩ := callerX_succ_to470 rd165 hfp
      refine CoupledState.refines.externalCallDecodeRevert st ?_ ?_
      · refine ⟨AccountAddress.ofNat (callerArg0 I).toNat, 0,
          [.int (Int.ofNat (callerArg1 I).toNat)],
          { initState cA gh bl σ σ₀ g A I with
            accountMap := σ', substate := A', createdAccounts := cA' },
          o, hrec, heth, hargs, ?_, hdecn⟩
        rw [hevm]
        exact hcoin
      · exact callerX_succ_revert rd470 ho32

set_option maxHeartbeats 3000000 in
/-- Coupled proof chunk for the post-call storage assignment and the remaining bytecode tail. -/
theorem callerCoupled_assignReturn {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256} {o : ByteArray}
    (hperm : I.perm = true) :
    ∀ st : CoupledState callerBytecode I g (initState cA gh bl σ σ₀ g A I)
      (CallerAssignRel (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        I g sel o) u144,
      CoupledState.refines st callerConfig
        [.assign .storage { base := "stored", steps := [] } (.var "tmp")]
        (CallerBodyPost callerBytecode g (initState cA gh bl σ σ₀ g A I)) := by
  intro st
  rcases st.hrel with
    ⟨cA', σ', A', kw, ho32, ho255, hkw, hevm, hstack, hmem, haw, hrdata, hwrel,
      hcontract, htmp, hstored⟩
  have hacc : st.cur.world = (cA', σ') := by
    rw [st.hworld, hevm]
    rfl
  have rd144cur := st.toRD hstack hmem haw hrdata
  have rd144 : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) u144
      (postCallStack I sel true) (o.write 0 (callerCalldataMem I) 128 32) u6 o
      (cA', σ') st.k st.C := by
    rw [hacc] at rd144cur
    exact rd144cur
  have hmsz : 160 ≤ (o.write 0 (callerCalldataMem I) 128 32).size := by
    have := callerWrite_size I o 32 (by omega) ho32
    omega
  have hfp : (if (⟨64⟩ : UInt256).toNat ≥
          (o.write 0 (callerCalldataMem I) 128 32).size
        ∨ (⟨64⟩ : UInt256) ≥ ⟨6⟩ * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((o.write 0 (callerCalldataMem I) 128 32).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ := by
    exact mloadFreePtrValue
      (by rw [callerWrite_size I o 32 (by omega) ho32]; decide)
      (by decide) (callerWrite_read64 I o 32 (by omega) ho32)
  have hword : (o.write 0 (callerCalldataMem I) 128 32).readWithPadding 128 32 =
      o.extract 0 32 :=
    write32_read_back o (callerCalldataMem I) 128 ho32
      (by rw [callerCalldataMem_size]; omega)
  have hret := callerX_successChain rd144 hperm ho32 ho255 hfp hword hmsz
  have hevalTmp : evalExpr? callerConfig st.frame st.evm (.var "tmp")
      = .ok (.int (Int.ofNat kw)) := by
    simp only [evalExpr?, EvalResult.ofOption, htmp]
  set frameS : Frame := { contract := Caller.callerContract, locals := st.frame.locals } with hframeS
  set evmS : State := EVM.storageStore st.evm st.evm.executionEnv.codeOwner ⟨0⟩
    (UInt256.ofNat kw) with hevmS
  have hassign : assignStorageRef? callerConfig st.frame st.evm .storage { base := "stored", steps := [] }
      (.int (Int.ofNat kw)) = .ok (frameS, evmS) := by
    have hframe : st.frame = { contract := Caller.callerContract, locals := st.frame.locals } := by
      cases hframe' : st.frame with
      | mk contract locals =>
          rw [hframe'] at hcontract
          simp only at hcontract
          rw [hcontract]
    rw [hframe, hframeS, hevmS]
    exact callerAssign st.evm st.frame.locals kw hstored
  have hstmt : ExecStmt callerConfig st.frame st.evm
      (.assign .storage { base := "stored", steps := [] } (.var "tmp")) (.ok frameS evmS) :=
    ExecStmt.assign hevalTmp hassign
  have hworldRet :
      (cA', sstoreAccountMap I.codeOwner σ' ⟨0⟩
          (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)))) = worldOf evmS := by
    rw [hevmS, worldOf, storageStore_createdAccounts, storageStore_accountMap, hevm, hkw]
    rfl
  have hretWorld : RDret callerBytecode g (initState cA gh bl σ σ₀ g A I) (worldOf evmS)
      ByteArray.empty := by
    rw [← hworldRet]
    exact hret
  exact ⟨.ok frameS evmS, ExecBlock.consNormal hstmt ExecBlock.nil,
    ByteArray.empty, hretWorld, returnEquiv.void rfl rfl rfl⟩

set_option maxHeartbeats 4000000 in
/-- Coupled body-suffix proof from the decoded `Caller.run` body entry at pc 66. -/
theorem callerCoupled_bodySuffix {cA : Batteries.RBSet AccountAddress compare}
    {gh : BlockHeader} {bl : ProcessedBlocks} {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : Sat256} {sel : UInt256}
    (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hclean : UInt256.eq (callerArg0 I)
      (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    ∀ st : CoupledState callerBytecode I g (initState cA gh bl σ σ₀ g A I)
      (CallerEntryRel (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        I g sel) u66,
      CoupledState.refines st callerConfig
        [.externalCall (.var "t") "pow2" (.intLit 0) [.var "n"] "tmp",
         .assign .storage { base := "stored", steps := [] } (.var "tmp")]
        (CallerBodyPost callerBytecode g (initState cA gh bl σ σ₀ g A I)) := by
  intro st
  obtain ⟨result, hcallBlock, hpost⟩ :=
    callerCoupled_externalCall (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) hperm hdepth hclean st
  cases hcallBlock with
  | consNormal hcall hnil =>
      cases hnil
      obtain ⟨o, cur', k', C', hpc', hRD', hw', hrel'⟩ := hpost
      obtain ⟨resultTail, htail, hpostTail⟩ :=
        callerCoupled_assignReturn (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) (sel := sel) (o := o) hperm
          (CoupledState.mk cur' k' C' _ _ hpc' hRD' hw' hrel')
      exact ⟨resultTail, ExecBlock.consNormal hcall htail, hpostTail⟩
  | consRevert hcall =>
      exact ⟨.reverted, ExecBlock.consRevert hcall, hpost⟩
  | consReturn hcall => exact hpost.elim
  | consBreak hcall => exact hpost.elim
  | consContinue hcall => exact hpost.elim

set_option maxHeartbeats 4000000 in
theorem callerExec_coupled_canonical {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hperm : I.perm = true) (hdepth : I.depth.val < 1024)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩) :
    runtimeEquivalenceFor callerConfig callerContract cA gh bl σ σ σ₀ g.toUInt256 A I := by
  have hcanon := callerArg0_canonical hclean
  have hd : dispatchMsg callerContract I.calldata = some runTransition := by
    rw [callerDispatch_eq, if_pos hmatch]
  have hdec := callerDecode_n hsz68 hbig hcanon
  obtain ⟨k66, C66, rd66⟩ :=
    callerX_decoded (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv (by omega) hsize hsz68 hbig hmatch hclean
  set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hsel
  let cur66 : Cursor :=
    cursorAt u66 (decodedStack I sel) solcFreePtrMem u3 ByteArray.empty (cA, σ)
  let frame0 : Frame := { contract := callerContract, locals := callerDecStore I }
  let evm0 : State := initState cA gh bl σ σ₀ g A I
  have hRDc : RDc callerBytecode I g (initState cA gh bl σ σ₀ g A I) cur66 k66 C66 := by
    change RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) cur66.pc
      cur66.stack cur66.mem cur66.aw cur66.rdata cur66.world k66 C66
    exact rd66
  have hw : cur66.world = worldOf evm0 := by
    rfl
  have hrel : CallerEntryRel (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) I g sel cur66 frame0 evm0 := by
    refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · rw [hsel]
      rfl
    · exact callerStore_t I
    · exact callerStore_n I
    · exact callerStore_stored_none I
  obtain ⟨result, hsuffix, hpost⟩ :=
    callerCoupled_bodySuffix (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (sel := sel) hperm hdepth hclean
      (CoupledState.mk cur66 k66 C66 frame0 evm0 rfl hRDc hw hrel)
  cases result with
  | ok frame' evm' =>
      obtain ⟨o, hret, henc⟩ := hpost
      have hbody : ExecTransitionBody callerConfig callerContract
          (initState cA gh bl σ σ₀ g A I) (callerDecStore I) runTransition.body
          (.returned frame' evm' none) := by
        exact ExecFuncBody.execBlockOK
          (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) hsuffix)
      exact RDret.reEquivExecutionGenAccountMapEquiv hcode hret hd hdec hbody
        rfl (accountMapEquiv.refl _) henc
  | reverted =>
      have hbody : ExecTransitionBody callerConfig callerContract
          (initState cA gh bl σ σ₀ g A I) (callerDecStore I) runTransition.body .reverted := by
        exact ExecFuncBody.execBlockRevert
          (ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) hsuffix)
      exact RDrev.reEquivExecutionRevert hcode hpost hd hdec hbody
  | returned frame' evm' rv => exact hpost.elim
  | «break» frame' evm' => exact hpost.elim
  | «continue» frame' evm' => exact hpost.elim

theorem callerX_callDepthLimit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsz68 : 68 ≤ I.calldata.size) (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true)
    (hclean : UInt256.eq (callerArg0 I) (UInt256.land (callerArg0 I) addrMask) = ⟨1⟩)
    (hdepth : I.depth = 1024) :
    RDrev callerBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k66, C66, rd66raw⟩ :=
    callerX_decoded (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (g := g) hcode hwv hsz hsize hsz68 hszhi hmatch hclean
  set sel := UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩ with hsel
  have rd66 : RD callerBytecode I g (initState cA gh bl σ σ₀ g A I) u66
      (decodedStack I sel) solcFreePtrMem u3 ByteArray.empty (cA, σ) k66 C66 := by
    rw [hsel]
    exact rd66raw
  obtain ⟨k142, C142, rd142⟩ := callerX_toCall142_from66 rd66
  obtain ⟨gv, rd143⟩ := rd142.gas (by decide) (by evm_ov)
  obtain ⟨k', C', rd144⟩ := rd143.callDepthLimit (by decide) hdepth (by evm_ov)
  exact callerX_postRevert rd144 (by simp)

set_option maxHeartbeats 5000000 in
theorem callerReEquiv_callvalueZero
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = callerBytecode) (hsize : I.calldata.size < Ethereum.UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true) :
    runtimeEquivalenceFor callerConfig callerContract cA gh bl σ σ σ₀ g.toUInt256 A I := by
  by_cases hsz : I.calldata.size < 4
  · exact (callerX_cvz_short hcode hwv hsz).reEquivNoDispatch hcode (callerDispatch_none_short hsz)
  · rw [not_lt] at hsz
    by_cases hmatch : ((⟨#[0x38, 0x1f, 0xd1, 0x90]⟩ : ByteArray) == I.calldata.extract 0 4) = true
    · have hd : dispatchMsg callerContract I.calldata = some runTransition := by
        rw [callerDispatch_eq, if_pos hmatch]
      by_cases hsz68 : 68 ≤ I.calldata.size
      · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
        · by_cases hcanon : (callerArg0 I).toNat < EVM.addressModulus
          · by_cases hdepth : I.depth.val < 1024
            · exact callerExec_coupled_canonical hcode hwv hsize hperm hdepth hsz68 hbig hmatch
                (callerCanon_eq hcanon)
            · rw [not_lt] at hdepth
              have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
              refine (callerX_callDepthLimit hcode hwv (by omega) hsize hsz68 hbig hmatch
                  (callerCanon_eq hcanon) hdepth1024).reEquivExecutionRevert hcode hd
                (callerDecode_n hsz68 hbig hcanon) ?_
              exact callerBodyExtFail _ (callerDecStore I) (by exact hwv) (callerStore_t I)
                (callerStore_n I) (callNotMade_depthLimit (callerEncode_eq I) hdepth1024)
          · exact (callerX_noncanon hcode hwv (by omega) hsize hsz68 hbig hmatch
                (ueq_zero_of_ne (fun he => hcanon (callerArg0_canonical he)))).reEquivDecodingFailed
              hcode hd (callerDecode_none_noncanon hsz68 hbig hcanon)
        · rw [not_lt] at hbig
          exact (callerX_hugearg hcode hwv (by omega) hsize hbig hmatch).reEquivDecodingFailed
            hcode hd (callerDecode_none_huge hbig)
      · rw [not_le] at hsz68
        exact (callerX_shortarg hcode hwv hsz hsize hsz68 hmatch).reEquivDecodingFailed
          hcode hd (callerDecode_none_short hsz hsz68)
    · rw [Bool.not_eq_true] at hmatch
      exact (callerX_cvz_revertB hcode hwv hsz hsize hmatch).reEquivNoDispatch hcode
        (callerDispatch_none_nomatch hmatch)

end

end CallerCoupled
