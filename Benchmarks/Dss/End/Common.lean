import Reasoning.ABIViews
import Reasoning.EVMWord
import Reasoning.SolcRoutines
import Benchmarks.Dss.End.Bytecode
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Reasoning.ExternalCall
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS End shared proof foundation

Contract-wide helpers for the optimized runtime and creation bytecode.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.End

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev endSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true


theorem endAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storageBackend.locate? er = some (.leaf (addrLoc slot))) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbackend := rfl) (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_address_offset0 evm slot))

theorem endUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storageBackend.locate? er = some (.leaf (wordLoc slot))) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbackend := rfl) (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (storageLocLoad_uint256 evm slot))

theorem endAddressGetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = endBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf endBytecode entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf endBytecode routine slot)
    (hroutine : (D_J endBytecode 0).contains routine = true)
    (hreturnJd : (D_J endBytecode 0).contains returnPc = true)
    (hretmem : solcReturnAddressFromMemWf endBytecode returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (solcAddressSlotWord slot σ I).toNat))]))) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray (solcAddressSlotWord slot σ I))
        (some [(.address (AccountAddress.ofNat (solcAddressSlotWord slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [solcAddressSlotWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (solcSlotWordAt slot σ I)))
  have hret := RD.solcAddressGetterExternal (code := endBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret endBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcAddressSlotWord slot σ I)) := by
    simpa [solcAddressSlotWord, solcSlotWordAt] using hret
  exact hret'.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by simp [initState]) henc

theorem endUint256GetterBodyCore
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = endBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD endBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hentry : solcGetterEntryWf endBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf endBytecode routine slot)
    (hroutine : (D_J endBytecode 0).contains routine = true)
    (hreturnJd : (D_J endBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf endBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))]))) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have henc :
      returnEquiv (UInt256.toByteArray (solcSlotWordAt slot σ I))
        (some [(.int (Int.ofNat (solcSlotWordAt slot σ I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (solcSlotWordAt slot σ I))
  have hret := RD.solcWordGetterExternal
    (code := endBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret endBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I) σ
        (UInt256.toByteArray (solcSlotWordAt slot σ I)) := by
    simpa [solcSlotWordAt] using hret
  exact hret'.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by simp [initState]) henc

/-! ## One-word calldata arguments -/

abbrev endBytes32ArgBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endBytes32ArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev endBytes32ArgValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (endBytes32ArgBytes I)

abbrev endBytes32ArgKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (endBytes32ArgBytes I)


theorem endBytes32ArgBytes_len {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (endBytes32ArgBytes I).length = bytes32Width.val + 1 := by
  unfold endBytes32ArgBytes
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  simp [bytes32Width]
  omega

theorem endBytes32ArgBytes_len32 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (endBytes32ArgBytes I).length = 32 := by
  have hlen := endBytes32ArgBytes_len (I := I) hsz36
  simpa [bytes32Width] using hlen

theorem endKeyValueToWord_bytes32ArgKey {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (endBytes32ArgKey I) = endBytes32ArgWord I := by
  have hlen32 : (endBytes32ArgBytes I).length = 32 :=
    endBytes32ArgBytes_len32 (I := I) hsz36
  have hword : ABI.bytesToWord (endBytes32ArgBytes I) = endBytes32ArgWord I := by
    simpa [endBytes32ArgBytes, endBytes32ArgWord] using
      (decode_word_at_eq_any I.calldata 4 (by simpa using hsz36))
  have hbytes : endBytes32ArgBytes I = EVM.Word.toBytesBE (endBytes32ArgWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := endBytes32ArgBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [endBytes32ArgKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (endBytes32ArgWord I)


/-!
The reasoning library has LOG1/LOG3/LOG4 combinators; this contract also emits two-topic auth logs.
-/


/-! ## End-local source arithmetic helpers -/

abbrev endUintBinaryLocals (x y : UInt256) : Store :=
  (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat)))

abbrev endUintBinaryLocalsZ (x y z : UInt256) : Store :=
  (endUintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

abbrev endUintBinaryLocalsM (x y m : UInt256) : Store :=
  (endUintBinaryLocals x y).insert "m" (.int (Int.ofNat m.toNat))

abbrev endWadWord : UInt256 := ⟨1000000000000000000⟩

abbrev endRayWord : UInt256 := ⟨1000000000000000000000000000⟩

theorem endUintBinaryLocals_get_x (x y : UInt256) :
    (endUintBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [endUintBinaryLocals, store_get_self]

theorem endUintBinaryLocals_get_y (x y : UInt256) :
    (endUintBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [endUintBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem endUintBinaryLocalsZ_get_x (x y z : UInt256) :
    (endUintBinaryLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [endUintBinaryLocalsZ, store_get_ne _ _ (by decide), endUintBinaryLocals_get_x]

theorem endUintBinaryLocalsZ_get_y (x y z : UInt256) :
    (endUintBinaryLocalsZ x y z).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [endUintBinaryLocalsZ, store_get_ne _ _ (by decide), endUintBinaryLocals_get_y]

theorem endUintBinaryLocalsZ_get_z (x y z : UInt256) :
    (endUintBinaryLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [endUintBinaryLocalsZ, store_get_self]

theorem endUintBinaryLocalsM_get_m (x y m : UInt256) :
    (endUintBinaryLocalsM x y m).get? "m" = some (.int (Int.ofNat m.toNat)) := by
  rw [endUintBinaryLocalsM, store_get_self]

theorem endUintBinaryLocalsM_get_y (x y m : UInt256) :
    (endUintBinaryLocalsM x y m).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [endUintBinaryLocalsM, store_get_ne _ _ (by decide), endUintBinaryLocals_get_y]

theorem endEvalExpr_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem endEvalExpr_add256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b)
    (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .add x y)) = .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem endEvalExpr_add256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .add x y)) = .revert := by
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem endEvalExpr_mul256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = a * b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .mul x y)) = .ok (.int (Int.ofNat prod.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : prod.toNat = a.toNat * b.toNat := by
    rw [hprod, umul_toNat a b hfit]
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem endEvalExpr_mul256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .mul x y)) = .revert := by
  simp [u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem endEvalExpr_div_uint256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b q : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b ≠ ⟨0⟩)
    (hq : q = UInt256.div a b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) =
      .ok (.int (Int.ofNat q.toNat)) := by
  have hbNat : ¬ b.toNat = 0 := by
    intro hzero
    exact hb (uint256_toNat_eq_zero hzero)
  have hqNat : q.toNat = a.toNat / b.toNat := by
    rw [hq, udiv_toNat]
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, hbNat, hqNat]

theorem endEvalExpr_div_uint256_revert_zero {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hb : b = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) =
      .revert := by
  subst b
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]

theorem endEvalExpr_ge_uint256_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hge : b.toNat ≤ a.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  exact_mod_cast hge

theorem endEvalExpr_eq_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem endEvalExpr_eq_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem endEvalExpr_ne_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ne lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem endEvalExpr_ne_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ne lhs rhs) =
      .ok (.bool false) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem endEvalExpr_extCodeGuard_true {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem endEvalExpr_extCodeGuard_false {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat =
        0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]


theorem endEvalExpr_or_true_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem endEvalExpr_or_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]


theorem endExecAddFunctionReturn (evm : EVM.State) {x y sum : UInt256}
    (hsum : sum = x + y) (hfit : x.toNat + y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      addFunction.body
      (.returned { contract := contract, locals := endUintBinaryLocalsZ x y sum } evm
        (some [.int (Int.ofNat sum.toNat)])) := by
  let locals := endUintBinaryLocals x y
  let localsZ := endUintBinaryLocalsZ x y sum
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hAdd :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .add (.var "x") (.var "y"))) =
          .ok (.int (Int.ofNat sum.toNat)) :=
    endEvalExpr_add256_ok hx hy hsum hfit
  have hz :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat sum.toNat)) := by
    simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := sum)
      (endUintBinaryLocalsZ_get_z x y sum)
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x)
      (endUintBinaryLocalsZ_get_x x y sum)
  have hsumNat : sum.toNat = x.toNat + y.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .ge (.var "z") (.var "x")) = .ok (.bool true) :=
    endEvalExpr_ge_uint256_true hz hxZ (by rw [hsumNat]; omega)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (u256 (.binary .add (.var "x") (.var "y"))),
          .require (.binary .ge (.var "z") (.var "x")),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat sum.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hAdd) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hz))
  simpa [addFunction, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem endExecAddFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat + y.toNat) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      addFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hAddRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .add (.var "x") (.var "y"))) = .revert :=
    endEvalExpr_add256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (u256 (.binary .add (.var "x") (.var "y"))),
          .require (.binary .ge (.var "z") (.var "x")),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hAddRev)
  simpa [addFunction, locals] using ExecFuncBody.execBlockRevert hblock

theorem endInternalAddFunctionReturn (evm : EVM.State) {locals : Store}
    {args : List Expr} {retVar : Ident} {x y sum : UInt256}
    (hargs :
      evalExprs? config { contract := contract, locals := locals } evm args =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (hsum : sum = x + y) (hfit : x.toNat + y.toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "add" args retVar)
      (.ok
        (resumeAfterInternalCall { contract := contract, locals := locals } retVar
          (some [.int (Int.ofNat sum.toNat)]))
        evm) := by
  exact internalCallFunctionReturn
    (cfg := config) (caller := { contract := contract, locals := locals })
    (evm := evm) (name := "add") (retVar := retVar) (args := args)
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (callee := addFunction) (locals := endUintBinaryLocals x y)
    hargs (by rfl)
    (by simp [addFunction, uint256, bindParams?, endUintBinaryLocals])
    (endExecAddFunctionReturn evm hsum hfit)

theorem endInternalAddFunctionRevert (evm : EVM.State) {locals : Store}
    {args : List Expr} {retVar : Ident} {x y : UInt256}
    (hargs :
      evalExprs? config { contract := contract, locals := locals } evm args =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (hover : UInt256.size ≤ x.toNat + y.toNat) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "add" args retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := { contract := contract, locals := locals })
    (evm := evm) (name := "add") (retVar := retVar) (args := args)
    (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
    (callee := addFunction) (locals := endUintBinaryLocals x y)
    hargs (by rfl)
    (by simp [addFunction, uint256, bindParams?, endUintBinaryLocals])
    (endExecAddFunctionRevert evm hover)

theorem endExecMulFunctionReturn (evm : EVM.State) {x y prod : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      mulFunction.body
      (.returned { contract := contract, locals := endUintBinaryLocalsZ x y prod } evm
        (some [.int (Int.ofNat prod.toNat)])) := by
  let locals := endUintBinaryLocals x y
  let localsZ := endUintBinaryLocalsZ x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hMul :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .mul (.var "x") (.var "y"))) =
          .ok (.int (Int.ofNat prod.toNat)) :=
    endEvalExpr_mul256_ok hx hy hprod hfit
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x)
      (endUintBinaryLocalsZ_get_x x y prod)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "y") (value := y)
      (endUintBinaryLocalsZ_get_y x y prod)
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := prod)
      (endUintBinaryLocalsZ_get_z x y prod)
  have hZeroLit :
      evalExpr? config { contract := contract, locals := localsZ } evm (.intLit 0) =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [evalExpr?, pure]
  have hReq :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .or
          (.binary .eq (.var "y") (.intLit 0))
          (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))) =
        .ok (.bool true) := by
    by_cases hy0 : y = (⟨0⟩ : UInt256)
    · have hyEqZero :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool true) := by
        apply endEvalExpr_eq_int_true hyZ hZeroLit
        rw [hy0]
      exact endEvalExpr_or_true_left hyEqZero
    · have hyEqZero :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool false) := by
        apply endEvalExpr_eq_int_false hyZ hZeroLit
        intro hbad
        exact hy0 (uint256_toNat_eq_zero (Int.ofNat.inj hbad))
      have hyNatNe : y.toNat ≠ 0 := by
        intro hzero
        exact hy0 (uint256_toNat_eq_zero hzero)
      have hdivWord : UInt256.div prod y = x := by
        apply u256_inj
        rw [udiv_toNat]
        have hprodNat : prod.toNat = x.toNat * y.toNat := by
          rw [hprod, umul_toNat x y hfit]
        rw [hprodNat]
        simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat (Nat.pos_of_ne_zero hyNatNe)
      have hDivY :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .div (.var "z") (.var "y")) = .ok (.int (Int.ofNat x.toNat)) := by
        have h := endEvalExpr_div_uint256_ok (evm := evm) (locals := localsZ)
          (x := .var "z") (y := .var "y") (a := prod) (b := y)
          (q := UInt256.div prod y) hzZ hyZ hy0 rfl
        simpa [hdivWord] using h
      have hRight :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x")) =
              .ok (.bool true) := by
        exact endEvalExpr_eq_int_true hDivY hxZ rfl
      exact endEvalExpr_or_false_right hyEqZero hRight
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (u256 (.binary .mul (.var "x") (.var "y"))),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .return [.var "z"] ]
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat prod.toNat)])) := by
    refine ExecBlock.consNormal (ExecStmt.letDecl hMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzZ))
  simpa [mulFunction, locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem endExecMulFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      mulFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hMulRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (u256 (.binary .mul (.var "x") (.var "y"))) = .revert :=
    endEvalExpr_mul256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .letDecl "z" (some uint256) (u256 (.binary .mul (.var "x") (.var "y"))),
          .require
            (.binary .or
              (.binary .eq (.var "y") (.intLit 0))
              (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))),
          .return [.var "z"] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hMulRev)
  simpa [mulFunction, locals] using ExecFuncBody.execBlockRevert hblock

theorem endExecRmulFunctionReturn (evm : EVM.State) {x y prod q : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size)
    (hq : q = UInt256.div prod endRayWord) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      rmulFunction.body
      (.returned { contract := contract, locals := endUintBinaryLocalsM x y prod } evm
        (some [.int (Int.ofNat q.toNat)])) := by
  let locals := endUintBinaryLocals x y
  let localsM := endUintBinaryLocalsM x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .var "y"] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] := by
    simp [evalExprs?, hx, hy, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
        some (endUintBinaryLocals x y) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .var "y"] "m")
        (.ok { contract := contract, locals := localsM } evm) := by
    have hbody :=
      endExecMulFunctionReturn (evm := evm) (x := x) (y := y) (prod := prod)
        hprod hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .var "y"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals x y)
      hargs (by rfl) hbind hbody
    simpa [localsM, endUintBinaryLocalsM, resumeAfterInternalCall, collapseReturns] using hstmt
  have hm :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "m") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsM] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsM) (name := "m") (value := prod)
      (endUintBinaryLocalsM_get_m x y prod)
  have hRay :
      evalExpr? config { contract := contract, locals := localsM } evm (.intLit RAY) =
        .ok (.int (Int.ofNat endRayWord.toNat)) := by
    have hRayEq : RAY = Int.ofNat endRayWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hRayEq]
  have hDiv :
      evalExpr? config { contract := contract, locals := localsM } evm
        (.binary .div (.var "m") (.intLit RAY)) =
          .ok (.int (Int.ofNat q.toNat)) :=
    endEvalExpr_div_uint256_ok hm hRay (by native_decide) hq
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "mul" [.var "x", .var "y"] "m",
          .return [.binary .div (.var "m") (.intLit RAY)] ]
        (.returned { contract := contract, locals := localsM } evm
          (some [.int (Int.ofNat q.toNat)])) := by
    refine ExecBlock.consNormal hmulStmt ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hDiv))
  simpa [rmulFunction, locals, localsM] using ExecFuncBody.execBlockRet hblock

theorem endExecRmulFunctionRevertMul (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      rmulFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (endUintBinaryLocals_get_y x y)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .var "y"] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] := by
    simp [evalExprs?, hx, hy, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
        some (endUintBinaryLocals x y) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .var "y"] "m") .reverted := by
    have hbody := endExecMulFunctionRevert (evm := evm) (x := x) (y := y) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .var "y"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals x y)
      hargs (by rfl) hbind hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "mul" [.var "x", .var "y"] "m",
          .return [.binary .div (.var "m") (.intLit RAY)] ]
        .reverted := by
    exact ExecBlock.consRevert hmulStmt
  simpa [rmulFunction, locals] using ExecFuncBody.execBlockRevert hblock

theorem endExecWdivFunctionReturn (evm : EVM.State) {x y prod q : UInt256}
    (hprod : prod = x * endWadWord) (hfit : x.toNat * endWadWord.toNat < UInt256.size)
    (hy : y ≠ ⟨0⟩) (hq : q = UInt256.div prod y) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      wdivFunction.body
      (.returned { contract := contract, locals := endUintBinaryLocalsM x y prod } evm
        (some [.int (Int.ofNat q.toNat)])) := by
  let locals := endUintBinaryLocals x y
  let localsM := endUintBinaryLocalsM x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hWad :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit WAD) =
        .ok (.int (Int.ofNat endWadWord.toNat)) := by
    have hWadEq : WAD = Int.ofNat endWadWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hWadEq]
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .intLit WAD] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] := by
    simp [evalExprs?, hx, hWad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] =
        some (endUintBinaryLocals x endWadWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .intLit WAD] "m")
        (.ok { contract := contract, locals := localsM } evm) := by
    have hbody :=
      endExecMulFunctionReturn (evm := evm) (x := x) (y := endWadWord) (prod := prod)
        hprod hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .intLit WAD])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals x endWadWord)
      hargs (by rfl) hbind hbody
    simpa [localsM, endUintBinaryLocalsM, resumeAfterInternalCall, collapseReturns] using hstmt
  have hm :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "m") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsM] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsM) (name := "m") (value := prod)
      (endUintBinaryLocalsM_get_m x y prod)
  have hyExpr :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsM] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsM) (name := "y") (value := y)
      (endUintBinaryLocalsM_get_y x y prod)
  have hDiv :
      evalExpr? config { contract := contract, locals := localsM } evm
        (.binary .div (.var "m") (.var "y")) =
          .ok (.int (Int.ofNat q.toNat)) :=
    endEvalExpr_div_uint256_ok hm hyExpr hy hq
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "mul" [.var "x", .intLit WAD] "m",
          .return [.binary .div (.var "m") (.var "y")] ]
        (.returned { contract := contract, locals := localsM } evm
          (some [.int (Int.ofNat q.toNat)])) := by
    refine ExecBlock.consNormal hmulStmt ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hDiv))
  simpa [wdivFunction, locals, localsM] using ExecFuncBody.execBlockRet hblock

theorem endExecWdivFunctionRevertMul (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * endWadWord.toNat) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      wdivFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hWad :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit WAD) =
        .ok (.int (Int.ofNat endWadWord.toNat)) := by
    have hWadEq : WAD = Int.ofNat endWadWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hWadEq]
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .intLit WAD] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] := by
    simp [evalExprs?, hx, hWad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] =
        some (endUintBinaryLocals x endWadWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .intLit WAD] "m") .reverted := by
    have hbody :=
      endExecMulFunctionRevert (evm := evm) (x := x) (y := endWadWord) hover
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .intLit WAD])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals x endWadWord)
      hargs (by rfl) hbind hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "mul" [.var "x", .intLit WAD] "m",
          .return [.binary .div (.var "m") (.var "y")] ]
        .reverted := by
    exact ExecBlock.consRevert hmulStmt
  simpa [wdivFunction, locals] using ExecFuncBody.execBlockRevert hblock

theorem endExecWdivFunctionRevertDivZero (evm : EVM.State) {x y prod : UInt256}
    (hprod : prod = x * endWadWord) (hfit : x.toNat * endWadWord.toNat < UInt256.size)
    (hy : y = ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := endUintBinaryLocals x y } evm
      wdivFunction.body .reverted := by
  let locals := endUintBinaryLocals x y
  let localsM := endUintBinaryLocalsM x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using endEvalExpr_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (endUintBinaryLocals_get_x x y)
  have hWad :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit WAD) =
        .ok (.int (Int.ofNat endWadWord.toNat)) := by
    have hWadEq : WAD = Int.ofNat endWadWord.toNat := by
      native_decide
    simp [evalExpr?, pure, hWadEq]
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [.var "x", .intLit WAD] =
        .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] := by
    simp [evalExprs?, hx, hWad, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)] =
        some (endUintBinaryLocals x endWadWord) := by
    simp [mulFunction, uint256, bindParams?, endUintBinaryLocals]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .intLit WAD] "m")
        (.ok { contract := contract, locals := localsM } evm) := by
    have hbody :=
      endExecMulFunctionReturn (evm := evm) (x := x) (y := endWadWord) (prod := prod)
        hprod hfit
    have hstmt := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "m")
      (args := [.var "x", .intLit WAD])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat endWadWord.toNat)])
      (callee := mulFunction) (locals := endUintBinaryLocals x endWadWord)
      hargs (by rfl) hbind hbody
    simpa [localsM, endUintBinaryLocalsM, resumeAfterInternalCall, collapseReturns] using hstmt
  have hm :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "m") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsM] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsM) (name := "m") (value := prod)
      (endUintBinaryLocalsM_get_m x y prod)
  have hyExpr :
      evalExpr? config { contract := contract, locals := localsM } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsM] using endEvalExpr_varUInt256 (evm := evm)
      (locals := localsM) (name := "y") (value := y)
      (endUintBinaryLocalsM_get_y x y prod)
  have hDiv :
      evalExpr? config { contract := contract, locals := localsM } evm
        (.binary .div (.var "m") (.var "y")) = .revert :=
    endEvalExpr_div_uint256_revert_zero hm hyExpr hy
  have hReturn :
      evalExprs? config { contract := contract, locals := localsM } evm
        [.binary .div (.var "m") (.var "y")] = .revert := by
    simp [evalExprs?, hDiv, EvalResult.bind, bind]
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .internalCall "mul" [.var "x", .intLit WAD] "m",
          .return [.binary .div (.var "m") (.var "y")] ]
        .reverted := by
    refine ExecBlock.consNormal hmulStmt ?_
    exact ExecBlock.consRevert (ExecStmt.returnRevert hReturn)
  simpa [wdivFunction, locals, localsM] using ExecFuncBody.execBlockRevert hblock

end Benchmarks.Dss.End
