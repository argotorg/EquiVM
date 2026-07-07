import Benchmarks.Dss.Spot.PokeBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Spot

theorem spotDecode_poke_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (pokeTransition.params.map Param.name)
      (transitionSignature pokeTransition).paramTypes I.calldata = some (pokeLocals I) := by
  simpa [config, pokeTransition, pokeLocals, pokeIlkValue, pokeIlkBytes, bytes32, bytes32Width]
    using
      (Benchmarks.Dss.Jug.decodeCalldataWithMode_legacyBytes32_ok
        (cd := I.calldata) (x := "ilk") hsz36)

theorem spotDecode_poke_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (pokeTransition.params.map Param.name)
      (transitionSignature pokeTransition).paramTypes I.calldata = none := by
  simpa [config, pokeTransition, bytes32, bytes32Width] using
    (Benchmarks.Dss.Jug.decodeCalldataWithMode_legacyBytes32_none_short
      (cd := I.calldata) (x := "ilk") hsz4 hshort)

theorem pokeIlkBytes_len32 {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (pokeIlkBytes I).length = 32 := by
  simpa [pokeIlkBytes] using ilksArgBytes_len32 (I := I) hsz36

theorem pokeIlkBytes_eq_toBytesBE {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    pokeIlkBytes I = EVM.Word.toBytesBE (pokeIlkWord I) := by
  have hlen32 : (pokeIlkBytes I).length = 32 :=
    pokeIlkBytes_len32 (I := I) hsz36
  have hword : ABI.bytesToWord (pokeIlkBytes I) = pokeIlkWord I := by
    simpa [pokeIlkBytes, pokeIlkWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hto := toBytesBE_bytesToWord_of_length (bs := pokeIlkBytes I) hlen32
  rw [hword] at hto
  exact hto.symm

theorem keyValueToWord_pokeIlkKey {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (pokeIlkKey I) = pokeIlkWord I := by
  simpa [pokeIlkKey, pokeIlkWord, pokeIlkBytes, ilksArgKey] using
    keyValueToWord_ilksArgKey (I := I) hsz36

theorem pokePipSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    pokePipSlotFor I = solcMappingSlot ⟨1⟩ (pokeIlkWord I) := by
  unfold pokePipSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_pokeIlkKey hsz36]

theorem pokeMatSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    pokeMatSlotFor I = solcMappingSlot ⟨1⟩ (pokeIlkWord I) + ⟨1⟩ := by
  simp [pokeMatSlotFor, pokePipSlotFor_eq hsz36]

theorem pokeLocals_get_ilk (I : ExecutionEnv) :
    (pokeLocals I).get? "ilk" =
      some (.fixedBytes bytes32Width (pokeIlkBytes I)) := by
  rw [pokeLocals, store_get_self]

theorem pokeLocals_get_ilks (I : ExecutionEnv) :
    (pokeLocals I).get? "ilks" = none := by
  rw [pokeLocals, store_get_ne _ _ (by decide)]
  simp

theorem pokeLocals_get_vat (I : ExecutionEnv) :
    (pokeLocals I).get? "vat" = none := by
  rw [pokeLocals, store_get_ne _ _ (by decide)]
  simp

theorem pokeSpotLocals_get_ilk (I : ExecutionEnv) (out : ByteArray) (spot : UInt256) :
    (pokeSpotLocals I out spot).get? "ilk" =
      some (.fixedBytes bytes32Width (pokeIlkBytes I)) := by
  rw [pokeSpotLocals, store_get_ne _ _ (by decide), pokeHasLocals,
    store_get_ne _ _ (by decide), pokeValLocals, store_get_ne _ _ (by decide),
    pokePeekLocals, store_get_ne _ _ (by decide), pokeLocals_get_ilk]

theorem pokeSpotLocals_get_vat (I : ExecutionEnv) (out : ByteArray) (spot : UInt256) :
    (pokeSpotLocals I out spot).get? "vat" = none := by
  rw [pokeSpotLocals, store_get_ne _ _ (by decide), pokeHasLocals,
    store_get_ne _ _ (by decide), pokeValLocals, store_get_ne _ _ (by decide),
    pokePeekLocals, store_get_ne _ _ (by decide), pokeLocals_get_vat]

theorem pokeSpotLocals_get_val (I : ExecutionEnv) (out : ByteArray) (spot : UInt256) :
    (pokeSpotLocals I out spot).get? "val" =
      some (.fixedBytes bytes32Width (pokePeekValBytes out)) := by
  rw [pokeSpotLocals, store_get_ne _ _ (by decide), pokeHasLocals,
    store_get_ne _ _ (by decide), pokeValLocals, store_get_self]

theorem pokeSpotLocals_get_spot (I : ExecutionEnv) (out : ByteArray) (spot : UInt256) :
    (pokeSpotLocals I out spot).get? "spot" = some (.int (Int.ofNat spot.toNat)) := by
  rw [pokeSpotLocals, store_get_self]

theorem evalExpr_pokePeekVal (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config { contract := contract, locals := pokePeekLocals I out } evm
      (.tupleGet (.var "peekRet") 0) =
        .ok (.fixedBytes bytes32Width (pokePeekValBytes out)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := pokePeekLocals I out } evm
        (.var "peekRet") =
          .ok (.tuple [.fixedBytes bytes32Width (pokePeekValBytes out),
            .bool (pokePeekHasBool out)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((pokePeekLocals I out).get? "peekRet") =
        .ok (.tuple [.fixedBytes bytes32Width (pokePeekValBytes out),
          .bool (pokePeekHasBool out)])
    rw [pokePeekLocals, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind, pokePeekReturnValues, collapseReturns]

theorem evalExpr_pokePeekHas (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config { contract := contract, locals := pokeValLocals I out } evm
      (.tupleGet (.var "peekRet") 1) =
        .ok (.bool (pokePeekHasBool out)) := by
  have hvar :
      evalExpr? config { contract := contract, locals := pokeValLocals I out } evm
        (.var "peekRet") =
          .ok (.tuple [.fixedBytes bytes32Width (pokePeekValBytes out),
            .bool (pokePeekHasBool out)]) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
      ((pokeValLocals I out).get? "peekRet") =
        .ok (.tuple [.fixedBytes bytes32Width (pokePeekValBytes out),
          .bool (pokePeekHasBool out)])
    rw [pokeValLocals, store_get_ne _ _ (by decide), pokePeekLocals, store_get_self]
    rfl
  rw [evalExpr?]
  simp [hvar, tupleGetValue?, EvalResult.bind, bind, pokePeekReturnValues, collapseReturns]

theorem evalExpr_pokeHas (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (.var "has") = .ok (.bool (pokePeekHasBool out)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable
      ((pokeSpotLocals I out ⟨0⟩).get? "has") =
    .ok (.bool (pokePeekHasBool out))
  rw [pokeSpotLocals, store_get_ne _ _ (by decide), pokeHasLocals, store_get_self]
  rfl

theorem evalExpr_pokeHas_false {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (hhas : pokePeekHasWord out = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (.var "has") = .ok (.bool false) := by
  have h := evalExpr_pokeHas evm I out
  simpa [pokePeekHasBool, hhas] using h

theorem evalExpr_pokeHas_true {evm : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (hhas : pokePeekHasWord out ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (.var "has") = .ok (.bool true) := by
  have h := evalExpr_pokeHas evm I out
  simpa [pokePeekHasBool, hhas] using h

theorem pokeBillion_toNat : pokeBillion.toNat = 1000000000 := by
  change (UInt256.ofNat 1000000000).toNat = 1000000000
  exact ulit_toNat' _ (by native_decide)

theorem pokeRay_toNat : pokeRay.toNat = 1000000000000000000000000000 := by
  change (UInt256.ofNat 1000000000000000000000000000).toNat =
    1000000000000000000000000000
  exact ulit_toNat' _ (by native_decide)

theorem billion_eq_pokeBillion_toNat : billion = Int.ofNat pokeBillion.toNat := by
  simp [billion, pokeBillion_toNat]

theorem one_eq_pokeRay_toNat : one = Int.ofNat pokeRay.toNat := by
  simp [one, pokeRay_toNat]

theorem spotUintBinaryLocals_get_x (x y : UInt256) :
    (spotUintBinaryLocals x y).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [spotUintBinaryLocals, store_get_self]

theorem spotUintBinaryLocals_get_y (x y : UInt256) :
    (spotUintBinaryLocals x y).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [spotUintBinaryLocals, store_get_ne _ _ (by decide), store_get_self]

theorem spotUintBinaryLocalsZ_get_x (x y z : UInt256) :
    (spotUintBinaryLocalsZ x y z).get? "x" = some (.int (Int.ofNat x.toNat)) := by
  rw [spotUintBinaryLocalsZ, store_get_ne _ _ (by decide), spotUintBinaryLocals_get_x]

theorem spotUintBinaryLocalsZ_get_y (x y z : UInt256) :
    (spotUintBinaryLocalsZ x y z).get? "y" = some (.int (Int.ofNat y.toNat)) := by
  rw [spotUintBinaryLocalsZ, store_get_ne _ _ (by decide), spotUintBinaryLocals_get_y]

theorem spotUintBinaryLocalsZ_get_z (x y z : UInt256) :
    (spotUintBinaryLocalsZ x y z).get? "z" = some (.int (Int.ofNat z.toNat)) := by
  rw [spotUintBinaryLocalsZ, store_get_self]

theorem spotUintBinaryLocalsZAssigned_get_z (x y old new : UInt256) :
    (spotUintBinaryLocalsZAssigned x y old new).get? "z" =
      some (.int (Int.ofNat new.toNat)) := by
  rw [spotUintBinaryLocalsZAssigned, store_get_self]

theorem pokeValScaledLocals_get_ilk (I : ExecutionEnv) (out : ByteArray)
    (valScaled : UInt256) :
    (pokeValScaledLocals I out valScaled).get? "ilk" =
      some (.fixedBytes bytes32Width (pokeIlkBytes I)) := by
  rw [pokeValScaledLocals, store_get_ne _ _ (by decide), pokeSpotLocals_get_ilk]

theorem pokeValScaledLocals_get_vat (I : ExecutionEnv) (out : ByteArray)
    (valScaled : UInt256) :
    (pokeValScaledLocals I out valScaled).get? "vat" = none := by
  rw [pokeValScaledLocals, store_get_ne _ _ (by decide), pokeSpotLocals_get_vat]

theorem pokeValScaledLocals_get_val (I : ExecutionEnv) (out : ByteArray)
    (valScaled : UInt256) :
    (pokeValScaledLocals I out valScaled).get? "val" =
      some (.fixedBytes bytes32Width (pokePeekValBytes out)) := by
  rw [pokeValScaledLocals, store_get_ne _ _ (by decide), pokeSpotLocals_get_val]

theorem pokeValScaledLocals_get_par (I : ExecutionEnv) (out : ByteArray)
    (valScaled : UInt256) :
    (pokeValScaledLocals I out valScaled).get? "par" = none := by
  rw [pokeValScaledLocals, store_get_ne _ _ (by decide), pokeSpotLocals,
    store_get_ne _ _ (by decide), pokeHasLocals, store_get_ne _ _ (by decide),
    pokeValLocals, store_get_ne _ _ (by decide), pokePeekLocals,
    store_get_ne _ _ (by decide), pokeLocals, store_get_ne _ _ (by decide)]
  simp

theorem pokeValScaledLocals_get_valScaled (I : ExecutionEnv) (out : ByteArray)
    (valScaled : UInt256) :
    (pokeValScaledLocals I out valScaled).get? "valScaled" =
      some (.int (Int.ofNat valScaled.toNat)) := by
  rw [pokeValScaledLocals, store_get_self]

theorem pokeSpot1Locals_get_ilk (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 : UInt256) :
    (pokeSpot1Locals I out valScaled spot1).get? "ilk" =
      some (.fixedBytes bytes32Width (pokeIlkBytes I)) := by
  rw [pokeSpot1Locals, store_get_ne _ _ (by decide),
    pokeValScaledLocals_get_ilk]

theorem pokeSpot1Locals_get_vat (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 : UInt256) :
    (pokeSpot1Locals I out valScaled spot1).get? "vat" = none := by
  rw [pokeSpot1Locals, store_get_ne _ _ (by decide),
    pokeValScaledLocals_get_vat]

theorem pokeSpot1Locals_get_ilks (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 : UInt256) :
    (pokeSpot1Locals I out valScaled spot1).get? "ilks" = none := by
  rw [pokeSpot1Locals, store_get_ne _ _ (by decide), pokeValScaledLocals,
    store_get_ne _ _ (by decide), pokeSpotLocals, store_get_ne _ _ (by decide),
    pokeHasLocals, store_get_ne _ _ (by decide), pokeValLocals,
    store_get_ne _ _ (by decide), pokePeekLocals, store_get_ne _ _ (by decide),
    pokeLocals_get_ilks]

theorem pokeSpot1Locals_get_spot1 (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 : UInt256) :
    (pokeSpot1Locals I out valScaled spot1).get? "spot1" =
      some (.int (Int.ofNat spot1.toNat)) := by
  rw [pokeSpot1Locals, store_get_self]

theorem pokeSpot2Locals_get_ilk (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 spot2 : UInt256) :
    (pokeSpot2Locals I out valScaled spot1 spot2).get? "ilk" =
      some (.fixedBytes bytes32Width (pokeIlkBytes I)) := by
  rw [pokeSpot2Locals, store_get_ne _ _ (by decide),
    pokeSpot1Locals_get_ilk]

theorem pokeSpot2Locals_get_vat (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 spot2 : UInt256) :
    (pokeSpot2Locals I out valScaled spot1 spot2).get? "vat" = none := by
  rw [pokeSpot2Locals, store_get_ne _ _ (by decide), pokeSpot1Locals_get_vat]

theorem pokeSpot2Locals_get_spot2 (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 spot2 : UInt256) :
    (pokeSpot2Locals I out valScaled spot1 spot2).get? "spot2" =
      some (.int (Int.ofNat spot2.toNat)) := by
  rw [pokeSpot2Locals, store_get_self]

theorem pokeSpotAssignedLocals_get_ilk (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 spot2 : UInt256) :
    (pokeSpotAssignedLocals I out valScaled spot1 spot2).get? "ilk" =
      some (.fixedBytes bytes32Width (pokeIlkBytes I)) := by
  rw [pokeSpotAssignedLocals, store_get_ne _ _ (by decide),
    pokeSpot2Locals_get_ilk]

theorem pokeSpotAssignedLocals_get_vat (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 spot2 : UInt256) :
    (pokeSpotAssignedLocals I out valScaled spot1 spot2).get? "vat" = none := by
  rw [pokeSpotAssignedLocals, store_get_ne _ _ (by decide),
    pokeSpot2Locals_get_vat]

theorem pokeSpotAssignedLocals_get_spot (I : ExecutionEnv) (out : ByteArray)
    (valScaled spot1 spot2 : UInt256) :
    (pokeSpotAssignedLocals I out valScaled spot1 spot2).get? "spot" =
      some (.int (Int.ofNat spot2.toNat)) := by
  rw [pokeSpotAssignedLocals, store_get_self]

theorem evalExpr_spot_varUInt256 {evm : EVM.State} {locals : Store}
    {name : Ident} {value : UInt256}
    (h : locals.get? name = some (.int (Int.ofNat value.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat value.toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? name) =
    .ok (.int (Int.ofNat value.toNat))
  rw [h]
  rfl

theorem evalExpr_spot_mul256_ok {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b prod : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hprod : prod = a * b)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .ok (.int (Int.ofNat prod.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : prod.toNat = a.toNat * b.toNat := by
    rw [hprod, umul_toNat a b hfit]
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem evalExpr_spot_mul256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (mul256 x y) =
      .revert := by
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem evalExpr_spot_div_uint256_ok {evm : EVM.State} {locals : Store}
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

theorem evalExpr_spot_div_uint256_revert {evm : EVM.State} {locals : Store}
    {x y : Expr} {a : UInt256}
    (hx : evalExpr? config { contract := contract, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? config { contract := contract, locals := locals } evm y =
      .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .div x y) =
      .revert := by
  simp [evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?]

theorem evalExpr_spot_eq_int_true {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a = b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool true) := by
  subst h
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]

theorem evalExpr_spot_eq_int_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : Int}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs = .ok (.int a))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs = .ok (.int b))
    (h : a ≠ b) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .eq lhs rhs) =
      .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?, h]

theorem evalExpr_spot_or_true_left {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool true)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs]

theorem evalExpr_spot_or_false_right {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {b : Bool}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.bool false))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.bool b)) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .or lhs rhs) =
      .ok (.bool b) := by
  simp [evalExpr?, EvalResult.bind, bind, pure, hlhs, hrhs]

theorem spot_u256_mul_div_overflow_ne (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (y * x) y ≠ x := by
  intro hEq
  have hyNatNe : y.toNat ≠ 0 := by
    intro hy0
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hy0]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hnat := congrArg UInt256.toNat hEq
  rw [udiv_toNat, u256_mul_op_toNat] at hnat
  have hremLt : y.toNat * x.toNat % UInt256.size < y.toNat * x.toNat := by
    have hmodLt : y.toNat * x.toNat % UInt256.size < UInt256.size :=
      Nat.mod_lt _ (by norm_num [UInt256.size])
    have hover' : UInt256.size ≤ y.toNat * x.toNat := by
      simpa [Nat.mul_comm] using hover
    omega
  have hle0 :=
    Nat.mul_div_le (y.toNat * x.toNat % UInt256.size) y.toNat
  rw [hnat] at hle0
  have hle : y.toNat * x.toNat ≤ y.toNat * x.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega

theorem evalExpr_pokeValCastUInt256_ofLocals {evm : EVM.State} {locals : Store}
    {out : ByteArray}
    (hval : locals.get? "val" = some (.fixedBytes bytes32Width (pokePeekValBytes out)))
    (hlo : 32 ≤ out.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.cast (.var "val") uint256St) =
        .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) := by
  have hval :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "val") = .ok (.fixedBytes bytes32Width (pokePeekValBytes out)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable
        (locals.get? "val") =
      .ok (.fixedBytes bytes32Width (pokePeekValBytes out))
    rw [hval]
    rfl
  have hword :
      ABI.bytesToWord (out.toList.take 32) = pokePeekValWord out := by
    simpa [pokePeekValWord] using
      (bytesToWord_take32_eq_extract0_32 (returndata := out))
  have htakeLen : (out.toList.take 32).length = 32 := by
    have hlist : out.toList.length = out.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [List.length_take, hlist]
    omega
  have hfromLt : fromBytesBigEndian (out.toList.take 32) < UInt256.size := by
    unfold fromBytesBigEndian
    have hle := EVM.fromBytes'_le (bs := (out.toList.take 32).reverse)
    rw [List.length_reverse, htakeLen] at hle
    simpa [UInt256.size] using hle
  have hwordNat :
      fromBytesBigEndian (out.toList.take 32) = (pokePeekValWord out).toNat := by
    have h := congrArg UInt256.toNat hword
    have hfromLtData :
        fromBytesBigEndian (List.take 32 out.data.toList) < UInt256.size := by
      simpa [byteArray_toList_eq] using hfromLt
    unfold ABI.bytesToWord at h
    simpa [fromByteArrayBigEndian, byteArray_toList_eq,
      UInt256.toNat_ofNat_of_lt hfromLtData] using h
  have hlen : min 32 out.toList.length = fixedBytesSize bytes32Width := by
    rw [byteArray_toList_eq, Array.length_toList]
    simp [fixedBytesSize, bytes32Width]
    omega
  simp [evalExpr?, EvalResult.bind, bind, hval, castValue?, fixedBytesToNat?,
    fixedBytesValid, bytes32Width, uint256St, uint256Int, pokePeekValBytes, hwordNat, hlen]
  rfl

theorem evalExpr_pokeValCastUInt256 (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (hlo : 32 ≤ out.size) :
    evalExpr? config { contract := contract, locals := pokeSpotLocals I out ⟨0⟩ } evm
      (.cast (.var "val") uint256St) =
        .ok (.int (Int.ofNat (pokePeekValWord out).toNat)) :=
  evalExpr_pokeValCastUInt256_ofLocals (evm := evm)
    (locals := pokeSpotLocals I out ⟨0⟩) (out := out)
    (pokeSpotLocals_get_val I out ⟨0⟩) hlo

abbrev pokeParWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  spotSlotWord ⟨3⟩ σ I

abbrev pokeMatWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  spotSlotWord (pokeMatSlotFor I) σ I

theorem evalExpr_pokeStorageParOfLocals {evm : EVM.State} {locals : Store}
    (hpar : locals.get? "par" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage parRef) =
      .ok (.int (Int.ofNat (pokeParWord evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := parRef) (er := ({ base := "par", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨3⟩)
    (value := .int (Int.ofNat (pokeParWord evm.accountMap evm.executionEnv).toNat))
    hpar
    (by simp [evalStorageRef, evalStorageRefSteps, parRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, parRef, uint256St])
    (by rfl)
    (by simpa [pokeParWord, spotSlotWord] using spotStorageLocLoad_uint256 evm ⟨3⟩)

theorem evalExpr_pokeStorageMatOfLocals {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store}
    (hsz36 : 36 ≤ I.calldata.size) (henv : evm.executionEnv = I)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (pokeIlkBytes I)))
    (hilks : locals.get? "ilks" = none) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (ilksF (.var "ilk") "mat")) =
        .ok (.int (Int.ofNat (pokeMatWord evm.accountMap I).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := ilksF (.var "ilk") "mat")
    (er := ({ base := "ilks", steps := [.mindex (pokeIlkKey I), .field "mat"] } :
      EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc (pokeMatSlotFor I))
    (value := .int (Int.ofNat (pokeMatWord evm.accountMap I).toNat))
    hilks
    (by
      have hkeyLen : (pokeIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using pokeIlkBytes_len32 (I := I) hsz36
      have hilk' :
          locals["ilk"]? = some (.fixedBytes bytes32Width (pokeIlkBytes I)) := by
        simpa [Std.HashMap.get?_eq_getElem?] using hilk
      simp [pokeIlkKey, pokeIlkValue, evalStorageRef, evalStorageRefSteps,
        evalStorageRefStep, ilksF, evalExpr?, valueToKey?, EvalResult.ofOption,
        EvalResult.bind, pure, bind, hkeyLen, hilk'])
    (by
      simp [pokeIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, uint256St])
    (by rfl)
    (by
      cases henv
      simpa [pokeMatWord, spotSlotWord] using
        spotStorageLocLoad_uint256 evm (pokeMatSlotFor evm.executionEnv))

theorem evalExprs_pokeVatFileArgs_ofLocals
    (evm : EVM.State) (I : ExecutionEnv) {locals : Store} (spot : UInt256)
    (hilk : locals.get? "ilk" = some (.fixedBytes bytes32Width (pokeIlkBytes I)))
    (hspot : locals.get? "spot" = some (.int (Int.ofNat spot.toNat))) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.var "ilk", spotParamLit, .var "spot"] =
        .ok [.fixedBytes bytes32Width (pokeIlkBytes I),
          .fixedBytes bytes32Width pokeSpotParamBytes, .int (Int.ofNat spot.toNat)] := by
  have hilkExpr :
      evalExpr? config { contract := contract, locals := locals } evm (.var "ilk") =
        .ok (.fixedBytes bytes32Width (pokeIlkBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") =
      .ok (.fixedBytes bytes32Width (pokeIlkBytes I))
    rw [hilk]
    rfl
  have hwhat :
      evalExpr? config { contract := contract, locals := locals } evm spotParamLit =
        .ok (.fixedBytes bytes32Width pokeSpotParamBytes) := by
    simp [spotParamLit, pokeSpotParamBytes, evalExpr?, pure]
  have hspotExpr :
      evalExpr? config { contract := contract, locals := locals } evm (.var "spot") =
        .ok (.int (Int.ofNat spot.toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "spot") =
      .ok (.int (Int.ofNat spot.toNat))
    rw [hspot]
    rfl
  simp [evalExprs?, hilkExpr, hwhat, hspotExpr, EvalResult.bind, bind, pure]

theorem execSpotMulFunctionReturn (evm : EVM.State) {x y prod : UInt256}
    (hprod : prod = x * y) (hfit : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody config { contract := contract, locals := spotUintBinaryLocals x y } evm
      mulFunction.body
      (.returned { contract := contract, locals := spotUintBinaryLocalsZ x y prod } evm
        (some [.int (Int.ofNat prod.toNat)])) := by
  let locals := spotUintBinaryLocals x y
  let localsZ := spotUintBinaryLocalsZ x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (spotUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (spotUintBinaryLocals_get_y x y)
  have hMul :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "y")) = .ok (.int (Int.ofNat prod.toNat)) :=
    evalExpr_spot_mul256_ok hx hy hprod hfit
  have hxZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [localsZ] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsZ) (name := "x") (value := x)
      (spotUintBinaryLocalsZ_get_x x y prod)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsZ) (name := "y") (value := y)
      (spotUintBinaryLocalsZ_get_y x y prod)
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := prod)
      (spotUintBinaryLocalsZ_get_z x y prod)
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
        apply evalExpr_spot_eq_int_true hyZ hZeroLit
        rw [hy0]
      exact evalExpr_spot_or_true_left hyEqZero
    · have hyEqZero :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool false) := by
        apply evalExpr_spot_eq_int_false hyZ hZeroLit
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
        simpa [Nat.mul_comm] using Nat.mul_div_right x.toNat
          (Nat.pos_of_ne_zero hyNatNe)
      have hDivY :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .div (.var "z") (.var "y")) = .ok (.int (Int.ofNat x.toNat)) := by
        have h := evalExpr_spot_div_uint256_ok (evm := evm) (locals := localsZ)
          (x := .var "z") (y := .var "y") (a := prod) (b := y)
          (q := UInt256.div prod y) hzZ hyZ hy0 rfl
        simpa [hdivWord] using h
      have hRight :
          evalExpr? config { contract := contract, locals := localsZ } evm
            (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x")) =
              .ok (.bool true) := by
        exact evalExpr_spot_eq_int_true hDivY hxZ rfl
      exact evalExpr_spot_or_false_right hyEqZero hRight
  have hzRet :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := hzZ
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm mulFunction.body
        (.returned { contract := contract, locals := localsZ } evm
          (some [.int (Int.ofNat prod.toNat)])) := by
    simp only [mulFunction, checkedMulUintInto, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.letDecl hMul) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hReq) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzRet))
  simpa [locals, localsZ] using ExecFuncBody.execBlockRet hblock

theorem execSpotMulFunctionRevert (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody config { contract := contract, locals := spotUintBinaryLocals x y } evm
      mulFunction.body .reverted := by
  let locals := spotUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (spotUintBinaryLocals_get_x x y)
  have hy :
      evalExpr? config { contract := contract, locals := locals } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [locals] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals) (name := "y") (value := y) (spotUintBinaryLocals_get_y x y)
  have hMulRev :
      evalExpr? config { contract := contract, locals := locals } evm
        (mul256 (.var "x") (.var "y")) = .revert :=
    evalExpr_spot_mul256_revert hx hy hover
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm mulFunction.body
        .reverted := by
    simp only [mulFunction, checkedMulUintInto, List.cons_append, List.nil_append]
    exact ExecBlock.consRevert (ExecStmt.letDeclRevert hMulRev)
  simpa [locals] using ExecFuncBody.execBlockRevert hblock

theorem execSpotRdivFunctionReturn (evm : EVM.State) {x y prod q : UInt256}
    (hprod : prod = x * pokeRay) (hfit : x.toNat * pokeRay.toNat < UInt256.size)
    (hy : y ≠ ⟨0⟩) (hq : q = UInt256.div prod y) :
    ExecFuncBody config { contract := contract, locals := spotUintBinaryLocals x y } evm
      rdivFunction.body
      (.returned { contract := contract, locals := spotUintBinaryLocalsZAssigned x y prod q }
        evm (some [.int (Int.ofNat q.toNat)])) := by
  let locals := spotUintBinaryLocals x y
  let localsZ := spotUintBinaryLocalsZ x y prod
  let localsQ := spotUintBinaryLocalsZAssigned x y prod q
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (spotUintBinaryLocals_get_x x y)
  have hRayLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit one) =
        .ok (.int (Int.ofNat pokeRay.toNat)) := by
    simp [evalExpr?, pure, one_eq_pokeRay_toNat]
  have hmulArgs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.var "x", .intLit one] =
          .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat pokeRay.toNat)] := by
    simp [evalExprs?, hx, hRayLit, EvalResult.bind, bind, pure]
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    rfl
  have hbindMul :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat pokeRay.toNat)] =
        some (spotUintBinaryLocals x pokeRay) := by
    simp [mulFunction, uint256, bindParams?, spotUintBinaryLocals,
      one_eq_pokeRay_toNat]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .intLit one] "z")
        (.ok { contract := contract, locals := localsZ } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "z")
      (args := [.var "x", .intLit one])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat pokeRay.toNat)])
      (callee := mulFunction) (locals := spotUintBinaryLocals x pokeRay)
      hmulArgs hlookupMul hbindMul
      (execSpotMulFunctionReturn evm (x := x) (y := pokeRay) (prod := prod)
        hprod hfit)
    simpa [resumeAfterInternalCall, locals, localsZ, spotUintBinaryLocalsZ] using h
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := prod)
      (spotUintBinaryLocalsZ_get_z x y prod)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat y.toNat)) := by
    simpa [localsZ] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsZ) (name := "y") (value := y)
      (spotUintBinaryLocalsZ_get_y x y prod)
  have hDiv :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "z") (.var "y")) = .ok (.int (Int.ofNat q.toNat)) :=
    evalExpr_spot_div_uint256_ok hzZ hyZ hy hq
  have hAssign :
      assignStorageRef? config { contract := contract, locals := localsZ } evm .localVar
          { base := "z" } (.int (Int.ofNat q.toNat)) =
        .ok ({ contract := contract, locals := localsQ }, evm) := by
    simp [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure, localsQ,
      spotUintBinaryLocalsZAssigned, localsZ, spotUintBinaryLocalsZ]
  have hzQ :
      evalExpr? config { contract := contract, locals := localsQ } evm (.var "z") =
        .ok (.int (Int.ofNat q.toNat)) := by
    simpa [localsQ] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsQ) (name := "z") (value := q)
      (spotUintBinaryLocalsZAssigned_get_z x y prod q)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rdivFunction.body
        (.returned { contract := contract, locals := localsQ } evm
          (some [.int (Int.ofNat q.toNat)])) := by
    simp only [rdivFunction, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.assign hDiv hAssign) ?_
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton hzQ))
  simpa [locals, localsQ] using ExecFuncBody.execBlockRet hblock

theorem execSpotRdivFunctionRevertMul (evm : EVM.State) {x y : UInt256}
    (hover : UInt256.size ≤ x.toNat * pokeRay.toNat) :
    ExecFuncBody config { contract := contract, locals := spotUintBinaryLocals x y } evm
      rdivFunction.body .reverted := by
  let locals := spotUintBinaryLocals x y
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (spotUintBinaryLocals_get_x x y)
  have hRayLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit one) =
        .ok (.int (Int.ofNat pokeRay.toNat)) := by
    simp [evalExpr?, pure, one_eq_pokeRay_toNat]
  have hmulArgs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.var "x", .intLit one] =
          .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat pokeRay.toNat)] := by
    simp [evalExprs?, hx, hRayLit, EvalResult.bind, bind, pure]
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    rfl
  have hbindMul :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat pokeRay.toNat)] =
        some (spotUintBinaryLocals x pokeRay) := by
    simp [mulFunction, uint256, bindParams?, spotUintBinaryLocals,
      one_eq_pokeRay_toNat]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .intLit one] "z") .reverted :=
    internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "z")
      (args := [.var "x", .intLit one])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat pokeRay.toNat)])
      (callee := mulFunction) (locals := spotUintBinaryLocals x pokeRay)
      hmulArgs hlookupMul hbindMul
      (execSpotMulFunctionRevert evm (x := x) (y := pokeRay) hover)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rdivFunction.body
        .reverted := by
    simp only [rdivFunction, List.cons_append, List.nil_append]
    exact ExecBlock.consRevert hmulStmt
  simpa [locals] using ExecFuncBody.execBlockRevert hblock

theorem execSpotRdivFunctionRevertDivZero (evm : EVM.State) {x y prod : UInt256}
    (hprod : prod = x * pokeRay) (hfit : x.toNat * pokeRay.toNat < UInt256.size)
    (hyZero : y = ⟨0⟩) :
    ExecFuncBody config { contract := contract, locals := spotUintBinaryLocals x y } evm
      rdivFunction.body .reverted := by
  let locals := spotUintBinaryLocals x y
  let localsZ := spotUintBinaryLocalsZ x y prod
  have hx :
      evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
        .ok (.int (Int.ofNat x.toNat)) := by
    simpa [locals] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := locals) (name := "x") (value := x) (spotUintBinaryLocals_get_x x y)
  have hRayLit :
      evalExpr? config { contract := contract, locals := locals } evm (.intLit one) =
        .ok (.int (Int.ofNat pokeRay.toNat)) := by
    simp [evalExpr?, pure, one_eq_pokeRay_toNat]
  have hmulArgs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.var "x", .intLit one] =
          .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat pokeRay.toNat)] := by
    simp [evalExprs?, hx, hRayLit, EvalResult.bind, bind, pure]
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    rfl
  have hbindMul :
      bindParams? mulFunction.params
          [.int (Int.ofNat x.toNat), .int (Int.ofNat pokeRay.toNat)] =
        some (spotUintBinaryLocals x pokeRay) := by
    simp [mulFunction, uint256, bindParams?, spotUintBinaryLocals,
      one_eq_pokeRay_toNat]
  have hmulStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.internalCall "mul" [.var "x", .intLit one] "z")
        (.ok { contract := contract, locals := localsZ } evm) := by
    have h := internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (name := "mul") (retVar := "z")
      (args := [.var "x", .intLit one])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat pokeRay.toNat)])
      (callee := mulFunction) (locals := spotUintBinaryLocals x pokeRay)
      hmulArgs hlookupMul hbindMul
      (execSpotMulFunctionReturn evm (x := x) (y := pokeRay) (prod := prod)
        hprod hfit)
    simpa [resumeAfterInternalCall, locals, localsZ, spotUintBinaryLocalsZ] using h
  have hzZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "z") =
        .ok (.int (Int.ofNat prod.toNat)) := by
    simpa [localsZ] using evalExpr_spot_varUInt256 (evm := evm)
      (locals := localsZ) (name := "z") (value := prod)
      (spotUintBinaryLocalsZ_get_z x y prod)
  have hyZ :
      evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
        .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    have hyRaw :
        evalExpr? config { contract := contract, locals := localsZ } evm (.var "y") =
          .ok (.int (Int.ofNat y.toNat)) := by
      simpa [localsZ] using evalExpr_spot_varUInt256 (evm := evm)
        (locals := localsZ) (name := "y") (value := y)
        (spotUintBinaryLocalsZ_get_y x y prod)
    simpa [hyZero] using hyRaw
  have hDivRev :
      evalExpr? config { contract := contract, locals := localsZ } evm
        (.binary .div (.var "z") (.var "y")) = .revert :=
    evalExpr_spot_div_uint256_revert hzZ hyZ
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm rdivFunction.body
        .reverted := by
    simp only [rdivFunction, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal hmulStmt ?_
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert hDivRev)
  simpa [locals] using ExecFuncBody.execBlockRevert hblock
end Benchmarks.Dss.Spot
