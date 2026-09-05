import Benchmarks.Dss.Clipper.Fallback
import Reasoning.EVMWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperRuntimePatchesWindowDisjoint32Bool (v : ClipperImmutables)
    (lo hi : Nat)
    (h : patchOffsetsWindowDisjoint32Bool lo hi
      [1463, 2437, 3145, 4318, 4441, 4751, 5115, 6295, 7936,
       1510, 1661, 2221, 2369, 4239, 4866, 5046, 6800, 8747] = true) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  apply patchesWindowDisjoint32_of_offsets_bool
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk, patchOffsetsWindowDisjoint32Bool]
  | some bs =>
      simpa [hIlk] using h

theorem clipperRuntimeDecodeDisjoint (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {pc : UInt256} {res : Operation × Option (UInt256 × Nat)}
    (hbyte : patchOffsetsWindowDisjoint32Bool pc.toNat (pc.toNat + 1)
      [1463, 2437, 3145, 4318, 4441, 4751, 5115, 6295, 7936,
       1510, 1661, 2221, 2369, 4239, 4866, 5046, 6800, 8747] = true)
    (hargs :
      patchOffsetsWindowDisjoint32Bool (pc.toNat + 1)
        (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2))
        [1463, 2437, 3145, 4318, 4441, 4751, 5115, 6295, 7936,
         1510, 1661, 2221, 2369, 4239, 4866, 5046, 6800, 8747] = true)
    (hdec : decode clipperBytecode pc = some res)
    (hi64 : pc.toNat + 1 < 2 ^ 64)
    (harg64 :
      pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2) < 2 ^ 64) :
    decode code pc = some res :=
  patchRuntime_decode_disjoint_of_decode_res hpatch
    (clipperRuntimePatchesWindowDisjoint32Bool v pc.toNat (pc.toNat + 1) hbyte)
    (clipperRuntimePatchesWindowDisjoint32Bool v (pc.toNat + 1)
      (pc.toNat + 1 + (match res.2 with | none => 0 | some p => p.2)) hargs)
    hdec hi64 harg64

macro "clipper_runtime_decode" : tactic =>
  `(tactic| first
    | clipper_decode
    | exact clipperRuntimeDecodeDisjoint _ (by assumption)
        (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide))

theorem clipperJumpDest8259 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8259⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8266 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8266⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8686 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8686⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8661 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8661⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8677 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8677⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8679 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8679⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8710 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8710⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8713 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8713⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest8722 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨8722⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest1806 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1806⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 9000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest502 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨502⟩ : UInt256) = true :=
  clipperJumpDestBeforeFirstPatch v hpatch (⟨502⟩ : UInt256) (by native_decide)

theorem clipperCheckedSubWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcCheckedSubSuccessWf code (⟨9274⟩ : UInt256) (⟨8722⟩ : UInt256) := by
  unfold solcCheckedSubSuccessWf
  repeat' first | apply And.intro
  all_goals
    clipper_runtime_decode

namespace Reasoning.Theory

theorem clipperMul_zero_left (x : UInt256) : UInt256.mul ⟨0⟩ x = ⟨0⟩ := by
  apply u256_inj
  rw [u256_mul_toNat]
  simp

theorem clipperMulDiv_cancel {x y : UInt256}
    (hx : x ≠ ⟨0⟩) (hmul : x.toNat * y.toNat < UInt256.size) :
    UInt256.div (UInt256.mul x y) x = y := by
  apply u256_inj
  rw [udiv_toNat, u256_mul_toNat]
  rw [Nat.mod_eq_of_lt hmul]
  have hxNat : 0 < x.toNat := by
    by_contra hzero
    have hxzero : x.toNat = 0 := by omega
    exact hx (uint256_toNat_eq_zero hxzero)
  exact Nat.mul_div_right y.toNat hxNat

theorem clipperMulDiv_cancel_comm {x y : UInt256}
    (hx : x ≠ ⟨0⟩) (hmul : x.toNat * y.toNat < UInt256.size) :
    UInt256.div (UInt256.mul y x) x = y := by
  rw [u256_mul_comm y x]
  exact clipperMulDiv_cancel hx hmul

theorem clipperMulDiv_overflow_ne (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    UInt256.div (UInt256.mul y x) x ≠ y := by
  intro hEq
  have hxNatNe : x.toNat ≠ 0 := by
    intro hx0
    have hprod0 : x.toNat * y.toNat = 0 := by simp [hx0]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hnat := congrArg UInt256.toNat hEq
  rw [udiv_toNat, u256_mul_toNat] at hnat
  have hremLt : y.toNat * x.toNat % UInt256.size < y.toNat * x.toNat := by
    have hmodLt : y.toNat * x.toNat % UInt256.size < UInt256.size :=
      Nat.mod_lt _ (by norm_num [UInt256.size])
    have hover' : UInt256.size ≤ y.toNat * x.toNat := by
      simpa [Nat.mul_comm] using hover
    omega
  have hle0 := Nat.mul_div_le (y.toNat * x.toNat % UInt256.size) x.toNat
  rw [hnat] at hle0
  have hle : y.toNat * x.toNat ≤ y.toNat * x.toNat % UInt256.size := by
    simpa [Nat.mul_comm] using hle0
  omega

end Reasoning.Theory

abbrev clipperUintBinaryLocals (x y : UInt256) : Store :=
  ((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x"
    (.int (Int.ofNat x.toNat))

abbrev clipperUintBinaryLocalsZ (x y z : UInt256) : Store :=
  (clipperUintBinaryLocals x y).insert "z" (.int (Int.ofNat z.toNat))

abbrev clipperWmulReturnLocals (x y xy : UInt256) : Store :=
  (clipperUintBinaryLocals x y).insert "xy" (.int (Int.ofNat xy.toNat))

abbrev clipperRayWord : UInt256 :=
  ⟨1000000000000000000000000000⟩

abbrev clipperRdivReturnLocals (x y xray : UInt256) : Store :=
  (clipperUintBinaryLocals x y).insert "xray" (.int (Int.ofNat xray.toNat))

theorem clipperLookupMulFunction (v : ClipperImmutables) :
    lookupCallable? (contract v) "mul" = some mulFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, FunctionDecl.toCallable,
    minFunction, addFunction, subFunction, mulFunction]

theorem clipperLookupSubFunction (v : ClipperImmutables) :
    lookupCallable? (contract v) "sub" = some subFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, FunctionDecl.toCallable,
    minFunction, addFunction, subFunction]

theorem clipperLookupWmulFunction (v : ClipperImmutables) :
    lookupCallable? (contract v) "wmul" = some wmulFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, FunctionDecl.toCallable,
    minFunction, addFunction, subFunction, mulFunction, wmulFunction]

theorem clipperLookupRmulFunction (v : ClipperImmutables) :
    lookupCallable? (contract v) "rmul" = some rmulFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, FunctionDecl.toCallable,
    minFunction, addFunction, subFunction, mulFunction, wmulFunction, rmulFunction]

theorem clipperLookupRdivFunction (v : ClipperImmutables) :
    lookupCallable? (contract v) "rdiv" = some rdivFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, FunctionDecl.toCallable,
    minFunction, addFunction, subFunction, mulFunction, wmulFunction, rmulFunction,
    rdivFunction]

theorem clipperBindParamsMul (x y : UInt256) :
    bindParams? mulFunction.params
      [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (clipperUintBinaryLocals x y) := by
  simp [mulFunction, bindParams?, clipperUintBinaryLocals]

theorem clipperBindParamsSub (x y : UInt256) :
    bindParams? subFunction.params
      [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (clipperUintBinaryLocals x y) := by
  simp [subFunction, bindParams?, clipperUintBinaryLocals]

theorem clipperBindParamsWmul (x y : UInt256) :
    bindParams? wmulFunction.params
      [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (clipperUintBinaryLocals x y) := by
  simp [wmulFunction, bindParams?, clipperUintBinaryLocals]

theorem clipperBindParamsRmul (x y : UInt256) :
    bindParams? rmulFunction.params
      [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (clipperUintBinaryLocals x y) := by
  simp [rmulFunction, bindParams?, clipperUintBinaryLocals]

theorem clipperBindParamsRdiv (x y : UInt256) :
    bindParams? rdivFunction.params
      [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (clipperUintBinaryLocals x y) := by
  simp [rdivFunction, bindParams?, clipperUintBinaryLocals]

theorem clipperEvalExprsUintBinary (v : ClipperImmutables) (evm : EVM.State)
    (locals : Store) (x y : UInt256) {xExpr yExpr : Expr}
    (hx : evalExpr? (config v) { contract := contract v, locals := locals } evm xExpr =
      .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? (config v) { contract := contract v, locals := locals } evm yExpr =
      .ok (.int (Int.ofNat y.toNat))) :
    evalExprs? (config v) { contract := contract v, locals := locals } evm [xExpr, yExpr] =
      .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] := by
  simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]

theorem clipperEvalVarX (v : ClipperImmutables) (evm : EVM.State) (x y : UInt256) :
    evalExpr? (config v) { contract := contract v, locals := clipperUintBinaryLocals x y }
      evm (.var "x") = .ok (.int (Int.ofNat x.toNat)) := by
  simp only [evalExpr?, clipperUintBinaryLocals]
  rw [store_get_self]
  rfl

theorem clipperEvalVarY (v : ClipperImmutables) (evm : EVM.State) (x y : UInt256) :
    evalExpr? (config v) { contract := contract v, locals := clipperUintBinaryLocals x y }
      evm (.var "y") = .ok (.int (Int.ofNat y.toNat)) := by
  simp only [evalExpr?, clipperUintBinaryLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalVarZ (v : ClipperImmutables) (evm : EVM.State) (x y z : UInt256) :
    evalExpr? (config v) { contract := contract v, locals := clipperUintBinaryLocalsZ x y z }
      evm (.var "z") = .ok (.int (Int.ofNat z.toNat)) := by
  simp only [evalExpr?, clipperUintBinaryLocalsZ]
  rw [store_get_self]
  rfl

theorem clipperEvalVarX_Z (v : ClipperImmutables) (evm : EVM.State) (x y z : UInt256) :
    evalExpr? (config v) { contract := contract v, locals := clipperUintBinaryLocalsZ x y z }
      evm (.var "x") = .ok (.int (Int.ofNat x.toNat)) := by
  simp only [evalExpr?, clipperUintBinaryLocalsZ, clipperUintBinaryLocals]
  rw [store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalVarY_Z (v : ClipperImmutables) (evm : EVM.State) (x y z : UInt256) :
    evalExpr? (config v) { contract := contract v, locals := clipperUintBinaryLocalsZ x y z }
      evm (.var "y") = .ok (.int (Int.ofNat y.toNat)) := by
  simp only [evalExpr?, clipperUintBinaryLocalsZ, clipperUintBinaryLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalVarXY (v : ClipperImmutables) (evm : EVM.State) (x y xy : UInt256) :
    evalExpr? (config v) { contract := contract v, locals := clipperWmulReturnLocals x y xy }
      evm (.var "xy") = .ok (.int (Int.ofNat xy.toNat)) := by
  simp only [evalExpr?, clipperWmulReturnLocals]
  rw [store_get_self]
  rfl

theorem clipperEvalVarXray (v : ClipperImmutables) (evm : EVM.State)
    (x y xray : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRdivReturnLocals x y xray }
      evm (.var "xray") = .ok (.int (Int.ofNat xray.toNat)) := by
  simp only [evalExpr?, clipperRdivReturnLocals]
  rw [store_get_self]
  rfl

theorem clipperEvalVarY_Xray (v : ClipperImmutables) (evm : EVM.State)
    (x y xray : UInt256) :
    evalExpr? (config v)
      { contract := contract v, locals := clipperRdivReturnLocals x y xray }
      evm (.var "y") = .ok (.int (Int.ofNat y.toNat)) := by
  simp only [evalExpr?, clipperRdivReturnLocals, clipperUintBinaryLocals]
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  rfl

theorem clipperEvalRdivMulArgs (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) :
    evalExprs? (config v) { contract := contract v, locals := clipperUintBinaryLocals x y }
      evm [.var "x", .intLit RAY] =
      .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat clipperRayWord.toNat)] := by
  have hray : RAY = Int.ofNat clipperRayWord.toNat := by native_decide
  simp only [evalExprs?, clipperEvalVarX, bind, EvalResult.bind, pure]
  simp [evalExpr?, hray]

theorem clipperEvalMul256_ok (v : ClipperImmutables) (evm : EVM.State) (x y : UInt256)
    (hmul : x.toNat * y.toNat < UInt256.size) :
    evalExpr? (config v) { contract := contract v, locals := clipperUintBinaryLocals x y }
      evm (mul256 (.var "x") (.var "y")) =
      .ok (.int (Int.ofNat (UInt256.mul x y).toNat)) := by
  have hlt : ¬ Int.ofNat (x.toNat * y.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hmul))
  have hword : (UInt256.mul x y).toNat = x.toNat * y.toNat := by
    rw [u256_mul_toNat, Nat.mod_eq_of_lt hmul]
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, clipperEvalVarX v evm x y,
    clipperEvalVarY v evm x y, evalBinaryOp?, uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem clipperEvalMul256_revert (v : ClipperImmutables) (evm : EVM.State) (x y : UInt256)
    (hover : UInt256.size ≤ x.toNat * y.toNat) :
    evalExpr? (config v) { contract := contract v, locals := clipperUintBinaryLocals x y }
      evm (mul256 (.var "x") (.var "y")) = .revert := by
  simp [mul256, u256, evalExpr?, EvalResult.bind, bind, clipperEvalVarX v evm x y,
    clipperEvalVarY v evm x y, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem clipperEvalAdd256_ok (v : ClipperImmutables) {evm : EVM.State} {locals : Store}
    {x y : Expr} {a b sum : UInt256}
    (hx : evalExpr? (config v) { contract := contract v, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? (config v) { contract := contract v, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hsum : sum = a + b) (hfit : a.toNat + b.toNat < UInt256.size) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (add256 x y) =
      .ok (.int (Int.ofNat sum.toNat)) := by
  have hlt : ¬ Int.ofNat (a.toNat + b.toNat) ≥ (2 : Int) ^ 256 :=
    not_le.mpr (Int.ofNat_lt.mpr (by simpa [UInt256.size] using hfit))
  have hword : sum.toNat = a.toNat + b.toNat := by
    rw [hsum, uadd_toNat, Nat.mod_eq_of_lt hfit]
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?,
    uint256Int, hword]
  rw [if_neg]
  · rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr (Int.natCast_nonneg _)) hbad
    · exact hlt hbad

theorem clipperEvalAdd256_revert (v : ClipperImmutables) {evm : EVM.State}
    {locals : Store} {x y : Expr} {a b : UInt256}
    (hx : evalExpr? (config v) { contract := contract v, locals := locals } evm x =
      .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? (config v) { contract := contract v, locals := locals } evm y =
      .ok (.int (Int.ofNat b.toNat)))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (add256 x y) =
      .revert := by
  simp [add256, u256, evalExpr?, EvalResult.bind, bind, hx, hy, evalBinaryOp?, uint256Int]
  intro _
  exact_mod_cast hover

theorem clipperEvalSub256_ok (v : ClipperImmutables) (evm : EVM.State) (x y : UInt256)
    (hle : y.toNat ≤ x.toNat) :
    evalExpr? (config v) { contract := contract v, locals := clipperUintBinaryLocals x y }
      evm (sub256 (.var "x") (.var "y")) =
      .ok (.int (Int.ofNat (UInt256.sub x y).toNat)) := by
  have hword : (UInt256.sub x y).toNat = x.toNat - y.toNat := usub_toNat hle
  have hsubInt :
      Int.ofNat x.toNat - Int.ofNat y.toNat = Int.ofNat (x.toNat - y.toNat) := by
    exact (Nat.cast_sub (R := Int) hle).symm
  have hnonneg : ¬Int.ofNat x.toNat - Int.ofNat y.toNat < 0 := by
    rw [hsubInt]
    exact not_lt.mpr (Int.natCast_nonneg _)
  have hsubVal : ((x.toNat : Int) - (y.toNat : Int)) = Int.ofNat (x.toNat - y.toNat) := by
    simpa using hsubInt
  have hlt : ¬Int.ofNat x.toNat - Int.ofNat y.toNat ≥ (2 : Int) ^ 256 := by
    intro hbad
    have hx : x.toNat < UInt256.size := x.val.isLt
    have hleSub : x.toNat - y.toNat < UInt256.size := by omega
    have hbadNat : UInt256.size ≤ x.toNat - y.toNat := by
      rw [hsubInt] at hbad
      have hbadNat' : 2 ^ 256 ≤ x.toNat - y.toNat := by
        exact Int.ofNat_le.mp (by simpa [ge_iff_le] using hbad)
      simpa [UInt256.size] using hbadNat'
    omega
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, clipperEvalVarX v evm x y,
    clipperEvalVarY v evm x y, evalBinaryOp?, uint256Int, hword]
  rw [if_neg]
  · rw [hsubVal]
    rfl
  · intro hbad
    rcases hbad with hbad | hbad
    · exact (not_lt.mpr hle) hbad
    · exact hlt hbad

theorem clipperEvalSub256_revert (v : ClipperImmutables) (evm : EVM.State) (x y : UInt256)
    (hlt : x.toNat < y.toNat) :
    evalExpr? (config v) { contract := contract v, locals := clipperUintBinaryLocals x y }
      evm (sub256 (.var "x") (.var "y")) = .revert := by
  simp [sub256, u256, evalExpr?, EvalResult.bind, bind, clipperEvalVarX v evm x y,
    clipperEvalVarY v evm x y, evalBinaryOp?, uint256Int]
  intro hle
  omega

theorem clipperEvalCheckedSubRequire_true (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hle : y.toNat ≤ x.toNat) :
    evalExpr? (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocalsZ x y (UInt256.sub x y) } :
        Frame) evm
      (.binary .le (.var "z") (.var "x")) =
      .ok (.bool true) := by
  have hsubNat : (UInt256.sub x y).toNat = x.toNat - y.toNat := usub_toNat hle
  have hleNat : (UInt256.sub x y).toNat ≤ x.toNat := by
    rw [hsubNat]
    exact Nat.sub_le x.toNat y.toNat
  simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?,
    clipperEvalVarZ v evm x y (UInt256.sub x y),
    clipperEvalVarX_Z v evm x y (UInt256.sub x y), hleNat]

theorem clipperEvalCheckedMulRequire_true (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hmul : x.toNat * y.toNat < UInt256.size) :
    evalExpr? (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocalsZ x y (UInt256.mul x y) } :
        Frame) evm
      (.binary .or
        (.binary .eq (.var "y") (.intLit 0))
        (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x"))) =
      .ok (.bool true) := by
  by_cases hy : y = ⟨0⟩
  · subst y
    simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
      clipperEvalVarY_Z v evm x ⟨0⟩ (UInt256.mul x ⟨0⟩)]
  · have hdiv :
        Int.ofNat (UInt256.mul x y).toNat / Int.ofNat y.toNat = Int.ofNat x.toNat := by
      have hcancel := Reasoning.Theory.clipperMulDiv_cancel (x := y) (y := x)
        (by simpa [eq_comm] using hy) (by simpa [Nat.mul_comm] using hmul)
      have hnat := congrArg UInt256.toNat hcancel
      rw [udiv_toNat, u256_mul_comm y x] at hnat
      exact (Int.ofNat_ediv_ofNat (a := (UInt256.mul x y).toNat) (b := y.toNat)).trans
        (congrArg Int.ofNat hnat)
    have hyInt : ¬Int.ofNat y.toNat = 0 := by
      intro hzero
      apply hy
      apply uint256_toNat_eq_zero
      exact Int.ofNat.inj hzero
    have hyNat : ¬y.toNat = 0 := by
      intro hzero
      exact hy (uint256_toNat_eq_zero hzero)
    have hleft :
        evalExpr? (config v)
          ({ contract := contract v, locals := clipperUintBinaryLocalsZ x y (UInt256.mul x y) } :
            Frame) evm
          (.binary .eq (.var "y") (.intLit 0)) = .ok (.bool false) := by
      simp [evalExpr?, EvalResult.bind, bind, pure, evalBinaryOp?,
        clipperEvalVarY_Z v evm x y (UInt256.mul x y), hyNat]
    have hright :
        evalExpr? (config v)
          ({ contract := contract v, locals := clipperUintBinaryLocalsZ x y (UInt256.mul x y) } :
            Frame) evm
          (.binary .eq (.binary .div (.var "z") (.var "y")) (.var "x")) =
          .ok (.bool true) := by
      simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?,
        clipperEvalVarZ v evm x y (UInt256.mul x y),
        clipperEvalVarY_Z v evm x y (UInt256.mul x y),
        clipperEvalVarX_Z v evm x y (UInt256.mul x y), hyNat]
      exact hdiv
    simp [evalExpr?, EvalResult.bind, bind, pure, hleft, hright]

theorem clipperEvalWmulReturn (v : ClipperImmutables) (evm : EVM.State) (x y : UInt256) :
    evalExpr? (config v)
      ({ contract := contract v, locals := clipperWmulReturnLocals x y (UInt256.mul x y) } :
        Frame) evm
      (.binary .div (.var "xy") (.intLit WAD)) =
      .ok (.int (Int.ofNat (UInt256.div (UInt256.mul x y) ⟨1000000000000000000⟩).toNat)) := by
  have hwad : ¬(WAD : Int) = 0 := by norm_num [WAD]
  have hdiv :
      Int.ofNat (UInt256.mul x y).toNat / WAD =
        Int.ofNat (UInt256.div (UInt256.mul x y) ⟨1000000000000000000⟩).toNat := by
    rw [udiv_toNat]
    have hw : WAD = Int.ofNat (⟨1000000000000000000⟩ : UInt256).toNat := by native_decide
    rw [hw]
    exact Int.ofNat_ediv_ofNat
      (a := (UInt256.mul x y).toNat) (b := (⟨1000000000000000000⟩ : UInt256).toNat)
  simp only [evalExpr?, clipperEvalVarXY, bind, EvalResult.bind, pure, evalBinaryOp?]
  rw [if_neg hwad, hdiv]

theorem clipperEvalRmulReturn (v : ClipperImmutables) (evm : EVM.State) (x y : UInt256) :
    evalExpr? (config v)
      ({ contract := contract v, locals := clipperWmulReturnLocals x y (UInt256.mul x y) } :
        Frame) evm
      (.binary .div (.var "xy") (.intLit RAY)) =
      .ok (.int (Int.ofNat
        (UInt256.div (UInt256.mul x y) clipperRayWord).toNat)) := by
  have hray : ¬(RAY : Int) = 0 := by norm_num [RAY]
  have hdiv :
      Int.ofNat (UInt256.mul x y).toNat / RAY =
        Int.ofNat (UInt256.div (UInt256.mul x y) clipperRayWord).toNat := by
    rw [udiv_toNat]
    have hw : RAY = Int.ofNat clipperRayWord.toNat := by native_decide
    rw [hw]
    exact Int.ofNat_ediv_ofNat
      (a := (UInt256.mul x y).toNat) (b := clipperRayWord.toNat)
  simp only [evalExpr?, clipperEvalVarXY, bind, EvalResult.bind, pure, evalBinaryOp?]
  rw [if_neg hray, hdiv]

theorem clipperEvalRdivReturn (v : ClipperImmutables) (evm : EVM.State)
    (x y xray : UInt256) (hy : y ≠ ⟨0⟩) :
    evalExpr? (config v)
      ({ contract := contract v, locals := clipperRdivReturnLocals x y xray } : Frame) evm
      (.binary .div (.var "xray") (.var "y")) =
      .ok (.int (Int.ofNat (UInt256.div xray y).toNat)) := by
  have hyNat : y.toNat ≠ 0 := by
    intro hzero
    exact hy (uint256_toNat_eq_zero hzero)
  have hyInt : ¬Int.ofNat y.toNat = 0 := by
    intro hzero
    exact hyNat (Int.ofNat.inj hzero)
  have hdiv :
      Int.ofNat xray.toNat / Int.ofNat y.toNat =
        Int.ofNat (UInt256.div xray y).toNat := by
    rw [udiv_toNat]
    exact Int.ofNat_ediv_ofNat
  simp only [evalExpr?, clipperEvalVarXray, clipperEvalVarY_Xray, bind, EvalResult.bind,
    evalBinaryOp?]
  rw [if_neg hyInt, hdiv]

theorem clipperEvalRdivReturn_revert (v : ClipperImmutables) (evm : EVM.State)
    (x y xray : UInt256) (hy : y = ⟨0⟩) :
    evalExpr? (config v)
      ({ contract := contract v, locals := clipperRdivReturnLocals x y xray } : Frame) evm
      (.binary .div (.var "xray") (.var "y")) = .revert := by
  subst y
  simp [evalExpr?, EvalResult.bind, bind, evalBinaryOp?, clipperEvalVarXray,
    clipperEvalVarY_Xray]

theorem clipperMulFunctionReturns (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hmul : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm mulFunction.body
      (.returned
        ({ contract := contract v, locals := clipperUintBinaryLocalsZ x y (UInt256.mul x y) } :
          Frame) evm
        (some [.int (Int.ofNat (UInt256.mul x y).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  simp only [mulFunction, checkedMulUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.letDecl (clipperEvalMul256_ok v evm x y hmul)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalCheckedMulRequire_true v evm x y hmul
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (clipperEvalVarZ v evm x y (UInt256.mul x y))))

theorem clipperMulFunctionReverts (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm mulFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  simp only [mulFunction, checkedMulUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert (clipperEvalMul256_revert v evm x y hover))

theorem clipperSubFunctionReturns (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hle : y.toNat ≤ x.toNat) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm subFunction.body
      (.returned
        ({ contract := contract v, locals := clipperUintBinaryLocalsZ x y (UInt256.sub x y) } :
          Frame) evm
        (some [.int (Int.ofNat (UInt256.sub x y).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  simp only [subFunction, checkedSubUintInto, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.letDecl (clipperEvalSub256_ok v evm x y hle)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact clipperEvalCheckedSubRequire_true v evm x y hle
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (clipperEvalVarZ v evm x y (UInt256.sub x y))))

theorem clipperSubFunctionReverts (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hlt : x.toNat < y.toNat) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm subFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  simp only [subFunction, checkedSubUintInto, List.cons_append, List.nil_append]
  exact ExecBlock.consRevert
    (ExecStmt.letDeclRevert (clipperEvalSub256_revert v evm x y hlt))

theorem clipperWmulFunctionReturns (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hmul : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm wmulFunction.body
      (.returned
        ({ contract := contract v, locals := clipperWmulReturnLocals x y (UInt256.mul x y) } :
          Frame) evm
        (some [.int (Int.ofNat
          (UInt256.div (UInt256.mul x y) ⟨1000000000000000000⟩).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  simp only [wmulFunction]
  let afterMul : Frame :=
    { contract := contract v, locals := clipperWmulReturnLocals x y (UInt256.mul x y) }
  have hcall :
      ExecStmt (config v)
        ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame) evm
        (.internalCall "mul" [.var "x", .var "y"] "xy") (.ok afterMul evm) := by
    simpa [afterMul, resumeAfterInternalCall, clipperWmulReturnLocals] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := { contract := contract v, locals := clipperUintBinaryLocals x y })
        (evm := evm) (calleeEvm := evm)
        (name := "mul") (retVar := "xy")
        (args := [.var "x", .var "y"])
        (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
        (callee := mulFunction)
        (locals := clipperUintBinaryLocals x y)
        (calleeSolm :=
          { contract := contract v, locals := clipperUintBinaryLocalsZ x y (UInt256.mul x y) })
        (value := some [.int (Int.ofNat (UInt256.mul x y).toNat)])
        (clipperEvalExprsUintBinary v evm (clipperUintBinaryLocals x y) x y
          (clipperEvalVarX v evm x y) (clipperEvalVarY v evm x y))
        (clipperLookupMulFunction v)
        (clipperBindParamsMul x y)
        (clipperMulFunctionReturns v evm x y hmul))
  refine ExecBlock.consNormal hcall ?_
  simpa [afterMul] using
    ExecBlock.consReturn
      (ExecStmt.return (evalExprs?_singleton (clipperEvalWmulReturn v evm x y)))

theorem clipperWmulFunctionReverts (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm wmulFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  simp only [wmulFunction]
  have hcall :
      ExecStmt (config v)
        ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame) evm
        (.internalCall "mul" [.var "x", .var "y"] "xy") .reverted :=
    internalCallFunctionRevert
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperUintBinaryLocals x y })
      (evm := evm)
      (name := "mul") (retVar := "xy")
      (args := [.var "x", .var "y"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
      (callee := mulFunction)
      (locals := clipperUintBinaryLocals x y)
      (clipperEvalExprsUintBinary v evm (clipperUintBinaryLocals x y) x y
        (clipperEvalVarX v evm x y) (clipperEvalVarY v evm x y))
      (clipperLookupMulFunction v)
      (clipperBindParamsMul x y)
      (clipperMulFunctionReverts v evm x y hover)
  exact ExecBlock.consRevert hcall

theorem clipperRmulFunctionReturns (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hmul : x.toNat * y.toNat < UInt256.size) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm rmulFunction.body
      (.returned
        ({ contract := contract v, locals := clipperWmulReturnLocals x y (UInt256.mul x y) } :
          Frame) evm
        (some [.int (Int.ofNat
          (UInt256.div (UInt256.mul x y) clipperRayWord).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  simp only [rmulFunction]
  let afterMul : Frame :=
    { contract := contract v, locals := clipperWmulReturnLocals x y (UInt256.mul x y) }
  have hcall :
      ExecStmt (config v)
        ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame) evm
        (.internalCall "mul" [.var "x", .var "y"] "xy") (.ok afterMul evm) := by
    simpa [afterMul, resumeAfterInternalCall, clipperWmulReturnLocals] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := { contract := contract v, locals := clipperUintBinaryLocals x y })
        (evm := evm) (calleeEvm := evm)
        (name := "mul") (retVar := "xy")
        (args := [.var "x", .var "y"])
        (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
        (callee := mulFunction) (locals := clipperUintBinaryLocals x y)
        (calleeSolm :=
          { contract := contract v, locals := clipperUintBinaryLocalsZ x y (UInt256.mul x y) })
        (value := some [.int (Int.ofNat (UInt256.mul x y).toNat)])
        (clipperEvalExprsUintBinary v evm (clipperUintBinaryLocals x y) x y
          (clipperEvalVarX v evm x y) (clipperEvalVarY v evm x y))
        (clipperLookupMulFunction v) (clipperBindParamsMul x y)
        (clipperMulFunctionReturns v evm x y hmul))
  refine ExecBlock.consNormal hcall ?_
  simpa [afterMul] using
    ExecBlock.consReturn
      (ExecStmt.return (evalExprs?_singleton (clipperEvalRmulReturn v evm x y)))

theorem clipperRmulFunctionReverts (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hover : UInt256.size ≤ x.toNat * y.toNat) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm rmulFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  simp only [rmulFunction]
  have hcall :
      ExecStmt (config v)
        ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame) evm
        (.internalCall "mul" [.var "x", .var "y"] "xy") .reverted :=
    internalCallFunctionRevert
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperUintBinaryLocals x y })
      (evm := evm) (name := "mul") (retVar := "xy")
      (args := [.var "x", .var "y"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)])
      (callee := mulFunction) (locals := clipperUintBinaryLocals x y)
      (clipperEvalExprsUintBinary v evm (clipperUintBinaryLocals x y) x y
        (clipperEvalVarX v evm x y) (clipperEvalVarY v evm x y))
      (clipperLookupMulFunction v) (clipperBindParamsMul x y)
      (clipperMulFunctionReverts v evm x y hover)
  exact ExecBlock.consRevert hcall

theorem clipperRdivFunctionReturns (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hmul : x.toNat * clipperRayWord.toNat < UInt256.size)
    (hy : y ≠ ⟨0⟩) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm rdivFunction.body
      (.returned
        ({ contract := contract v,
            locals := clipperRdivReturnLocals x y (UInt256.mul x clipperRayWord) } : Frame)
          evm
        (some [.int (Int.ofNat
          (UInt256.div (UInt256.mul x clipperRayWord) y).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  simp only [rdivFunction]
  let afterMul : Frame :=
    { contract := contract v, locals := clipperRdivReturnLocals x y (UInt256.mul x clipperRayWord) }
  have hcall :
      ExecStmt (config v)
        ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame) evm
        (.internalCall "mul" [.var "x", .intLit RAY] "xray") (.ok afterMul evm) := by
    simpa [afterMul, resumeAfterInternalCall, clipperRdivReturnLocals] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := { contract := contract v, locals := clipperUintBinaryLocals x y })
        (evm := evm) (calleeEvm := evm)
        (name := "mul") (retVar := "xray")
        (args := [.var "x", .intLit RAY])
        (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat clipperRayWord.toNat)])
        (callee := mulFunction)
        (locals := clipperUintBinaryLocals x clipperRayWord)
        (calleeSolm :=
          { contract := contract v,
            locals := clipperUintBinaryLocalsZ x clipperRayWord
              (UInt256.mul x clipperRayWord) })
        (value := some [.int (Int.ofNat (UInt256.mul x clipperRayWord).toNat)])
        (clipperEvalRdivMulArgs v evm x y)
        (clipperLookupMulFunction v)
        (clipperBindParamsMul x clipperRayWord)
        (clipperMulFunctionReturns v evm x clipperRayWord hmul))
  refine ExecBlock.consNormal hcall ?_
  simpa [afterMul] using
    ExecBlock.consReturn
      (ExecStmt.return
        (evalExprs?_singleton
          (clipperEvalRdivReturn v evm x y (UInt256.mul x clipperRayWord) hy)))

theorem clipperRdivFunctionRevertsMul (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hover : UInt256.size ≤ x.toNat * clipperRayWord.toNat) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm rdivFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  simp only [rdivFunction]
  have hcall :
      ExecStmt (config v)
        ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame) evm
        (.internalCall "mul" [.var "x", .intLit RAY] "xray") .reverted :=
    internalCallFunctionRevert
      (cfg := config v)
      (caller := { contract := contract v, locals := clipperUintBinaryLocals x y })
      (evm := evm)
      (name := "mul") (retVar := "xray")
      (args := [.var "x", .intLit RAY])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat clipperRayWord.toNat)])
      (callee := mulFunction)
      (locals := clipperUintBinaryLocals x clipperRayWord)
      (clipperEvalRdivMulArgs v evm x y)
      (clipperLookupMulFunction v)
      (clipperBindParamsMul x clipperRayWord)
      (clipperMulFunctionReverts v evm x clipperRayWord hover)
  exact ExecBlock.consRevert hcall

theorem clipperRdivFunctionRevertsDivZero (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hmul : x.toNat * clipperRayWord.toNat < UInt256.size)
    (hy : y = ⟨0⟩) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm rdivFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  simp only [rdivFunction]
  let afterMul : Frame :=
    { contract := contract v, locals := clipperRdivReturnLocals x y (UInt256.mul x clipperRayWord) }
  have hcall :
      ExecStmt (config v)
        ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame) evm
        (.internalCall "mul" [.var "x", .intLit RAY] "xray") (.ok afterMul evm) := by
    simpa [afterMul, resumeAfterInternalCall, clipperRdivReturnLocals] using
      (internalCallFunctionReturn
        (cfg := config v)
        (caller := { contract := contract v, locals := clipperUintBinaryLocals x y })
        (evm := evm) (calleeEvm := evm)
        (name := "mul") (retVar := "xray")
        (args := [.var "x", .intLit RAY])
        (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat clipperRayWord.toNat)])
        (callee := mulFunction)
        (locals := clipperUintBinaryLocals x clipperRayWord)
        (calleeSolm :=
          { contract := contract v,
            locals := clipperUintBinaryLocalsZ x clipperRayWord
              (UInt256.mul x clipperRayWord) })
        (value := some [.int (Int.ofNat (UInt256.mul x clipperRayWord).toNat)])
        (clipperEvalRdivMulArgs v evm x y)
        (clipperLookupMulFunction v)
        (clipperBindParamsMul x clipperRayWord)
        (clipperMulFunctionReturns v evm x clipperRayWord hmul))
  refine ExecBlock.consNormal hcall ?_
  exact ExecBlock.consRevert
    (ExecStmt.returnRevert (by
      simp only [afterMul, evalExprs?, bind, EvalResult.bind, pure]
      rw [clipperEvalRdivReturn_revert v evm x y (UInt256.mul x clipperRayWord) hy]))

abbrev clipperMinWord (x y : UInt256) : UInt256 :=
  if x.toNat ≤ y.toNat then x else y

theorem clipperMinWord_le_right (x y : UInt256) :
    (clipperMinWord x y).toNat ≤ y.toNat := by
  unfold clipperMinWord
  by_cases hxy : x.toNat ≤ y.toNat
  · simp [hxy]
  · simp [hxy]

theorem clipperMinWord_comm (x y : UInt256) :
    clipperMinWord x y = clipperMinWord y x := by
  unfold clipperMinWord
  by_cases hxy : x.toNat ≤ y.toNat
  · by_cases hyx : y.toNat ≤ x.toNat
    · have hnat : x.toNat = y.toNat := by omega
      have hword : x = y := Reasoning.Theory.u256_inj hnat
      subst y
      simp
    · simp [hxy, hyx]
  · have hyx : y.toNat ≤ x.toNat := by omega
    simp [hxy, hyx]

theorem clipperTakeTabDivPrice_le_lot_of_owe_gt {tab price slice lot : UInt256}
    (hmul : slice.toNat * price.toNat < UInt256.size)
    (hgt : tab.toNat < (UInt256.mul slice price).toNat)
    (hsliceLot : slice.toNat ≤ lot.toNat) :
    (UInt256.div tab price).toNat ≤ lot.toNat := by
  have hmulNat : (UInt256.mul slice price).toNat = slice.toNat * price.toNat := by
    rw [u256_mul_toNat]
    exact Nat.mod_eq_of_lt hmul
  have hgtNat : tab.toNat < slice.toNat * price.toNat := by
    simpa [hmulNat] using hgt
  have hdivLt : tab.toNat / price.toNat < slice.toNat := by
    apply Nat.div_lt_of_lt_mul
    simpa [Nat.mul_comm] using hgtNat
  rw [udiv_toNat]
  omega

theorem clipperLookupMinFunction (v : ClipperImmutables) :
    lookupCallable? (contract v) "min" = some minFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, FunctionDecl.toCallable,
    minFunction]

theorem clipperBindParamsMin (x y : UInt256) :
    bindParams? minFunction.params
      [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] =
      some (clipperUintBinaryLocals x y) := by
  simp [minFunction, bindParams?, clipperUintBinaryLocals]

theorem clipperEvalMinLe_true (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hle : x.toNat ≤ y.toNat) :
    evalExpr? (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm (.binary .le (.var "x") (.var "y")) = .ok (.bool true) := by
  simp only [evalExpr?, clipperEvalVarX v evm x y, clipperEvalVarY v evm x y,
    EvalResult.bind, bind]
  simp [evalBinaryOp?, hle]

theorem clipperEvalMinLe_false (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) (hle : ¬x.toNat ≤ y.toNat) :
    evalExpr? (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm (.binary .le (.var "x") (.var "y")) = .ok (.bool false) := by
  simp only [evalExpr?, clipperEvalVarX v evm x y, clipperEvalVarY v evm x y,
    EvalResult.bind, bind]
  simp [evalBinaryOp?, hle]

theorem clipperMinFunctionReturns (v : ClipperImmutables) (evm : EVM.State)
    (x y : UInt256) :
    ExecFuncBody (config v)
      ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
      evm minFunction.body
      (.returned
        ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame) evm
        (some [.int (Int.ofNat (clipperMinWord x y).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  simp only [minFunction]
  by_cases hle : x.toNat ≤ y.toNat
  · have hcond := clipperEvalMinLe_true v evm x y hle
    have hthen :
        ExecBlock (config v)
          ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
          evm [.return [.var "x"]]
          (.returned
            ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame) evm
            (some [.int (Int.ofNat x.toNat)])) := by
      exact ExecBlock.consReturn
        (ExecStmt.return (evalExprs?_singleton (clipperEvalVarX v evm x y)))
    have hmin : clipperMinWord x y = x := by
      simp [clipperMinWord, hle]
    simpa [hmin] using ExecBlock.consReturn (ExecStmt.iteTrue hcond hthen)
  · have hcond := clipperEvalMinLe_false v evm x y hle
    have helse :
        ExecBlock (config v)
          ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame)
          evm [.return [.var "y"]]
          (.returned
            ({ contract := contract v, locals := clipperUintBinaryLocals x y } : Frame) evm
            (some [.int (Int.ofNat y.toNat)])) := by
      exact ExecBlock.consReturn
        (ExecStmt.return (evalExprs?_singleton (clipperEvalVarY v evm x y)))
    have hmin : clipperMinWord x y = y := by
      simp [clipperMinWord, hle]
    simpa [hmin] using ExecBlock.consReturn (ExecStmt.iteFalse hcond helse)

/-! ## Source-level wrapping subtraction -/

theorem clipperIntModWord_sub_toNat (a b : UInt256) :
    (Int.ofNat a.toNat - Int.ofNat b.toNat) % wordModulus =
      Int.ofNat (UInt256.sub a b).toNat := by
  by_cases hle : b.toNat ≤ a.toNat
  · have hsub : Int.ofNat a.toNat - Int.ofNat b.toNat =
        Int.ofNat (a.toNat - b.toNat) := by
      exact (Int.ofNat_sub hle).symm
    have hlt : a.toNat - b.toNat < UInt256.size := by
      exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt
    have hltInt : Int.ofNat (a.toNat - b.toNat) < wordModulus := by
      rw [wordModulus]
      norm_num [UInt256.size] at hlt ⊢
      exact_mod_cast hlt
    rw [hsub]
    rw [Int.emod_eq_of_lt (by exact Int.natCast_nonneg _) hltInt]
    rw [usub_toNat (a := a) (b := b) hle]
  · have hlt : a.toNat < b.toNat := Nat.lt_of_not_ge hle
    let d := b.toNat - a.toNat
    have hdpos : 0 < d := by
      dsimp [d]
      exact Nat.sub_pos_of_lt hlt
    have hdiff : Int.ofNat a.toNat - Int.ofNat b.toNat = -Int.ofNat d := by
      have hsub : Int.ofNat d = Int.ofNat b.toNat - Int.ofNat a.toNat := by
        dsimp [d]
        exact Int.ofNat_sub (le_of_lt hlt)
      rw [hsub]
      ring
    have hwrapEq : UInt256.size + a.toNat - b.toNat = UInt256.size - d := by
      dsimp [d]
      omega
    have hdLe : d ≤ UInt256.size := by
      dsimp [d]
      exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_of_lt b.val.isLt)
    have hwrapLt : UInt256.size + a.toNat - b.toNat < UInt256.size := by
      rw [hwrapEq]
      exact Nat.sub_lt (by norm_num [UInt256.size]) hdpos
    have hwrapLtInt : Int.ofNat (UInt256.size + a.toNat - b.toNat) < wordModulus := by
      rw [wordModulus]
      norm_num [UInt256.size] at hwrapLt ⊢
      exact_mod_cast hwrapLt
    have hwrapMod : Int.ofNat (UInt256.size + a.toNat - b.toNat) % wordModulus =
        Int.ofNat (UInt256.size + a.toNat - b.toNat) :=
      Int.emod_eq_of_lt (Int.natCast_nonneg _) hwrapLtInt
    have hrepr : -Int.ofNat d =
        Int.ofNat (UInt256.size + a.toNat - b.toNat) - Int.ofNat UInt256.size := by
      rw [hwrapEq]
      have hcast : Int.ofNat (UInt256.size - d) =
          Int.ofNat UInt256.size - Int.ofNat d :=
        Int.ofNat_sub hdLe
      rw [hcast]
      ring
    rw [hdiff, hrepr]
    rw [Int.sub_emod]
    have hsizeMod : (Int.ofNat UInt256.size) % wordModulus = 0 := by
      rw [wordModulus]
      norm_num [UInt256.size]
    rw [hsizeMod]
    simp
    rw [usub_toNat_underflow (a := a) (b := b) hlt]
    exact hwrapMod

theorem clipperSubOne_eq_addNotZero (a : UInt256) :
    UInt256.sub a ⟨1⟩ = a + UInt256.lnot ⟨0⟩ := by
  apply u256_inj
  rw [uadd_toNat,
    show (UInt256.lnot ⟨0⟩).toNat = UInt256.size - 1 by native_decide]
  by_cases hz : a.toNat = 0
  · rw [usub_toNat_underflow (by
      rw [hz, show (⟨1⟩ : UInt256).toNat = 1 by native_decide]
      omega)]
    rw [hz, show (⟨1⟩ : UInt256).toNat = 1 by native_decide]
    norm_num [UInt256.size]
  · have hone : (⟨1⟩ : UInt256).toNat ≤ a.toNat := by
      rw [show (⟨1⟩ : UInt256).toNat = 1 by native_decide]
      omega
    rw [usub_toNat hone]
    rw [show (⟨1⟩ : UInt256).toNat = 1 by native_decide]
    have hadd : a.toNat + (UInt256.size - 1) = UInt256.size + (a.toNat - 1) := by
      have hsize : 1 ≤ UInt256.size := by norm_num [UInt256.size]
      omega
    rw [hadd, Nat.add_mod, Nat.mod_self, zero_add]
    have hlt : a.toNat - 1 < UInt256.size :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt
    simp [Nat.mod_eq_of_lt hlt]

namespace Reasoning.Reach

set_option maxHeartbeats 1000000 in
theorem RD.clipperMin {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨8661⟩ (x :: y :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (clipperMinWord x y :: R) mem aw rdata acc k' C' := by
  have rd8671pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw dup4 (by clipper_runtime_decode) (by evm_ov),
    raw gt (by clipper_runtime_decode) (by evm_ov),
    raw iszero (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8677⟩ (by clipper_runtime_decode) (by evm_ov)]
  by_cases hlt : x.toNat < y.toNat
  · have hgt : UInt256.gt y x = ⟨1⟩ := by
      exact ugt_one hlt
    have hcond : UInt256.isZero (UInt256.gt y x) = ⟨0⟩ := by
      rw [hgt]
      native_decide
    have rd8672 := rd8671pre.jumpiNT (by clipper_runtime_decode) hcond (by evm_ov)
    have rd8676 := evm_run rd8672 with [
      raw dup2 (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨8679⟩ (by clipper_runtime_decode) (by evm_ov)]
    have rd8679 := rd8676.jump (by clipper_runtime_decode)
      (clipperJumpDest8679 v hpatch) (by evm_ov)
    have rdret := evm_run rd8679 with [
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw swap4 (by clipper_runtime_decode) (by evm_ov),
      raw swap3 (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw jump (by clipper_runtime_decode) hret (by evm_ov)]
    exact ⟨_, _, by simpa [clipperMinWord, Nat.le_of_lt hlt] using rdret⟩
  · have hylex : y.toNat ≤ x.toNat := Nat.le_of_not_gt hlt
    have hgt : UInt256.gt y x = ⟨0⟩ := by
      exact ugt_zero hylex
    have hcond : UInt256.isZero (UInt256.gt y x) ≠ ⟨0⟩ := by
      rw [hgt]
      native_decide
    have rd8677 := rd8671pre.jumpiT (by clipper_runtime_decode) hcond
      (clipperJumpDest8677 v hpatch) (by evm_ov)
    have rdret := evm_run rd8677 with [
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw dup3 (by clipper_runtime_decode) (by evm_ov),
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw swap4 (by clipper_runtime_decode) (by evm_ov),
      raw swap3 (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw jump (by clipper_runtime_decode) hret (by evm_ov)]
    have hmin : clipperMinWord x y = y := by
      by_cases hle : x.toNat ≤ y.toNat
      · have hxyNat : x.toNat = y.toNat := by omega
        have hxy : x = y := by
          cases x with
          | mk xv =>
              cases y with
              | mk yv =>
                  simp only [UInt256.toNat] at hxyNat
                  exact congrArg UInt256.mk (Fin.ext hxyNat)
        simp [clipperMinWord, hxy]
      · simp [clipperMinWord, hle]
    exact ⟨_, _, by simpa [hmin] using rdret⟩

set_option maxHeartbeats 1000000 in
theorem RD.clipperCheckedMul {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨8686⟩ (x :: y :: ret :: R) mem aw rdata acc k C)
    (hmul : x.toNat * y.toNat < UInt256.size)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (UInt256.mul x y :: R) mem aw rdata acc k' C' := by
  by_cases hx : x = ⟨0⟩
  · subst x
    have hprod : UInt256.mul ⟨0⟩ y = ⟨0⟩ :=
      Reasoning.Theory.clipperMul_zero_left y
    exact ⟨_, _, by
      simpa [hprod] using (evm_run h with [
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
      raw dup2 (by clipper_runtime_decode) (by evm_ov),
      raw iszero (by clipper_runtime_decode) (by evm_ov),
      raw dup1 (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨8713⟩ (by clipper_runtime_decode) (by evm_ov),
      raw jumpiT (by clipper_runtime_decode) (by decide) (clipperJumpDest8713 v hpatch)
        (by evm_ov),
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨8722⟩ (by clipper_runtime_decode) (by evm_ov),
      raw jumpiT (by clipper_runtime_decode) (by decide) (clipperJumpDest8722 v hpatch)
        (by evm_ov),
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw swap3 (by clipper_runtime_decode) (by evm_ov),
      raw swap2 (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw jump (by clipper_runtime_decode) hret (by evm_ov) ])⟩
  · have hdiv :
        UInt256.div (UInt256.mul y x) x = y :=
      Reasoning.Theory.clipperMulDiv_cancel_comm hx hmul
    have hcond :
        UInt256.eq (UInt256.div (UInt256.mul y x) x) y ≠ ⟨0⟩ := by
      rw [hdiv, uInt256_eq_self]
      decide
    exact ⟨_, _, by
      simpa [u256_mul_comm y x] using (evm_run h with [
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
      raw dup2 (by clipper_runtime_decode) (by evm_ov),
      raw iszero (by clipper_runtime_decode) (by evm_ov),
      raw dup1 (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨8713⟩ (by clipper_runtime_decode) (by evm_ov),
      raw jumpiNT (by clipper_runtime_decode) (by
        rw [Reasoning.Theory.isZero_eq_zero_of_ne hx]) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw dup1 (by clipper_runtime_decode) (by evm_ov),
      raw dup3 (by clipper_runtime_decode) (by evm_ov),
      raw mul (by clipper_runtime_decode) (by evm_ov),
      raw dup3 (by clipper_runtime_decode) (by evm_ov),
      raw dup3 (by clipper_runtime_decode) (by evm_ov),
      raw dup3 (by clipper_runtime_decode) (by evm_ov),
      raw dup2 (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨8710⟩ (by clipper_runtime_decode) (by evm_ov),
      raw jumpiT (by clipper_runtime_decode) hx (clipperJumpDest8710 v hpatch)
        (by evm_ov),
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw div (by clipper_runtime_decode) (by evm_ov),
      raw eq (by clipper_runtime_decode) (by evm_ov),
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨8722⟩ (by clipper_runtime_decode) (by evm_ov),
      raw jumpiT (by clipper_runtime_decode) hcond (clipperJumpDest8722 v hpatch)
        (by evm_ov),
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw swap3 (by clipper_runtime_decode) (by evm_ov),
      raw swap2 (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw jump (by clipper_runtime_decode) hret (by evm_ov) ])⟩

theorem RD.clipperCheckedMulRevert {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨8686⟩ (x :: y :: ret :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ x.toNat * y.toNat) (hov : R.length + 12 ≤ 1024) :
    RDrev code g s0 := by
  have hx : x ≠ ⟨0⟩ := by
    intro hx
    subst x
    norm_num [UInt256.size] at hover
  have hdivNe :
      UInt256.div (UInt256.mul y x) x ≠ y :=
    Reasoning.Theory.clipperMulDiv_overflow_ne x y hover
  have hcond :
      UInt256.eq (UInt256.div (UInt256.mul y x) x) y = ⟨0⟩ := by
    apply Reasoning.Theory.uInt256_eq_zero_of_ne
    intro hone
    exact hdivNe (Reasoning.Theory.uInt256_eq_one_eq hone)
  have rd8718 := by
    simpa [u256_mul_comm y x, hcond] using (evm_run h with [
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
      raw dup2 (by clipper_runtime_decode) (by evm_ov),
      raw iszero (by clipper_runtime_decode) (by evm_ov),
      raw dup1 (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨8713⟩ (by clipper_runtime_decode) (by evm_ov),
      raw jumpiNT (by clipper_runtime_decode) (by
        rw [Reasoning.Theory.isZero_eq_zero_of_ne hx]) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw pop (by clipper_runtime_decode) (by evm_ov),
      raw dup1 (by clipper_runtime_decode) (by evm_ov),
      raw dup3 (by clipper_runtime_decode) (by evm_ov),
      raw mul (by clipper_runtime_decode) (by evm_ov),
      raw dup3 (by clipper_runtime_decode) (by evm_ov),
      raw dup3 (by clipper_runtime_decode) (by evm_ov),
      raw dup3 (by clipper_runtime_decode) (by evm_ov),
      raw dup2 (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨8710⟩ (by clipper_runtime_decode) (by evm_ov),
      raw jumpiT (by clipper_runtime_decode) hx (clipperJumpDest8710 v hpatch)
        (by evm_ov),
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw div (by clipper_runtime_decode) (by evm_ov),
      raw eq (by clipper_runtime_decode) (by evm_ov),
      raw jumpdest (by clipper_runtime_decode) (by evm_ov),
      raw push2 ⟨8722⟩ (by clipper_runtime_decode) (by evm_ov),
      raw jumpiNT (by clipper_runtime_decode) hcond (by evm_ov) ])
  exact RD.solcPush1Dup1Revert0 rd8718
    (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    (by evm_ov)

theorem RD.clipperWmulRoutine {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret keep : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨8238⟩ (x :: y :: ret :: keep :: R) mem aw rdata acc k C)
    (hmul : x.toNat * y.toNat < UInt256.size)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.div (UInt256.mul x y) ⟨1000000000000000000⟩ :: keep :: R)
      mem aw rdata acc k' C' := by
  have rd8241 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov) ]
  have rd8250 := RD.pushConst rd8241 ⟨1000000000000000000⟩
    (width := 8) (op := .PUSH8) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd8686 := evm_run rd8250 with [
    raw push2 ⟨8259⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8686 v hpatch) (by evm_ov) ]
  obtain ⟨_, _, rd8259⟩ :=
    RD.clipperCheckedMul v hpatch rd8686 hmul (clipperJumpDest8259 v hpatch) (by evm_ov)
  have hwad : (⟨1000000000000000000⟩ : UInt256) ≠ ⟨0⟩ := by decide
  exact ⟨_, _, evm_run rd8259 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8266⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiT (by clipper_runtime_decode) hwad (clipperJumpDest8266 v hpatch)
      (by evm_ov),
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) hret (by evm_ov) ]⟩

theorem RD.clipperWmulRoutineRevert {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret keep : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨8238⟩ (x :: y :: ret :: keep :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ x.toNat * y.toNat) (hov : R.length + 18 ≤ 1024) :
    RDrev code g s0 := by
  have rd8241 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov) ]
  have rd8250 := RD.pushConst rd8241 ⟨1000000000000000000⟩
    (width := 8) (op := .PUSH8) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd8686 := evm_run rd8250 with [
    raw push2 ⟨8259⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8686 v hpatch) (by evm_ov) ]
  exact RD.clipperCheckedMulRevert v hpatch rd8686 hover (by evm_ov)

/-! The optimizer emits `rmul` as the same checked-multiply/divide routine as
    `wmul`, with `RAY` in place of `WAD`.  Both `kick` and `redo` use it. -/

theorem RD.clipperRmulRoutine {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret keep : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨9233⟩ (x :: y :: ret :: keep :: R) mem aw rdata acc k C)
    (hmul : x.toNat * y.toNat < UInt256.size)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.div (UInt256.mul x y) clipperRayWord :: keep :: R)
      mem aw rdata acc k' C' := by
  have rd9236 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd9249 := RD.pushConst rd9236 clipperRayWord
    (width := 12) (op := .PUSH12) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd8686 := evm_run rd9249 with [
    raw push2 ⟨8259⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8686 v hpatch) (by evm_ov)]
  obtain ⟨_, _, rd8259⟩ :=
    RD.clipperCheckedMul v hpatch rd8686 hmul (clipperJumpDest8259 v hpatch)
      (by evm_ov)
  have hray : clipperRayWord ≠ ⟨0⟩ := by decide
  exact ⟨_, _, evm_run rd8259 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8266⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiT (by clipper_runtime_decode) hray (clipperJumpDest8266 v hpatch)
      (by evm_ov),
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) hret (by evm_ov)]⟩

theorem RD.clipperRmulRoutineRevert {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret keep : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨9233⟩ (x :: y :: ret :: keep :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ x.toNat * y.toNat) (hov : R.length + 18 ≤ 1024) :
    RDrev code g s0 := by
  have rd9236 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov)]
  have rd9249 := RD.pushConst rd9236 clipperRayWord
    (width := 12) (op := .PUSH12) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd8686 := evm_run rd9249 with [
    raw push2 ⟨8259⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8686 v hpatch) (by evm_ov)]
  exact RD.clipperCheckedMulRevert v hpatch rd8686 hover (by evm_ov)

theorem RD.clipperRdivRoutine {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret keep : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨9290⟩ (y :: x :: ret :: keep :: R) mem aw rdata acc k C)
    (hmul : x.toNat * clipperRayWord.toNat < UInt256.size)
    (hy : y ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.div (UInt256.mul x clipperRayWord) y :: keep :: R)
      mem aw rdata acc k' C' := by
  have rd9293 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8259⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov) ]
  have rd9311 := RD.pushConst rd9293 clipperRayWord
    (width := 12) (op := .PUSH12) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd8686 := evm_run rd9311 with [
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8686 v hpatch) (by evm_ov) ]
  have hmul' : clipperRayWord.toNat * x.toNat < UInt256.size := by
    simpa [Nat.mul_comm] using hmul
  obtain ⟨_, _, rd8259⟩ :=
    RD.clipperCheckedMul v hpatch rd8686 hmul' (clipperJumpDest8259 v hpatch) (by evm_ov)
  have rd8266 := evm_run rd8259 with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8266⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jumpiT (by clipper_runtime_decode) hy (clipperJumpDest8266 v hpatch)
      (by evm_ov),
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw div (by clipper_runtime_decode) (by evm_ov),
    raw swap4 (by clipper_runtime_decode) (by evm_ov),
    raw swap3 (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) hret (by evm_ov) ]
  exact ⟨_, _, by simpa [u256_mul_comm clipperRayWord x] using rd8266⟩

theorem RD.clipperRdivRoutineRevertMul {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret keep : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨9290⟩ (y :: x :: ret :: keep :: R) mem aw rdata acc k C)
    (hover : UInt256.size ≤ x.toNat * clipperRayWord.toNat)
    (hov : R.length + 18 ≤ 1024) :
    RDrev code g s0 := by
  have rd9293 := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨0⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup2 (by clipper_runtime_decode) (by evm_ov),
    raw push2 ⟨8259⟩ (by clipper_runtime_decode) (by evm_ov),
    raw dup5 (by clipper_runtime_decode) (by evm_ov) ]
  have rd9311 := RD.pushConst rd9293 clipperRayWord
    (width := 12) (op := .PUSH12) (by decide) (by clipper_runtime_decode) (by evm_ov)
  have rd8686 := evm_run rd9311 with [
    raw push2 ⟨8686⟩ (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest8686 v hpatch) (by evm_ov) ]
  have hover' : UInt256.size ≤ clipperRayWord.toNat * x.toNat := by
    simpa [Nat.mul_comm] using hover
  exact RD.clipperCheckedMulRevert v hpatch rd8686 hover' (by evm_ov)

theorem RD.clipperSubRoutine {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨9274⟩ (y :: x :: ret :: R) mem aw rdata acc k C)
    (hle : y.toNat ≤ x.toNat)
    (hret : (D_J code 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (UInt256.sub x y :: R) mem aw rdata acc k' C' := by
  exact RD.solcCheckedSubSuccess h (clipperCheckedSubWf v hpatch) hle hret
    (clipperJumpDest8722 v hpatch) hov

theorem RD.clipperSubRoutineRevert {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {x y ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨9274⟩ (y :: x :: ret :: R) mem aw rdata acc k C)
    (hlt : x.toNat < y.toNat) (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases clipperCheckedSubWf v hpatch with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsubNat : (UInt256.sub x y).toNat = UInt256.size + x.toNat - y.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub x y) x = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub x y > x)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub x y).toNat > x.toNat
      rw [hsubNat]
      have hy : y.toNat < UInt256.size := y.val.isLt
      omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7 := evm_run rd6 with [raw gt hd6 (by evm_ov)]
  rw [hgt] at rd7
  have rd8 := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdRevert := evm_run rd8 with [
    raw push2 ⟨8722⟩ hd8 (by evm_ov),
    raw jumpiNT hd11 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)]
  exact RD.solcPush1Dup1Revert0 rdRevert
    (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    (by clipper_runtime_decode)
    (by evm_ov)

theorem RD.clipperUpchostStoreChostReturn {code : ByteArray} (v : ClipperImmutables)
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {k C : ℕ}
    {chost dust sel : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 ⟨1806⟩ (chost :: dust :: ⟨502⟩ :: sel :: []) mem aw rdata
      (cA, σ) k C)
    (hperm : ee.perm = true) :
    RDret code g s0 (cA, sstoreAccountMap ee.codeOwner σ ⟨9⟩ chost) ByteArray.empty := by
  have rd1809pre := evm_run h with [
    raw jumpdest (by clipper_runtime_decode) (by evm_ov),
    raw push1 ⟨9⟩ (by clipper_runtime_decode) (by evm_ov)]
  obtain ⟨_, _, rd1810raw⟩ := rd1809pre.sstore hperm (by clipper_runtime_decode)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1811 := evm_run rd1810raw with [
    raw pop (by clipper_runtime_decode) (by evm_ov),
    raw jump (by clipper_runtime_decode) (clipperJumpDest502 v hpatch) (by evm_ov),
    raw jumpdest (by clipper_runtime_decode) (by evm_ov)]
  exact RD.stop rd1811 (by clipper_runtime_decode) (by evm_ov)

end Reasoning.Reach

end Benchmarks.Dss.Clipper
