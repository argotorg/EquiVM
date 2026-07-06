import Benchmarks.Dss.Pot.RpowGeneric
import Benchmarks.Dss.Pot.Arith
import Benchmarks.Dss.Pot.Dispatch
import Reasoning.ExternalCall

/-!
# Pot `drip()` — shared foundation

Reach lemma to the `drip` logic block `@1819`, empty-calldata decode, the `now >= rho` guard on both
the EVM and Solm sides, and the storage-word abbreviations used throughout the `drip` port.

`drip()` has no parameters (empty decode → `∅` locals) and returns `[uint256]`. Structure:
`require now≥rho ; pow=_rpow(dsr,now-rho,ONE) ; tmp=_rmul(pow,chi) ; chi_=_sub(tmp,chi) ;
 chi=tmp ; rho=now ; rad=_mul(Pie,chi_) ; vat.suck(vow,this,rad) ; return tmp`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-! ## Storage-word abbreviations (flat scalar slots) -/

abbrev dripDsrWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := potSlotWord ⟨3⟩ σ I
abbrev dripChiWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := potSlotWord ⟨4⟩ σ I
abbrev dripRhoWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := potSlotWord ⟨7⟩ σ I
abbrev dripPieWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := potSlotWord ⟨2⟩ σ I

/-- `vat` address (slot 5) masked to 160 bits — the external-call target for `suck`. -/
abbrev dripVatTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  potAddressReturnWord ⟨5⟩ σ I

/-- `vow` address (slot 6) masked to 160 bits — first `suck` argument. -/
abbrev dripVowTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  potAddressReturnWord ⟨6⟩ σ I

abbrev dripVatAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (dripVatTargetWord σ I).toNat

/-- `now` as a machine word. -/
abbrev dripNowWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.header.timestamp

/-! ## Empty-calldata decode -/

theorem potDecode_drip {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (dripTransition.params.map Param.name)
      (transitionSignature dripTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-! ## Reach the drip logic block `@1819` -/

theorem potReachDripEntry {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 4)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨583⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x9f678cca⟩ :=
    potSelWord_eq_of_beq I hsz 0x9f 0x67 0x8c 0xca ⟨0x9f678cca⟩
      (by native_decide) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have h43 : UInt256.gt (armSelNat potBytecode potSplit43Pc) (potSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by
    intro j hj; interval_cases j; rw [hword]; native_decide
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG54FirstArmPc 1))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; native_decide
  exact potReachG54Body 1 (by omega) ⟨583⟩ hcode hwv hsz hsize hroot h43 heq0 htake
    (by jump_dest) (by native_decide)

/-- Entry `@583`: push return addr `341`, push logic `1819`, jump. -/
theorem potDripX_entered {cA σ I} {g : Sat256} {s0 : State} {sel : UInt256}
    (hreach : ∃ k C, RD potBytecode I g s0 ⟨583⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1819⟩ [⟨341⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨k, C, h⟩ := hreach
  have rd584 := h.jumpdest (by native_decide) (by evm_ov)
  have rd587 := rd584.push2 ⟨341⟩ (by native_decide) (by evm_ov)
  have rd590 := rd587.push2 ⟨1819⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd590.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem potReachDripBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 4)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1819⟩ [⟨341⟩, potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C :=
  potDripX_entered (potReachDripEntry hcode hwv hsz hsize hsel)

/-! ## EVM-side `now >= rho` guard (`@1819`–`@1831`) -/

/-- Common prefix: load rho (slot 7), compare with `now`, land on `@1828` after `ISZERO`
with the guard condition on top of `[0, 341, sel]`. -/
theorem potDripX_guardCond {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (h : RD potBytecode I g s0 ⟨1819⟩ [⟨341⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1828⟩
      (UInt256.isZero (UInt256.lt (dripNowWord I) (dripRhoWord σ I)) ::
        ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1820 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1822 := rd1820.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1824 := rd1822.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1825, C1825, rd1825raw⟩ := rd1824.sload (by native_decide) (by evm_ov)
  have rd1825 : RD potBytecode I g s0 ⟨1825⟩
      (dripRhoWord σ I :: ⟨0⟩ :: ⟨341⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1825 C1825 := by
    simpa [dripRhoWord, potSlotWord, solcSlotWord] using rd1825raw
  have rd1826 := RD.timestamp rd1825 (by native_decide) (by evm_ov)
  have rd1827 := rd1826.lt (by native_decide) (by evm_ov)
  have rd1828 := rd1827.iszero (by native_decide) (by evm_ov)
  exact ⟨_, _, by simpa [dripNowWord] using rd1828⟩

/-- `now >= rho`: the guard is taken, landing at `@1894` with `[0, 341, sel]`. -/
theorem potDripX_nowOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (hle : (dripRhoWord σ I).toNat ≤ (dripNowWord I).toNat)
    (h : RD potBytecode I g s0 ⟨1819⟩ [⟨341⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨1894⟩ [⟨0⟩, ⟨341⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1828⟩ := potDripX_guardCond h
  have hltZero : UInt256.lt (dripNowWord I) (dripRhoWord σ I) = ⟨0⟩ := ult_zero hle
  rw [hltZero, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1828
  have rd1831 := rd1828.pushConst (⟨1894⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1831.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

/-- `now < rho`: the guard falls through to the `"Pot/invalid-now"` string revert. -/
theorem potDripX_invalidNow {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (hlt : (dripNowWord I).toNat < (dripRhoWord σ I).toNat)
    (h : RD potBytecode I g s0 ⟨1819⟩ [⟨341⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  obtain ⟨_, _, rd1828⟩ := potDripX_guardCond h
  have hltOne : UInt256.lt (dripNowWord I) (dripRhoWord σ I) = ⟨1⟩ := ult_one hlt
  rw [hltOne, show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1828
  have rd1831 := rd1828.pushConst (⟨1894⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1832 := rd1831.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1832⟩)
    (len := ⟨15⟩)
    (rawWord := ⟨0x506f742f696e76616c69642d6e6f77⟩)
    (shift := ⟨136⟩)
    (word := ⟨0x506f742f696e76616c69642d6e6f770000000000000000000000000000000000⟩)
    (op := .PUSH15)
    (width := 15)
    rd1832
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | native_decide)
    (by decide)
    (by native_decide)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## Solm-side `now >= rho` guard -/

theorem evalExpr_ge_uint256_false {evm : EVM.State} {locals : Store}
    {lhs rhs : Expr} {a b : UInt256}
    (hlhs : evalExpr? config { contract := contract, locals := locals } evm lhs =
      .ok (.int (Int.ofNat a.toNat)))
    (hrhs : evalExpr? config { contract := contract, locals := locals } evm rhs =
      .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? config { contract := contract, locals := locals } evm (.binary .ge lhs rhs) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, hlhs, hrhs, evalBinaryOp?]
  have : ¬ (b.toNat : Int) ≤ (a.toNat : Int) := by exact_mod_cast Nat.not_le.mpr hlt
  simp [this]

/-- Evaluate `.storage rhoRef` (scalar slot 7) in an empty-locals frame. -/
theorem evalExpr_dripStorageRho (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm (.storage rhoRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := (∅ : Store) })
    (slot := rhoRef) (er := ({ base := "rho", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨7⟩)
    (hbase := by simp [rhoRef])
    (her := by simp [evalStorageRef, evalStorageRefSteps, rhoRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
    (hload := potStorageLocLoad_uint256 evm ⟨7⟩)]

theorem evalExpr_dripNowGeRho_true (evm : EVM.State)
    (hle : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .ge (.env .timestamp) (.storage rhoRef)) = .ok (.bool true) := by
  refine evalExpr_ge_uint256_true
    (a := UInt256.ofNat evm.executionEnv.header.timestamp)
    (b := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
    ?_ (evalExpr_dripStorageRho evm) hle
  simp [evalExpr?, envValue, pure]

theorem evalExpr_dripNowGeRho_false (evm : EVM.State)
    (hlt : (UInt256.ofNat evm.executionEnv.header.timestamp).toNat <
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat) :
    evalExpr? config { contract := contract, locals := (∅ : Store) } evm
      (.binary .ge (.env .timestamp) (.storage rhoRef)) = .ok (.bool false) := by
  refine evalExpr_ge_uint256_false
    (a := UInt256.ofNat evm.executionEnv.header.timestamp)
    (b := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
    ?_ (evalExpr_dripStorageRho evm) hlt
  simp [evalExpr?, envValue, pure]

end Benchmarks.Dss.Pot
