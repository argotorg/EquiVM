import Reasoning.SolcRoutines
import Benchmarks.Dss.Cat.Common
import Solm.Equiv

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cat

/-! # Shared auth + store machinery for the Cat auth-guarded setters

Ported almost verbatim from the proven `Benchmarks/Dss/Vow/Deny.lean` (auth machinery +
deny store-zero) and `Benchmarks/Dss/Vow/Rely.lean` (rely store-one), renaming `vow → cat`.
The `cat`-prefixed generic auth/store routine lemmas below are contract-agnostic and are
LIBRARY CANDIDATEs: they should be lifted out of the per-contract Vow/Cat copies. -/

/-! ## `wards[msg.sender]` auth guard (Solm side) -/

abbrev catCallerWardsSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨0⟩ (solcSourceWord I)

abbrev catCallerWardsEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (.address I.source)] }

theorem catCallerWardsEvaledRef_ok {σ σ₀ A I} {g : Sat256} {locals : Store}
    (_hbase : locals.get? "wards" = none) :
    evalStorageRef config { contract := contract, locals := locals }
      (initState σ σ₀ g A I) (wardsRef sender) =
        .ok (catCallerWardsEvaledRef I) := by
  simp [catCallerWardsEvaledRef, wardsRef, sender, evalStorageRef, evalStorageRefSteps,
    evalStorageRefStep, evalExpr?, envValue, valueToKey?, EvalResult.ofOption,
    EvalResult.bind, pure, bind, initState]

theorem catAuthGuardEval_true {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : solcSlotWordAt (catCallerWardsSlot I) σ I = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have her := catCallerWardsEvaledRef_ok (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  have hload : Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
      (catCallerWardsSlot I) = ⟨1⟩ := by
    simpa [solcSlotWordAt] using hauth
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (catCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        catCallerWardsEvaledRef, catCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  simp only [initState] at hload ⊢
  rw [hload]
  simp [evalExpr?, evalBinaryOp?]
  all_goals native_decide

theorem catAuthGuardEval_false {σ σ₀ A I} {g : Sat256} {locals : Store}
    (hbase : locals.get? "wards" = none)
    (hauth : solcSlotWordAt (catCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals }
      (initState σ σ₀ g A I)
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have her := catCallerWardsEvaledRef_ok (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (locals := locals) hbase
  let w := Solm.EVM.storageLoad (initState σ σ₀ g A I) I.codeOwner
      (catCallerWardsSlot I)
  have hload : w ≠ ⟨1⟩ := by
    intro hw
    exact hauth (by simpa [w, solcSlotWordAt] using hw)
  rw [evalExpr?]
  simp only [EvalResult.bind, bind]
  rw [evalExpr_storage_scalar
    (t := .int uint256Int) (loc := wordLoc (catCallerWardsSlot I))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw,
        catCallerWardsEvaledRef, catCallerWardsSlot, wardsSlot, mapSlot, solcMappingSlot,
        keyValueToWord_address, solcSourceWord])]
  rw [show wordLoc = uint256Loc from rfl, storageLocLoad_uint256]
  simp only [initState] at hload ⊢
  simp [evalExpr?, evalBinaryOp?]
  · intro hnat
    apply hload
    apply u256_inj
    simpa using hnat
  all_goals native_decide

/-! ## Auth-check bytecode helper (`Cat/not-authorized`)

LIBRARY CANDIDATE: generic auth/store routine, lift from Vow. -/


/-- The PUSH18 immediate `0x10d85d0bdb9bdd0b585d5d1a1bdc9a5e9959` encoding
"Cat/not-authorized" (18 bytes, SHL 114). -/
abbrev catNotAuthorizedRawWord : UInt256 :=
  ⟨1467421245936156573805427109727019649112409⟩


theorem RD.catAuthCheckRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : solcAuthCheckWf code pc okPc)
    (htail : solcErrorStringRevertTailWf code (solcAuthTailPc pc) ⟨18⟩
      catNotAuthorizedRawWord ⟨114⟩ .PUSH18 18)
    (hauth : solcSlotWord σ ee (solcMappingSlot ⟨0⟩ (solcSourceWord ee)) ≠ ⟨1⟩)
    (hov : R.length + 7 ≤ 1024) :
    RDrev code g s0 :=
  Reasoning.Reach.RD.solcAuthCheckRevert18 h hwf htail hauth hov

/-! ## Mapping store routines (`wards[usr] := 0/1`)

LIBRARY CANDIDATE: generic auth/store routine, lift from Vow. -/


/-! ## Scalar store routine (`live := 0`, slot 2, no keccak) for `cage`

Verified against `runtime.hex` @2922: `JUMPDEST PUSH1 0 PUSH1 2 SSTORE JUMP`.
LIBRARY CANDIDATE: generic scalar store routine. -/


end Benchmarks.Dss.Cat
