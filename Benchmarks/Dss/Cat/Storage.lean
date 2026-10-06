import Reasoning.SolcRoutines
import Benchmarks.Dss.Cat.Common
import Solm.Equiv


open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cat

@[reducible] def catStoreLiveZeroWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨2⟩, 1))
  ∧ decode code p5 = some (.SSTORE, .none)
  ∧ decode code p6 = some (.JUMP, .none)

end Benchmarks.Dss.Cat

namespace Benchmarks.Dss.Cat.RD

theorem catStoreLiveZero {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem (UInt256.ofNat 3) rdata σ k C)
    (hwf : catStoreLiveZeroWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R mem (UInt256.ofNat 3) rdata
      (sstoreAccountMap ee.codeOwner σ ⟨2⟩ ⟨0⟩) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd5, hd6⟩
  have rdStore := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨0⟩ hd1 (by evm_ov),
    raw push1 ⟨2⟩ hd3 (by evm_ov)]
  obtain ⟨_, _, rdOut⟩ := rdStore.sstore hperm hd5 (by evm_ov)
  exact ⟨_, _, rdOut.jump hd6 hret (by evm_ov)⟩

end Benchmarks.Dss.Cat.RD

end

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
