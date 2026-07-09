import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController non-selector paths

* `tlcNoMatchBodyCore` — calldata ≥ 4 but no selector matches: the EVM binary-search tree walks to a
  leaf arm group, all arms miss, and it reverts (`PUSH0 PUSH0 REVERT`).  Solm `dispatchMsg = none`
  (no matching selector, calldata ≠ ∅ so no receive, no fallback) → `noDispatch`.
* `tlcShortBodyCore` — calldata < 4: empty calldata runs the payable `receive` (EVM `STOP` @440,
  Solm `receive` empty body → both succeed, no state change); 1–3 bytes reverts (EVM @441, Solm
  `dispatchMsg = none` → `noDispatch`).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- Short calldata (`< 4` bytes): the prologue's `calldatasize < 4` guard jumps directly to the
    receive / short-revert handler at pc 434 with an empty stack. -/
theorem tlcReachFallback434 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hshort : I.calldata.size < 4) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨434⟩ []
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have h5 := (RD.initState (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode)
    |>.push1 ⟨128⟩ (by native_decide) (by decide)
    |>.push1 ⟨64⟩ (by native_decide) (by decide)
    |>.mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by native_decide)
        mem_cost (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
        (by decide) (by decide)
  have h434 := h5
    |>.push1 ⟨4⟩ (by native_decide) (by simp)
    |>.calldatasize (by native_decide) (by simp)
    |>.lt (by native_decide) (by simp)
    |>.pushConst (⟨434⟩ : UInt256) (width := 2) (op := .PUSH2) (by native_decide)
        (by native_decide) (by simp)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hshort) (by jump_dest) (by simp)
  exact ⟨_, _, h434⟩

/-- Empty calldata dispatches to the payable `receive`. -/
theorem tlcReceiveDispatch {cd : ByteArray} (h0 : cd.size = 0) :
    receiveDispatchMsg contract cd = some receiveTransition := by
  simp only [receiveDispatchMsg, h0, if_pos, contract]

theorem tlcSelDispatch_none_short {cd : ByteArray} (hshort : cd.size < 4) :
    selectorDispatchMsg contract cd = none := by
  rw [selectorDispatchMsg_eq_dispatchList contract cd]
  exact dispatchList_none_short contract.transitions
    (fun t _ => by rw [selectorOf, ByteArray.size_extract, keccak_size]; decide) hshort

/-- Non-empty, `< 4`-byte calldata: no selector, no receive (nonempty), no fallback ⇒ no dispatch. -/
theorem tlcDispatch_none_posShort {cd : ByteArray} (hpos : 0 < cd.size) (hshort : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg, tlcSelDispatch_none_short hshort]
  simp only [receiveDispatchMsg, if_neg (show ¬ cd.size = 0 by omega)]
  rfl

/-! ## No-match dispatch: Solm side (`dispatchMsg = none`) -/

/-- No named selector matches (`calldata ≥ 4`): `selectorDispatchMsg` yields nothing. -/
theorem tlcSelDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 28 → (tlcSelBytes i == cd.extract 0 4) = false) :
    selectorDispatchMsg contract cd = none := by
  rw [selectorDispatchMsg_eq_dispatchList contract cd]
  apply dispatchList_none_of_all_ne
  intro t ht
  simp only [contract] at ht
  fin_cases ht
  · rw [selectorOf, cancellerRoleSelectorBytes]; exact hnm 0 (by omega)
  · rw [selectorOf, cancelSelectorBytes]; exact hnm 1 (by omega)
  · rw [selectorOf, defaultAdminRoleSelectorBytes]; exact hnm 2 (by omega)
  · rw [selectorOf, executeBatchSelectorBytes]; exact hnm 3 (by omega)
  · rw [selectorOf, executeSelectorBytes]; exact hnm 4 (by omega)
  · rw [selectorOf, executorRoleSelectorBytes]; exact hnm 5 (by omega)
  · rw [selectorOf, getMinDelaySelectorBytes]; exact hnm 6 (by omega)
  · rw [selectorOf, getOperationStateSelectorBytes]; exact hnm 7 (by omega)
  · rw [selectorOf, getRoleAdminSelectorBytes]; exact hnm 8 (by omega)
  · rw [selectorOf, getTimestampSelectorBytes]; exact hnm 9 (by omega)
  · rw [selectorOf, grantRoleSelectorBytes]; exact hnm 10 (by omega)
  · rw [selectorOf, hasRoleSelectorBytes]; exact hnm 11 (by omega)
  · rw [selectorOf, hashOperationBatchSelectorBytes]; exact hnm 12 (by omega)
  · rw [selectorOf, hashOperationSelectorBytes]; exact hnm 13 (by omega)
  · rw [selectorOf, isOperationDoneSelectorBytes]; exact hnm 14 (by omega)
  · rw [selectorOf, isOperationPendingSelectorBytes]; exact hnm 15 (by omega)
  · rw [selectorOf, isOperationReadySelectorBytes]; exact hnm 16 (by omega)
  · rw [selectorOf, isOperationSelectorBytes]; exact hnm 17 (by omega)
  · rw [selectorOf, onERC1155BatchReceivedSelectorBytes]; exact hnm 18 (by omega)
  · rw [selectorOf, onERC1155ReceivedSelectorBytes]; exact hnm 19 (by omega)
  · rw [selectorOf, onERC721ReceivedSelectorBytes]; exact hnm 20 (by omega)
  · rw [selectorOf, proposerRoleSelectorBytes]; exact hnm 21 (by omega)
  · rw [selectorOf, renounceRoleSelectorBytes]; exact hnm 22 (by omega)
  · rw [selectorOf, revokeRoleSelectorBytes]; exact hnm 23 (by omega)
  · rw [selectorOf, scheduleBatchSelectorBytes]; exact hnm 24 (by omega)
  · rw [selectorOf, scheduleSelectorBytes]; exact hnm 25 (by omega)
  · rw [selectorOf, supportsInterfaceSelectorBytes]; exact hnm 26 (by omega)
  · rw [selectorOf, updateDelaySelectorBytes]; exact hnm 27 (by omega)

/-- No selector, non-empty (`≥ 4`-byte) calldata, no fallback ⇒ no dispatch. -/
theorem tlcDispatch_none_nomatch {cd : ByteArray} (hsz : 4 ≤ cd.size)
    (hnm : ∀ i, i < 28 → (tlcSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg, tlcSelDispatch_none_nomatch hnm]
  simp only [receiveDispatchMsg, if_neg (show ¬ cd.size = 0 by omega)]
  rfl

/-! ## No-match dispatch: EVM side (per-group arm selectors, decode facts, and reverts)

Each leaf arm group ends in `PUSH0; PUSH0; REVERT` once all its arms miss.  The arm selectors below
are in bytecode order; `tlcG<X>ArmEq` couples the EVM `EQ`-arm compare to a byte compare, and
`tlcG<X>NoMatchRevert` scans a group's arms (all missing) and reverts. -/

def tlcG51SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xd5, 0x47, 0x74, 0x1f]⟩ -- revokeRole
  | 1 => ⟨#[0xe3, 0x83, 0x35, 0xe5]⟩ -- executeBatch
  | 2 => ⟨#[0xf2, 0x3a, 0x6e, 0x61]⟩ -- onERC1155Received
  | _ => ⟨#[0xf2, 0x7a, 0x0c, 0x92]⟩ -- getMinDelay

def tlcG98SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xbc, 0x19, 0x7c, 0x81]⟩ -- onERC1155BatchReceived
  | 1 => ⟨#[0xc4, 0xd2, 0x52, 0xf5]⟩ -- cancel
  | _ => ⟨#[0xd4, 0x5c, 0x44, 0x35]⟩ -- getTimestamp

def tlcG147SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x91, 0xd1, 0x48, 0x54]⟩ -- hasRole
  | 1 => ⟨#[0xa2, 0x17, 0xfd, 0xdf]⟩ -- DEFAULT_ADMIN_ROLE
  | 2 => ⟨#[0xb0, 0x8e, 0x51, 0xc0]⟩ -- CANCELLER_ROLE
  | _ => ⟨#[0xb1, 0xc5, 0xf4, 0x27]⟩ -- hashOperationBatch

def tlcG194SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x80, 0x65, 0x65, 0x7f]⟩ -- hashOperation
  | 1 => ⟨#[0x8f, 0x2a, 0x0b, 0xb0]⟩ -- scheduleBatch
  | _ => ⟨#[0x8f, 0x61, 0xf4, 0xf5]⟩ -- PROPOSER_ROLE

def tlcG254SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x36, 0x56, 0x8a, 0xbe]⟩ -- renounceRole
  | 1 => ⟨#[0x58, 0x4b, 0x15, 0x3e]⟩ -- isOperationPending
  | 2 => ⟨#[0x64, 0xd6, 0x23, 0x53]⟩ -- updateDelay
  | _ => ⟨#[0x79, 0x58, 0x00, 0x4c]⟩ -- getOperationState

def tlcG301SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x2a, 0xb0, 0xf5, 0x29]⟩ -- isOperationDone
  | 1 => ⟨#[0x2f, 0x2f, 0xf1, 0x5d]⟩ -- grantRole
  | _ => ⟨#[0x31, 0xd5, 0x07, 0x50]⟩ -- isOperation

def tlcG350SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x13, 0x40, 0x08, 0xd3]⟩ -- execute
  | 1 => ⟨#[0x13, 0xbc, 0x9f, 0x20]⟩ -- isOperationReady
  | 2 => ⟨#[0x15, 0x0b, 0x7a, 0x02]⟩ -- onERC721Received
  | _ => ⟨#[0x24, 0x8a, 0x9c, 0xa3]⟩ -- getRoleAdmin

def tlcG397SelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x01, 0xd5, 0x06, 0x2a]⟩ -- schedule
  | 1 => ⟨#[0x01, 0xff, 0xc9, 0xa7]⟩ -- supportsInterface
  | _ => ⟨#[0x07, 0xbd, 0x02, 0x65]⟩ -- EXECUTOR_ROLE

theorem tlcG51ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 4) :
    UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨51⟩ j)) (tlcSelWord I) =
      if (tlcG51SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem tlcG98ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 3) :
    UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨99⟩ j)) (tlcSelWord I) =
      if (tlcG98SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem tlcG147ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 4) :
    UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨147⟩ j)) (tlcSelWord I) =
      if (tlcG147SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem tlcG194ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 3) :
    UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨195⟩ j)) (tlcSelWord I) =
      if (tlcG194SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem tlcG254ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 4) :
    UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨254⟩ j)) (tlcSelWord I) =
      if (tlcG254SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem tlcG301ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 3) :
    UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨302⟩ j)) (tlcSelWord I) =
      if (tlcG301SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem tlcG350ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 4) :
    UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨350⟩ j)) (tlcSelWord I) =
      if (tlcG350SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem tlcG397ArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size) (j : ℕ) (hj : j < 3) :
    UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨398⟩ j)) (tlcSelWord I) =
      if (tlcG397SelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem tlcG51NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨51⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 → UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨51⟩ j)) (tlcSelWord I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (tlcG51ArmsWF 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG51ArmsWF 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG51ArmsWF 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG51ArmsWF 3 (by omega)) (heq0 3 (by omega)) (by simp)
  exact hend.revertStub (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem tlcG98NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨99⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 3 → UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨99⟩ j)) (tlcSelWord I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (tlcG98ArmsWF 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG98ArmsWF 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG98ArmsWF 2 (by omega)) (heq0 2 (by omega)) (by simp)
  exact hend.revertStub (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem tlcG147NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨147⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 → UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨147⟩ j)) (tlcSelWord I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (tlcG147ArmsWF 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG147ArmsWF 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG147ArmsWF 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG147ArmsWF 3 (by omega)) (heq0 3 (by omega)) (by simp)
  exact hend.revertStub (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem tlcG194NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨195⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 3 → UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨195⟩ j)) (tlcSelWord I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (tlcG194ArmsWF 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG194ArmsWF 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG194ArmsWF 2 (by omega)) (heq0 2 (by omega)) (by simp)
  exact hend.revertStub (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem tlcG254NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨254⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 → UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨254⟩ j)) (tlcSelWord I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (tlcG254ArmsWF 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG254ArmsWF 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG254ArmsWF 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG254ArmsWF 3 (by omega)) (heq0 3 (by omega)) (by simp)
  exact hend.revertStub (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem tlcG301NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨302⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 3 → UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨302⟩ j)) (tlcSelWord I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (tlcG301ArmsWF 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG301ArmsWF 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG301ArmsWF 2 (by omega)) (heq0 2 (by omega)) (by simp)
  exact hend.revertStub (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem tlcG350NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨350⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 4 → UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨350⟩ j)) (tlcSelWord I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (tlcG350ArmsWF 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG350ArmsWF 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG350ArmsWF 2 (by omega)) (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG350ArmsWF 3 (by omega)) (heq0 3 (by omega)) (by simp)
  exact hend.revertStub (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem tlcG397NoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨398⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 3 → UInt256.eq (armSelNat timelockControllerBenchBytecode
        (nthArmPc timelockControllerBenchBytecode ⟨398⟩ j)) (tlcSelWord I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hend := h
    |>.selectorArmNotTakenAuto (tlcG397ArmsWF 0 (by omega)) (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG397ArmsWF 1 (by omega)) (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (tlcG397ArmsWF 2 (by omega)) (heq0 2 (by omega)) (by simp)
  exact hend.revertStub (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem tlcNoMatchBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsz : 4 ≤ I.calldata.size)
    (hnm : ∀ i, i < 28 → (tlcSelBytes i == I.calldata.extract 0 4) = false)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  refine RDrev.reEquivNoDispatch (g := Sat256.ofUInt256 g) hcode ?_
    (tlcDispatch_none_nomatch hsz hnm)
  by_cases hroot : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨18⟩) (tlcSelWord I) = ⟨0⟩
  · by_cases h29 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨29⟩) (tlcSelWord I) = ⟨0⟩
    · by_cases h40 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨40⟩) (tlcSelWord I) = ⟨0⟩
      · -- G51: revokeRole, executeBatch, onERC1155Received, getMinDelay
        obtain ⟨_, _, hfirst⟩ := tlcReachG51First (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hroot h29 h40
        refine tlcG51NoMatchRevert hfirst ?_
        intro j hj; interval_cases j
        · rw [tlcG51ArmEq I hsz 0 (by omega), show (tlcG51SelBytes 0 == I.calldata.extract 0 4)
            = false from by simpa [tlcG51SelBytes, tlcSelBytes] using hnm 23 (by omega)]; rfl
        · rw [tlcG51ArmEq I hsz 1 (by omega), show (tlcG51SelBytes 1 == I.calldata.extract 0 4)
            = false from by simpa [tlcG51SelBytes, tlcSelBytes] using hnm 3 (by omega)]; rfl
        · rw [tlcG51ArmEq I hsz 2 (by omega), show (tlcG51SelBytes 2 == I.calldata.extract 0 4)
            = false from by simpa [tlcG51SelBytes, tlcSelBytes] using hnm 19 (by omega)]; rfl
        · rw [tlcG51ArmEq I hsz 3 (by omega), show (tlcG51SelBytes 3 == I.calldata.extract 0 4)
            = false from by simpa [tlcG51SelBytes, tlcSelBytes] using hnm 6 (by omega)]; rfl
      · -- G98: onERC1155BatchReceived, cancel, getTimestamp
        obtain ⟨_, _, hfirst⟩ := tlcReachG98First (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hroot h29 h40
        refine tlcG98NoMatchRevert hfirst ?_
        intro j hj; interval_cases j
        · rw [tlcG98ArmEq I hsz 0 (by omega), show (tlcG98SelBytes 0 == I.calldata.extract 0 4)
            = false from by simpa [tlcG98SelBytes, tlcSelBytes] using hnm 18 (by omega)]; rfl
        · rw [tlcG98ArmEq I hsz 1 (by omega), show (tlcG98SelBytes 1 == I.calldata.extract 0 4)
            = false from by simpa [tlcG98SelBytes, tlcSelBytes] using hnm 1 (by omega)]; rfl
        · rw [tlcG98ArmEq I hsz 2 (by omega), show (tlcG98SelBytes 2 == I.calldata.extract 0 4)
            = false from by simpa [tlcG98SelBytes, tlcSelBytes] using hnm 9 (by omega)]; rfl
    · by_cases h136 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨136⟩) (tlcSelWord I) = ⟨0⟩
      · -- G147: hasRole, DEFAULT_ADMIN_ROLE, CANCELLER_ROLE, hashOperationBatch
        obtain ⟨_, _, hfirst⟩ := tlcReachG147First (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hroot h29 h136
        refine tlcG147NoMatchRevert hfirst ?_
        intro j hj; interval_cases j
        · rw [tlcG147ArmEq I hsz 0 (by omega), show (tlcG147SelBytes 0 == I.calldata.extract 0 4)
            = false from by simpa [tlcG147SelBytes, tlcSelBytes] using hnm 11 (by omega)]; rfl
        · rw [tlcG147ArmEq I hsz 1 (by omega), show (tlcG147SelBytes 1 == I.calldata.extract 0 4)
            = false from by simpa [tlcG147SelBytes, tlcSelBytes] using hnm 2 (by omega)]; rfl
        · rw [tlcG147ArmEq I hsz 2 (by omega), show (tlcG147SelBytes 2 == I.calldata.extract 0 4)
            = false from by simpa [tlcG147SelBytes, tlcSelBytes] using hnm 0 (by omega)]; rfl
        · rw [tlcG147ArmEq I hsz 3 (by omega), show (tlcG147SelBytes 3 == I.calldata.extract 0 4)
            = false from by simpa [tlcG147SelBytes, tlcSelBytes] using hnm 12 (by omega)]; rfl
      · -- G194: hashOperation, scheduleBatch, PROPOSER_ROLE
        obtain ⟨_, _, hfirst⟩ := tlcReachG194First (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hroot h29 h136
        refine tlcG194NoMatchRevert hfirst ?_
        intro j hj; interval_cases j
        · rw [tlcG194ArmEq I hsz 0 (by omega), show (tlcG194SelBytes 0 == I.calldata.extract 0 4)
            = false from by simpa [tlcG194SelBytes, tlcSelBytes] using hnm 13 (by omega)]; rfl
        · rw [tlcG194ArmEq I hsz 1 (by omega), show (tlcG194SelBytes 1 == I.calldata.extract 0 4)
            = false from by simpa [tlcG194SelBytes, tlcSelBytes] using hnm 24 (by omega)]; rfl
        · rw [tlcG194ArmEq I hsz 2 (by omega), show (tlcG194SelBytes 2 == I.calldata.extract 0 4)
            = false from by simpa [tlcG194SelBytes, tlcSelBytes] using hnm 21 (by omega)]; rfl
  · by_cases h232 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨232⟩) (tlcSelWord I) = ⟨0⟩
    · by_cases h243 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨243⟩) (tlcSelWord I) = ⟨0⟩
      · -- G254: renounceRole, isOperationPending, updateDelay, getOperationState
        obtain ⟨_, _, hfirst⟩ := tlcReachG254First (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hroot h232 h243
        refine tlcG254NoMatchRevert hfirst ?_
        intro j hj; interval_cases j
        · rw [tlcG254ArmEq I hsz 0 (by omega), show (tlcG254SelBytes 0 == I.calldata.extract 0 4)
            = false from by simpa [tlcG254SelBytes, tlcSelBytes] using hnm 22 (by omega)]; rfl
        · rw [tlcG254ArmEq I hsz 1 (by omega), show (tlcG254SelBytes 1 == I.calldata.extract 0 4)
            = false from by simpa [tlcG254SelBytes, tlcSelBytes] using hnm 15 (by omega)]; rfl
        · rw [tlcG254ArmEq I hsz 2 (by omega), show (tlcG254SelBytes 2 == I.calldata.extract 0 4)
            = false from by simpa [tlcG254SelBytes, tlcSelBytes] using hnm 27 (by omega)]; rfl
        · rw [tlcG254ArmEq I hsz 3 (by omega), show (tlcG254SelBytes 3 == I.calldata.extract 0 4)
            = false from by simpa [tlcG254SelBytes, tlcSelBytes] using hnm 7 (by omega)]; rfl
      · -- G301: isOperationDone, grantRole, isOperation
        obtain ⟨_, _, hfirst⟩ := tlcReachG301First (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hroot h232 h243
        refine tlcG301NoMatchRevert hfirst ?_
        intro j hj; interval_cases j
        · rw [tlcG301ArmEq I hsz 0 (by omega), show (tlcG301SelBytes 0 == I.calldata.extract 0 4)
            = false from by simpa [tlcG301SelBytes, tlcSelBytes] using hnm 14 (by omega)]; rfl
        · rw [tlcG301ArmEq I hsz 1 (by omega), show (tlcG301SelBytes 1 == I.calldata.extract 0 4)
            = false from by simpa [tlcG301SelBytes, tlcSelBytes] using hnm 10 (by omega)]; rfl
        · rw [tlcG301ArmEq I hsz 2 (by omega), show (tlcG301SelBytes 2 == I.calldata.extract 0 4)
            = false from by simpa [tlcG301SelBytes, tlcSelBytes] using hnm 17 (by omega)]; rfl
    · by_cases h339 : UInt256.gt (armSelNat timelockControllerBenchBytecode ⟨339⟩) (tlcSelWord I) = ⟨0⟩
      · -- G350: execute, isOperationReady, onERC721Received, getRoleAdmin
        obtain ⟨_, _, hfirst⟩ := tlcReachG350First (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hroot h232 h339
        refine tlcG350NoMatchRevert hfirst ?_
        intro j hj; interval_cases j
        · rw [tlcG350ArmEq I hsz 0 (by omega), show (tlcG350SelBytes 0 == I.calldata.extract 0 4)
            = false from by simpa [tlcG350SelBytes, tlcSelBytes] using hnm 4 (by omega)]; rfl
        · rw [tlcG350ArmEq I hsz 1 (by omega), show (tlcG350SelBytes 1 == I.calldata.extract 0 4)
            = false from by simpa [tlcG350SelBytes, tlcSelBytes] using hnm 16 (by omega)]; rfl
        · rw [tlcG350ArmEq I hsz 2 (by omega), show (tlcG350SelBytes 2 == I.calldata.extract 0 4)
            = false from by simpa [tlcG350SelBytes, tlcSelBytes] using hnm 20 (by omega)]; rfl
        · rw [tlcG350ArmEq I hsz 3 (by omega), show (tlcG350SelBytes 3 == I.calldata.extract 0 4)
            = false from by simpa [tlcG350SelBytes, tlcSelBytes] using hnm 8 (by omega)]; rfl
      · -- G397: schedule, supportsInterface, EXECUTOR_ROLE
        obtain ⟨_, _, hfirst⟩ := tlcReachG397First (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hroot h232 h339
        refine tlcG397NoMatchRevert hfirst ?_
        intro j hj; interval_cases j
        · rw [tlcG397ArmEq I hsz 0 (by omega), show (tlcG397SelBytes 0 == I.calldata.extract 0 4)
            = false from by simpa [tlcG397SelBytes, tlcSelBytes] using hnm 25 (by omega)]; rfl
        · rw [tlcG397ArmEq I hsz 1 (by omega), show (tlcG397SelBytes 1 == I.calldata.extract 0 4)
            = false from by simpa [tlcG397SelBytes, tlcSelBytes] using hnm 26 (by omega)]; rfl
        · rw [tlcG397ArmEq I hsz 2 (by omega), show (tlcG397SelBytes 2 == I.calldata.extract 0 4)
            = false from by simpa [tlcG397SelBytes, tlcSelBytes] using hnm 5 (by omega)]; rfl

/-- Short/receive path (calldata < 4): reach @434, then `STOP` (size 0 → receive) or `REVERT`
    (1–3 bytes → no-dispatch).  Reach + dispatch helpers above are complete; the receive-execution /
    no-dispatch framework glue is finished together with the constructor. -/
theorem tlcShortBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hshort : I.calldata.size < 4)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨k, C, h434⟩ := tlcReachFallback434 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hshort
  by_cases hsize0 : I.calldata.size = 0
  · -- Empty calldata: the JUMPI is not taken, `STOP` @440 runs the empty payable `receive`.
    have hcond0 : UInt256.ofNat I.calldata.size = ⟨0⟩ := by rw [hsize0]; rfl
    have hStop : RDret timelockControllerBenchBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm) ByteArray.empty :=
      (h434.jumpdest (by native_decide) (by simp)
        |>.calldatasize (by native_decide) (by simp)
        |>.push2 ⟨441⟩ (by native_decide) (by simp)
        |>.jumpiNT (by native_decide) hcond0 (by simp)).stop (by native_decide) (by simp)
    rcases hStop with hoog | ⟨s, hX, hacc⟩
    · exact reEquiv_outOfGas (Xi_error_of_X (g := g) (by
        rw [← hcode] at hoog
        simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hoog))
    · have hxi := Xi_success_of_X (g := g) (by
        rw [← hcode] at hX
        simpa [initState, Sat256.ofUInt256, Sat256.toUInt256] using hX)
      have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
      have hσ : s.accountMap = σ_evm := congrArg Prod.snd hacc
      rw [hcA, hσ] at hxi
      refine reEquiv_receiveExecution (tlcReceiveDispatch hsize0) rfl rfl
        (ExecFuncBody.execBlockOK ExecBlock.nil) ?_
      rw [hxi]
      exact execResultsEquiv.success rfl rfl rfl (by simpa [initState] using hAccounts)
        (returnDataEquiv.abi (returnEquiv.fallthrough (dvs := []) rfl rfl (by native_decide)))
  · -- 1–3 bytes: the JUMPI is taken, jumpdest @441 falls into `PUSH0 PUSH0 REVERT`; no dispatch.
    have hcondNe : UInt256.ofNat I.calldata.size ≠ ⟨0⟩ := by
      intro hz
      have hz' : (UInt256.ofNat I.calldata.size).toNat = 0 := by rw [hz]; rfl
      rw [UInt256.toNat_ofNat_of_lt hsize] at hz'
      exact hsize0 hz'
    have hRev : RDrev timelockControllerBenchBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
      (h434.jumpdest (by native_decide) (by simp)
        |>.calldatasize (by native_decide) (by simp)
        |>.push2 ⟨441⟩ (by native_decide) (by simp)
        |>.jumpiT (by native_decide) hcondNe (by jump_dest) (by simp)
        |>.jumpdest (by native_decide) (by simp)).revertStub
          (by native_decide) (by native_decide) (by native_decide) (by simp)
    exact RDrev.reEquivNoDispatch (g := Sat256.ofUInt256 g) hcode hRev
      (tlcDispatch_none_posShort (Nat.pos_of_ne_zero hsize0) hshort)

end OpenZeppelinBench.TimelockController
