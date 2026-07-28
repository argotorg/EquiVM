import Benchmarks.OpenZeppelinBench.TimelockController.HasRole
import Benchmarks.OpenZeppelinBench.TimelockController.IsOperationPending
import Benchmarks.OpenZeppelinBench.TimelockController.GetOperationState
import Benchmarks.OpenZeppelinBench.TimelockController.GetTimestamp
import Benchmarks.OpenZeppelinBench.TimelockController.CancellerRole
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines
import Reasoning.MemCascade

/-!
# OpenZeppelin TimelockController `cancel(bytes32)` refinement

`cancel` (selector index 1, dispatch group G98 arm 1, body pc 1276) is the first function combining a
constant-role `onlyRole` guard, a mapping read, and a storage **delete**.  It decodes one `bytes32 id`
via the shared word decoder `@4702`, enforces `onlyRole(CANCELLER_ROLE)` (the `_checkRole` helper
`@3461 → @3655 → @2762` — the same nested read `hasRole` uses, but with the constant role
`CANCELLER_ROLE` and account `msg.sender`), requires `isOperationPending(id)` (`_timestamps[id] > 1`
via the inlined `_getOperationState @2232` + range test `@2048`), then **deletes** `_timestamps[id]`
(`SSTORE 0` at the mapping slot `keccak(id ‖ 1)`) and emits a `Cancelled` `LOG2`.

The delete `.delete (timestampRef id)` clears the `uint256` slot to `0` (`clearStorage?` on the
`.elem` leaf), coupling to the EVM `SSTORE 0` via `accountMapEquiv_sstoreAccountMap`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## LOG2 stepping (absent from the shared library — only `LOG1/3/4` are provided there)

    Copied verbatim from the WETH9 `RD.log2`: pop `[offset, size, t1, t2]`, append a 2-topic log over
    `mem[offset..offset+size]` (cost `memExp + Glog + Glogdata·size + 2·Glogtopic`, pc += 1).  Requires
    `ee.perm`; the `substate.logSeries` append is invisible to `RD`. -/
def stLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  {s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat
            + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem log2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat
            < memoryExpansionCost s .LOG2
              + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
         then .error .OutOfGass else .ok (stLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog2]

theorem RD.log2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := log2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog2]; exact hcode
      · simp only [stLog2]; rw [hpc]
      · simp only [stLog2]
      · simp only [stLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog2]; exact hmem
      · simp only [stLog2]; rw [haw, hawout]
      · simp only [stLog2]; exact hrdata
      · simp only [stLog2]; exact hacc
      · simp only [stLog2]; exact hee
      · simp only [stLog2]; exact hworld

/-! ## Decoded argument, role slot, and stored words

`cancel(bytes32 id)` binds the same one-`bytes32` local store as `getTimestamp` (`tlcGetTimestampStore`),
and its timestamp lives at the same mapping slot `keccak(id ‖ 1)`.  The `onlyRole` guard reads the
nested slot `keccak(msg.sender ‖ keccak(CANCELLER_ROLE ‖ 0))`. -/

/-- `msg.sender` as an EVM word (what `CALLER` pushes). -/
abbrev tlcCancelCallerWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.source.val

/-- The nested `_roles[CANCELLER_ROLE].hasRole[msg.sender]` slot as the runtime computes it. -/
abbrev tlcCancelRoleSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨0⟩ tlcCancellerRoleWord)
    (UInt256.land solcAddrMask (tlcCancelCallerWord I))

/-- The stored `_roles[CANCELLER_ROLE].hasRole[msg.sender]` word. -/
abbrev tlcCancelRoleWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (tlcCancelRoleSlot I)

/-! ## EVM: reach the body and run the `bytes32` decoder -/

/-- Reach the `cancel` body pc 1276 (G98 arm 1). -/
theorem tlcReachCancel {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 1)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1276⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0xc4d252f5⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xc4 0xd2 0x52 0xf5 ⟨0xc4d252f5⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG98Body 1 (by omega) ⟨1276⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j; rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard, push the return/decode continuations `⟨476⟩`/`⟨1302⟩`, and run the
    `bytes32` decoder prologue @4702 to the availability `JUMPI` @4714. -/
theorem tlcCancelReachLenCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 1)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4714⟩
      [⟨4718⟩, UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩),
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1302⟩, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h1276⟩ := tlcReachCancel (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h1289⟩ := tlcGuardPeelOk (gt := ⟨1287⟩) h1276 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, h1289.push2 ⟨476⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1302⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨4702⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨4718⟩ (by native_decide) (by evm_ov)⟩

/-- After the length check passes, finish the decoder (`CALLDATALOAD(4)`), jump back to the decode
    continuation @1302, and enter the `cancel` body logic @2870 with `[id, ⟨476⟩, sel]`. -/
theorem tlcCancelReach2870 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 1)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2870⟩
      [calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsz : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h4714⟩ := tlcCancelReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel
  exact ⟨_, _, h4714.jumpiT (by native_decide)
      (by rw [solcDecodeLenCheckOk_4_32 hsz36 hbig hsize]; decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨2870⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-! ## EVM: the `onlyRole(CANCELLER_ROLE)` guard (@2870 → `_checkRole` @3461 → @3655 → @2762)

    The scratch memory the nested `hasRole` read leaves at @3665. -/
noncomputable abbrev tlcCancelHasRoleMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (UInt256.land solcAddrMask (tlcCancelCallerWord I))
    (solcMappingSlot ⟨0⟩ tlcCancellerRoleWord)
    (twoWordHashMem tlcCancellerRoleWord ⟨0⟩ solcFreePtrMem)

/-- From the body @2870, push the constant role, dispatch `_checkRole(role) @3461 → @3655`, and reuse
    `tlcHasRoleSlotLoad @2762` for the nested `_roles[role].hasRole[msg.sender]` read — reaching the
    `if authorized` `JUMPI` @3665 with the masked stored byte on top. -/
theorem tlcCancelReach3665 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2870⟩
      [calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcCancelRoleWord σ I), tlcCancelCallerWord I, tlcCancellerRoleWord, ⟨3471⟩,
        tlcCancellerRoleWord, ⟨2912⟩, tlcCancellerRoleWord, calldataWord I.calldata 4, ⟨476⟩,
        tlcSelWord I]
      (tlcCancelHasRoleMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h2762 := h.jumpdest (by native_decide) (by evm_ov)
    |>.pushConst tlcCancellerRoleWord (op := .PUSH32) (width := 32) (by decide)
      (by native_decide) (by evm_ov)
    |>.push2 ⟨2912⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨3461⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3471⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.caller (by native_decide) (by evm_ov)
    |>.push2 ⟨3655⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3665⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.push2 ⟨2762⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact tlcHasRoleSlotLoad h2762 (by jump_dest) (by simp)

/-- `msg.sender` has the canceller role: continue past the `_checkRole` `JUMPI` @3665 through the
    `_checkRole`/`onlyRole` return trampolines back to the body @2912. -/
theorem tlcCancelReach2912 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2870⟩
      [calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hhas : ¬ UInt256.land ⟨255⟩ (tlcCancelRoleWord σ I) = ⟨0⟩) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2912⟩
      [tlcCancellerRoleWord, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      (tlcCancelHasRoleMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, h3665⟩ := tlcCancelReach3665 h
  exact ⟨_, _, h3665.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3712⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) hhas (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-! ## EVM: the `isOperationPending` helper `@2048` used by `cancel` (@2912 → @2921)

    The `_getOperationState @2232` tail `@2059` — generic in the return address `ret` and the stack
    tail `below`, unlike the fixed `IsOperationPending.tlcIsOperationPendingTail` (`ret = 509`,
    `below = [sel]`).  From `[state, 0, 0, key, ret] ++ below` it computes `state == 1 ∨ state == 2`
    (the `DUP1;…;JUMPI` short-circuit) and returns to `ret` with `[boolOf state] ++ below`. -/
theorem tlcCancelPendingTail {cA gh bl σ σ₀ A I} {g : Sat256} {R key ret : UInt256}
    {below : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2059⟩
      (R :: ⟨0⟩ :: ⟨0⟩ :: key :: ret :: below) mem aw ByteArray.empty (cA, σ) k C)
    (hbound : UInt256.isZero (UInt256.gt R ⟨3⟩) ≠ ⟨0⟩)
    (hret : (D_J timelockControllerBenchBytecode 0).contains ret = true)
    (hov : below.length + 8 ≤ 1024) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (tlcIsOperationPendingBoolOf R :: below) mem aw ByteArray.empty (cA, σ) k' C' := by
  by_cases heq1 : R = ⟨1⟩
  · have hc1 : UInt256.eq R ⟨1⟩ ≠ ⟨0⟩ := by rw [heq1]; decide
    have hret' := h.jumpdest (by native_decide) (by evm_ov)
      |>.swap1 (by native_decide) (by evm_ov)
      |>.pop (by native_decide) (by evm_ov)
      |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
      |>.dup2 (by native_decide) (by evm_ov)
      |>.push1 ⟨3⟩ (by native_decide) (by evm_ov)
      |>.dup2 (by native_decide) (by evm_ov)
      |>.gt (by native_decide) (by evm_ov)
      |>.iszero (by native_decide) (by evm_ov)
      |>.push2 ⟨2081⟩ (by native_decide) (by evm_ov)
      |>.jumpiT (by native_decide) hbound (by jump_dest) (by evm_ov)
      |>.jumpdest (by native_decide) (by evm_ov)
      |>.eq (by native_decide) (by evm_ov)
      |>.dup1 (by native_decide) (by evm_ov)
      |>.push2 ⟨2110⟩ (by native_decide) (by evm_ov)
      |>.jumpiT (by native_decide) hc1 (by jump_dest) (by evm_ov)
      |>.jumpdest (by native_decide) (by evm_ov)
      |>.swap4 (by native_decide) (by evm_ov)
      |>.swap3 (by native_decide) (by evm_ov)
      |>.pop (by native_decide) (by evm_ov)
      |>.pop (by native_decide) (by evm_ov)
      |>.pop (by native_decide) (by evm_ov)
      |>.jump (by native_decide) hret (by evm_ov)
    rw [show UInt256.eq R ⟨1⟩ = tlcIsOperationPendingBoolOf R from by
      unfold tlcIsOperationPendingBoolOf; rw [if_pos heq1]] at hret'
    exact ⟨_, _, hret'⟩
  · have hc0 : UInt256.eq R ⟨1⟩ = ⟨0⟩ := by
      show UInt256.fromBool (decide (R = ⟨1⟩)) = ⟨0⟩
      rw [decide_eq_false heq1]; rfl
    have hret' := h.jumpdest (by native_decide) (by evm_ov)
      |>.swap1 (by native_decide) (by evm_ov)
      |>.pop (by native_decide) (by evm_ov)
      |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
      |>.dup2 (by native_decide) (by evm_ov)
      |>.push1 ⟨3⟩ (by native_decide) (by evm_ov)
      |>.dup2 (by native_decide) (by evm_ov)
      |>.gt (by native_decide) (by evm_ov)
      |>.iszero (by native_decide) (by evm_ov)
      |>.push2 ⟨2081⟩ (by native_decide) (by evm_ov)
      |>.jumpiT (by native_decide) hbound (by jump_dest) (by evm_ov)
      |>.jumpdest (by native_decide) (by evm_ov)
      |>.eq (by native_decide) (by evm_ov)
      |>.dup1 (by native_decide) (by evm_ov)
      |>.push2 ⟨2110⟩ (by native_decide) (by evm_ov)
      |>.jumpiNT (by native_decide) hc0 (by evm_ov)
      |>.pop (by native_decide) (by evm_ov)
      |>.push1 ⟨2⟩ (by native_decide) (by evm_ov)
      |>.dup2 (by native_decide) (by evm_ov)
      |>.push1 ⟨3⟩ (by native_decide) (by evm_ov)
      |>.dup2 (by native_decide) (by evm_ov)
      |>.gt (by native_decide) (by evm_ov)
      |>.iszero (by native_decide) (by evm_ov)
      |>.push2 ⟨2108⟩ (by native_decide) (by evm_ov)
      |>.jumpiT (by native_decide) hbound (by jump_dest) (by evm_ov)
      |>.jumpdest (by native_decide) (by evm_ov)
      |>.eq (by native_decide) (by evm_ov)
      |>.jumpdest (by native_decide) (by evm_ov)
      |>.swap4 (by native_decide) (by evm_ov)
      |>.swap3 (by native_decide) (by evm_ov)
      |>.pop (by native_decide) (by evm_ov)
      |>.pop (by native_decide) (by evm_ov)
      |>.pop (by native_decide) (by evm_ov)
      |>.jump (by native_decide) hret (by evm_ov)
    rw [show UInt256.eq R ⟨2⟩ = tlcIsOperationPendingBoolOf R from by
      unfold tlcIsOperationPendingBoolOf; rw [if_neg heq1]] at hret'
    exact ⟨_, _, hret'⟩

/-- The scratch after the `_getOperationState` mapping keccak (over the `onlyRole` read's scratch). -/
noncomputable abbrev tlcCancelPendingMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (calldataWord I.calldata 4) ⟨1⟩ (tlcCancelHasRoleMem I)

theorem tlcCancelHasRoleMem_size (I : ExecutionEnv) : (tlcCancelHasRoleMem I).size = 96 :=
  twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)

/-- From the body @2912 (canceller role confirmed), call the inlined `isOperationPending` helper
    `@2048 → _getOperationState @2232`, resolve the four state leaves, and reach the `if pending`
    `JUMPI` @2921 with the bool word `_timestamps[id] > 1` on top. -/
theorem tlcCancelReach2921 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2912⟩
      [tlcCancellerRoleWord, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      (tlcCancelHasRoleMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2921⟩
      [tlcIsOperationPendingBoolWord (tlcGetTimestampWord σ I), tlcCancellerRoleWord,
        calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      (tlcCancelPendingMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hmem96 := tlcCancelHasRoleMem_size I
  have hkec := evm_run h with [
    jumpdest, push2 ⟨2921⟩, dup3, push2 ⟨2048⟩, jump (by jump_dest),
    jumpdest, push0, push0, push2 ⟨2059⟩, dup4, push2 ⟨2232⟩, jump (by jump_dest),
    jumpdest, push0, dup2, dup2,
    raw mstore 0 (wordAt0Mem (calldataWord I.calldata 4) (tlcCancelHasRoleMem I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (twoWordHashMem (calldataWord I.calldata 4) ⟨1⟩ (tlcCancelHasRoleMem I))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
          exact twoWordHashMem_solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) hmem96)
      (by native_decide) (by evm_ov) ]
  obtain ⟨_, _, hsl⟩ := hkec.sload (by native_decide) (by evm_ov)
  by_cases ht0 : tlcGetTimestampWord σ I = ⟨0⟩
  · have hcond : UInt256.sub ⟨0⟩ (tlcGetTimestampWord σ I) = (⟨0⟩ : UInt256) := by
      rw [ht0]; exact u256_sub_self ⟨0⟩
    have h2059 := evm_run hsl with [
      dup1, push0, sub, push2 ⟨2261⟩, jumpiNT hcond,
      pop, push0, swap3, swap2, pop, pop, jump (by jump_dest) ]
    obtain ⟨_, _, h2921⟩ := tlcCancelPendingTail h2059 (by decide) (by jump_dest) (by simp)
    have hb : tlcIsOperationPendingBoolOf (⟨0⟩ : UInt256)
        = tlcIsOperationPendingBoolWord (tlcGetTimestampWord σ I) := by
      unfold tlcIsOperationPendingBoolWord
      rw [if_neg (show ¬ 1 < (tlcGetTimestampWord σ I).toNat by rw [ht0]; decide)]
      decide
    rw [hb] at h2921; exact ⟨_, _, h2921⟩
  · have hcond0 : UInt256.sub ⟨0⟩ (tlcGetTimestampWord σ I) ≠ (⟨0⟩ : UInt256) :=
      u256_zero_sub_ne_zero ht0
    have h2269 := evm_run hsl with [
      dup1, push0, sub, push2 ⟨2261⟩, jumpiT hcond0 (by jump_dest),
      jumpdest, push1 ⟨1⟩, dup2, sub, push2 ⟨2278⟩ ]
    by_cases ht1 : tlcGetTimestampWord σ I = ⟨1⟩
    · have hcond1 : UInt256.sub (tlcGetTimestampWord σ I) ⟨1⟩ = (⟨0⟩ : UInt256) := by
        rw [ht1]; exact u256_sub_self ⟨1⟩
      have h2059 := evm_run h2269 with [
        jumpiNT hcond1,
        pop, push1 ⟨3⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
      obtain ⟨_, _, h2921⟩ := tlcCancelPendingTail h2059 (by decide) (by jump_dest) (by simp)
      have hb : tlcIsOperationPendingBoolOf (⟨3⟩ : UInt256)
          = tlcIsOperationPendingBoolWord (tlcGetTimestampWord σ I) := by
        unfold tlcIsOperationPendingBoolWord
        rw [if_neg (show ¬ 1 < (tlcGetTimestampWord σ I).toNat by rw [ht1]; decide)]
        decide
      rw [hb] at h2921; exact ⟨_, _, h2921⟩
    · have hne1 : (tlcGetTimestampWord σ I).toNat ≠ 1 :=
        fun hh => ht1 (by apply u256_inj; simpa using hh)
      have hne0 : (tlcGetTimestampWord σ I).toNat ≠ 0 :=
        fun hh => ht0 (by apply u256_inj; simpa using hh)
      have h2gt : 1 < (tlcGetTimestampWord σ I).toNat := by omega
      have hcond1 : UInt256.sub (tlcGetTimestampWord σ I) ⟨1⟩ ≠ (⟨0⟩ : UInt256) :=
        u256_sub_ne_zero_of_ne ht1
      have h2286 := evm_run h2269 with [
        jumpiT hcond1 (by jump_dest),
        jumpdest, timestamp, dup2, gt, iszero, push2 ⟨2295⟩ ]
      by_cases htgt : UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp) = ⟨0⟩
      · have hcondr : UInt256.isZero
            (UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp)) ≠ (⟨0⟩ : UInt256) := by
          rw [htgt]; decide
        have h2059 := evm_run h2286 with [
          jumpiT hcondr (by jump_dest),
          jumpdest, pop, push1 ⟨2⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
        obtain ⟨_, _, h2921⟩ := tlcCancelPendingTail h2059 (by decide) (by jump_dest) (by simp)
        have hb : tlcIsOperationPendingBoolOf (⟨2⟩ : UInt256)
            = tlcIsOperationPendingBoolWord (tlcGetTimestampWord σ I) := by
          unfold tlcIsOperationPendingBoolWord; rw [if_pos h2gt]; decide
        rw [hb] at h2921; exact ⟨_, _, h2921⟩
      · have hcondw : UInt256.isZero
            (UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp)) = (⟨0⟩ : UInt256) :=
          isZero_eq_zero_of_ne htgt
        have h2059 := evm_run h2286 with [
          jumpiNT hcondw,
          pop, push1 ⟨1⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
        obtain ⟨_, _, h2921⟩ := tlcCancelPendingTail h2059 (by decide) (by jump_dest) (by simp)
        have hb : tlcIsOperationPendingBoolOf (⟨1⟩ : UInt256)
            = tlcIsOperationPendingBoolWord (tlcGetTimestampWord σ I) := by
          unfold tlcIsOperationPendingBoolWord; rw [if_pos h2gt]; decide
        rw [hb] at h2921; exact ⟨_, _, h2921⟩

/-! ## EVM: the pending branch — delete `_timestamps[id]` + `Cancelled` LOG2 + STOP -/

/-- The `Cancelled(bytes32)` event topic (the `PUSH32` at pc 3002). -/
abbrev tlcCancelledTopic : UInt256 :=
  ⟨0xbaa1eb22f2a492ba1a5fea61b8df4d27c6c8b5f3971e63bb58fa14ff72eedb70⟩

theorem tlcCancelHasRoleMem_read64 (I : ExecutionEnv) :
    (tlcCancelHasRoleMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)

theorem tlcCancelPendingMem_size (I : ExecutionEnv) : (tlcCancelPendingMem I).size = 96 :=
  twoWordHashMem_size_96 _ _ (tlcCancelHasRoleMem_size I)

theorem tlcCancelPendingMem_read64 (I : ExecutionEnv) :
    (tlcCancelPendingMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ (tlcCancelHasRoleMem_size I) (tlcCancelHasRoleMem_read64 I)

/-- Canceller role held and operation pending: delete `_timestamps[id]` (`SSTORE 0` at the mapping
    slot `keccak(id ‖ 1)`), emit `Cancelled(id)` (`LOG2`), and `STOP` — halting with the account map
    carrying the single timestamp-slot clear. -/
theorem tlcCancelX_pending {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2912⟩
      [tlcCancellerRoleWord, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      (tlcCancelHasRoleMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hpending : ¬ tlcIsOperationPendingBoolWord (tlcGetTimestampWord σ I) = ⟨0⟩) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) ⟨0⟩)
      ByteArray.empty := by
  obtain ⟨_, _, h2921⟩ := tlcCancelReach2921 h
  have hsstorepre := evm_run h2921 with [
    jumpdest, push2 ⟨2981⟩, jumpiT hpending (by jump_dest),
    jumpdest, push0, dup3, dup2,
    raw mstore 0 (wordAt0Mem (calldataWord I.calldata 4) (tlcCancelPendingMem I)) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (twoWordHashMem (calldataWord I.calldata 4) ⟨1⟩ (tlcCancelPendingMem I))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup3,
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
          exact twoWordHashMem_solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)
            (tlcCancelPendingMem_size I))
      (by native_decide) (by evm_ov),
    dup3, swap1 ]
  obtain ⟨_, _, hss⟩ := hsstorepre.sstore hperm (by native_decide) (by evm_ov)
  have h476 := hss.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (mloadFreePtrValue (by rw [twoWordHashMem_size_96 _ _ (tlcCancelPendingMem_size I)]; decide)
        (by decide)
        (twoWordHashMem_read64 _ _ (tlcCancelPendingMem_size I) (tlcCancelPendingMem_read64 I)))
      (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pushConst tlcCancelledTopic (op := .PUSH32) (width := 32) (by decide) (by native_decide)
      (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
  have hlog := RD.log2 0 (UInt256.ofNat 3) h476 (by native_decide) hperm mem_cost (by native_decide)
    (by evm_ov)
  have hstop := hlog.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
  exact hstop.stop (by native_decide) (by evm_ov)

/-! ## EVM revert paths

    A custom-error revert (`@…→ dispatcher @2157`) `MSTORE`s the selector + args into the free-memory
    region `[0x80, …)` then `REVERT`s.  `RD.rev` ignores the memory contents; only the dispatcher's
    `MLOAD 0x40` (still the free pointer `0x80`, preserved because every write is at offset ≥ 0x80) and
    the resulting stack matter.  These two facts capture that free-pointer preservation for a
    three-word error region, generic in the (irrelevant) stored words. -/

theorem tlcCancelErrMem_read64 {mem : ByteArray} (hsz : mem.size = 96)
    (hr64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) (u1 u2 u3 : UInt256) :
    (writeWord (writeWord (writeWord mem 128 u1) 132 u2) 164 u3).readWithPadding 64 32
      = UInt256.toByteArray ⟨128⟩ := by
  have hwin : WindowDisjointFromWrites 96 64 32 [(128, u1), (132, u2), (164, u3)] :=
    ⟨lt_usize _ (by norm_num), Or.inl ⟨by omega, by omega⟩,
     lt_usize _ (by norm_num), Or.inl ⟨by omega, by omega⟩,
     lt_usize _ (by norm_num), Or.inl ⟨by omega, by omega⟩, trivial⟩
  have h := writeCascade_read_preserved_of_base mem [(128, u1), (132, u2), (164, u3)] hsz hwin
  exact h.trans hr64

theorem tlcCancelErrMem_size {mem : ByteArray} (hsz : mem.size = 96) (u1 u2 u3 : UInt256) :
    64 < (writeWord (writeWord (writeWord mem 128 u1) 132 u2) 164 u3).size := by
  have hgaps : WriteGapsOk 96 [(128, u1), (132, u2), (164, u3)] :=
    ⟨lt_usize _ (by norm_num), lt_usize _ (by norm_num), lt_usize _ (by norm_num), trivial⟩
  have h : (writeWord (writeWord (writeWord mem 128 u1) 132 u2) 164 u3).size = 196 := by
    show (writeCascade mem [(128, u1), (132, u2), (164, u3)]).size = 196
    exact writeCascade_size_of_base mem _ hsz hgaps rfl
  omega

/-- `msg.sender` lacks the canceller role: the `_checkRole` `JUMPI` @3665 falls through, building the
    `AccessControlUnauthorizedAccount(sender, role)` custom error into memory and reverting via the
    revert dispatcher @2157. -/
theorem tlcCancelOnlyRoleRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2870⟩
      [calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnhas : UInt256.land ⟨255⟩ (tlcCancelRoleWord σ I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h3665⟩ := tlcCancelReach3665 h
  have hb96 := tlcCancelHasRoleMem_size I
  have hbr64 := tlcCancelHasRoleMem_read64 I
  have hrev := evm_run h3665 with [
    jumpdest, push2 ⟨3712⟩, jumpiNT hnhas,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (mloadFreePtrValue (by rw [hb96]; decide) (by decide) hbr64) (by native_decide) (by evm_ov),
    raw push4 ⟨0xe2517d3f⟩ (by native_decide) (by evm_ov),
    push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (writeWord (tlcCancelHasRoleMem I) 128 (UInt256.shiftLeft ⟨0xe2517d3f⟩ ⟨224⟩))
      (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3 (writeWord (writeWord (tlcCancelHasRoleMem I) 128 (UInt256.shiftLeft ⟨0xe2517d3f⟩ ⟨224⟩))
        132 (UInt256.land (tlcCancelCallerWord I) (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩)))
      (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, dup4, swap1,
    raw mstore 3 (writeWord (writeWord (writeWord (tlcCancelHasRoleMem I) 128
          (UInt256.shiftLeft ⟨0xe2517d3f⟩ ⟨224⟩))
        132 (UInt256.land (tlcCancelCallerWord I) (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩)))
        164 tlcCancellerRoleWord)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨68⟩, add, push2 ⟨2157⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide) mem_cost
      (mloadFreePtrValue (tlcCancelErrMem_size hb96 _ _ _) (by decide)
        (tlcCancelErrMem_read64 hb96 hbr64 _ _ _)) (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact hrev.rev 0 (by native_decide) mem_cost (by evm_ov)

/-- `_encodeStateBitmap(state) @4201`: from `[state, ret] ++ R` (with `state ≤ 3`), return to `ret`
    with `[1 << (state & 0xff)] ++ R`. -/
theorem tlcCancelEncodeBitmap {cA gh bl σ σ₀ A I} {g : Sat256} {state ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4201⟩
      (state :: ret :: R) mem aw ByteArray.empty (cA, σ) k C)
    (hb : UInt256.gt state ⟨3⟩ = ⟨0⟩)
    (hret : (D_J timelockControllerBenchBytecode 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ret
      (UInt256.shiftLeft ⟨1⟩ (UInt256.land ⟨255⟩ state) :: R) mem aw ByteArray.empty (cA, σ) k' C' := by
  refine ⟨_, _, h.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push1 ⟨3⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.gt (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨4220⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by rw [hb]; decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨255⟩ (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) hret (by evm_ov)⟩

/-- The operation is not pending: the `if pending` `JUMPI` @2921 falls through, building the
    `TimelockUnexpectedOperationState(id, bitmap)` custom error (two `_encodeStateBitmap` calls
    combined by `OR`) into memory and reverting via the revert dispatcher @2157. -/
theorem tlcCancelPendingRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2912⟩
      [tlcCancellerRoleWord, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      (tlcCancelHasRoleMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hnpending : tlcIsOperationPendingBoolWord (tlcGetTimestampWord σ I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h2921⟩ := tlcCancelReach2921 h
  have hp96 := tlcCancelPendingMem_size I
  have hpr64 := tlcCancelPendingMem_read64 I
  -- Fall through the `if pending` JUMPI to @2926, call `_encodeStateBitmap(2) @4201`.
  have h2926 := h2921.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨2981⟩ (by native_decide) (by evm_ov)
    |>.jumpiNT (by native_decide) hnpending (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.push2 ⟨2936⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨2⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨4201⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, h2936⟩ := tlcCancelEncodeBitmap h2926 (by decide) (by jump_dest) (by simp)
  -- @2936: call `_encodeStateBitmap(1) @4201`.
  have h2946pre := h2936.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨2946⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨4201⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, h2946⟩ := tlcCancelEncodeBitmap h2946pre (by decide) (by jump_dest) (by simp)
  -- @2946: encode the error (3 writes at 0x80/0x84/0xa4) and revert via @2157.
  have hrev := evm_run h2946 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (mloadFreePtrValue (by rw [hp96]; decide) (by decide) hpr64) (by native_decide) (by evm_ov),
    raw push4 ⟨0x5ead8eb5⟩ (by native_decide) (by evm_ov),
    push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (writeWord (tlcCancelPendingMem I) 128 (UInt256.shiftLeft ⟨0x5ead8eb5⟩ ⟨224⟩))
      (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨4⟩, dup2, add, swap4, swap1, swap4,
    raw mstore 3 (writeWord (writeWord (tlcCancelPendingMem I) 128 (UInt256.shiftLeft ⟨0x5ead8eb5⟩ ⟨224⟩))
        132 (calldataWord I.calldata 4)) (UInt256.ofNat 6) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    lor, push1 ⟨36⟩, dup3, add,
    raw mstore 3 (writeWord (writeWord (writeWord (tlcCancelPendingMem I) 128
          (UInt256.shiftLeft ⟨0x5ead8eb5⟩ ⟨224⟩)) 132 (calldataWord I.calldata 4)) 164
        (UInt256.lor (UInt256.shiftLeft ⟨1⟩ (UInt256.land ⟨255⟩ ⟨1⟩))
          (UInt256.shiftLeft ⟨1⟩ (UInt256.land ⟨255⟩ ⟨2⟩)))) (UInt256.ofNat 7) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨68⟩, add, push2 ⟨2157⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide) mem_cost
      (mloadFreePtrValue (tlcCancelErrMem_size hp96 _ _ _) (by decide)
        (tlcCancelErrMem_read64 hp96 hpr64 _ _ _)) (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact hrev.rev 0 (by native_decide) mem_cost (by evm_ov)

/-! ## ABI decode (a single `bytes32`, exactly like `getTimestamp`) -/

theorem tlcDecodeCancel_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (cancelTransition.params.map Param.name)
      (transitionSignature cancelTransition).paramTypes I.calldata = some (tlcGetTimestampStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = _
  exact decodeCalldata_bytes32_ok hsz36 hbig

theorem tlcDecodeCancel_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (cancelTransition.params.map Param.name)
      (transitionSignature cancelTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_short hsz4 hshort

theorem tlcDecodeCancel_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cancelTransition.params.map Param.name)
      (transitionSignature cancelTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_huge hbig

/-- EVM decode revert (mis-sized calldata): the `bytes32` decoder's `SLT` availability check fails,
    falling into its `PUSH0 PUSH0 REVERT` stub. -/
theorem tlcCancelDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 1))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4714⟩ := tlcCancelReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel
  exact h4714.jumpiNT (by native_decide) (by rw [hslt]; decide) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## Solm body -/

/-- The evaluated `CANCELLER_ROLE` mapping key (as `evalExpr?` of the `bytes32` literal produces it). -/
def tlcCancelRoleKey : KeyValue := .fixedBytes bytes32Width
  [ 0xfd, 0x64, 0x3c, 0x72, 0x71, 0x0c, 0x63, 0xc0,
    0x18, 0x02, 0x59, 0xab, 0xa6, 0xb2, 0xd0, 0x54,
    0x51, 0xe3, 0x59, 0x1a, 0x24, 0xe5, 0x8b, 0x62,
    0x23, 0x93, 0x78, 0x08, 0x57, 0x26, 0xf7, 0x83 ]

theorem tlcCancelRoleKey_word : keyValueToWord tlcCancelRoleKey = tlcCancellerRoleWord := by
  native_decide

theorem tlcCancelSourceCanon (I : ExecutionEnv) :
    (UInt256.ofNat I.source.val).toNat < EVM.addressModulus := by
  have hlt : (I.source.val : ℕ) < EVM.addressModulus := I.source.isLt
  rw [ulit_toNat' _ (Nat.lt_of_lt_of_le hlt (by native_decide))]
  exact hlt

/-- The runtime nested role slot equals the spec `roleHasRoleSlot`. -/
theorem tlcCancelRoleSlot_eq (I : ExecutionEnv) :
    roleHasRoleSlot tlcCancelRoleKey (.address I.source) = tlcCancelRoleSlot I := by
  unfold roleHasRoleSlot roleDataSlot mapSlot tlcCancelRoleSlot solcMappingSlot
  rw [keyValueToWord_address, tlcCancelRoleKey_word,
    solcAddrMask_clean_left (tlcCancelSourceCanon I)]

theorem tlcCancelStore_get_roles (I : ExecutionEnv) :
    (tlcGetTimestampStore I).get? "_roles" = none := by
  simp [tlcGetTimestampStore]

/-- `wordToElem .bool (word & 0xff)` is `true` exactly when the caller holds the role. -/
theorem tlcCancelWordToElem_present {σ : AccountMap} {I : ExecutionEnv}
    (hp : ¬ UInt256.land ⟨255⟩ (tlcCancelRoleWord σ I) = ⟨0⟩) :
    Solm.wordToElem .bool (UInt256.land (tlcCancelRoleWord σ I) ⟨255⟩) = .bool true := by
  have hz : UInt256.land (tlcCancelRoleWord σ I) ⟨255⟩ ≠ ⟨0⟩ := by rw [u256_land_comm]; exact hp
  by_cases hval : (UInt256.land (tlcCancelRoleWord σ I) ⟨255⟩).val = 0
  · exact absurd (u256_inj (congrArg Fin.val hval)) hz
  · simp [Solm.wordToElem, hval]

theorem tlcCancelWordToElem_absent {σ : AccountMap} {I : ExecutionEnv}
    (ha : UInt256.land ⟨255⟩ (tlcCancelRoleWord σ I) = ⟨0⟩) :
    Solm.wordToElem .bool (UInt256.land (tlcCancelRoleWord σ I) ⟨255⟩) = .bool false := by
  have hz : UInt256.land (tlcCancelRoleWord σ I) ⟨255⟩ = ⟨0⟩ := by rw [u256_land_comm]; exact ha
  simp [Solm.wordToElem, hz]

/-- The `onlyRole(CANCELLER_ROLE)` storage read: `_roles[CANCELLER_ROLE].hasRole[msg.sender]`. -/
theorem tlcCancelHasRoleEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := tlcGetTimestampStore I }
      (initState cA gh bl σ σ₀ g A I) (hasRoleExpr cancellerRole sender)
      = .ok (Solm.wordToElem .bool (UInt256.land (tlcCancelRoleWord σ I) ⟨255⟩)) := by
  have hstore : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (tlcCancelRoleSlot I)
        = tlcCancelRoleWord σ I :=
    codeOwnerStorageWord_initState (tlcCancelRoleSlot I)
  refine evalExpr_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tlcGetTimestampStore I })
    (slot := roleHasRoleRef cancellerRole sender)
    (er := ({ base := "_roles", steps := [.mindex tlcCancelRoleKey, .field "hasRole",
        .mindex (.address I.source)] } : EvaledStorageRef))
    (t := .bool)
    (loc := boolLoc (roleHasRoleSlot tlcCancelRoleKey (.address I.source)))
    (value := Solm.wordToElem .bool (UInt256.land (tlcCancelRoleWord σ I) ⟨255⟩)) ?_ ?_ ?_ ?_ ?_
  · simp only [roleHasRoleRef]; exact tlcCancelStore_get_roles I
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleHasRoleRef, cancellerRole,
      fixedBytes32, sender, envValue, tlcCancelRoleKey, bytes32Width, valueToKey?, initState,
      EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt, boolSt]
  · rfl
  · rw [tlcCancelRoleSlot_eq]
    show storageLocLoad (initState cA gh bl σ σ₀ g A I) (boolOffset0Loc (tlcCancelRoleSlot I)) = _
    rw [storageLocLoad_bool_offset0, hstore]

/-- The `isOperationPending(id)` guard reads `_timestamps[id]` and compares `> 1`. -/
theorem tlcCancelPendingEval {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := tlcGetTimestampStore I }
      (initState cA gh bl σ σ₀ g A I) (isOperationPendingExpr (.var "id"))
      = .ok (.bool ((Int.ofNat (tlcGetTimestampWord σ I).toNat : Int) > 1)) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hvk : valueToKey? (Value.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32))
      = some (tlcGetTimestampKey I) := by
    simp [valueToKey?, tlcGetTimestampKey, abiBytes32Width, hlen]
  have hslot : timestampSlot (tlcGetTimestampKey I)
      = solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) := by
    unfold timestampSlot mapSlot solcMappingSlot
    rw [tlcGetTimestampKey_eq I hsz36]
  have hstore : evalExpr? config { contract := contract, locals := tlcGetTimestampStore I }
      (initState cA gh bl σ σ₀ g A I) (timestampExpr (.var "id"))
      = .ok (.int (Int.ofNat (tlcGetTimestampWord σ I).toNat)) := by
    unfold timestampExpr
    rw [evalExpr_storage_scalar (cfg := config)
      (solm := { contract := contract, locals := tlcGetTimestampStore I })
      (slot := timestampRef (.var "id"))
      (er := ({ base := "_timestamps", steps := [.mindex (tlcGetTimestampKey I)] } : EvaledStorageRef))
      (t := .int uint256Int) (loc := uint256Loc (timestampSlot (tlcGetTimestampKey I)))
      (hbase := by simp [timestampRef])
      (her := by
        simp [evalStorageRef, evalStorageRefStep, timestampRef, tlcGetTimestampStore,
          EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hvk])
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, tlcGetTimestampKey, uint256St])
      (hloc := by rfl)]
    rw [hslot]
    exact congrArg EvalResult.ok
      (storageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I)
        (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)))
  unfold isOperationPendingExpr doneTimestamp
  simp only [evalExpr?, hstore, EvalResult.bind, bind, evalBinaryOp?, pure]

/-- The `delete _timestamps[id]` statement clears the mapping slot to `0`. -/
theorem tlcCancelDelete {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size) :
    deleteStorage? config { contract := contract, locals := tlcGetTimestampStore I }
      (initState cA gh bl σ σ₀ g A I) (timestampRef (.var "id"))
      = .ok (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
          (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) ⟨0⟩) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hvk : valueToKey? (Value.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32))
      = some (tlcGetTimestampKey I) := by
    simp [valueToKey?, tlcGetTimestampKey, abiBytes32Width, hlen]
  have hslot : timestampSlot (tlcGetTimestampKey I)
      = solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) := by
    unfold timestampSlot mapSlot solcMappingSlot
    rw [tlcGetTimestampKey_eq I hsz36]
  have hlayout : config.storage.layout
      { base := "_timestamps", steps := [.mindex (tlcGetTimestampKey I)] }
      (initState cA gh bl σ σ₀ g A I)
      = some (uint256Loc (timestampSlot (tlcGetTimestampKey I))) := rfl
  unfold deleteStorage?
  rw [resolveStorageRef?_ok (cfg := config)
    (slot := timestampRef (.var "id"))
    (er := ({ base := "_timestamps", steps := [.mindex (tlcGetTimestampKey I)] } : EvaledStorageRef))
    (ty := uint256St)
    (hbase := by simp [timestampRef])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, timestampRef, tlcGetTimestampStore,
        EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hvk])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, tlcGetTimestampKey, uint256St])]
  simp only [EvalResult.bind, bind, clearStorage?, uint256St, hlayout, hslot]
  rw [show (0 : Int) = Int.ofNat (⟨0⟩ : UInt256).toNat from rfl]
  exact congrArg (EvalResult.ofOption EvalError.storageError)
    (storageLocStore_uint256 (initState cA gh bl σ σ₀ g A I)
      (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) ⟨0⟩)

/-- Bridge: the EVM bool word is nonzero exactly when the timestamp exceeds `1` (pending). -/
theorem tlcCancelPendingWord_pos {t : UInt256} (h : ¬ tlcIsOperationPendingBoolWord t = ⟨0⟩) :
    1 < t.toNat := by
  by_contra hc
  exact h (by unfold tlcIsOperationPendingBoolWord; rw [if_neg hc])

theorem tlcCancelPendingWord_zero {t : UInt256} (h : tlcIsOperationPendingBoolWord t = ⟨0⟩) :
    ¬ 1 < t.toNat := by
  intro hc
  rw [show tlcIsOperationPendingBoolWord t = ⟨1⟩ from by
    unfold tlcIsOperationPendingBoolWord; rw [if_pos hc]] at h
  exact absurd h (by decide)

/-- The Solm `isOperationPending(id)` guard is `true` when the timestamp exceeds `1`. -/
theorem tlcCancelPendingEvalTrue {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size)
    (h : 1 < (tlcGetTimestampWord σ I).toNat) :
    evalExpr? config { contract := contract, locals := tlcGetTimestampStore I }
      (initState cA gh bl σ σ₀ g A I) (isOperationPendingExpr (.var "id")) = .ok (.bool true) := by
  rw [tlcCancelPendingEval hsz36]
  exact congrArg (fun b => EvalResult.ok (Value.bool b))
    (decide_eq_true_eq.mpr (Int.ofNat_lt.mpr h))

theorem tlcCancelPendingEvalFalse {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size)
    (h : ¬ 1 < (tlcGetTimestampWord σ I).toNat) :
    evalExpr? config { contract := contract, locals := tlcGetTimestampStore I }
      (initState cA gh bl σ σ₀ g A I) (isOperationPendingExpr (.var "id")) = .ok (.bool false) := by
  rw [tlcCancelPendingEval hsz36]
  exact congrArg (fun b => EvalResult.ok (Value.bool b))
    (decide_eq_false (fun hc => h (Int.ofNat_lt.mp hc)))

/-- Happy path: `require`s pass, the `delete` clears `_timestamps[id]`, and the body falls through. -/
theorem tlcCancelBodyPending {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hhas : ¬ UInt256.land ⟨255⟩ (tlcCancelRoleWord σ I) = ⟨0⟩)
    (hpend : 1 < (tlcGetTimestampWord σ I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcGetTimestampStore I)
      cancelTransition.body
      (.returned { contract := contract, locals := tlcGetTimestampStore I }
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I)
          (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner
          (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) ⟨0⟩) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [tlcCancelHasRoleEval, tlcCancelWordToElem_present hhas]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (tlcCancelPendingEvalTrue hsz36 hpend)) ?_
  exact ExecBlock.consNormal (ExecStmt.delete (tlcCancelDelete hsz36)) ExecBlock.nil

/-- Caller lacks the role: the body reverts at the `onlyRole` `require`. -/
theorem tlcCancelBodyRevertRole {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hnhas : UInt256.land ⟨255⟩ (tlcCancelRoleWord σ I) = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcGetTimestampStore I)
      cancelTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (by rw [tlcCancelHasRoleEval, tlcCancelWordToElem_absent hnhas]))

/-- Operation not pending: the body reverts at the `isOperationPending` `require`. -/
theorem tlcCancelBodyRevertPending {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hhas : ¬ UInt256.land ⟨255⟩ (tlcCancelRoleWord σ I) = ⟨0⟩)
    (hnpend : ¬ 1 < (tlcGetTimestampWord σ I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcGetTimestampStore I)
      cancelTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [tlcCancelHasRoleEval, tlcCancelWordToElem_present hhas]
  exact ExecBlock.consRevert (ExecStmt.requireFalse (tlcCancelPendingEvalFalse hsz36 hnpend))

/-! ## Refinement -/

/-- Refinement of `Cancel` (selector index 1). -/
theorem tlcCancelBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 1))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 1) (by native_decide) hsel
  have hroleword : tlcCancelRoleWord σ_evm I = tlcCancelRoleWord σ_solm I := by
    simp only [tlcCancelRoleWord]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner (tlcCancelRoleSlot I) ⟨0⟩
  have htsword : tlcGetTimestampWord σ_evm I = tlcGetTimestampWord σ_solm I := by
    simp only [tlcGetTimestampWord]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner
      (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) ⟨0⟩
  have henc : returnEquiv ByteArray.empty none cancelTransition.returnType := by
    simpa [cancelTransition] using
      (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
        (dvs := []) rfl (by native_decide) (by native_decide))
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · obtain ⟨_, _, h2870⟩ := tlcCancelReach2870 (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize hsel
        by_cases hhas : UInt256.land ⟨255⟩ (tlcCancelRoleWord σ_evm I) = ⟨0⟩
        · -- caller lacks the role: both revert
          exact tlcReEquivExecRev hcode (tlcCancelOnlyRoleRevert h2870 hhas)
            (tlcSelectorDispatchCancel hsel) (tlcDecodeCancel_ok hsz36 hbig)
            (tlcCancelBodyRevertRole (σ := σ_solm) hwv (by rw [← hroleword]; exact hhas))
        · -- caller has the role: reach the body @2912
          obtain ⟨_, _, h2912⟩ := tlcCancelReach2912 h2870 hhas
          by_cases hpend : tlcIsOperationPendingBoolWord (tlcGetTimestampWord σ_evm I) = ⟨0⟩
          · -- not pending: both revert
            exact tlcReEquivExecRev hcode (tlcCancelPendingRevert h2912 hpend)
              (tlcSelectorDispatchCancel hsel) (tlcDecodeCancel_ok hsz36 hbig)
              (tlcCancelBodyRevertPending (σ := σ_solm) hwv hsz36 (by rw [← hroleword]; exact hhas)
                (by rw [← htsword]; exact tlcCancelPendingWord_zero hpend))
          · -- pending: both delete `_timestamps[id]`
            refine tlcReEquivExecGen hcode (tlcCancelX_pending h2912 _hperm hpend)
              (tlcSelectorDispatchCancel hsel) (tlcDecodeCancel_ok hsz36 hbig)
              (tlcCancelBodyPending (σ := σ_solm) hwv hsz36 (by rw [← hroleword]; exact hhas)
                (by rw [← htsword]; exact tlcCancelPendingWord_pos hpend))
              (by simp [initState, storageStore_createdAccounts]) ?_ henc
            simpa [initState, storageStore_accountMap] using
              accountMapEquiv_sstoreAccountMap I.codeOwner
                (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) ⟨0⟩ hAccounts
      · -- huge calldata: EVM reverts at the length check, Solm decode fails
        have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := Nat.not_lt.mp hbig
        exact tlcReEquivDecodeFailed hcode
          (tlcCancelDecodeRevert (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
            (solcDecodeLenCheckHuge_4_32 hhuge hsize))
          (tlcSelectorDispatchCancel hsel) (tlcDecodeCancel_none_huge hhuge)
    · -- short calldata: EVM reverts at the length check, Solm decode fails
      have hshort : I.calldata.size < 36 := by omega
      exact tlcReEquivDecodeFailed hcode
        (tlcCancelDecodeRevert (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
          (solcDecodeLenCheckShort_4_32 hsz hshort hsize))
        (tlcSelectorDispatchCancel hsel) (tlcDecodeCancel_none_short hsz hshort)
  · -- nonpayable guard: callvalue ≠ 0
    obtain ⟨_, _, h1276⟩ := tlcReachCancel (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨1287⟩) h1276 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchCancel hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
