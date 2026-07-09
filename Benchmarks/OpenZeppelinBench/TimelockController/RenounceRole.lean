import Benchmarks.OpenZeppelinBench.TimelockController.HasRole
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `renounceRole(bytes32,address)` refinement

`renounceRole` (selector index 22, dispatch group G254 arm 0, body pc 851) is the first
**nested-mapping storage-write** function proven for this contract.  It decodes `(bytes32 role,
address callerConfirmation)` via the shared two-arg decoder `@4999` (the same one `hasRole` uses),
enforces `require(callerConfirmation == msg.sender)`, then calls the inlined `_revokeRole` helper
`@4096`: it computes the nested slot `keccak(account ‖ keccak(role ‖ 0))` (reusing
`tlcHasRoleSlotLoad @2762`), `SLOAD`s it, and — **only if the role is currently present** — clears the
low byte with `SLOAD; AND(NOT 0xff); SSTORE` and emits a `RoleRevoked` `LOG4`, otherwise it does
nothing.

Template for the other nested-mapping mutations (`grantRole`/`revokeRole`): the conditional write is a
Solm `.ite` whose true branch `.assign .storage (roleHasRoleRef …) (.boolLit false)` couples to the
EVM `SSTORE` of `land word (lnot 0xff)` via `storageLocStore_bool_false_offset0`; the false branch is
a no-op matching the EVM jump-around at `@4089`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Decoded arguments, source store, and post-state

The role key / confirmation key / nested slot / stored word are all shared with `hasRole`
(`tlcHasRoleRoleKey`, `tlcHasRoleAccountKey`, `tlcHasRoleSlot`, `tlcHasRoleWord`): the same calldata
words hash to the same slot.  Only the source-level local store differs (the second param is named
`callerConfirmation`, not `account`). -/

/-- The decoded local store bound by `renounceRole(bytes32 role, address callerConfirmation)`. -/
abbrev tlcRenounceRoleStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "role"
      (.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32))).insert
    "callerConfirmation" (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))

/-- The nested-mapping slot `keccak(account ‖ keccak(role ‖ 0))` (= `tlcHasRoleSlot I`), as an
    `abbrev` so it unfolds to the raw `solcMappingSlot` form produced by `tlcHasRoleSlotLoad`. -/
abbrev tlcRenounceRoleSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
    (UInt256.land solcAddrMask (calldataWord I.calldata 36))

/-- The stored `_roles[role].hasRole[callerConfirmation]` word. -/
abbrev tlcRenounceRoleWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (tlcRenounceRoleSlot I)

/-- Scratch memory after the `_revokeRole` slot computation: `account‖inner` staged over the
    inner-slot preimage `role‖0` (the memory `tlcHasRoleSlotLoad` leaves at its exit). -/
noncomputable abbrev tlcRenounceRoleKecMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (UInt256.land solcAddrMask (calldataWord I.calldata 36))
    (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
    (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ solcFreePtrMem)

/-- The `EVM.State` after `_roles[role].hasRole[callerConfirmation] = false` (nested slot write);
    stated exactly as `storageLocStore_bool_false_offset0` produces it. -/
abbrev tlcRenounceRolePost (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (tlcRenounceRoleSlot I)
    (UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tlcRenounceRoleSlot I))
      (UInt256.lnot ⟨255⟩))

/-- The runtime recomputes the outer slot with the mask on the right (`account & ((1<<160)-1)`); it
    equals the spec/`tlcHasRoleSlotLoad` slot (mask on the left). -/
theorem tlcRenounceRoleOuterSlot (I : ExecutionEnv) :
    solcMappingSlot (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
        (UInt256.land (calldataWord I.calldata 36)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
      = tlcRenounceRoleSlot I := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [hmask, u256_land_comm]

/-! ## ABI decode (two-arg `(bytes32, address)`, shared decoder) -/

theorem tlcDecodeRenounceRole_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (renounceRoleTransition.params.map Param.name)
      (transitionSignature renounceRoleTransition).paramTypes I.calldata
      = some (tlcRenounceRoleStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "callerConfirmation"] [bytes32, addr]
    I.calldata = _
  exact decodeCalldata_bytes32_address_ok hsz68 hbig hcanon

theorem tlcDecodeRenounceRole_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (renounceRoleTransition.params.map Param.name)
      (transitionSignature renounceRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "callerConfirmation"] [bytes32, addr]
    I.calldata = none
  exact decodeCalldata_bytes32_address_none_short hsz4 hshort

theorem tlcDecodeRenounceRole_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (renounceRoleTransition.params.map Param.name)
      (transitionSignature renounceRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "callerConfirmation"] [bytes32, addr]
    I.calldata = none
  exact decodeCalldata_bytes32_address_none_huge hbig

theorem tlcDecodeRenounceRole_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (renounceRoleTransition.params.map Param.name)
      (transitionSignature renounceRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "callerConfirmation"] [bytes32, addr]
    I.calldata = none
  exact decodeCalldata_bytes32_address_none_noncanon hsz68 hbig hnc

/-! ## EVM: reach the body and run the shared two-arg decoder -/

/-- Reach the `renounceRole` body pc 851 (G254 arm 0). -/
theorem tlcReachRenounceRole {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 22)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨851⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x36568abe⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x36 0x56 0x8a 0xbe ⟨0x36568abe⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG254Body 0 (by omega) ⟨851⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; exact absurd hj (Nat.not_lt_zero j))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard, push the two continuations `[476, 877]`, and run the two-arg decoder
    prologue to the `SLT` length-check `JUMPI` @5012 (identical to `tlcHasRoleReachLenCheck` but with
    the `renounceRole` return/decode continuations `476`/`877`). -/
theorem tlcRenounceRoleReachLenCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 22)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5012⟩
      [⟨5016⟩, UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩),
        ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨877⟩, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h851⟩ := tlcReachRenounceRole (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h864⟩ := tlcGuardPeelOk (gt := ⟨862⟩) h851 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, h864.push2 ⟨476⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨877⟩ (by native_decide) (by evm_ov)
    |>.calldatasize (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨4999⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup6 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.slt (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨5016⟩ (by native_decide) (by evm_ov)⟩

/-- After the length check passes, run the two-arg decoder to the address sub-decoder's canonicality
    `EQ`/`JUMPI` @4374 (identical to `tlcHasRoleReachEqCheck` with continuations `476`/`877`). -/
theorem tlcRenounceRoleReachEqCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 22)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4374⟩
      [⟨4378⟩,
        UInt256.eq (calldataWord I.calldata 36)
          (UInt256.land (calldataWord I.calldata 36)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)),
        calldataWord I.calldata 36, ⟨36⟩, ⟨5032⟩, ⟨0⟩, calldataWord I.calldata 4, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨877⟩, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hbig hsize
  obtain ⟨_, _, h5012⟩ := tlcRenounceRoleReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv (by omega) hsize hsel
  have hoff : (⟨4⟩ : UInt256) + ⟨32⟩ = ⟨36⟩ := by decide
  have hafterAdd := h5012.jumpiT (by native_decide) (by rw [hslt]; decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.push2 ⟨5032⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  rw [hoff] at hafterAdd
  exact ⟨_, _, hafterAdd.push2 ⟨4356⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
    |>.push2 ⟨4378⟩ (by native_decide) (by evm_ov)⟩

/-- With a canonical confirmation address, finish the decoder tail (@4374 `EQ` passes) and jump through
    the decode continuation `@877` into the `renounceRole` body logic `@1992`, leaving
    `[callerConfirmation, role, 476, sel]` on the stack over `solcFreePtrMem`. -/
theorem tlcRenounceRoleReach1992 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 22))
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1992⟩
      [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  obtain ⟨_, _, h4374⟩ := tlcRenounceRoleReachEqCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz68 hbig hsize hsel
  exact ⟨_, _, h4374.jumpiT (by native_decide)
      (by rw [hmask, solcAddrCanon_eq hcanon]; decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨1992⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-! ## The `callerConfirmation == msg.sender` check (body @1992-2008) -/

/-- Masking a canonical confirmation address with the runtime `(1<<160)-1` mask is the identity. -/
theorem tlcRenounceRoleMaskConf {I : ExecutionEnv}
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    UInt256.land (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
      = calldataWord I.calldata 36 := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [hmask]; exact solcAddrMask_clean hcanon

/-- `msg.sender` (as a word) equals the decoded confirmation word exactly when the confirmation
    address decodes back to `msg.sender`. -/
theorem tlcRenounceRoleSourceConf {I : ExecutionEnv}
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    (UInt256.ofNat I.source.val = calldataWord I.calldata 36)
      ↔ AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source := by
  have hv : (AccountAddress.ofNat (calldataWord I.calldata 36).toNat).val
      = (calldataWord I.calldata 36).toNat := by
    unfold AccountAddress.ofNat
    exact Nat.mod_eq_of_lt (by
      rw [show AccountAddress.size = EVM.addressModulus from by decide]; exact hcanon)
  constructor
  · intro h
    have hval : I.source.val = (calldataWord I.calldata 36).toNat := by
      rw [← solcSourceWord_toNat I, solcSourceWord]; rw [h]
    exact (Fin.ext (by rw [hv, hval]))
  · intro h
    rw [← h]
    rw [show (AccountAddress.ofNat (calldataWord I.calldata 36).toNat).val
        = (calldataWord I.calldata 36).toNat from hv]
    exact u256_ofNat_toNat _

/-- Confirmation matches: the EVM `CALLER == callerConfirmation` `EQ` is `1`. -/
theorem tlcRenounceRoleConfEqTrue {I : ExecutionEnv}
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hconf : AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source) :
    UInt256.eq (UInt256.ofNat I.source.val)
      (UInt256.land (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨1⟩ := by
  rw [tlcRenounceRoleMaskConf hcanon, (tlcRenounceRoleSourceConf hcanon).2 hconf]
  exact uInt256_eq_self _

/-- Confirmation mismatches: the EVM `CALLER == callerConfirmation` `EQ` is `0`. -/
theorem tlcRenounceRoleConfEqFalse {I : ExecutionEnv}
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hnconf : ¬ AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source) :
    UInt256.eq (UInt256.ofNat I.source.val)
      (UInt256.land (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) = ⟨0⟩ := by
  rw [tlcRenounceRoleMaskConf hcanon]
  apply uInt256_eq_zero_of_ne
  intro hbad
  exact hnconf ((tlcRenounceRoleSourceConf hcanon).1 (uInt256_eq_one_eq hbad))

/-- Confirmation-mismatch revert: build the `AccessControlBadConfirmation()` custom error and
    `REVERT` (body @1992 → @2032). -/
theorem tlcRenounceRoleRevConfirm {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1992⟩
      [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hnconf : ¬ AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h2032 := evm_run h with [
    jumpdest,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    raw caller (by native_decide) (by evm_ov),
    eq, push2 ⟨2033⟩,
    jumpiNT (by exact tlcRenounceRoleConfEqFalse hcanon hnconf),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost solcFreePtrMem_mload64
      (by native_decide) (by evm_ov),
    raw push4 ⟨0x334bd919⟩ (by native_decide) (by evm_ov),
    push1 ⟨225⟩, shl, dup2,
    raw mstore 6 (solcReturnMem (UInt256.shiftLeft ⟨0x334bd919⟩ ⟨225⟩)) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨4⟩, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost
      (mloadFreePtrValue (by rw [solcReturnMem_size]; decide) (by decide)
        (solcReturnMem_read64 _)) (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact h2032.rev 0 (by native_decide) mem_cost (by evm_ov)

/-! ## `_revokeRole` (body @1992 → @4096 → slot load @2762 → @4107) -/

/-- Confirmation matches: run the confirmation check, dispatch to `_revokeRole @4096`, and reuse
    `tlcHasRoleSlotLoad @2762` for the nested-slot `SLOAD`, reaching the `if present` `ISZERO/JUMPI`
    @4107 with the masked stored word on top and the recomputation scratch in memory. -/
theorem tlcRenounceRoleReach4107 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1992⟩
      [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hconf : AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4107⟩
      [UInt256.land ⟨255⟩ (tlcRenounceRoleWord σ I), ⟨0⟩, calldataWord I.calldata 36,
        calldataWord I.calldata 4, ⟨2043⟩, calldataWord I.calldata 36, calldataWord I.calldata 4,
        ⟨476⟩, tlcSelWord I]
      (tlcRenounceRoleKecMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h2762 := evm_run h with [
    jumpdest,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and,
    raw caller (by native_decide) (by evm_ov),
    eq, push2 ⟨2033⟩,
    jumpiT (by rw [tlcRenounceRoleConfEqTrue hcanon hconf]; decide) (by jump_dest),
    jumpdest,
    push2 ⟨2043⟩, dup3, dup3, push2 ⟨4096⟩,
    jump (by jump_dest),
    jumpdest,
    push0, push2 ⟨4107⟩, dup4, dup4, push2 ⟨2762⟩,
    jump (by jump_dest) ]
  exact tlcHasRoleSlotLoad h2762 (by jump_dest) (by evm_ov)

/-- Role absent (`_roles[role].hasRole[account]` already `false`): `_revokeRole` takes the `@4089`
    skip branch, does no `SSTORE`/`LOG`, and `STOP`s with the account map unchanged. -/
theorem tlcRenounceRoleX_absent {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1992⟩
      [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hconf : AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source)
    (habsent : UInt256.land ⟨255⟩ (tlcRenounceRoleWord σ I) = ⟨0⟩) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      ByteArray.empty := by
  obtain ⟨_, _, h4107⟩ := tlcRenounceRoleReach4107 h hcanon hconf
  have h476 := evm_run h4107 with [
    jumpdest,
    iszero, push2 ⟨4089⟩,
    jumpiT (by rw [habsent]; decide) (by jump_dest),
    jumpdest,
    pop, push0, push2 ⟨1685⟩,
    jump (by jump_dest),
    jumpdest,
    swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest,
    pop, pop, pop,
    jump (by jump_dest),
    jumpdest ]
  exact h476.stop (by native_decide) (by evm_ov)

/-- The `RoleRevoked(bytes32,address,address)` event topic (the `PUSH32` at pc 4158). -/
abbrev tlcRenounceRoleRevokedTopic : UInt256 :=
  ⟨0xf6391f5c32d9c69d2a47ea670b442974b53935d1edc7fd64eb21e047a839171b⟩

/-- Role present (`_roles[role].hasRole[account]` currently `true`): `_revokeRole` recomputes the
    nested slot, `SSTORE`s `word & ~0xff` (clearing the bool to `false`), emits `RoleRevoked` `LOG4`,
    and `STOP`s — halting with the account map carrying the single nested-slot write. -/
theorem tlcRenounceRoleX_present {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1992⟩
      [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus)
    (hconf : AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source)
    (hpresent : ¬ UInt256.land ⟨255⟩ (tlcRenounceRoleWord σ I) = ⟨0⟩) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (tlcRenounceRoleSlot I)
        (UInt256.land (UInt256.lnot ⟨255⟩) (tlcRenounceRoleWord σ I))) ByteArray.empty := by
  obtain ⟨_, _, h4107⟩ := tlcRenounceRoleReach4107 h hcanon hconf
  have hM0 : (tlcRenounceRoleKecMem I).size = 96 :=
    twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
  have hM2 : (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRenounceRoleKecMem I)).size = 96 :=
    twoWordHashMem_size_96 _ _ hM0
  have hM4size : (twoWordHashMem
      (UInt256.land (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
      (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
      (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRenounceRoleKecMem I))).size = 96 :=
    twoWordHashMem_size_96 _ _ hM2
  have hM4read64 : (twoWordHashMem
      (UInt256.land (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
      (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
      (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRenounceRoleKecMem I))).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 _ _ hM2 (twoWordHashMem_read64 _ _ hM0
      (twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
        (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)))
  have hkec := evm_run h4107 with [
    jumpdest,
    iszero, push2 ⟨4089⟩,
    jumpiNT (by exact isZero_eq_zero_of_ne hpresent),
    push0, dup4, dup2,
    raw mstore 0 (wordAt0Mem (calldataWord I.calldata 4) (tlcRenounceRoleKecMem I))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRenounceRoleKecMem I))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
          exact twoWordHashMem_solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4) hM0)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and, dup1, dup6,
    raw mstore 0 (wordAt0Mem
        (UInt256.land (calldataWord I.calldata 36)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
        (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRenounceRoleKecMem I)))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    swap3,
    raw mstore 0 (twoWordHashMem
        (UInt256.land (calldataWord I.calldata 36)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
        (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
        (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRenounceRoleKecMem I)))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    dup1, dup4,
    raw keccak256 0 (tlcRenounceRoleSlot I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
          exact (twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
            (UInt256.land (calldataWord I.calldata 36)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) hM2).trans
            (tlcRenounceRoleOuterSlot I))
      (by native_decide) (by evm_ov),
    dup1 ]
  obtain ⟨_, _, hsl⟩ := hkec.sload (by native_decide) (by evm_ov)
  have hsstorepre := evm_run hsl with [ push1 ⟨255⟩, not, and, swap1 ]
  obtain ⟨_, _, hss⟩ := hsstorepre.sstore hperm (by native_decide) (by evm_ov)
  have hlogpre := evm_run hss with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (mloadFreePtrValue (by rw [hM4size]; decide) (by decide) hM4read64)
      (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    swap3, dup7, swap2 ]
  have hlog := (hlogpre.pushConst tlcRenounceRoleRevokedTopic (width := 32) (op := .PUSH32)
      (by decide) (by native_decide) (by evm_ov)).swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  have h476 := (hlog.log4 0 (UInt256.ofNat 3) (by native_decide) hperm mem_cost
      (by native_decide) (by evm_ov)) |>.pop (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1685⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
  exact h476.stop (by native_decide) (by evm_ov)

/-! ## EVM decode-revert paths (shared two-arg decoder) -/

/-- Mis-sized calldata: the signed length check fails the `JUMPI`, falling into the decoder's
    `PUSH0 PUSH0 REVERT` stub @5013. -/
theorem tlcRenounceRoleDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 22))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h5012⟩ := tlcRenounceRoleReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz hsize hsel
  exact h5012.jumpiNT (by native_decide) (by rw [hslt]; decide) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-- Non-canonical confirmation address: the sub-decoder's canonicality `EQ` fails the `JUMPI`,
    falling into the `PUSH0 PUSH0 REVERT` stub @4375. -/
theorem tlcRenounceRoleNoncanonRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 22))
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  obtain ⟨_, _, h4374⟩ := tlcRenounceRoleReachEqCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz68 hbig hsize hsel
  exact h4374.jumpiNT (by native_decide) (by rw [hmask]; exact tlcHasRoleNoncanon_eq hnc) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## Solm body -/

theorem tlcRenounceRoleStore_get_roles (I : ExecutionEnv) :
    (tlcRenounceRoleStore I).get? "_roles" = none := by
  unfold tlcRenounceRoleStore
  rw [store_get_ne2 _ _ _ (by native_decide) (by native_decide)]
  simp

theorem tlcRenounceRoleStore_index_role (I : ExecutionEnv) :
    (tlcRenounceRoleStore I)["role"] =
      Value.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32) := by
  unfold tlcRenounceRoleStore
  rw [Std.HashMap.getElem_insert]; simp

/-- `wordToElem .bool (word & 0xff)` is `true` exactly when the packed byte is nonzero. -/
theorem tlcRenounceRoleWordToElem_present {σ : AccountMap} {I : ExecutionEnv}
    (hpres : ¬ UInt256.land ⟨255⟩ (tlcRenounceRoleWord σ I) = ⟨0⟩) :
    Solm.wordToElem .bool (UInt256.land (tlcRenounceRoleWord σ I) ⟨255⟩) = .bool true := by
  have hz : UInt256.land (tlcRenounceRoleWord σ I) ⟨255⟩ ≠ ⟨0⟩ := by
    rw [u256_land_comm]; exact hpres
  by_cases hval : (UInt256.land (tlcRenounceRoleWord σ I) ⟨255⟩).val = 0
  · exact absurd (u256_inj (congrArg Fin.val hval)) hz
  · simp [Solm.wordToElem, hval]

/-- `wordToElem .bool (word & 0xff)` is `false` exactly when the packed byte is zero. -/
theorem tlcRenounceRoleWordToElem_absent {σ : AccountMap} {I : ExecutionEnv}
    (habs : UInt256.land ⟨255⟩ (tlcRenounceRoleWord σ I) = ⟨0⟩) :
    Solm.wordToElem .bool (UInt256.land (tlcRenounceRoleWord σ I) ⟨255⟩) = .bool false := by
  have hz : UInt256.land (tlcRenounceRoleWord σ I) ⟨255⟩ = ⟨0⟩ := by
    rw [u256_land_comm]; exact habs
  simp [Solm.wordToElem, hz]

/-- The `callerConfirmation == msg.sender` guard evaluates to `true` when the decoded confirmation
    address is `msg.sender`. -/
theorem tlcRenounceRoleGuardEval (evm : EVM.State) (I : ExecutionEnv)
    (hself : AccountAddress.ofNat (calldataWord I.calldata 36).toNat = evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := tlcRenounceRoleStore I } evm
      (.binary .eq (.var "callerConfirmation") sender) = .ok (.bool true) := by
  have hcc : (tlcRenounceRoleStore I).get? "callerConfirmation"
      = some (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)) := by
    simp [tlcRenounceRoleStore]
  simp only [sender, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, hcc, envValue,
    evalBinaryOp?, hself, beq_self_eq_true]

/-- The `callerConfirmation == msg.sender` guard evaluates to `false` when it is not. -/
theorem tlcRenounceRoleGuardEvalFalse (evm : EVM.State) (I : ExecutionEnv)
    (hself : ¬ AccountAddress.ofNat (calldataWord I.calldata 36).toNat = evm.executionEnv.source) :
    evalExpr? config { contract := contract, locals := tlcRenounceRoleStore I } evm
      (.binary .eq (.var "callerConfirmation") sender) = .ok (.bool false) := by
  have hcc : (tlcRenounceRoleStore I).get? "callerConfirmation"
      = some (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)) := by
    simp [tlcRenounceRoleStore]
  simp only [sender, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind, pure, hcc, envValue,
    evalBinaryOp?]
  rw [show ((Value.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))
      == (Value.address evm.executionEnv.source)) = false from by
    simp only [beq_eq_false_iff_ne, ne_eq, Value.address.injEq]; exact hself]

/-- The `_roles[role].hasRole[callerConfirmation]` storage read (the `.ite` condition). -/
theorem tlcRenounceRoleHasRoleEval {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := tlcRenounceRoleStore I }
      (initState cA gh bl σ σ₀ g A I)
      (hasRoleExpr (.var "role") (.var "callerConfirmation"))
      = .ok (Solm.wordToElem .bool (UInt256.land (tlcRenounceRoleWord σ I) ⟨255⟩)) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hslot : roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I) = tlcRenounceRoleSlot I :=
    tlcHasRoleSlot_eq I hsz36
  have hstore : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (tlcRenounceRoleSlot I)
        = tlcRenounceRoleWord σ I :=
    codeOwnerStorageWord_initState (tlcRenounceRoleSlot I)
  refine evalExpr_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tlcRenounceRoleStore I })
    (slot := roleHasRoleRef (.var "role") (.var "callerConfirmation"))
    (er := ({ base := "_roles", steps := [.mindex (tlcHasRoleRoleKey I), .field "hasRole",
        .mindex (tlcHasRoleAccountKey I)] } : EvaledStorageRef))
    (t := .bool)
    (loc := boolLoc (roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I)))
    (value := Solm.wordToElem .bool (UInt256.land (tlcRenounceRoleWord σ I) ⟨255⟩)) ?_ ?_ ?_ ?_ ?_
  · simp only [roleHasRoleRef]; exact tlcRenounceRoleStore_get_roles I
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleHasRoleRef,
      tlcRenounceRoleStore_index_role, tlcHasRoleAccountKey, valueToKey?,
      hlen, abiBytes32Width, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt, boolSt]
  · rfl
  · rw [hslot]
    show storageLocLoad (initState cA gh bl σ σ₀ g A I) (boolOffset0Loc (tlcRenounceRoleSlot I)) = _
    rw [storageLocLoad_bool_offset0, hstore]

/-- The `_roles[role].hasRole[callerConfirmation] = false` nested storage write collapses to a single
    bool `storageStore` on the nested slot. -/
theorem tlcRenounceRoleAssign {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size) :
    assignStorageRef? config { contract := contract, locals := tlcRenounceRoleStore I }
      (initState cA gh bl σ σ₀ g A I) .storage
      (roleHasRoleRef (.var "role") (.var "callerConfirmation")) (.bool false)
      = .ok ({ contract := contract, locals := tlcRenounceRoleStore I },
        tlcRenounceRolePost (initState cA gh bl σ σ₀ g A I) I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hslot : roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I) = tlcRenounceRoleSlot I :=
    tlcHasRoleSlot_eq I hsz36
  have hstore : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (tlcRenounceRoleSlot I)
        = tlcRenounceRoleWord σ I :=
    codeOwnerStorageWord_initState (tlcRenounceRoleSlot I)
  refine assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tlcRenounceRoleStore I })
    (slot := roleHasRoleRef (.var "role") (.var "callerConfirmation"))
    (er := ({ base := "_roles", steps := [.mindex (tlcHasRoleRoleKey I), .field "hasRole",
        .mindex (tlcHasRoleAccountKey I)] } : EvaledStorageRef))
    (ty := boolSt)
    (loc := boolLoc (roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I)))
    (value := .bool false) ?_ ?_ ?_ ?_ (by trivial) ?_
  · simp only [roleHasRoleRef]; exact tlcRenounceRoleStore_get_roles I
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleHasRoleRef,
      tlcRenounceRoleStore_index_role, tlcHasRoleAccountKey, valueToKey?,
      hlen, abiBytes32Width, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt, boolSt]
  · rfl
  · rw [hslot]
    show storageLocStore (initState cA gh bl σ σ₀ g A I) (boolOffset0Loc (tlcRenounceRoleSlot I))
        (.bool false) = some (tlcRenounceRolePost (initState cA gh bl σ σ₀ g A I) I)
    rw [storageLocStore_bool_false_offset0]

/-- Happy path, role present: the body runs `require`s, takes the `.ite` `then` branch, and writes
    `false`, falling through (`none`). -/
theorem tlcRenounceRoleBodyPresent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hself : AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source)
    (hpres : ¬ UInt256.land ⟨255⟩ (tlcRenounceRoleWord σ I) = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcRenounceRoleStore I)
      renounceRoleTransition.body
      (.returned { contract := contract, locals := tlcRenounceRoleStore I }
        (tlcRenounceRolePost (initState cA gh bl σ σ₀ g A I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (tlcRenounceRoleGuardEval _ I
    (by simp only [initState]; exact hself))) ?_
  refine ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil
  · rw [tlcRenounceRoleHasRoleEval hsz36, tlcRenounceRoleWordToElem_present hpres]
  · exact ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) (tlcRenounceRoleAssign hsz36))
      ExecBlock.nil

/-- Happy path, role absent: the body runs `require`s, takes the empty `.ite` `else` branch, and
    falls through with the state unchanged (`none`). -/
theorem tlcRenounceRoleBodyAbsent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hself : AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source)
    (habs : UInt256.land ⟨255⟩ (tlcRenounceRoleWord σ I) = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcRenounceRoleStore I)
      renounceRoleTransition.body
      (.returned { contract := contract, locals := tlcRenounceRoleStore I }
        (initState cA gh bl σ σ₀ g A I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (tlcRenounceRoleGuardEval _ I
    (by simp only [initState]; exact hself))) ?_
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil
  rw [tlcRenounceRoleHasRoleEval hsz36, tlcRenounceRoleWordToElem_absent habs]

/-- Confirmation mismatch: the body reverts at the `require(callerConfirmation == msg.sender)`. -/
theorem tlcRenounceRoleBodyRevertConfirm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hself : ¬ AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcRenounceRoleStore I)
      renounceRoleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (tlcRenounceRoleGuardEvalFalse _ I
    (by simp only [initState]; exact hself)))

/-- Refinement of `RenounceRole` (selector index 22). -/
theorem tlcRenounceRoleBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 22))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 22) (by native_decide) hsel
  have hword : tlcRenounceRoleWord σ_evm I = tlcRenounceRoleWord σ_solm I := by
    simp only [tlcRenounceRoleWord]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner (tlcRenounceRoleSlot I) ⟨0⟩
  have henc : returnEquiv ByteArray.empty none renounceRoleTransition.returnType := by
    simpa [renounceRoleTransition] using
      (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
        (dvs := []) rfl (by native_decide) (by native_decide))
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz68 : 68 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · by_cases hconf : AccountAddress.ofNat (calldataWord I.calldata 36).toNat = I.source
          · -- confirmation matches: both mutate (or no-op) the nested slot
            obtain ⟨_, _, h1992⟩ := tlcRenounceRoleReach1992 (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
              hcode hwv hsz68 hbig hsize hsel hcanon
            by_cases hpres : UInt256.land ⟨255⟩ (tlcRenounceRoleWord σ_evm I) = ⟨0⟩
            · -- role absent: no write on either side
              exact tlcReEquivExecGen hcode
                (tlcRenounceRoleX_absent h1992 hcanon hconf hpres)
                (tlcSelectorDispatchRenounceRole hsel) (tlcDecodeRenounceRole_ok hsz68 hbig hcanon)
                (tlcRenounceRoleBodyAbsent (σ := σ_solm) hwv
                  (by omega) hconf (by rw [← hword]; exact hpres))
                (by simp [initState])
                (by simpa [initState] using hAccounts) henc
            · -- role present: both SSTORE `false` to the nested slot
              refine tlcReEquivExecGen hcode
                (tlcRenounceRoleX_present h1992 _hperm hcanon hconf hpres)
                (tlcSelectorDispatchRenounceRole hsel) (tlcDecodeRenounceRole_ok hsz68 hbig hcanon)
                (tlcRenounceRoleBodyPresent (σ := σ_solm) hwv
                  (by omega) hconf (by rw [← hword]; exact hpres))
                (by simp [tlcRenounceRolePost, initState, storageStore_createdAccounts]) ?_ henc
              have hval : UInt256.land (UInt256.lnot ⟨255⟩) (tlcRenounceRoleWord σ_evm I)
                  = UInt256.land (tlcRenounceRoleWord σ_solm I) (UInt256.lnot ⟨255⟩) := by
                rw [u256_land_comm, hword]
              rw [hval]
              simpa [tlcRenounceRolePost, initState, storageStore_accountMap,
                codeOwnerStorageWord_initState] using
                accountMapEquiv_sstoreAccountMap I.codeOwner (tlcRenounceRoleSlot I)
                  (UInt256.land (tlcRenounceRoleWord σ_solm I) (UInt256.lnot ⟨255⟩)) hAccounts
          · -- confirmation mismatches: both revert
            obtain ⟨_, _, h1992⟩ := tlcRenounceRoleReach1992 (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
              hcode hwv hsz68 hbig hsize hsel hcanon
            exact tlcReEquivExecRev hcode (tlcRenounceRoleRevConfirm h1992 hcanon hconf)
              (tlcSelectorDispatchRenounceRole hsel) (tlcDecodeRenounceRole_ok hsz68 hbig hcanon)
              (tlcRenounceRoleBodyRevertConfirm (σ := σ_solm) hwv hconf)
        · -- non-canonical confirmation: EVM reverts at the address check, Solm decode fails
          exact tlcReEquivDecodeFailed hcode
            (tlcRenounceRoleNoncanonRevert (g := Sat256.ofUInt256 g) hcode hwv hsz68 hbig hsize hsel
              hcanon)
            (tlcSelectorDispatchRenounceRole hsel) (tlcDecodeRenounceRole_none_noncanon hsz68 hbig
              hcanon)
      · -- huge calldata: EVM reverts at the length check, Solm decode fails
        have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := Nat.not_lt.mp hbig
        exact tlcReEquivDecodeFailed hcode
          (tlcRenounceRoleDecodeRevert (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
            (solcDecodeLenCheckHuge_4_64 hhuge hsize))
          (tlcSelectorDispatchRenounceRole hsel) (tlcDecodeRenounceRole_none_huge hhuge)
    · -- short calldata: EVM reverts at the length check, Solm decode fails
      have hshort : I.calldata.size < 68 := by omega
      exact tlcReEquivDecodeFailed hcode
        (tlcRenounceRoleDecodeRevert (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
          (solcDecodeLenCheckShort_4_64 hsz hshort hsize))
        (tlcSelectorDispatchRenounceRole hsel) (tlcDecodeRenounceRole_none_short hsz hshort)
  · -- nonpayable guard: callvalue ≠ 0
    obtain ⟨_, _, h851⟩ := tlcReachRenounceRole (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨862⟩) h851 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchRenounceRole hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
