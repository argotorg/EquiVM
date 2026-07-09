import Benchmarks.OpenZeppelinBench.TimelockController.RevokeRole
import Benchmarks.OpenZeppelinBench.TimelockController.RenounceRole
import Benchmarks.OpenZeppelinBench.TimelockController.GetRoleAdmin
import Benchmarks.OpenZeppelinBench.TimelockController.HasRole
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `grantRole(bytes32,address)` refinement

`grantRole` (selector index 10, dispatch group G301 arm 1, body pc 789) is `revokeRole` with the write
inverted: it decodes `(bytes32 role, address account)`, reads `_roles[role].adminRole`, enforces
`require(hasRole(adminRole, msg.sender))` (the SAME onlyRole helper `@3461→@3655→@2762`), then calls
the inlined `_grantRole @3953`: it SETS `_roles[role].hasRole[account]` (via `AND(~0xff); OR 1; SSTORE`)
and emits `RoleGranted`, but ONLY IF the role is currently ABSENT.

The admin read, onlyRole nested-slot load, error-scratch, decoded store, and `letDecl`/onlyRole Solm
evaluations are identical to `revokeRole` and are imported from `RevokeRole.lean`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## ABI decode (two-arg `(bytes32, address)`, shared decoder; produces `tlcHasRoleStore`) -/

theorem tlcDecodeGrantRole_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (grantRoleTransition.params.map Param.name)
      (transitionSignature grantRoleTransition).paramTypes I.calldata = some (tlcHasRoleStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = _
  exact decodeCalldata_bytes32_address_ok hsz68 hbig hcanon

theorem tlcDecodeGrantRole_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (grantRoleTransition.params.map Param.name)
      (transitionSignature grantRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = none
  exact decodeCalldata_bytes32_address_none_short hsz4 hshort

theorem tlcDecodeGrantRole_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (grantRoleTransition.params.map Param.name)
      (transitionSignature grantRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = none
  exact decodeCalldata_bytes32_address_none_huge hbig

theorem tlcDecodeGrantRole_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (grantRoleTransition.params.map Param.name)
      (transitionSignature grantRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = none
  exact decodeCalldata_bytes32_address_none_noncanon hsz68 hbig hnc

/-! ## EVM: reach the body @789 and run the shared two-arg decoder -/

/-- Reach the `grantRole` body pc 789 (G301 arm 1). -/
theorem tlcReachGrantRole {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 10)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨789⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x2f2ff15d⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x2f 0x2f 0xf1 0x5d ⟨0x2f2ff15d⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG301Body 1 (by omega) ⟨789⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j; rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard (gt @800), push continuations `[476, 815]`, and run the two-arg decoder
    prologue to the `SLT` length-check `JUMPI` @5012. -/
theorem tlcGrantRoleReachLenCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 10)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5012⟩
      [⟨5016⟩, UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩),
        ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨815⟩, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h789⟩ := tlcReachGrantRole (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h802⟩ := tlcGuardPeelOk (gt := ⟨800⟩) h789 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, h802.push2 ⟨476⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨815⟩ (by native_decide) (by evm_ov)
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

/-- After the length check passes, run the decoder to the address canonicality `EQ`/`JUMPI` @4374. -/
theorem tlcGrantRoleReachEqCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 10)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4374⟩
      [⟨4378⟩,
        UInt256.eq (calldataWord I.calldata 36)
          (UInt256.land (calldataWord I.calldata 36)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)),
        calldataWord I.calldata 36, ⟨36⟩, ⟨5032⟩, ⟨0⟩, calldataWord I.calldata 4, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨815⟩, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hbig hsize
  obtain ⟨_, _, h5012⟩ := tlcGrantRoleReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
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

/-- With a canonical account, finish the decoder and jump through `@815` into the body logic `@1914`,
    leaving `[account, role, 476, sel]` over `solcFreePtrMem`. -/
theorem tlcGrantRoleReach1914 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 10))
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1914⟩
      [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  obtain ⟨_, _, h4374⟩ := tlcGrantRoleReachEqCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
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
    |>.push2 ⟨1914⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-! ## EVM: admin read + onlyRole nested-slot load, reaching @3665 (cont `1940`) -/

/-- From body-logic `@1914`, compute `adminRole`, dispatch through the onlyRole helpers, and run the
    shared `@2762` load, reaching the onlyRole `JUMPI` @3665.  Identical to `revokeRole` except the
    onlyRole return continuation is `1940` (not `3066`). -/
theorem tlcGrantRoleReachAdminBit {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1914⟩
      [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I), solcSourceWord I,
        tlcRevokeRoleAdminWord σ I, ⟨3471⟩, tlcRevokeRoleAdminWord σ I, ⟨1940⟩,
        tlcRevokeRoleAdminWord σ I, calldataWord I.calldata 36, calldataWord I.calldata 4,
        ⟨476⟩, tlcSelWord I]
      (tlcRevokeRoleOnlyMem σ I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hk := h.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.mstore 0 (wordAt0Mem (calldataWord I.calldata 4) solcFreePtrMem) (UInt256.ofNat 3)
        (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.mstore 0 (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ solcFreePtrMem) (UInt256.ofNat 3)
        (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.keccak256 0 (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4)) (UInt256.ofNat 3)
        (by native_decide) mem_cost
        (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
            exact twoWordHashMem_solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4) solcFreePtrMem_size)
        (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hsl⟩ := hk.sload (by native_decide) (by evm_ov)
  rw [tlcRevokeRoleAdminSlot_eq I hsz36] at hsl
  have h2762 := hsl.push2 ⟨1940⟩ (by native_decide) (by evm_ov)
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
  exact tlcRevokeRoleSlotLoadGen h2762 (tlcRevokeRoleMem1_size I) (by jump_dest) (by evm_ov)

/-- `msg.sender` lacks `adminRole`: the onlyRole `JUMPI` is not taken and `@2157` `REVERT`s.  Same
    error scratch as `revokeRole` (the `1940` return continuation lives below the error's stack use). -/
theorem tlcGrantRoleRevAdmin {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I), solcSourceWord I,
        tlcRevokeRoleAdminWord σ I, ⟨3471⟩, tlcRevokeRoleAdminWord σ I, ⟨1940⟩,
        tlcRevokeRoleAdminWord σ I, calldataWord I.calldata 36, calldataWord I.calldata 4,
        ⟨476⟩, tlcSelWord I]
      (tlcRevokeRoleOnlyMem σ I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hunauth : UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h2165 := evm_run h with [
    jumpdest,
    push2 ⟨3712⟩,
    jumpiNT (by exact hunauth),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (mloadFreePtrValue (by rw [tlcRevokeRoleOnlyMem_size]; decide) (by decide)
        (tlcRevokeRoleOnlyMem_read64 σ I)) (by native_decide) (by evm_ov),
    raw push4 ⟨0xe2517d3f⟩ (by native_decide) (by evm_ov),
    push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (tlcRevokeRoleErr1 _ σ I) (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and,
    push1 ⟨4⟩, dup3, add,
    raw mstore 3 (tlcRevokeRoleErr2 _ _ σ I) (UInt256.ofNat 6) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ + ⟨4⟩ : UInt256).toNat = 132 from by native_decide])
      (by native_decide) (by evm_ov),
    push1 ⟨36⟩, dup2, add, dup4, swap1,
    raw mstore 3 (tlcRevokeRoleErr3 _ _ _ σ I) (UInt256.ofNat 7) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ + ⟨36⟩ : UInt256).toNat = 164 from by native_decide])
      (by native_decide) (by evm_ov),
    push1 ⟨68⟩, add, push2 ⟨2157⟩, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 7) (by native_decide) mem_cost
      (mloadFreePtrValue (by rw [tlcRevokeRoleErr3_size]; decide) (by decide)
        (tlcRevokeRoleErr3_read64 _ _ _ σ I)) (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact h2165.rev 0 (by native_decide) mem_cost (by evm_ov)

/-- `msg.sender` has `adminRole`: dispatch to `_grantRole @3953` and run the shared `@2762` load for
    `_roles[role].hasRole[account]`, reaching the `if present` `JUMPI` @3964 (no `ISZERO` — inverted
    from `_revokeRole`). -/
theorem tlcGrantRoleReach3964 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I), solcSourceWord I,
        tlcRevokeRoleAdminWord σ I, ⟨3471⟩, tlcRevokeRoleAdminWord σ I, ⟨1940⟩,
        tlcRevokeRoleAdminWord σ I, calldataWord I.calldata 36, calldataWord I.calldata 4,
        ⟨476⟩, tlcSelWord I]
      (tlcRevokeRoleOnlyMem σ I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3964⟩
      [UInt256.land ⟨255⟩ (tlcHasRoleWord σ I), ⟨0⟩, calldataWord I.calldata 36,
        calldataWord I.calldata 4, ⟨1950⟩, tlcRevokeRoleAdminWord σ I, calldataWord I.calldata 36,
        calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      (tlcRevokeRoleWriteMem σ I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have h2762 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨3712⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) (by exact hauth) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.push2 ⟨1950⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.push2 ⟨3953⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push2 ⟨3964⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.push2 ⟨2762⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact tlcRevokeRoleSlotLoadGen h2762 (tlcRevokeRoleOnlyMem_size σ I) (by jump_dest) (by evm_ov)

/-- Role present (`_roles[role].hasRole[account]` already `true`): `_grantRole` skips at `@4089`,
    does no `SSTORE`/`LOG`, and `STOP`s with the account map unchanged. -/
theorem tlcGrantRoleXSkip {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I), solcSourceWord I,
        tlcRevokeRoleAdminWord σ I, ⟨3471⟩, tlcRevokeRoleAdminWord σ I, ⟨1940⟩,
        tlcRevokeRoleAdminWord σ I, calldataWord I.calldata 36, calldataWord I.calldata 4,
        ⟨476⟩, tlcSelWord I]
      (tlcRevokeRoleOnlyMem σ I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩)
    (hpresent : ¬ UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      ByteArray.empty := by
  obtain ⟨_, _, h3964⟩ := tlcGrantRoleReach3964 h hauth
  have h476 := evm_run h3964 with [
    jumpdest,
    push2 ⟨4089⟩,
    jumpiT (by exact hpresent) (by jump_dest),
    jumpdest,
    pop, push0, push2 ⟨1685⟩,
    jump (by jump_dest),
    jumpdest,
    swap3, swap2, pop, pop,
    jump (by jump_dest),
    jumpdest,
    pop, pop, pop, pop,
    jump (by jump_dest),
    jumpdest ]
  exact h476.stop (by native_decide) (by evm_ov)

/-- The `RoleGranted(bytes32,address,address)` event topic (the `PUSH32` at pc 4038). -/
abbrev tlcGrantRoleGrantedTopic : UInt256 :=
  ⟨0x2f8788117e7eff1d82e926ec794901d17c78024a50270940304540a733656f0d⟩

/-- The `EVM.State` after `_roles[role].hasRole[account] = true` (set low byte via `OR 1`). -/
abbrev tlcGrantRolePost (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (tlcHasRoleSlot I)
    (UInt256.lor
      (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (tlcHasRoleSlot I))
        (UInt256.lnot ⟨255⟩)) ⟨1⟩)

/-- Role absent (`_roles[role].hasRole[account]` currently `false`): `_grantRole` recomputes the
    nested slot, `SSTORE`s `(word & ~0xff) | 1` (setting the bool to `true`), emits `RoleGranted`
    `LOG4`, and `STOP`s — halting with the account map carrying the single nested-slot write. -/
theorem tlcGrantRoleXWrite {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I), solcSourceWord I,
        tlcRevokeRoleAdminWord σ I, ⟨3471⟩, tlcRevokeRoleAdminWord σ I, ⟨1940⟩,
        tlcRevokeRoleAdminWord σ I, calldataWord I.calldata 36, calldataWord I.calldata 4,
        ⟨476⟩, tlcSelWord I]
      (tlcRevokeRoleOnlyMem σ I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩)
    (habsent : UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (tlcHasRoleSlot I)
        (UInt256.lor ⟨1⟩ (UInt256.land (UInt256.lnot ⟨255⟩) (tlcHasRoleWord σ I)))) ByteArray.empty := by
  obtain ⟨_, _, h3964⟩ := tlcGrantRoleReach3964 h hauth
  have hM0 : (tlcRevokeRoleWriteMem σ I).size = 96 :=
    twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ (tlcRevokeRoleOnlyMem_size σ I))
  have hM2 : (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRevokeRoleWriteMem σ I)).size = 96 :=
    twoWordHashMem_size_96 _ _ hM0
  have hM4size : (twoWordHashMem
      (UInt256.land (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
      (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
      (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRevokeRoleWriteMem σ I))).size = 96 :=
    twoWordHashMem_size_96 _ _ hM2
  have hM4read64 : (twoWordHashMem
      (UInt256.land (calldataWord I.calldata 36)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
      (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
      (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRevokeRoleWriteMem σ I))).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 _ _ hM2 (twoWordHashMem_read64 _ _ hM0
      (twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ (tlcRevokeRoleOnlyMem_size σ I))
        (twoWordHashMem_read64 _ _ (tlcRevokeRoleOnlyMem_size σ I) (tlcRevokeRoleOnlyMem_read64 σ I))))
  have hkec := evm_run h3964 with [
    jumpdest,
    push2 ⟨4089⟩,
    jumpiNT (by exact habsent),
    push0, dup4, dup2,
    raw mstore 0 (wordAt0Mem (calldataWord I.calldata 4) (tlcRevokeRoleWriteMem σ I))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨32⟩, dup2, dup2,
    raw mstore 0 (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRevokeRoleWriteMem σ I))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup1, dup4,
    raw keccak256 0 (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
          exact twoWordHashMem_solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4) hM0)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and, dup5,
    raw mstore 0 (wordAt0Mem
        (UInt256.land (calldataWord I.calldata 36)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
        (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRevokeRoleWriteMem σ I)))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    swap1, swap2,
    raw mstore 0 (twoWordHashMem
        (UInt256.land (calldataWord I.calldata 36)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
        (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
        (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRevokeRoleWriteMem σ I)))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    swap1,
    raw keccak256 0 (tlcHasRoleSlot I) (UInt256.ofNat 3) (by native_decide) mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
          exact (twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
            (UInt256.land (calldataWord I.calldata 36)
              (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)) hM2).trans
            (tlcRenounceRoleOuterSlot I))
      (by native_decide) (by evm_ov),
    dup1 ]
  obtain ⟨_, _, hsl⟩ := hkec.sload (by native_decide) (by evm_ov)
  have hsstorepre := evm_run hsl with [ push1 ⟨255⟩, not, and, push1 ⟨1⟩, lor, swap1 ]
  obtain ⟨_, _, hss⟩ := hsstorepre.sstore hperm (by native_decide) (by evm_ov)
  have hlogpre := evm_run hss with [
    push2 ⟨4017⟩,
    raw caller (by native_decide) (by evm_ov),
    swap1, jump (by jump_dest),
    jumpdest,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup3,
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, and, dup5 ]
  have hlog := (hlogpre.pushConst tlcGrantRoleGrantedTopic (width := 32) (op := .PUSH32)
      (by decide) (by native_decide) (by evm_ov)).push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
        (mloadFreePtrValue (by rw [hM4size]; decide) (by decide) hM4read64) (by native_decide)
        (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
        (mloadFreePtrValue (by rw [hM4size]; decide) (by decide) hM4read64) (by native_decide)
        (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
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
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
  exact h476.stop (by native_decide) (by evm_ov)

/-! ## EVM decode-revert paths -/

theorem tlcGrantRoleDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 10))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h5012⟩ := tlcGrantRoleReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz hsize hsel
  exact h5012.jumpiNT (by native_decide) (by rw [hslt]; decide) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem tlcGrantRoleNoncanonRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 10))
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  obtain ⟨_, _, h4374⟩ := tlcGrantRoleReachEqCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz68 hbig hsize hsel
  exact h4374.jumpiNT (by native_decide) (by rw [hmask]; exact tlcHasRoleNoncanon_eq hnc) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## Solm body (`grantRoleIfMissing`: write `true` only if the role is currently absent) -/

/-- The `_roles[role].hasRole[account] = true` write collapses to a single bool `storageStore`. -/
theorem tlcGrantRoleAssign {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size) :
    assignStorageRef? config { contract := contract, locals := tlcRevokeRoleStore' σ I }
      (initState cA gh bl σ σ₀ g A I) .storage
      (roleHasRoleRef (.var "role") (.var "account")) (.bool true)
      = .ok ({ contract := contract, locals := tlcRevokeRoleStore' σ I },
        tlcGrantRolePost (initState cA gh bl σ σ₀ g A I) I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hslot : roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I) = tlcHasRoleSlot I :=
    tlcHasRoleSlot_eq I hsz36
  refine assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tlcRevokeRoleStore' σ I })
    (slot := roleHasRoleRef (.var "role") (.var "account"))
    (er := ({ base := "_roles", steps := [.mindex (tlcHasRoleRoleKey I), .field "hasRole",
        .mindex (tlcHasRoleAccountKey I)] } : EvaledStorageRef))
    (ty := boolSt)
    (loc := boolLoc (roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I)))
    (value := .bool true) ?_ ?_ ?_ ?_ (by trivial) ?_
  · simp only [roleHasRoleRef]; exact tlcRevokeRoleStore'_get_roles σ I
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleHasRoleRef,
      tlcRevokeRoleStore'_index_role, tlcRevokeRoleStore'_index_account, tlcHasRoleAccountKey,
      valueToKey?, hlen, abiBytes32Width, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt, boolSt]
  · rfl
  · rw [hslot]
    show storageLocStore (initState cA gh bl σ σ₀ g A I) (boolOffset0Loc (tlcHasRoleSlot I))
        (.bool true) = some (tlcGrantRolePost (initState cA gh bl σ σ₀ g A I) I)
    rw [storageLocStore_bool_true_offset0]

/-- The inverted guard `!hasRole(role, account)` is `true` when the role is absent. -/
theorem tlcGrantRoleGuardEvalTrue {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size)
    (habs : UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tlcRevokeRoleStore' σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.unary .not (hasRoleExpr (.var "role") (.var "account"))) = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.bind, bind, tlcRevokeRoleHasRoleEval hsz36,
    tlcRevokeRoleWordToElem_absent habs]
  rfl

/-- The inverted guard `!hasRole(role, account)` is `false` when the role is present. -/
theorem tlcGrantRoleGuardEvalFalse {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size)
    (hpres : ¬ UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    evalExpr? config { contract := contract, locals := tlcRevokeRoleStore' σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.unary .not (hasRoleExpr (.var "role") (.var "account"))) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.bind, bind, tlcRevokeRoleHasRoleEval hsz36,
    tlcRevokeRoleWordToElem_present hpres]
  rfl

/-- Authorized + role absent: the body sets the bit (`.ite` then-branch writes `true`). -/
theorem tlcGrantRoleBodyWrite {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩)
    (habs : UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcHasRoleStore I)
      grantRoleTransition.body
      (.returned { contract := contract, locals := tlcRevokeRoleStore' σ I }
        (tlcGrantRolePost (initState cA gh bl σ σ₀ g A I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (tlcRevokeRoleLetDeclEval hsz36)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (by rw [tlcRevokeRoleOnlyRoleEval, tlcRevokeRoleAdminWordToElem_present hauth])) ?_
  refine ExecBlock.consNormal (ExecStmt.iteTrue (tlcGrantRoleGuardEvalTrue hsz36 habs) ?_)
    ExecBlock.nil
  exact ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure]) (tlcGrantRoleAssign hsz36))
    ExecBlock.nil

/-- Authorized + role present: the body takes the empty `.ite` else-branch, state unchanged. -/
theorem tlcGrantRoleBodySkip {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩)
    (hpres : ¬ UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcHasRoleStore I)
      grantRoleTransition.body
      (.returned { contract := contract, locals := tlcRevokeRoleStore' σ I }
        (initState cA gh bl σ σ₀ g A I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (tlcRevokeRoleLetDeclEval hsz36)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (by rw [tlcRevokeRoleOnlyRoleEval, tlcRevokeRoleAdminWordToElem_present hauth])) ?_
  exact ExecBlock.consNormal (ExecStmt.iteFalse (tlcGrantRoleGuardEvalFalse hsz36 hpres)
    ExecBlock.nil) ExecBlock.nil

/-- Unauthorized: the body reverts at `require(hasRole(adminRole, msg.sender))`. -/
theorem tlcGrantRoleBodyRevertAdmin {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hunauth : UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcHasRoleStore I)
      grantRoleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (tlcRevokeRoleLetDeclEval hsz36)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (by rw [tlcRevokeRoleOnlyRoleEval, tlcRevokeRoleAdminWordToElem_absent hunauth]))

/-! ## Refinement -/

/-- Refinement of `GrantRole` (selector index 10). -/
theorem tlcGrantRoleBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 10) (by native_decide) hsel
  have hword : tlcHasRoleWord σ_evm I = tlcHasRoleWord σ_solm I := by
    simp only [tlcHasRoleWord]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner (tlcHasRoleSlot I) ⟨0⟩
  have hadminword : tlcRevokeRoleAdminWord σ_evm I = tlcRevokeRoleAdminWord σ_solm I := by
    simp only [tlcRevokeRoleAdminWord]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner (roleAdminSlot (tlcHasRoleRoleKey I)) ⟨0⟩
  have hadminslot : tlcRevokeRoleAdminSlot σ_evm I = tlcRevokeRoleAdminSlot σ_solm I := by
    simp only [tlcRevokeRoleAdminSlot, hadminword]
  have hadminhasrole : tlcRevokeRoleAdminHasRoleWord σ_evm I = tlcRevokeRoleAdminHasRoleWord σ_solm I := by
    simp only [tlcRevokeRoleAdminHasRoleWord, hadminslot]
    exact accountMapEquiv_storage_findD hAccounts I.codeOwner (tlcRevokeRoleAdminSlot σ_solm I) ⟨0⟩
  have henc : returnEquiv ByteArray.empty none grantRoleTransition.returnType := by
    simpa [grantRoleTransition] using
      (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
        (dvs := []) rfl (by native_decide) (by native_decide))
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz68 : 68 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · obtain ⟨_, _, h1914⟩ := tlcGrantRoleReach1914 (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
            hcode hwv hsz68 hbig hsize hsel hcanon
          obtain ⟨_, _, h3665⟩ := tlcGrantRoleReachAdminBit h1914 (by omega)
          by_cases hauth : UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ_evm I) = ⟨0⟩
          · -- unauthorized: both revert
            exact tlcReEquivExecRev hcode (tlcGrantRoleRevAdmin h3665 hauth)
              (tlcSelectorDispatchGrantRole hsel) (tlcDecodeGrantRole_ok hsz68 hbig hcanon)
              (tlcGrantRoleBodyRevertAdmin (σ := σ_solm) hwv (by omega)
                (by rw [← hadminhasrole]; exact hauth))
          · by_cases hpres : UInt256.land ⟨255⟩ (tlcHasRoleWord σ_evm I) = ⟨0⟩
            · -- role absent: both SSTORE `true`
              refine tlcReEquivExecGen hcode
                (tlcGrantRoleXWrite h3665 _hperm hauth hpres)
                (tlcSelectorDispatchGrantRole hsel) (tlcDecodeGrantRole_ok hsz68 hbig hcanon)
                (tlcGrantRoleBodyWrite (σ := σ_solm) hwv (by omega)
                  (by rw [← hadminhasrole]; exact hauth) (by rw [← hword]; exact hpres))
                (by simp [tlcGrantRolePost, initState, storageStore_createdAccounts]) ?_ henc
              have hval : UInt256.lor ⟨1⟩ (UInt256.land (UInt256.lnot ⟨255⟩) (tlcHasRoleWord σ_evm I))
                  = UInt256.lor (UInt256.land (tlcHasRoleWord σ_solm I) (UInt256.lnot ⟨255⟩)) ⟨1⟩ := by
                rw [u256_land_comm, hword, u256_lor_comm]
              rw [hval]
              simpa [tlcGrantRolePost, initState, storageStore_accountMap,
                codeOwnerStorageWord_initState] using
                accountMapEquiv_sstoreAccountMap I.codeOwner (tlcHasRoleSlot I)
                  (UInt256.lor (UInt256.land (tlcHasRoleWord σ_solm I) (UInt256.lnot ⟨255⟩)) ⟨1⟩)
                  hAccounts
            · -- role present: no write on either side
              exact tlcReEquivExecGen hcode
                (tlcGrantRoleXSkip h3665 hauth hpres)
                (tlcSelectorDispatchGrantRole hsel) (tlcDecodeGrantRole_ok hsz68 hbig hcanon)
                (tlcGrantRoleBodySkip (σ := σ_solm) hwv (by omega)
                  (by rw [← hadminhasrole]; exact hauth) (by rw [← hword]; exact hpres))
                (by simp [initState])
                (by simpa [initState] using hAccounts) henc
        · -- non-canonical account: EVM reverts at the address check, Solm decode fails
          exact tlcReEquivDecodeFailed hcode
            (tlcGrantRoleNoncanonRevert (g := Sat256.ofUInt256 g) hcode hwv hsz68 hbig hsize hsel
              hcanon)
            (tlcSelectorDispatchGrantRole hsel) (tlcDecodeGrantRole_none_noncanon hsz68 hbig hcanon)
      · -- huge calldata
        have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := Nat.not_lt.mp hbig
        exact tlcReEquivDecodeFailed hcode
          (tlcGrantRoleDecodeRevert (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
            (solcDecodeLenCheckHuge_4_64 hhuge hsize))
          (tlcSelectorDispatchGrantRole hsel) (tlcDecodeGrantRole_none_huge hhuge)
    · -- short calldata
      have hshort : I.calldata.size < 68 := by omega
      exact tlcReEquivDecodeFailed hcode
        (tlcGrantRoleDecodeRevert (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
          (solcDecodeLenCheckShort_4_64 hsz hshort hsize))
        (tlcSelectorDispatchGrantRole hsel) (tlcDecodeGrantRole_none_short hsz hshort)
  · -- nonpayable guard: callvalue ≠ 0
    obtain ⟨_, _, h789⟩ := tlcReachGrantRole (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨800⟩) h789 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchGrantRole hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
