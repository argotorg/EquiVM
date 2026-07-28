import Benchmarks.OpenZeppelinBench.TimelockController.RenounceRole
import Benchmarks.OpenZeppelinBench.TimelockController.GetRoleAdmin
import Benchmarks.OpenZeppelinBench.TimelockController.HasRole
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `revokeRole(bytes32,address)` refinement

`revokeRole` (selector index 23, dispatch group G51 arm 0, body pc 1350) is `renounceRole` plus an
`onlyRole(getRoleAdmin(role))` admin check.  It decodes `(bytes32 role, address account)` via the
shared two-arg decoder `@4999` (continuations `476`/`1376`, body-logic `@3040`), reads
`_roles[role].adminRole` (`keccak(role‖0)+1; SLOAD`), enforces `require(hasRole(adminRole, msg.sender))`
via the shared onlyRole helper `@3461→@3655→@2762`, then calls the inlined `_revokeRole @4096` (the
SAME helper `renounceRole` uses): it clears `_roles[role].hasRole[account]` only if currently present.

The admin read dirties the keccak scratch, so the two `@2762` nested-slot loads (onlyRole and the
`_revokeRole` write) run over a *non-`solcFreePtrMem`* memory; `tlcRevokeRoleSlotLoadGen` is the
memory-generic form of `HasRole.tlcHasRoleSlotLoad` used for both.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Decoded data, slots, and stored words (shared with `hasRole`) -/

/-- The `_roles[role].adminRole` word (mapping slot `keccak(role ‖ 0)`, struct offset `+1`). -/
abbrev tlcRevokeRoleAdminWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (roleAdminSlot (tlcHasRoleRoleKey I))

/-- The onlyRole nested slot `keccak(msg.sender ‖ keccak(adminRole ‖ 0))`. -/
abbrev tlcRevokeRoleAdminSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨0⟩ (tlcRevokeRoleAdminWord σ I))
    (UInt256.land solcAddrMask (solcSourceWord I))

/-- The stored `_roles[adminRole].hasRole[msg.sender]` word (the onlyRole check reads its low byte). -/
abbrev tlcRevokeRoleAdminHasRoleWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (tlcRevokeRoleAdminSlot σ I)

/-- The runtime computes the admin slot as `1 + keccak(role ‖ 0)`; it equals `roleAdminSlot role`. -/
theorem tlcRevokeRoleAdminSlot_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    (⟨1⟩ : UInt256) + solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4)
      = roleAdminSlot (tlcHasRoleRoleKey I) := by
  have hbaseslot : solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4)
      = roleDataSlot (tlcHasRoleRoleKey I) := by
    unfold roleDataSlot mapSlot solcMappingSlot
    rw [tlcHasRoleRoleKey_eq I hsz36]
  rw [hbaseslot]
  exact tlcOneAddEqAddSlot (roleDataSlot (tlcHasRoleRoleKey I))

/-! ## ABI decode (two-arg `(bytes32, address)`, shared decoder; produces `tlcHasRoleStore`) -/

theorem tlcDecodeRevokeRole_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (revokeRoleTransition.params.map Param.name)
      (transitionSignature revokeRoleTransition).paramTypes I.calldata = some (tlcHasRoleStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = _
  exact decodeCalldata_bytes32_address_ok hsz68 hbig hcanon

theorem tlcDecodeRevokeRole_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (revokeRoleTransition.params.map Param.name)
      (transitionSignature revokeRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = none
  exact decodeCalldata_bytes32_address_none_short hsz4 hshort

theorem tlcDecodeRevokeRole_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (revokeRoleTransition.params.map Param.name)
      (transitionSignature revokeRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = none
  exact decodeCalldata_bytes32_address_none_huge hbig

theorem tlcDecodeRevokeRole_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (revokeRoleTransition.params.map Param.name)
      (transitionSignature revokeRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = none
  exact decodeCalldata_bytes32_address_none_noncanon hsz68 hbig hnc

/-! ## Memory-generic nested-mapping slot load @2762

    The `HasRole.tlcHasRoleSlotLoad` proof only reads memory in `[0,0x40)` (which it overwrites) via
    `.size` facts, so it lifts verbatim to any 96-byte input `mem`.  Needed because the admin read
    leaves `twoWordHashMem …` (not `solcFreePtrMem`) before the two onlyRole/write `@2762` calls. -/
theorem tlcRevokeRoleSlotLoadGen {cA gh bl σ σ₀ A I} {g : Sat256}
    {account role cont : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2762⟩
      (account :: role :: cont :: R) mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hret : (D_J timelockControllerBenchBytecode 0).contains cont = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) cont
      (UInt256.land ⟨255⟩
        (solcSlotWord σ I
          (solcMappingSlot (solcMappingSlot ⟨0⟩ role) (UInt256.land solcAddrMask account))) :: R)
      (twoWordHashMem (UInt256.land solcAddrMask account) (solcMappingSlot ⟨0⟩ role)
        (twoWordHashMem role ⟨0⟩ mem)) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have hkec := h.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.mstore 0 (wordAt0Mem role mem) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rfl) (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.mstore 0 (twoWordHashMem role ⟨0⟩ mem) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rfl) (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.keccak256 0 (solcMappingSlot ⟨0⟩ role) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
            exact twoWordHashMem_solcMappingSlot ⟨0⟩ role hmem)
        (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.push1 ⟨160⟩ (by native_decide) (by evm_ov)
    |>.shl (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.swap4 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.swap4 (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.mstore 0
        (wordAt0Mem (UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) account)
          (twoWordHashMem role ⟨0⟩ mem)) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rfl) (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.mstore 0
        (twoWordHashMem (UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) account)
          (solcMappingSlot ⟨0⟩ role) (twoWordHashMem role ⟨0⟩ mem)) (UInt256.ofNat 3)
        (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.keccak256 0
        (solcMappingSlot (solcMappingSlot ⟨0⟩ role)
          (UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) account))
        (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
            exact twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨0⟩ role)
              (UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) account)
              (twoWordHashMem_size_96 role ⟨0⟩ hmem))
        (by native_decide) (by evm_ov)
  obtain ⟨_, _, hsl⟩ := hkec.sload (by native_decide) (by evm_ov)
  have hfin := hsl.push1 ⟨255⟩ (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.jump (by native_decide) hret (by evm_ov)
  exact ⟨_, _, by simpa only [hmask] using hfin⟩

/-! ## EVM: reach the body @1350 and run the shared two-arg decoder -/

/-- Reach the `revokeRole` body pc 1350 (G51 arm 0). -/
theorem tlcReachRevokeRole {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 23)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1350⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0xd547741f⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xd5 0x47 0x74 0x1f ⟨0xd547741f⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG51Body 0 (by omega) ⟨1350⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; exact absurd hj (Nat.not_lt_zero j))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard (gt @1361), push continuations `[476, 1376]`, and run the two-arg
    decoder prologue to the `SLT` length-check `JUMPI` @5012. -/
theorem tlcRevokeRoleReachLenCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 23)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5012⟩
      [⟨5016⟩, UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩),
        ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1376⟩, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h1350⟩ := tlcReachRevokeRole (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h1363⟩ := tlcGuardPeelOk (gt := ⟨1361⟩) h1350 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, h1363.push2 ⟨476⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1376⟩ (by native_decide) (by evm_ov)
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
theorem tlcRevokeRoleReachEqCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 23)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4374⟩
      [⟨4378⟩,
        UInt256.eq (calldataWord I.calldata 36)
          (UInt256.land (calldataWord I.calldata 36)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)),
        calldataWord I.calldata 36, ⟨36⟩, ⟨5032⟩, ⟨0⟩, calldataWord I.calldata 4, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨1376⟩, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hbig hsize
  obtain ⟨_, _, h5012⟩ := tlcRevokeRoleReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
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

/-- With a canonical account, finish the decoder and jump through `@1376` into the body logic `@3040`,
    leaving `[account, role, 476, sel]` over `solcFreePtrMem`. -/
theorem tlcRevokeRoleReach3040 {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 23))
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3040⟩
      [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  obtain ⟨_, _, h4374⟩ := tlcRevokeRoleReachEqCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
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
    |>.push2 ⟨3040⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-! ## Memory chain across the admin read and the two nested-slot loads -/

/-- Memory after the admin `keccak(role‖0)` (before the onlyRole `@2762` load). -/
noncomputable abbrev tlcRevokeRoleMem1 (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ solcFreePtrMem

/-- Memory after the onlyRole `@2762` load (before the `_revokeRole @2762` write load). -/
noncomputable abbrev tlcRevokeRoleOnlyMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (UInt256.land solcAddrMask (solcSourceWord I))
    (solcMappingSlot ⟨0⟩ (tlcRevokeRoleAdminWord σ I))
    (twoWordHashMem (tlcRevokeRoleAdminWord σ I) ⟨0⟩ (tlcRevokeRoleMem1 I))

theorem tlcRevokeRoleMem1_size (I : ExecutionEnv) : (tlcRevokeRoleMem1 I).size = 96 :=
  twoWordHashMem_size_96 _ _ solcFreePtrMem_size

theorem tlcRevokeRoleMem1_read64 (I : ExecutionEnv) :
    (tlcRevokeRoleMem1 I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64

theorem tlcRevokeRoleOnlyMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (tlcRevokeRoleOnlyMem σ I).size = 96 :=
  twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ (tlcRevokeRoleMem1_size I))

theorem tlcRevokeRoleOnlyMem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (tlcRevokeRoleOnlyMem σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ (tlcRevokeRoleMem1_size I))
    (twoWordHashMem_read64 _ _ (tlcRevokeRoleMem1_size I) (tlcRevokeRoleMem1_read64 I))

/-! ## EVM: admin read `_roles[role].adminRole` + onlyRole nested-slot load, reaching @3665 -/

/-- From body-logic `@3040`, compute `adminRole = _roles[role].adminRole` (`keccak(role‖0)+1; SLOAD`),
    dispatch through the onlyRole helpers `@3461→@3655`, and run the shared `@2762` load for
    `_roles[adminRole].hasRole[msg.sender]`, reaching the `if authorized` `JUMPI` @3665 with the
    masked admin-hasRole bit on top. -/
theorem tlcRevokeRoleReachAdminBit {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3040⟩
      [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨476⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I), solcSourceWord I,
        tlcRevokeRoleAdminWord σ I, ⟨3471⟩, tlcRevokeRoleAdminWord σ I, ⟨3066⟩,
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
  have h2762 := hsl.push2 ⟨3066⟩ (by native_decide) (by evm_ov)
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

/-! ## EVM: onlyRole revert (`AccessControlUnauthorizedAccount`), @3665 → @2157 REVERT

    Error scratch: selector `@0x80`, masked `msg.sender` `@0x84`, `adminRole` `@0xa4` — writes at
    128/132/164 over the onlyRole memory (free pointer `@0x40` intact). -/

/-- Error scratch after the selector `MSTORE @0x80`. -/
noncomputable abbrev tlcRevokeRoleErr1 (v : UInt256) (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray v).write 0 (tlcRevokeRoleOnlyMem σ I) 128 32

/-- Error scratch after the masked-sender `MSTORE @0x84`. -/
noncomputable abbrev tlcRevokeRoleErr2 (v w : UInt256) (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray w).write 0 (tlcRevokeRoleErr1 v σ I) 132 32

/-- Error scratch after the `adminRole` `MSTORE @0xa4`. -/
noncomputable abbrev tlcRevokeRoleErr3 (v w x : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  (UInt256.toByteArray x).write 0 (tlcRevokeRoleErr2 v w σ I) 164 32

theorem tlcRevokeRoleErr1_size (v : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    (tlcRevokeRoleErr1 v σ I).size = 160 := by
  unfold tlcRevokeRoleErr1
  rw [toByteArray_write_eq _ _ _ (by rw [tlcRevokeRoleOnlyMem_size]; omega)
      (by rw [tlcRevokeRoleOnlyMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, tlcRevokeRoleOnlyMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem tlcRevokeRoleErr2_size (v w : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    (tlcRevokeRoleErr2 v w σ I).size = 164 := by
  unfold tlcRevokeRoleErr2
  exact toByteArray_write32_size_of_le (tlcRevokeRoleErr1 v σ I) w 132 160 164
    (tlcRevokeRoleErr1_size v σ I) (by rw [tlcRevokeRoleErr1_size]; omega) (by decide)

theorem tlcRevokeRoleErr3_size (v w x : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    (tlcRevokeRoleErr3 v w x σ I).size = 196 := by
  unfold tlcRevokeRoleErr3
  exact toByteArray_write32_size_of_le (tlcRevokeRoleErr2 v w σ I) x 164 164 196
    (tlcRevokeRoleErr2_size v w σ I) (by rw [tlcRevokeRoleErr2_size]) (by decide)

theorem tlcRevokeRoleErr3_read64 (v w x : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    (tlcRevokeRoleErr3 v w x σ I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold tlcRevokeRoleErr3
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size]) (by rw [tlcRevokeRoleErr2_size])
    (by omega)]
  unfold tlcRevokeRoleErr2
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size]) (by rw [tlcRevokeRoleErr1_size]; omega)
    (by omega)]
  unfold tlcRevokeRoleErr1
  rw [toByteArray_write_read_below_of_gap _ _ 128 64 (by rw [tlcRevokeRoleOnlyMem_size])
    (by omega) (by rw [tlcRevokeRoleOnlyMem_size]; exact lt_usize _ (by norm_num))]
  exact tlcRevokeRoleOnlyMem_read64 σ I

/-- `msg.sender` lacks `adminRole` (`land 0xff` of the admin-hasRole word is `0`): the onlyRole `JUMPI`
    is not taken, the `AccessControlUnauthorizedAccount(sender, adminRole)` error is built, and `@2157`
    `REVERT`s. -/
theorem tlcRevokeRoleRevAdmin {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I), solcSourceWord I,
        tlcRevokeRoleAdminWord σ I, ⟨3471⟩, tlcRevokeRoleAdminWord σ I, ⟨3066⟩,
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

/-! ## EVM: authorized path — `_revokeRole @4096` conditional clear of `_roles[role].hasRole[account]` -/

/-- Memory after the `_revokeRole @2762` write-slot load (`@4107`). -/
noncomputable abbrev tlcRevokeRoleWriteMem (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (UInt256.land solcAddrMask (calldataWord I.calldata 36))
    (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
    (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRevokeRoleOnlyMem σ I))

/-- `msg.sender` has `adminRole`: take the onlyRole `JUMPI`, dispatch to `_revokeRole @4096`, and run
    the shared `@2762` load for `_roles[role].hasRole[account]`, reaching the `if present` `ISZERO/JUMPI`
    @4107 with the masked stored word on top. -/
theorem tlcRevokeRoleReach4107 {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I), solcSourceWord I,
        tlcRevokeRoleAdminWord σ I, ⟨3471⟩, tlcRevokeRoleAdminWord σ I, ⟨3066⟩,
        tlcRevokeRoleAdminWord σ I, calldataWord I.calldata 36, calldataWord I.calldata 4,
        ⟨476⟩, tlcSelWord I]
      (tlcRevokeRoleOnlyMem σ I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4107⟩
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
    |>.push2 ⟨4096⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.push2 ⟨4107⟩ (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.dup4 (by native_decide) (by evm_ov)
    |>.push2 ⟨2762⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact tlcRevokeRoleSlotLoadGen h2762 (tlcRevokeRoleOnlyMem_size σ I) (by jump_dest) (by evm_ov)

/-- Role absent (`_roles[role].hasRole[account]` already `false`): `_revokeRole` skips at `@4089`,
    does no `SSTORE`/`LOG`, and `STOP`s with the account map unchanged. -/
theorem tlcRevokeRoleXAbsent {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I), solcSourceWord I,
        tlcRevokeRoleAdminWord σ I, ⟨3471⟩, tlcRevokeRoleAdminWord σ I, ⟨3066⟩,
        tlcRevokeRoleAdminWord σ I, calldataWord I.calldata 36, calldataWord I.calldata 4,
        ⟨476⟩, tlcSelWord I]
      (tlcRevokeRoleOnlyMem σ I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩)
    (habsent : UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      ByteArray.empty := by
  obtain ⟨_, _, h4107⟩ := tlcRevokeRoleReach4107 h hauth
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
    pop, pop, pop, pop,
    jump (by jump_dest),
    jumpdest ]
  exact h476.stop (by native_decide) (by evm_ov)

/-- Role present (`_roles[role].hasRole[account]` currently `true`): `_revokeRole` recomputes the
    nested slot, `SSTORE`s `word & ~0xff` (clearing the bool to `false`), emits `RoleRevoked` `LOG4`,
    and `STOP`s — halting with the account map carrying the single nested-slot write. -/
theorem tlcRevokeRoleXPresent {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3665⟩
      [UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I), solcSourceWord I,
        tlcRevokeRoleAdminWord σ I, ⟨3471⟩, tlcRevokeRoleAdminWord σ I, ⟨3066⟩,
        tlcRevokeRoleAdminWord σ I, calldataWord I.calldata 36, calldataWord I.calldata 4,
        ⟨476⟩, tlcSelWord I]
      (tlcRevokeRoleOnlyMem σ I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩)
    (hpresent : ¬ UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (tlcHasRoleSlot I)
        (UInt256.land (UInt256.lnot ⟨255⟩) (tlcHasRoleWord σ I))) ByteArray.empty := by
  obtain ⟨_, _, h4107⟩ := tlcRevokeRoleReach4107 h hauth
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
  have hkec := evm_run h4107 with [
    jumpdest,
    iszero, push2 ⟨4089⟩,
    jumpiNT (by exact isZero_eq_zero_of_ne hpresent),
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
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup7, and, dup1, dup6,
    raw mstore 0 (wordAt0Mem
        (UInt256.land (calldataWord I.calldata 36)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
        (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRevokeRoleWriteMem σ I)))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    swap3,
    raw mstore 0 (twoWordHashMem
        (UInt256.land (calldataWord I.calldata 36)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩))
        (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
        (twoWordHashMem (calldataWord I.calldata 4) ⟨0⟩ (tlcRevokeRoleWriteMem σ I)))
      (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    dup1, dup4,
    raw keccak256 0 (tlcHasRoleSlot I) (UInt256.ofNat 3) (by native_decide) mem_cost
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
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
  exact h476.stop (by native_decide) (by evm_ov)

/-! ## EVM decode-revert paths (shared two-arg decoder) -/

/-- Mis-sized calldata: the signed length check fails, falling into the decoder's `PUSH0 PUSH0 REVERT`
    stub @5013. -/
theorem tlcRevokeRoleDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 23))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h5012⟩ := tlcRevokeRoleReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz hsize hsel
  exact h5012.jumpiNT (by native_decide) (by rw [hslt]; decide) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-- Non-canonical account: the sub-decoder's canonicality `EQ` fails, falling into the `PUSH0 PUSH0
    REVERT` stub @4375. -/
theorem tlcRevokeRoleNoncanonRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 23))
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  obtain ⟨_, _, h4374⟩ := tlcRevokeRoleReachEqCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz68 hbig hsize hsel
  exact h4374.jumpiNT (by native_decide) (by rw [hmask]; exact tlcHasRoleNoncanon_eq hnc) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## Solm body

The body is `nonpayable ++ [letDecl "adminRole" …, require (hasRole adminRole sender)] ++
revokeRoleIfPresent role account`.  After the `letDecl` the local store gains `adminRole`. -/

/-- The local store after the `letDecl "adminRole" := _roles[role].adminRole` binding. -/
abbrev tlcRevokeRoleStore' (σ : AccountMap) (I : ExecutionEnv) : Store :=
  (tlcHasRoleStore I).insert "adminRole"
    (.fixedBytes bytes32Width (EVM.Word.toBytesBE (tlcRevokeRoleAdminWord σ I)))

theorem tlcRevokeRoleStore'_get_roles (σ : AccountMap) (I : ExecutionEnv) :
    (tlcRevokeRoleStore' σ I).get? "_roles" = none := by
  unfold tlcRevokeRoleStore' tlcHasRoleStore
  rw [store_get_ne3 _ _ _ _ (by native_decide) (by native_decide) (by native_decide)]
  simp

theorem tlcRevokeRoleStore'_index_role (σ : AccountMap) (I : ExecutionEnv) :
    (tlcRevokeRoleStore' σ I)["role"] =
      Value.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32) := by
  unfold tlcRevokeRoleStore' tlcHasRoleStore
  rw [Std.HashMap.getElem_insert]; simp [tlcHasRoleStore_index_role]

theorem tlcRevokeRoleStore'_index_account (σ : AccountMap) (I : ExecutionEnv) :
    (tlcRevokeRoleStore' σ I)["account"] =
      Value.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat) := by
  unfold tlcRevokeRoleStore' tlcHasRoleStore
  rw [Std.HashMap.getElem_insert]; simp

theorem tlcRevokeRoleStore'_index_adminRole (σ : AccountMap) (I : ExecutionEnv) :
    (tlcRevokeRoleStore' σ I)["adminRole"] =
      Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (tlcRevokeRoleAdminWord σ I)) := by
  unfold tlcRevokeRoleStore' tlcHasRoleStore
  rw [Std.HashMap.getElem_insert]; simp

/-- The Solm onlyRole nested slot `_roles[adminRole].hasRole[msg.sender]` equals the runtime slot. -/
theorem tlcRevokeRoleOnlyRoleSlot_eq (σ : AccountMap) (I : ExecutionEnv) :
    roleHasRoleSlot (.fixedBytes bytes32Width (EVM.Word.toBytesBE (tlcRevokeRoleAdminWord σ I)))
        (.address I.source)
      = tlcRevokeRoleAdminSlot σ I := by
  unfold tlcRevokeRoleAdminSlot roleHasRoleSlot roleDataSlot mapSlot solcMappingSlot
  rw [show bytes32Width = (⟨31, by decide⟩ : Fin 32) from rfl,
    keyValueToWord_fixedBytes32 (tlcRevokeRoleAdminWord σ I), keyValueToWord_address,
    solcAddrMask_clean_left (solcSourceWord_canonical I)]

/-- The `letDecl "adminRole"` reads `_roles[role].adminRole` as a `bytes32`. -/
theorem tlcRevokeRoleLetDeclEval {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := tlcHasRoleStore I }
      (initState cA gh bl σ σ₀ g A I) (.storage (roleAdminRef (.var "role")))
      = .ok (.fixedBytes bytes32Width (EVM.Word.toBytesBE (tlcRevokeRoleAdminWord σ I))) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hvk : valueToKey? (Value.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32))
      = some (tlcHasRoleRoleKey I) := by
    simp [valueToKey?, tlcHasRoleRoleKey, abiBytes32Width, hlen]
  rw [evalExpr_storage_scalar (cfg := config)
    (solm := { contract := contract, locals := tlcHasRoleStore I })
    (slot := roleAdminRef (.var "role"))
    (er := ({ base := "_roles", steps := [.mindex (tlcHasRoleRoleKey I), .field "adminRole"] } :
      EvaledStorageRef))
    (t := .bytes bytes32Width) (loc := bytes32Loc (roleAdminSlot (tlcHasRoleRoleKey I)))
    (hbase := by simp only [roleAdminRef]; exact tlcHasRoleStore_get_roles I)
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleAdminRef,
        tlcHasRoleStore_index_role, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hvk])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt,
        tlcHasRoleRoleKey, bytes32St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok
    (storageLocLoad_bytes32 (initState cA gh bl σ σ₀ g A I) (roleAdminSlot (tlcHasRoleRoleKey I)))

/-- The onlyRole guard `hasRole(adminRole, msg.sender)` reads `_roles[adminRole].hasRole[sender]`. -/
theorem tlcRevokeRoleOnlyRoleEval {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? config { contract := contract, locals := tlcRevokeRoleStore' σ I }
      (initState cA gh bl σ σ₀ g A I) (hasRoleExpr (.var "adminRole") sender)
      = .ok (Solm.wordToElem .bool
          (UInt256.land (tlcRevokeRoleAdminHasRoleWord σ I) ⟨255⟩)) := by
  have hstore : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (tlcRevokeRoleAdminSlot σ I)
        = tlcRevokeRoleAdminHasRoleWord σ I :=
    codeOwnerStorageWord_initState (tlcRevokeRoleAdminSlot σ I)
  refine evalExpr_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tlcRevokeRoleStore' σ I })
    (slot := roleHasRoleRef (.var "adminRole") sender)
    (er := ({ base := "_roles", steps := [.mindex
        (.fixedBytes bytes32Width (EVM.Word.toBytesBE (tlcRevokeRoleAdminWord σ I))),
        .field "hasRole", .mindex (.address I.source)] } : EvaledStorageRef))
    (t := .bool)
    (loc := boolLoc (roleHasRoleSlot
        (.fixedBytes bytes32Width (EVM.Word.toBytesBE (tlcRevokeRoleAdminWord σ I)))
        (.address I.source)))
    (value := Solm.wordToElem .bool (UInt256.land (tlcRevokeRoleAdminHasRoleWord σ I) ⟨255⟩))
    ?_ ?_ ?_ ?_ ?_
  · simp only [roleHasRoleRef]; exact tlcRevokeRoleStore'_get_roles σ I
  · have hadminlen : (EVM.Word.toBytesBE (tlcRevokeRoleAdminWord σ I)).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size (tlcRevokeRoleAdminWord σ I)
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleHasRoleRef, sender,
      valueToKey?, envValue, initState,
      bytes32Width, hadminlen, EvalResult.bind, EvalResult.ofOption,
      bind, pure, evalExpr?]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt, boolSt]
  · rfl
  · rw [tlcRevokeRoleOnlyRoleSlot_eq σ I]
    show storageLocLoad (initState cA gh bl σ σ₀ g A I) (boolOffset0Loc (tlcRevokeRoleAdminSlot σ I))
      = _
    rw [storageLocLoad_bool_offset0, hstore]

/-- `wordToElem .bool (word & 0xff)` is `true` exactly when the packed byte is nonzero. -/
theorem tlcRevokeRoleWordToElem_present {σ : AccountMap} {I : ExecutionEnv}
    (hpres : ¬ UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    Solm.wordToElem .bool (UInt256.land (tlcHasRoleWord σ I) ⟨255⟩) = .bool true := by
  have hz : UInt256.land (tlcHasRoleWord σ I) ⟨255⟩ ≠ ⟨0⟩ := by
    rw [u256_land_comm]; exact hpres
  by_cases hval : (UInt256.land (tlcHasRoleWord σ I) ⟨255⟩).val = 0
  · exact absurd (u256_inj (congrArg Fin.val hval)) hz
  · simp [Solm.wordToElem, hval]

/-- `wordToElem .bool (word & 0xff)` is `false` exactly when the packed byte is zero. -/
theorem tlcRevokeRoleWordToElem_absent {σ : AccountMap} {I : ExecutionEnv}
    (habs : UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    Solm.wordToElem .bool (UInt256.land (tlcHasRoleWord σ I) ⟨255⟩) = .bool false := by
  have hz : UInt256.land (tlcHasRoleWord σ I) ⟨255⟩ = ⟨0⟩ := by
    rw [u256_land_comm]; exact habs
  simp [Solm.wordToElem, hz]

/-- The `_roles[role].hasRole[account]` storage read (the `.ite` condition), in the extended store. -/
theorem tlcRevokeRoleHasRoleEval {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size) :
    evalExpr? config { contract := contract, locals := tlcRevokeRoleStore' σ I }
      (initState cA gh bl σ σ₀ g A I)
      (hasRoleExpr (.var "role") (.var "account"))
      = .ok (Solm.wordToElem .bool (UInt256.land (tlcHasRoleWord σ I) ⟨255⟩)) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hslot : roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I) = tlcHasRoleSlot I :=
    tlcHasRoleSlot_eq I hsz36
  have hstore : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (tlcHasRoleSlot I) = tlcHasRoleWord σ I :=
    codeOwnerStorageWord_initState (tlcHasRoleSlot I)
  refine evalExpr_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tlcRevokeRoleStore' σ I })
    (slot := roleHasRoleRef (.var "role") (.var "account"))
    (er := ({ base := "_roles", steps := [.mindex (tlcHasRoleRoleKey I), .field "hasRole",
        .mindex (tlcHasRoleAccountKey I)] } : EvaledStorageRef))
    (t := .bool)
    (loc := boolLoc (roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I)))
    (value := Solm.wordToElem .bool (UInt256.land (tlcHasRoleWord σ I) ⟨255⟩)) ?_ ?_ ?_ ?_ ?_
  · simp only [roleHasRoleRef]; exact tlcRevokeRoleStore'_get_roles σ I
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleHasRoleRef,
      tlcRevokeRoleStore'_index_role, tlcRevokeRoleStore'_index_account, tlcHasRoleAccountKey,
      valueToKey?, hlen, abiBytes32Width, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt, boolSt]
  · rfl
  · rw [hslot]
    show storageLocLoad (initState cA gh bl σ σ₀ g A I) (boolOffset0Loc (tlcHasRoleSlot I)) = _
    rw [storageLocLoad_bool_offset0, hstore]

/-- The `_roles[role].hasRole[account] = false` write collapses to a single bool `storageStore`. -/
theorem tlcRevokeRoleAssign {cA gh bl σ σ₀ A I} {g : Sat256} (hsz36 : 36 ≤ I.calldata.size) :
    assignStorageRef? config { contract := contract, locals := tlcRevokeRoleStore' σ I }
      (initState cA gh bl σ σ₀ g A I) .storage
      (roleHasRoleRef (.var "role") (.var "account")) (.bool false)
      = .ok ({ contract := contract, locals := tlcRevokeRoleStore' σ I },
        tlcRenounceRolePost (initState cA gh bl σ σ₀ g A I) I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hslot : roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I) = tlcRenounceRoleSlot I :=
    tlcHasRoleSlot_eq I hsz36
  refine assignStorageRef_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tlcRevokeRoleStore' σ I })
    (slot := roleHasRoleRef (.var "role") (.var "account"))
    (er := ({ base := "_roles", steps := [.mindex (tlcHasRoleRoleKey I), .field "hasRole",
        .mindex (tlcHasRoleAccountKey I)] } : EvaledStorageRef))
    (ty := boolSt)
    (loc := boolLoc (roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I)))
    (value := .bool false) ?_ ?_ ?_ ?_ (by trivial) ?_
  · simp only [roleHasRoleRef]; exact tlcRevokeRoleStore'_get_roles σ I
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleHasRoleRef,
      tlcRevokeRoleStore'_index_role, tlcRevokeRoleStore'_index_account, tlcHasRoleAccountKey,
      valueToKey?, hlen, abiBytes32Width, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt, boolSt]
  · rfl
  · rw [hslot]
    show storageLocStore (initState cA gh bl σ σ₀ g A I) (boolOffset0Loc (tlcRenounceRoleSlot I))
        (.bool false) = some (tlcRenounceRolePost (initState cA gh bl σ σ₀ g A I) I)
    rw [storageLocStore_bool_false_offset0]

/-- The onlyRole admin bit is nonzero → the guard evaluates `true`. -/
theorem tlcRevokeRoleAdminWordToElem_present {σ : AccountMap} {I : ExecutionEnv}
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩) :
    Solm.wordToElem .bool (UInt256.land (tlcRevokeRoleAdminHasRoleWord σ I) ⟨255⟩) = .bool true := by
  have hz : UInt256.land (tlcRevokeRoleAdminHasRoleWord σ I) ⟨255⟩ ≠ ⟨0⟩ := by
    rw [u256_land_comm]; exact hauth
  by_cases hval : (UInt256.land (tlcRevokeRoleAdminHasRoleWord σ I) ⟨255⟩).val = 0
  · exact absurd (u256_inj (congrArg Fin.val hval)) hz
  · simp [Solm.wordToElem, hval]

/-- The onlyRole admin bit is zero → the guard evaluates `false`. -/
theorem tlcRevokeRoleAdminWordToElem_absent {σ : AccountMap} {I : ExecutionEnv}
    (hunauth : UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩) :
    Solm.wordToElem .bool (UInt256.land (tlcRevokeRoleAdminHasRoleWord σ I) ⟨255⟩) = .bool false := by
  have hz : UInt256.land (tlcRevokeRoleAdminHasRoleWord σ I) ⟨255⟩ = ⟨0⟩ := by
    rw [u256_land_comm]; exact hunauth
  simp [Solm.wordToElem, hz]

/-- Authorized + role present: the body clears the bit (`.ite` then-branch writes `false`). -/
theorem tlcRevokeRoleBodyPresent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩)
    (hpres : ¬ UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcHasRoleStore I)
      revokeRoleTransition.body
      (.returned { contract := contract, locals := tlcRevokeRoleStore' σ I }
        (tlcRenounceRolePost (initState cA gh bl σ σ₀ g A I) I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (tlcRevokeRoleLetDeclEval hsz36)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (by rw [tlcRevokeRoleOnlyRoleEval, tlcRevokeRoleAdminWordToElem_present hauth])) ?_
  refine ExecBlock.consNormal (ExecStmt.iteTrue ?_ ?_) ExecBlock.nil
  · rw [tlcRevokeRoleHasRoleEval hsz36, tlcRevokeRoleWordToElem_present hpres]
  · exact ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) (tlcRevokeRoleAssign hsz36))
      ExecBlock.nil

/-- Authorized + role absent: the body takes the empty `.ite` else-branch, state unchanged. -/
theorem tlcRevokeRoleBodyAbsent {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hauth : ¬ UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩)
    (habs : UInt256.land ⟨255⟩ (tlcHasRoleWord σ I) = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcHasRoleStore I)
      revokeRoleTransition.body
      (.returned { contract := contract, locals := tlcRevokeRoleStore' σ I }
        (initState cA gh bl σ σ₀ g A I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (tlcRevokeRoleLetDeclEval hsz36)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (by rw [tlcRevokeRoleOnlyRoleEval, tlcRevokeRoleAdminWordToElem_present hauth])) ?_
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ExecBlock.nil
  rw [tlcRevokeRoleHasRoleEval hsz36, tlcRevokeRoleWordToElem_absent habs]

/-- Unauthorized: the body reverts at `require(hasRole(adminRole, msg.sender))`. -/
theorem tlcRevokeRoleBodyRevertAdmin {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size)
    (hunauth : UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ I) = ⟨0⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcHasRoleStore I)
      revokeRoleTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true
    (by simp only [initState]; exact hwv))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (tlcRevokeRoleLetDeclEval hsz36)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (by rw [tlcRevokeRoleOnlyRoleEval, tlcRevokeRoleAdminWordToElem_absent hunauth]))

/-! ## Refinement -/

/-- Refinement of `RevokeRole` (selector index 23). -/
theorem tlcRevokeRoleBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 23))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 23) (by native_decide) hsel
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
  have henc : returnEquiv ByteArray.empty none revokeRoleTransition.returnType := by
    simpa [revokeRoleTransition] using
      (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
        (dvs := []) rfl (by native_decide) (by native_decide))
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz68 : 68 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · -- decode succeeds; reach the onlyRole check
          obtain ⟨_, _, h3040⟩ := tlcRevokeRoleReach3040 (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
            hcode hwv hsz68 hbig hsize hsel hcanon
          obtain ⟨_, _, h3665⟩ := tlcRevokeRoleReachAdminBit h3040 (by omega)
          by_cases hauth : UInt256.land ⟨255⟩ (tlcRevokeRoleAdminHasRoleWord σ_evm I) = ⟨0⟩
          · -- unauthorized: both revert at the onlyRole check
            exact tlcReEquivExecRev hcode (tlcRevokeRoleRevAdmin h3665 hauth)
              (tlcSelectorDispatchRevokeRole hsel) (tlcDecodeRevokeRole_ok hsz68 hbig hcanon)
              (tlcRevokeRoleBodyRevertAdmin (σ := σ_solm) hwv (by omega)
                (by rw [← hadminhasrole]; exact hauth))
          · -- authorized: conditional clear
            by_cases hpres : UInt256.land ⟨255⟩ (tlcHasRoleWord σ_evm I) = ⟨0⟩
            · -- role absent: no write on either side
              exact tlcReEquivExecGen hcode
                (tlcRevokeRoleXAbsent h3665 hauth hpres)
                (tlcSelectorDispatchRevokeRole hsel) (tlcDecodeRevokeRole_ok hsz68 hbig hcanon)
                (tlcRevokeRoleBodyAbsent (σ := σ_solm) hwv (by omega)
                  (by rw [← hadminhasrole]; exact hauth) (by rw [← hword]; exact hpres))
                (by simp [initState])
                (by simpa [initState] using hAccounts) henc
            · -- role present: both SSTORE `false`
              refine tlcReEquivExecGen hcode
                (tlcRevokeRoleXPresent h3665 _hperm hauth hpres)
                (tlcSelectorDispatchRevokeRole hsel) (tlcDecodeRevokeRole_ok hsz68 hbig hcanon)
                (tlcRevokeRoleBodyPresent (σ := σ_solm) hwv (by omega)
                  (by rw [← hadminhasrole]; exact hauth) (by rw [← hword]; exact hpres))
                (by simp [tlcRenounceRolePost, initState, storageStore_createdAccounts]) ?_ henc
              have hval : UInt256.land (UInt256.lnot ⟨255⟩) (tlcHasRoleWord σ_evm I)
                  = UInt256.land (tlcHasRoleWord σ_solm I) (UInt256.lnot ⟨255⟩) := by
                rw [u256_land_comm, hword]
              rw [hval]
              simpa [tlcRenounceRolePost, initState, storageStore_accountMap,
                codeOwnerStorageWord_initState] using
                accountMapEquiv_sstoreAccountMap I.codeOwner (tlcHasRoleSlot I)
                  (UInt256.land (tlcHasRoleWord σ_solm I) (UInt256.lnot ⟨255⟩)) hAccounts
        · -- non-canonical account: EVM reverts at the address check, Solm decode fails
          exact tlcReEquivDecodeFailed hcode
            (tlcRevokeRoleNoncanonRevert (g := Sat256.ofUInt256 g) hcode hwv hsz68 hbig hsize hsel
              hcanon)
            (tlcSelectorDispatchRevokeRole hsel) (tlcDecodeRevokeRole_none_noncanon hsz68 hbig hcanon)
      · -- huge calldata: EVM reverts at the length check, Solm decode fails
        have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := Nat.not_lt.mp hbig
        exact tlcReEquivDecodeFailed hcode
          (tlcRevokeRoleDecodeRevert (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
            (solcDecodeLenCheckHuge_4_64 hhuge hsize))
          (tlcSelectorDispatchRevokeRole hsel) (tlcDecodeRevokeRole_none_huge hhuge)
    · -- short calldata: EVM reverts at the length check, Solm decode fails
      have hshort : I.calldata.size < 68 := by omega
      exact tlcReEquivDecodeFailed hcode
        (tlcRevokeRoleDecodeRevert (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
          (solcDecodeLenCheckShort_4_64 hsz hshort hsize))
        (tlcSelectorDispatchRevokeRole hsel) (tlcDecodeRevokeRole_none_short hsz hshort)
  · -- nonpayable guard: callvalue ≠ 0
    obtain ⟨_, _, h1350⟩ := tlcReachRevokeRole (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨1361⟩) h1350 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchRevokeRole hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
