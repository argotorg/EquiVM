import Benchmarks.OpenZeppelinBench.TimelockController.Storage
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `hasRole(bytes32,address)` refinement

`hasRole` is a public non-payable `bool` getter over the NESTED mapping `_roles[role].hasRole[account]`
(base slot 0): the slot is `keccak(account ‖ keccak(role ‖ 0))`.  Selector index 11, dispatch group
G147 arm 0, body pc 1101.  The runtime peels its non-payable guard, jumps to the out-of-line two-arg
decoder (`@4999`, a signed `SLT(size-4, 64)` length check + an address-canonicality `EQ` check in the
sub-decoder `@4356`), computes the nested slot with two `MSTORE+KECCAK256` rounds (`@2762`), `SLOAD`s
it, masks the low byte, and returns the `iszero(iszero(word & 0xff))`-normalized bool (`@509`).
Template for nested-mapping `bool` getters (grantRole/revokeRole read the same slot).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Decoded arguments, storage slot, and stored word -/

/-- The ABI-decoded `bytes32` role key (the 32-byte calldata word at offset 4), as a mapping key. -/
abbrev tlcHasRoleRoleKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32)

/-- The ABI-decoded `address` account key (the canonical word at offset 36), as a mapping key. -/
abbrev tlcHasRoleAccountKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)

/-- The decoded local store bound by `hasRole(bytes32 role, address account)`. -/
abbrev tlcHasRoleStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "role" (.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32))).insert
    "account" (.address (AccountAddress.ofNat (calldataWord I.calldata 36).toNat))

/-- The nested-mapping slot `keccak(account ‖ keccak(role ‖ 0))` as the solc runtime computes it. -/
def tlcHasRoleSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
    (UInt256.land solcAddrMask (calldataWord I.calldata 36))

/-- The stored `_roles[role].hasRole[account]` word. -/
abbrev tlcHasRoleWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (tlcHasRoleSlot I)

/-- The decoded `bytes32` role key hashes to the same word `CALLDATALOAD(4)` loads. -/
theorem tlcHasRoleRoleKey_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (tlcHasRoleRoleKey I) = calldataWord I.calldata 4 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have key_eq : tlcHasRoleRoleKey I
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32))) := by
    simp only [tlcHasRoleRoleKey]
    rw [show abiBytes32Width = (⟨31, by decide⟩ : Fin 32) from rfl,
      toBytesBE_bytesToWord_of_length hlen]
  rw [key_eq, keyValueToWord_fixedBytes32, decode_word_at_eq_any I.calldata 4 (by omega)]

/-- The spec `roleHasRoleSlot` equals the runtime nested keccak slot. -/
theorem tlcHasRoleSlot_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I) = tlcHasRoleSlot I := by
  unfold tlcHasRoleSlot roleHasRoleSlot roleDataSlot mapSlot solcMappingSlot
  rw [tlcHasRoleRoleKey_eq I hsz36,
    keyValueToWord_address_ofNat_mask (calldataWord I.calldata 36)]

/-- A non-canonical address word (solc's `EQ` returns `0`, forcing a revert). -/
theorem tlcHasRoleNoncanon_eq {w : UInt256} (hnc : ¬ w.toNat < EVM.addressModulus) :
    UInt256.eq w (UInt256.land w solcAddrMask) = ⟨0⟩ := by
  have hne : ¬ (w = UInt256.land w solcAddrMask) := fun h =>
    hnc (h ▸ solcAddrMask_result_canonical w)
  show UInt256.fromBool (decide (w = UInt256.land w solcAddrMask)) = ⟨0⟩
  rw [decide_eq_false hne]; rfl

/-- Low-byte mask commutes: solc emits `AND(0xff, word)`, the spec uses `word & 0xff`. -/
theorem tlcHasRoleLand255_comm (w : UInt256) :
    UInt256.land ⟨255⟩ w = UInt256.land w ⟨255⟩ := by
  apply u256_inj
  rw [uland_toNat, uland_toNat]
  exact nat_land_comm _ _

/-! ## ABI decode -/

theorem tlcDecodeHasRole_ok {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (hasRoleTransition.params.map Param.name)
      (transitionSignature hasRoleTransition).paramTypes I.calldata = some (tlcHasRoleStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = _
  exact decodeCalldata_bytes32_address_ok hsz68 hbig hcanon

theorem tlcDecodeHasRole_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (hasRoleTransition.params.map Param.name)
      (transitionSignature hasRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = none
  exact decodeCalldata_bytes32_address_none_short hsz4 hshort

theorem tlcDecodeHasRole_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (hasRoleTransition.params.map Param.name)
      (transitionSignature hasRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = none
  exact decodeCalldata_bytes32_address_none_huge hbig

theorem tlcDecodeHasRole_none_noncanon {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (hasRoleTransition.params.map Param.name)
      (transitionSignature hasRoleTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role", "account"] [bytes32, addr] I.calldata = none
  exact decodeCalldata_bytes32_address_none_noncanon hsz68 hbig hnc

/-! ## EVM: reach the body and the out-of-line decoder length check -/

/-- Reach the `hasRole` body pc 1101 (G147 arm 0). -/
theorem tlcReachHasRole {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 11)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1101⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x91d14854⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x91 0xd1 0x48 0x54 ⟨0x91d14854⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG147Body 0 (by omega) ⟨1101⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; exact absurd hj (Nat.not_lt_zero j))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard and run the two-arg decoder prologue to the `SLT` length-check `JUMPI`
    @5012.  Stack: `[⟨5016⟩, ISZERO(SLT(size-4, 64)), ⟨0⟩, ⟨0⟩, ⟨4⟩, size, ⟨1127⟩, ⟨509⟩, sel]`. -/
theorem tlcHasRoleReachLenCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 11)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5012⟩
      [⟨5016⟩, UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩),
        ⟨0⟩, ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1127⟩, ⟨509⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h1101⟩ := tlcReachHasRole (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h1114⟩ := tlcGuardPeelOk (gt := ⟨1112⟩) h1101 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, h1114.push2 ⟨509⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1127⟩ (by native_decide) (by evm_ov)
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

/-! ## Bool-return encoder @509 (memory-generic; normalizes `word & 0xff`)

    Store `iszero(iszero val)` at the free pointer, fall through the return dispatcher @521,
    `RETURN(0x80, 0x20)`.  A nested-mapping getter dirties the `[0,0x40)` scratch, so this runs over
    any free-pointer-preserving 96-byte memory (unlike `SupportsInterface.tlcSuppIfaceReturnBool`,
    which is fixed to `solcFreePtrMem`). -/
theorem tlcHasRoleReturnBool {cA gh bl σ σ₀ A I} {g : Sat256} {val : UInt256} {R : List UInt256}
    {mem : ByteArray} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨509⟩
      (val :: R) mem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 5 ≤ 1024) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) := by
  set nv := UInt256.isZero (UInt256.isZero val) with hnv
  have h521 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
        (mloadFreePtrValue (by rw [hsize]; decide) (by decide) hread64) (by decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.mstore 6 (tlcRetMem mem nv) (UInt256.ofNat 5) (by native_decide) mem_cost
        (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl) (by decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  have hret := h521.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost
        (tlcRetMem_mload64 hsize hread64 nv) (by decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.sub (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
  exact hret.ret 0 (UInt256.toByteArray nv) (by native_decide) mem_cost
    (by rw [show ((⟨32⟩ + ⟨128⟩ : UInt256).sub ⟨128⟩).toNat = 32 from by decide,
        show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact tlcRetMem_read128 hsize nv)
    (by evm_ov)

/-! ## Nested-mapping slot computation + `SLOAD` @2762

    Entry stack `[account, role, cont, …R]` over `solcFreePtrMem`.  Writes `role‖0`, hashes the inner
    slot `keccak(role‖0)`, masks `account`, writes `account‖inner`, hashes the outer slot, `SLOAD`s
    it, masks the low byte, and `JUMP`s to `cont` leaving `[account&0xff-loaded-word, …R]`. -/
theorem tlcHasRoleSlotLoad {cA gh bl σ σ₀ A I} {g : Sat256}
    {account role cont : UInt256} {R : List UInt256} {rdata : ByteArray} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2762⟩
      (account :: role :: cont :: R) solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hret : (D_J timelockControllerBenchBytecode 0).contains cont = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) cont
      (UInt256.land ⟨255⟩
        (solcSlotWord σ I
          (solcMappingSlot (solcMappingSlot ⟨0⟩ role) (UInt256.land solcAddrMask account))) :: R)
      (twoWordHashMem (UInt256.land solcAddrMask account) (solcMappingSlot ⟨0⟩ role)
        (twoWordHashMem role ⟨0⟩ solcFreePtrMem)) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have hkec := h.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.mstore 0 (wordAt0Mem role solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rfl) (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup3 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.mstore 0 (twoWordHashMem role ⟨0⟩ solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rfl) (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.dup1 (by native_decide) (by evm_ov)
    |>.dup5 (by native_decide) (by evm_ov)
    |>.keccak256 0 (solcMappingSlot ⟨0⟩ role) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
            exact twoWordHashMem_solcMappingSlot ⟨0⟩ role solcFreePtrMem_size)
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
          (twoWordHashMem role ⟨0⟩ solcFreePtrMem)) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rfl) (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.mstore 0
        (twoWordHashMem (UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) account)
          (solcMappingSlot ⟨0⟩ role) (twoWordHashMem role ⟨0⟩ solcFreePtrMem)) (UInt256.ofNat 3)
        (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.keccak256 0
        (solcMappingSlot (solcMappingSlot ⟨0⟩ role)
          (UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) account))
        (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
            exact twoWordHashMem_solcMappingSlot (solcMappingSlot ⟨0⟩ role)
              (UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) account)
              (twoWordHashMem_size_96 role ⟨0⟩ solcFreePtrMem_size))
        (by native_decide) (by evm_ov)
  obtain ⟨_, _, hsl⟩ := hkec.sload (by native_decide) (by evm_ov)
  have hfin := hsl.push1 ⟨255⟩ (by native_decide) (by evm_ov)
    |>.and (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.jump (by native_decide) hret (by evm_ov)
  exact ⟨_, _, by simpa only [hmask] using hfin⟩

/-! ## EVM: the full execute trace, reaching the address-canonicality check -/

/-- After the length check passes (`68 ≤ size < 2^255+4`), run the two-arg decoder to the address
    sub-decoder's canonicality `EQ`/`JUMPI` @4374.  Stack top is the check condition. -/
theorem tlcHasRoleReachEqCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 11)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4374⟩
      [⟨4378⟩,
        UInt256.eq (calldataWord I.calldata 36)
          (UInt256.land (calldataWord I.calldata 36)
            (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)),
        calldataWord I.calldata 36, ⟨36⟩, ⟨5032⟩, ⟨0⟩, calldataWord I.calldata 4, ⟨4⟩,
        UInt256.ofNat I.calldata.size, ⟨1127⟩, ⟨509⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hbig hsize
  obtain ⟨_, _, h5012⟩ := tlcHasRoleReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
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

/-- EVM: with zero callvalue, a well-sized calldata, and a canonical account, `hasRole` returns the
    normalized `_roles[role].hasRole[account]` bool. -/
theorem tlcHasRoleX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 11))
    (hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (UInt256.isZero (UInt256.isZero (UInt256.land (tlcHasRoleWord σ I) ⟨255⟩)))) := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  obtain ⟨_, _, h4374⟩ := tlcHasRoleReachEqCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz68 hbig hsize hsel
  have h2762 := h4374.jumpiT (by native_decide)
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
    |>.push2 ⟨2762⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, h509⟩ := tlcHasRoleSlotLoad h2762 (by jump_dest) (by evm_ov)
  rw [tlcHasRoleLand255_comm] at h509
  exact tlcHasRoleReturnBool h509
    (twoWordHashMem_size_96 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (twoWordHashMem_read64 _ _ (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
      (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
    (by evm_ov)

/-- EVM revert path for a mis-sized calldata: the signed length check `SLT(size-4, 64) = 1`
    fails the `JUMPI`, falling into the `PUSH0 PUSH0 REVERT` stub @5013. -/
theorem tlcHasRoleDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 11))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h5012⟩ := tlcHasRoleReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz hsize hsel
  exact h5012.jumpiNT (by native_decide) (by rw [hslt]; decide) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-- EVM revert path for a non-canonical address: the sub-decoder's `EQ` check fails the `JUMPI`,
    falling into the `PUSH0 PUSH0 REVERT` stub @4375. -/
theorem tlcHasRoleNoncanonRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 11))
    (hnc : ¬ (calldataWord I.calldata 36).toNat < EVM.addressModulus) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  obtain ⟨_, _, h4374⟩ := tlcHasRoleReachEqCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (g := g) hcode hwv hsz68 hbig hsize hsel
  exact h4374.jumpiNT (by native_decide) (by rw [hmask]; exact tlcHasRoleNoncanon_eq hnc) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## Solm body -/

theorem tlcHasRoleStore_get_roles (I : ExecutionEnv) :
    (tlcHasRoleStore I).get? "_roles" = none := by
  unfold tlcHasRoleStore
  rw [store_get_ne2 _ _ _ (by native_decide) (by native_decide)]
  simp

theorem tlcHasRoleStore_index_role (I : ExecutionEnv) :
    (tlcHasRoleStore I)["role"] =
      Value.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32) := by
  unfold tlcHasRoleStore
  rw [Std.HashMap.getElem_insert]; simp

/-- The Solm `hasRole(role, account)` body returns `_roles[role].hasRole[account]`. -/
theorem tlcHasRoleBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcHasRoleStore I)
      hasRoleTransition.body
      (.returned { contract := contract, locals := tlcHasRoleStore I } (initState cA gh bl σ σ₀ g A I)
        (some [Solm.wordToElem .bool (UInt256.land (tlcHasRoleWord σ I) ⟨255⟩)])) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hslot : roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I) = tlcHasRoleSlot I :=
    tlcHasRoleSlot_eq I hsz36
  have hstore : Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I)
      (initState cA gh bl σ σ₀ g A I).executionEnv.codeOwner (tlcHasRoleSlot I) = tlcHasRoleWord σ I :=
    codeOwnerStorageWord_initState (tlcHasRoleSlot I)
  refine nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) ?_
  refine evalExpr_storage_scalar_value (cfg := config)
    (solm := { contract := contract, locals := tlcHasRoleStore I })
    (slot := roleHasRoleRef (.var "role") (.var "account"))
    (er := ({ base := "_roles", steps := [.mindex (tlcHasRoleRoleKey I), .field "hasRole",
        .mindex (tlcHasRoleAccountKey I)] } : EvaledStorageRef))
    (t := .bool)
    (loc := boolLoc (roleHasRoleSlot (tlcHasRoleRoleKey I) (tlcHasRoleAccountKey I)))
    (value := Solm.wordToElem .bool (UInt256.land (tlcHasRoleWord σ I) ⟨255⟩)) ?_ ?_ ?_ ?_ ?_
  · simp only [roleHasRoleRef]; exact tlcHasRoleStore_get_roles I
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleHasRoleRef,
      tlcHasRoleStore_index_role, tlcHasRoleAccountKey, valueToKey?,
      hlen, abiBytes32Width, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?]
  · simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt, boolSt]
  · rfl
  · rw [hslot]
    show storageLocLoad (initState cA gh bl σ σ₀ g A I) (boolOffset0Loc (tlcHasRoleSlot I)) = _
    rw [storageLocLoad_bool_offset0, hstore]

/-! ## Refinement -/

/-- Refinement of `HasRole` (selector index 11). -/
theorem tlcHasRoleBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 11))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 11) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz68 : 68 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · -- execute: canonical account
          have hword : tlcHasRoleWord σ_evm I = tlcHasRoleWord σ_solm I := by
            simp only [tlcHasRoleWord]
            exact accountMapEquiv_storage_findD hAccounts I.codeOwner (tlcHasRoleSlot I) ⟨0⟩
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (tlcHasRoleStore I)
                hasRoleTransition.body
                (.returned { contract := contract, locals := tlcHasRoleStore I }
                  (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                  (some [Solm.wordToElem .bool (UInt256.land (tlcHasRoleWord σ_solm I) ⟨255⟩)])) :=
            tlcHasRoleBodyReturns (g := Sat256.ofUInt256 g) hwv (by omega)
          exact tlcReEquivExecTransport hcode
            (tlcHasRoleX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz68 hbig hsize hsel hcanon)
            (tlcSelectorDispatchHasRole hsel) (tlcDecodeHasRole_ok hsz68 hbig hcanon) hbody
            (by rw [← hword]) hAccounts
            (returnEquiv_of_encode (by
              simpa [boolTy] using boolWordReturnEncoding (tlcHasRoleWord σ_evm I)))
        · -- non-canonical account: EVM reverts at the address check, Solm decode fails
          exact tlcReEquivDecodeFailed hcode
            (tlcHasRoleNoncanonRevert (g := Sat256.ofUInt256 g) hcode hwv hsz68 hbig hsize hsel hcanon)
            (tlcSelectorDispatchHasRole hsel) (tlcDecodeHasRole_none_noncanon hsz68 hbig hcanon)
      · -- huge calldata: EVM reverts at the length check, Solm decode fails
        have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := Nat.not_lt.mp hbig
        exact tlcReEquivDecodeFailed hcode
          (tlcHasRoleDecodeRevert (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
            (solcDecodeLenCheckHuge_4_64 hhuge hsize))
          (tlcSelectorDispatchHasRole hsel) (tlcDecodeHasRole_none_huge hhuge)
    · -- short calldata: EVM reverts at the length check, Solm decode fails
      have hshort : I.calldata.size < 68 := by omega
      exact tlcReEquivDecodeFailed hcode
        (tlcHasRoleDecodeRevert (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
          (solcDecodeLenCheckShort_4_64 hsz hshort hsize))
        (tlcSelectorDispatchHasRole hsel) (tlcDecodeHasRole_none_short hsz hshort)
  · -- nonpayable guard: callvalue ≠ 0
    obtain ⟨_, _, h1101⟩ := tlcReachHasRole (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨1112⟩) h1101 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchHasRole hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
