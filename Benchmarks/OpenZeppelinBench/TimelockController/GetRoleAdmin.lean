import Benchmarks.OpenZeppelinBench.TimelockController.Storage
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch

/-!
# OpenZeppelin TimelockController `getRoleAdmin(bytes32)` refinement

`getRoleAdmin` is a public non-payable `bytes32` getter over `_roles[role].adminRole`.  In this
contract's layout `_roles` is a `mapping(bytes32 => RoleData)` at base slot `0`, and `.adminRole` is
field offset `1` of the struct, so the read slot is `keccak(role ‖ 0) + 1`.  Selector index 8,
dispatch group G350 arm 3, body pc 712.  The runtime peels its own non-payable guard, runs the modern
word-argument decoder (`@4702`, a signed `SLT(calldatasize - 4, 32)` availability check), hashes the
mapping slot `keccak(role ‖ 0)`, `ADD`s the field offset `1`, `SLOAD`s it, and returns the 32-byte
word.  Template for arg-taking struct-field `bytes32` mapping getters (cf. `GetTimestamp`, the
base-slot-`1` `uint256` analogue).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Decoded argument, storage word, and ABI decode -/

/-- The ABI-decoded `bytes32` role (the 32-byte calldata word at offset 4), as a mapping key value. -/
abbrev tlcGetRoleAdminKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32)

/-- The decoded local store bound by `getRoleAdmin(bytes32 role)`. -/
abbrev tlcGetRoleAdminStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "role" (.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32))

/-- The stored `_roles[role].adminRole` value (mapping slot `keccak(role ‖ 0)`, struct offset `+1`). -/
def tlcGetRoleAdminWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (roleAdminSlot (tlcGetRoleAdminKey I))

/-- The decoded `bytes32` key hashes to the same word the EVM `CALLDATALOAD(4)` loads. -/
theorem tlcGetRoleAdminKey_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (tlcGetRoleAdminKey I) = calldataWord I.calldata 4 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have key_eq : tlcGetRoleAdminKey I
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32))) := by
    simp only [tlcGetRoleAdminKey]
    rw [show abiBytes32Width = (⟨31, by decide⟩ : Fin 32) from rfl,
      toBytesBE_bytesToWord_of_length hlen]
  rw [key_eq, keyValueToWord_fixedBytes32, decode_word_at_eq_any I.calldata 4 (by omega)]

theorem tlcDecodeGetRoleAdmin_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (getRoleAdminTransition.params.map Param.name)
      (transitionSignature getRoleAdminTransition).paramTypes I.calldata
      = some (tlcGetRoleAdminStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["role"] [bytes32] I.calldata = _
  exact decodeCalldata_bytes32_ok hsz36 hbig

theorem tlcDecodeGetRoleAdmin_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (getRoleAdminTransition.params.map Param.name)
      (transitionSignature getRoleAdminTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_short hsz4 hshort

theorem tlcDecodeGetRoleAdmin_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (getRoleAdminTransition.params.map Param.name)
      (transitionSignature getRoleAdminTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["role"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_huge hbig

/-! ## Slot arithmetic: `keccak(role ‖ 0) + 1` -/

/-- The EVM `ADD` of a `PUSH1 1` onto a slot word is the Solm layout's struct-field offset `+1`. -/
theorem tlcOneAddEqAddSlot (s : UInt256) : (⟨1⟩ : UInt256) + s = addSlot s 1 := by
  rw [u256_add_comm]
  unfold addSlot
  rw [← u256_ofNat_toNat s]; rfl

/-! ## EVM: reach the body and the length check -/

/-- Reach the `getRoleAdmin` body pc 712 (G350 arm 3). -/
theorem tlcReachGetRoleAdmin {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 8)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨712⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x248a9ca3⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x24 0x8a 0x9c 0xa3 ⟨0x248a9ca3⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG350Body 3 (by omega) ⟨712⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j <;> (rw [hsw]; native_decide))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard and run the decoder prologue to the `SLT` availability `JUMPI` @4714.
    Stack: `[⟨4718⟩, ISZERO(SLT(size-4, 32)), ⟨0⟩, ⟨4⟩, size, ⟨738⟩, ⟨581⟩, sel]`. -/
theorem tlcGetRoleAdminReachLenCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 8)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4714⟩
      [⟨4718⟩, UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩),
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨738⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h712⟩ := tlcReachGetRoleAdmin (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h725⟩ := tlcGuardPeelOk (gt := ⟨723⟩) h712 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, h725.push2 ⟨581⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨738⟩ (by native_decide) (by evm_ov)
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

/-! ## Base-slot-0 struct-field mapping getter (@738 in the TimelockController runtime)

    Stack at entry `[key, ret, R]`; the routine writes `key‖0` into scratch, hashes, `ADD`s the
    field offset `1`, loads the slot, and `JUMP`s to `ret` leaving `[slotWord, R]`.  Memory becomes
    `twoWordHashMem key ⟨0⟩ solcFreePtrMem`.  The base-slot-`0`-plus-offset-`1` analogue of
    `tlcMappingGetSlot1` (which is base slot `1` with no offset). -/
theorem tlcGetRoleAdminGetSlot0Plus1 {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    {key ret : UInt256} {R : List UInt256} {rdata : ByteArray} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode ee g s0 ⟨738⟩ (key :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hret : (D_J timelockControllerBenchBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD timelockControllerBenchBytecode ee g s0 ret
      (solcSlotWord σ ee (⟨1⟩ + solcMappingSlot ⟨0⟩ key) :: R)
      (twoWordHashMem key ⟨0⟩ solcFreePtrMem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hk := h.jumpdest (by native_decide) (by evm_ov)
    |>.push0 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.mstore 0 (wordAt0Mem key solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rfl) (by native_decide) (by evm_ov)
    |>.push1 ⟨32⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.mstore 0 (twoWordHashMem key ⟨0⟩ solcFreePtrMem) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rfl) (by native_decide) (by evm_ov)
    |>.push1 ⟨64⟩ (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.keccak256 0 (solcMappingSlot ⟨0⟩ key) (UInt256.ofNat 3) (by native_decide) mem_cost
        (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
            exact tlcTwoWordKeccakSlot ⟨0⟩ key)
        (by native_decide) (by evm_ov)
    |>.push1 ⟨1⟩ (by native_decide) (by evm_ov)
    |>.add (by native_decide) (by evm_ov)
  obtain ⟨_, _, hsl⟩ := hk.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, hsl.swap1 (by native_decide) (by evm_ov) |>.jump (by native_decide) hret (by evm_ov)⟩

/-- EVM: with zero callvalue and a well-sized calldata, `getRoleAdmin(role)` returns
    `_roles[role].adminRole`. -/
theorem tlcGetRoleAdminX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 8)) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (tlcGetRoleAdminWord σ I)) := by
  have hsz : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h4714⟩ := tlcGetRoleAdminReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel
  have h738 := h4714.jumpiT (by native_decide)
      (by rw [solcDecodeLenCheckOk_4_32 hsz36 hbig hsize]; decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, h581⟩ := tlcGetRoleAdminGetSlot0Plus1 h738 (by jump_dest) (by simp)
  have hslot : (⟨1⟩ : UInt256) + solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4)
      = roleAdminSlot (tlcGetRoleAdminKey I) := by
    have hbaseslot : solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4)
        = roleDataSlot (tlcGetRoleAdminKey I) := by
      unfold roleDataSlot mapSlot solcMappingSlot
      rw [tlcGetRoleAdminKey_eq I hsz36]
    rw [hbaseslot]
    exact tlcOneAddEqAddSlot (roleDataSlot (tlcGetRoleAdminKey I))
  have hval : solcSlotWord σ I (⟨1⟩ + solcMappingSlot ⟨0⟩ (calldataWord I.calldata 4))
      = tlcGetRoleAdminWord σ I := by
    unfold tlcGetRoleAdminWord
    rw [hslot]
  rw [← hval]
  exact tlcReturnWordFromMem h581 (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64) (by simp)

/-- EVM revert path for a mis-sized calldata: the signed length check `SLT(size-4, 32) = 1`
    fails the `JUMPI`, falling into the `PUSH0 PUSH0 REVERT` stub. -/
theorem tlcGetRoleAdminDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 8))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4714⟩ := tlcGetRoleAdminReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel
  exact h4714.jumpiNT (by native_decide) (by rw [hslt]; decide) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## Solm body -/

/-- The Solm `getRoleAdmin(role)` body returns `_roles[role].adminRole`. -/
theorem tlcGetRoleAdminBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcGetRoleAdminStore I)
      getRoleAdminTransition.body
      (.returned { contract := contract, locals := tlcGetRoleAdminStore I }
        (initState cA gh bl σ σ₀ g A I)
        (some [(.fixedBytes bytes32Width (EVM.Word.toBytesBE (tlcGetRoleAdminWord σ I)))])) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hvk : valueToKey? (Value.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32))
      = some (tlcGetRoleAdminKey I) := by
    simp [valueToKey?, tlcGetRoleAdminKey, abiBytes32Width, hlen]
  refine nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) ?_
  rw [evalExpr_storage_scalar (cfg := config)
    (solm := { contract := contract, locals := tlcGetRoleAdminStore I })
    (slot := roleAdminRef (.var "role"))
    (er := ({ base := "_roles", steps := [.mindex (tlcGetRoleAdminKey I), .field "adminRole"] } :
      EvaledStorageRef))
    (t := .bytes bytes32Width) (loc := bytes32Loc (roleAdminSlot (tlcGetRoleAdminKey I)))
    (hbase := by simp [roleAdminRef])
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, roleAdminRef,
        tlcGetRoleAdminStore, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hvk])
    (hty := by
      simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, roleDataSt,
        tlcGetRoleAdminKey, bytes32St])
    (hloc := by rfl)]
  exact congrArg EvalResult.ok
    (storageLocLoad_bytes32 (initState cA gh bl σ σ₀ g A I) (roleAdminSlot (tlcGetRoleAdminKey I)))

/-! ## Refinement -/

theorem tlcGetRoleAdminBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 8))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 8) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · -- execute: `36 ≤ size < 2^255 + 4`
        have hword : tlcGetRoleAdminWord σ_evm I = tlcGetRoleAdminWord σ_solm I := by
          simp only [tlcGetRoleAdminWord, solcSlotWord]
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner
            (roleAdminSlot (tlcGetRoleAdminKey I)) ⟨0⟩
        exact tlcReEquivExecTransport hcode
          (tlcGetRoleAdminX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize hsel)
          (tlcSelectorDispatchGetRoleAdmin hsel) (tlcDecodeGetRoleAdmin_ok hsz36 hbig)
          (tlcGetRoleAdminBodyReturns (g := Sat256.ofUInt256 g) hwv hsz36) (by rw [← hword]; rfl)
          hAccounts
          (returnEquiv_of_encode (bytes32ReturnEncoding (tlcGetRoleAdminWord σ_evm I)))
      · -- huge calldata: `2^255 + 4 ≤ size`; EVM reverts at the signed length check, Solm decode fails
        have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := Nat.not_lt.mp hbig
        have hrev := tlcGetRoleAdminDecodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
          (solcDecodeLenCheckHuge_4_32 hhuge hsize)
        exact tlcReEquivDecodeFailed hcode hrev (tlcSelectorDispatchGetRoleAdmin hsel)
          (tlcDecodeGetRoleAdmin_none_huge hhuge)
    · -- short calldata: `size < 36`; EVM reverts at the length check, Solm decode fails
      have hshort : I.calldata.size < 36 := by omega
      have hrev := tlcGetRoleAdminDecodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
        (solcDecodeLenCheckShort_4_32 hsz hshort hsize)
      exact tlcReEquivDecodeFailed hcode hrev (tlcSelectorDispatchGetRoleAdmin hsel)
        (tlcDecodeGetRoleAdmin_none_short hsz hshort)
  · -- nonpayable guard: `callvalue ≠ 0`
    obtain ⟨_, _, h712⟩ := tlcReachGetRoleAdmin (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨723⟩) h712 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchGetRoleAdmin hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
