import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `updateDelay(uint256)` refinement

`updateDelay` (selector index 27, dispatch group G254 arm 2, body pc 913) is the first
**state-mutating** function proven for this contract.  It peels its non-payable callvalue guard,
decodes a single `uint256` word (via the shared `@4702` decoder, inlined here to avoid colliding with
a shared `Storage.lean`), enforces `require(msg.sender == address(this))`, emits the `MinDelayChange`
event (`LOG1`, ignored by the spec), and `SSTORE`s the new delay to storage slot 2 (`_minDelay`),
returning nothing (`STOP`).

Template for the other mutations: the EVM trace ends at `RD.stop` (empty return) with the account map
carrying a single `sstoreAccountMap`, coupled to the Solm `.assign .storage` body result by
`accountMapEquiv_sstoreAccountMap`; the void return is `returnEquiv.fallthrough`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Decoded value, source-level store, and post-state -/

/-- The decoded `newDelay` word (calldata bytes `[4, 36)`). -/
abbrev tlcUpdateDelayWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

/-- The source-level locals after decoding `updateDelay(uint256 newDelay)`. -/
abbrev tlcUpdateDelayStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "newDelay" (Value.int (Int.ofNat (tlcUpdateDelayWord I).toNat))

/-- The decoded `newDelay` as a Solm value. -/
abbrev tlcUpdateDelayVal (I : ExecutionEnv) : Value :=
  Value.int (Int.ofNat (tlcUpdateDelayWord I).toNat)

/-- The Solm EVM state after `_minDelay = newDelay` (storage slot 2). -/
abbrev tlcUpdateDelayPost (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ (tlcUpdateDelayWord I)

/-! ## ABI decode (modern mode, one `uint256` word) -/

theorem tlcUpdateDelayDecodeOk {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (updateDelayTransition.params.map Param.name)
      (transitionSignature updateDelayTransition).paramTypes I.calldata
    = some (tlcUpdateDelayStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["newDelay"] [uint256] I.calldata = _
  exact decodeCalldata_uint256_ok hsz36 hhi

theorem tlcUpdateDelayDecodeShort {I : ExecutionEnv} (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (updateDelayTransition.params.map Param.name)
      (transitionSignature updateDelayTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["newDelay"] [uint256] I.calldata = none
  exact decodeCalldata_uint256_none_short hshort

theorem tlcUpdateDelayDecodeHuge {I : ExecutionEnv} (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (updateDelayTransition.params.map Param.name)
      (transitionSignature updateDelayTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["newDelay"] [uint256] I.calldata = none
  exact decodeCalldata_uint256_none_huge hbig

/-! ## Solm-side body -/

/-- `newDelay` reads back from the decoded store. -/
theorem tlcUpdateDelayRhs (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := tlcUpdateDelayStore I } evm (.var "newDelay")
      = .ok (tlcUpdateDelayVal I) := by
  simp only [evalExpr?, EvalResult.ofOption, tlcUpdateDelayStore, tlcUpdateDelayVal]
  rw [show (((∅ : Store).insert "newDelay"
        (Value.int (Int.ofNat (tlcUpdateDelayWord I).toNat))).get? "newDelay")
      = some (Value.int (Int.ofNat (tlcUpdateDelayWord I).toNat)) from by simp]

/-- The `_minDelay = newDelay` scalar storage write collapses to a single `storageStore` on slot 2. -/
theorem tlcUpdateDelayAssign (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := tlcUpdateDelayStore I } evm
      .storage minDelayRef (tlcUpdateDelayVal I) =
        .ok ({ contract := contract, locals := tlcUpdateDelayStore I }, tlcUpdateDelayPost evm I) := by
  apply assignStorageRef_storage_scalar
    (er := ({ base := "_minDelay", steps := [] } : EvaledStorageRef))
    (ty := uint256St) (loc := uint256Loc ⟨2⟩)
    (hbase := by simp [tlcUpdateDelayStore, minDelayRef])
    (her := by simp [evalStorageRef, minDelayRef, EvalResult.bind, bind, pure])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St, uint256Int])
    (hloc := by rfl)
  simpa [tlcUpdateDelayVal, tlcUpdateDelayPost, uint256Loc, uint256Int] using
    storageLocStore_uint256 evm ⟨2⟩ (tlcUpdateDelayWord I)

/-- With `msg.sender == address(this)`, the body stores `newDelay` and falls through (`none`). -/
theorem tlcUpdateDelayBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.source = evm.executionEnv.codeOwner) :
    ExecTransitionBody config contract evm (tlcUpdateDelayStore I) updateDelayTransition.body
      (.returned { contract := contract, locals := tlcUpdateDelayStore I }
        (tlcUpdateDelayPost evm I) none) := by
  refine ExecFuncBody.execBlockOK ?_
  have hguard : evalExpr? config { contract := contract, locals := tlcUpdateDelayStore I } evm
      (.binary .eq sender thisAddr) = .ok (.bool true) := by
    simp only [sender, thisAddr, evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?,
      hself, beq_self_eq_true]
  exact nonpayableRequireAssignStorageBlock hwv hguard (tlcUpdateDelayRhs evm I)
    (tlcUpdateDelayAssign evm I)

/-- With `msg.sender ≠ address(this)`, the body reverts at the `require`. -/
theorem tlcUpdateDelayBodyReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody config contract evm (tlcUpdateDelayStore I) updateDelayTransition.body
      .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hguard : evalExpr? config { contract := contract, locals := tlcUpdateDelayStore I } evm
      (.binary .eq sender thisAddr) = .ok (.bool false) := by
    simp only [sender, thisAddr, evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?]
    rw [show ((Value.address evm.executionEnv.source) == (Value.address evm.executionEnv.codeOwner))
        = false from by
      simp only [beq_eq_false_iff_ne, ne_eq, Value.address.injEq]; exact hself]
  exact nonpayableSecondRequireReverts hwv hguard

/-! ## EVM-side scratch memory for the `MinDelayChange` LOG

The event stores `oldDelay` at the free pointer `0x80` (giving `solcReturnMem oldDelay`) then the new
value `wd` at `0x80 + 0x20 = 0xa0`.  The custom-error revert path (caller ≠ this) stores the error
selector at `0x80` (again `solcReturnMem …`) then the masked caller at `0x84`.  Both keep the free
pointer word at `[0x40, 0x60)` intact, so `MLOAD 0x40` still reads `0x80`. -/

/-- Memory after `SSTORE`-side event build: `oldDelay@0x80`, `wd@0xa0` (active-words 6). -/
abbrev tlcUpdateDelayLogMem (oldDelay wd : UInt256) : ByteArray :=
  (UInt256.toByteArray wd).write 0 (solcReturnMem oldDelay) 160 32

theorem tlcUpdateDelayLogMem_size (oldDelay wd : UInt256) :
    (tlcUpdateDelayLogMem oldDelay wd).size = 192 := by
  unfold tlcUpdateDelayLogMem
  exact toByteArray_write32_size_of_le (solcReturnMem oldDelay) wd 160 160 192
    (solcReturnMem_size oldDelay) (by rw [solcReturnMem_size]) (by decide)

theorem tlcUpdateDelayLogMem_read64 (oldDelay wd : UInt256) :
    (tlcUpdateDelayLogMem oldDelay wd).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold tlcUpdateDelayLogMem
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size]) (by rw [solcReturnMem_size]) (by omega)]
  exact solcReturnMem_read64 oldDelay

theorem tlcUpdateDelayLogMem_mload64 (oldDelay wd : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (tlcUpdateDelayLogMem oldDelay wd).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((tlcUpdateDelayLogMem oldDelay wd).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [tlcUpdateDelayLogMem_size]; decide) (by decide)
    (tlcUpdateDelayLogMem_read64 oldDelay wd)

/-- The `MinDelayChange(uint256,uint256)` event topic (the `PUSH32` at pc 2184). -/
abbrev tlcUpdateDelayTopic : UInt256 :=
  ⟨0x11c24f4ead16507c69ac467fbd5e4eed5fb5c699626d2cc6d66421df253886d5⟩

/-- Memory after the custom-error build: error selector `v@0x80`, masked caller `w@0x84`. -/
abbrev tlcUpdateDelayErrMem (v w : UInt256) : ByteArray :=
  (UInt256.toByteArray w).write 0 (solcReturnMem v) 132 32

theorem tlcUpdateDelayErrMem_mload64 (v w : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (tlcUpdateDelayErrMem v w).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat (fromByteArrayBigEndian
       ((tlcUpdateDelayErrMem v w).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  apply mloadFreePtrValue
  · have : (tlcUpdateDelayErrMem v w).size = 164 := by
      unfold tlcUpdateDelayErrMem
      exact toByteArray_write32_size_of_le (solcReturnMem v) w 132 160 164
        (solcReturnMem_size v) (by rw [solcReturnMem_size]; omega) (by decide)
    omega
  · decide
  · unfold tlcUpdateDelayErrMem
    rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [solcReturnMem_size]; omega) (by omega)]
    exact solcReturnMem_read64 v

/-! ## EVM trace : reach the body, decode the word, run to the caller check -/

/-- Reach the `updateDelay` body pc 913 (G254 arm 2). -/
theorem tlcUpdateDelayReach {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 27)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨913⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x64d62353⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x64 0xd6 0x23 0x53 ⟨0x64d62353⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG254Body 2 (by omega) ⟨913⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j <;> (rw [hsw]; native_decide))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Decode detour `926 → 2117`: pass the `size ≥ 36` guard, `CALLDATALOAD` the word, jump to the
    caller check with `[newDelay, 476, sel]` on the stack. -/
theorem tlcUpdateDelayReachCaller {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨926⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2117⟩
      [tlcUpdateDelayWord I, ⟨476⟩, tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k' C' := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have h2117 := evm_run h with [
    push2 ⟨476⟩, push2 ⟨939⟩, calldatasize, push1 ⟨4⟩, push2 ⟨4702⟩, jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4718⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, pop, calldataload, swap2, swap1, pop, jump (by jump_dest),
    jumpdest, push2 ⟨2117⟩, jump (by jump_dest) ]
  exact ⟨_, _, by simpa [tlcUpdateDelayWord, calldataWord] using h2117⟩

/-! ## EVM trace : the store + LOG happy path, and the two revert paths -/

/-- Happy path (`msg.sender == address(this)`): emit the `MinDelayChange` `LOG1`, `SSTORE` slot 2, and
    `STOP` — halting with the account map carrying a single `sstoreAccountMap` and an empty return. -/
theorem tlcUpdateDelayX_ok {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2117⟩
      [tlcUpdateDelayWord I, ⟨476⟩, tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hperm : I.perm = true) (hself : I.source = I.codeOwner) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩ (tlcUpdateDelayWord I)) ByteArray.empty := by
  have h2167 := evm_run h with [
    jumpdest,
    raw caller (by native_decide) (by evm_ov),
    raw address (by native_decide) (by evm_ov),
    dup2, eq, push2 ⟨2166⟩,
    jumpiT (by rw [hself, uInt256_eq_self]; decide) (by jump_dest),
    jumpdest, push1 ⟨2⟩ ]
  obtain ⟨_, _, h2169⟩ := h2167.sload (by native_decide) (by evm_ov)
  have h2184 := evm_run h2169 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost solcFreePtrMem_mload64
      (by native_decide) (by evm_ov),
    swap2, dup3,
    raw mstore 6 (solcReturnMem _) (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩, dup3, add, dup5, swap1,
    raw mstore 3 (tlcUpdateDelayLogMem _ (tlcUpdateDelayWord I)) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by native_decide) (by evm_ov) ]
  have h2217 := h2184.pushConst tlcUpdateDelayTopic (width := 32) (op := .PUSH32) (by decide)
    (by native_decide) (by evm_ov)
  have h2226pre := evm_run h2217 with [
    swap2, add, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide) mem_cost
      (tlcUpdateDelayLogMem_mload64 _ (tlcUpdateDelayWord I)) (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  have h2227 := h2226pre.log1 0 (UInt256.ofNat 6) (by native_decide) hperm mem_cost
    (by native_decide) (by evm_ov)
  have h2230 := evm_run h2227 with [ pop, push1 ⟨2⟩ ]
  obtain ⟨_, _, h2231⟩ := h2230.sstore hperm (by native_decide) (by evm_ov)
  have h476 := h2231.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact h476.jumpdest (by native_decide) (by evm_ov) |>.stop (by native_decide) (by evm_ov)

/-- Caller-check revert (`msg.sender ≠ address(this)`): build the `AccessControlUnauthorizedAccount`-
    style custom error and `REVERT`. -/
theorem tlcUpdateDelayRevCaller {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2117⟩
      [tlcUpdateDelayWord I, ⟨476⟩, tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C)
    (hself : I.source ≠ I.codeOwner) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heq0 : UInt256.eq (UInt256.ofNat I.source.val) (UInt256.ofNat I.codeOwner.val) = ⟨0⟩ := by
    apply uInt256_eq_zero_of_ne
    intro hbad
    refine hself (Fin.ext ?_)
    have h1 : (UInt256.ofNat I.source.val).toNat = I.source.val :=
      ulit_toNat' _ (lt_of_lt_of_le I.source.isLt (by decide : AccountAddress.size ≤ UInt256.size))
    have h2 : (UInt256.ofNat I.codeOwner.val).toNat = I.codeOwner.val :=
      ulit_toNat' _ (lt_of_lt_of_le I.codeOwner.isLt (by decide : AccountAddress.size ≤ UInt256.size))
    rw [← h1, ← h2, uInt256_eq_one_eq hbad]
  have h2165pre := evm_run h with [
    jumpdest,
    raw caller (by native_decide) (by evm_ov),
    raw address (by native_decide) (by evm_ov),
    dup2, eq, push2 ⟨2166⟩,
    jumpiNT (by exact heq0),
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost solcFreePtrMem_mload64
      (by native_decide) (by evm_ov),
    raw push4 ⟨0xe2850c59⟩ (by native_decide) (by evm_ov),
    push1 ⟨224⟩, shl, dup2,
    raw mstore 6 (solcReturnMem _) (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup3, and, push1 ⟨4⟩, dup3, add,
    raw mstore 3 (tlcUpdateDelayErrMem _ _) (UInt256.ofNat 6) (by native_decide) mem_cost
      (by rw [show (⟨128⟩ + ⟨4⟩ : UInt256).toNat = 132 from by native_decide])
      (by native_decide) (by evm_ov),
    push1 ⟨36⟩, add, jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide) mem_cost
      (tlcUpdateDelayErrMem_mload64 _ _) (by native_decide) (by evm_ov),
    dup1, swap2, sub, swap1 ]
  exact h2165pre.rev 0 (by native_decide) mem_cost (by evm_ov)

/-- Decode-guard revert (`size < 36` or `size ≥ 2²⁵⁵+4`): the modern `SLT(cds-4, 32)` guard is `1`,
    so `ISZERO` is `0`, the `JUMPI` falls through, and the `PUSH0 PUSH0 REVERT` stub fires. -/
theorem tlcUpdateDelayRevDecode {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨926⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h4715 := evm_run h with [
    push2 ⟨476⟩, push2 ⟨939⟩, calldatasize, push1 ⟨4⟩, push2 ⟨4702⟩, jump (by jump_dest),
    jumpdest, push0, push1 ⟨32⟩, dup3, dup5, sub, slt, iszero, push2 ⟨4718⟩,
    jumpiNT (by rw [hslt]; decide) ]
  exact h4715.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## Refinement -/

/-- Refinement of `updateDelay` (selector index 27). -/
theorem tlcUpdateDelayBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 27))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 27) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · -- callvalue == 0
    by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · -- decode succeeds : 36 ≤ size < 2^255 + 4
        obtain ⟨_, _, h913⟩ := tlcUpdateDelayReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
        obtain ⟨_, _, h926⟩ := tlcGuardPeelOk (gt := ⟨924⟩) h913 hwv
          (by native_decide) (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        obtain ⟨_, _, h2117⟩ := tlcUpdateDelayReachCaller h926 hsz36 hhi hsize
        by_cases hself : I.source = I.codeOwner
        · -- msg.sender == address(this) : both mutate slot 2
          exact tlcReEquivExecGen hcode
            (tlcUpdateDelayX_ok h2117 _hperm hself)
            (tlcSelectorDispatchUpdateDelay hsel) (tlcUpdateDelayDecodeOk hsz36 hhi)
            (tlcUpdateDelayBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) (by simp only [initState]; exact hself))
            (by simp [tlcUpdateDelayPost, initState, storageStore_createdAccounts])
            (by simpa [tlcUpdateDelayPost, initState, storageStore_accountMap] using
              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ (tlcUpdateDelayWord I) hAccounts)
            (by simpa [updateDelayTransition] using
              (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                (dvs := []) rfl (by native_decide) (by native_decide)))
        · -- msg.sender ≠ address(this) : both revert
          exact tlcReEquivExecRev hcode (tlcUpdateDelayRevCaller h2117 hself)
            (tlcSelectorDispatchUpdateDelay hsel) (tlcUpdateDelayDecodeOk hsz36 hhi)
            (tlcUpdateDelayBodyReverts (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simp only [initState]; exact hwv) (by simp only [initState]; exact hself))
      · -- calldata too large : decode fails, EVM reverts at the SLT guard
        obtain ⟨_, _, h913⟩ := tlcUpdateDelayReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
        obtain ⟨_, _, h926⟩ := tlcGuardPeelOk (gt := ⟨924⟩) h913 hwv
          (by native_decide) (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
        exact tlcReEquivDecodeFailed hcode
          (tlcUpdateDelayRevDecode h926 (solcDecodeLenCheckHuge_4_32 (by omega) hsize))
          (tlcSelectorDispatchUpdateDelay hsel) (tlcUpdateDelayDecodeHuge (by omega))
    · -- calldata too short : decode fails, EVM reverts at the SLT guard
      obtain ⟨_, _, h913⟩ := tlcUpdateDelayReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
      obtain ⟨_, _, h926⟩ := tlcGuardPeelOk (gt := ⟨924⟩) h913 hwv
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
        (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
      exact tlcReEquivDecodeFailed hcode
        (tlcUpdateDelayRevDecode h926 (solcDecodeLenCheckShort_4_32 hsz (by omega) hsize))
        (tlcSelectorDispatchUpdateDelay hsel) (tlcUpdateDelayDecodeShort (by omega))
  · -- callvalue ≠ 0 : nonpayable guard reverts on both sides
    obtain ⟨_, _, h913⟩ := tlcUpdateDelayReach (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨924⟩) h913 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchUpdateDelay hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
