import Benchmarks.OpenZeppelinBench.TimelockController.GetTimestamp
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `getOperationState(bytes32)` refinement

`getOperationState` is a public non-payable `uint8` getter.  The compiled body (pc 944, dispatch group
G254 arm 3) decodes one `bytes32 id`, then calls the inlined `_getOperationState` helper @2232 which
hashes the `_timestamps` mapping slot `keccak(id ‖ 1)`, `SLOAD`s the timestamp `t`, and returns the
4-way operation state (`0=Unset` if `t=0`, `3=Done` if `t=1`, `1=Waiting` if `t>block.timestamp`,
`2=Ready` otherwise), which the body ABI-encodes as a `uint8` (encoder @5061, dispatcher @521).

Front half (guard peel, `bytes32` decoder @4702, slot-1 mapping keccak) and the `_getOperationState`
leaf traversal @2232 reuse `GetTimestamp`/`Storage`/`IsOperation` infrastructure; the `uint8` encoder
@5061→@521 stores the low-byte state word at the free pointer and `RETURN`s it, generalized over the
dirtied scratch memory (`twoWordHashMem …`) via `Storage.tlcRetMem*`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- The `uint8` operation-state word `getOperationState` returns for a stored timestamp `t` and block
    timestamp `ts`: `0` if `t=0`, `3` if `t=1`, `1` if `ts < t`, else `2`. -/
def tlcGetOperationStateWord (t : UInt256) (ts : Nat) : UInt256 :=
  if t = ⟨0⟩ then ⟨0⟩
  else if t = ⟨1⟩ then ⟨3⟩
  else if (UInt256.ofNat ts).toNat < t.toNat then ⟨1⟩
  else ⟨2⟩

theorem tlcGetOperationStateWord_lt_4 (t : UInt256) (ts : Nat) :
    (tlcGetOperationStateWord t ts).toNat < 4 := by
  unfold tlcGetOperationStateWord; split_ifs <;> decide

/-! ## Memory-generic `uint8` return encoder @5061 → @521

    From @975 with `[state, sel]` over any free-pointer-preserving scratch memory (`size = 96`,
    `mem[0x40] = 0x80`): the encoder @5061 stores the low-byte `state` word at the free pointer
    (after the `state < 4` enum bounds check, always taken here), and the dispatcher @521
    `RETURN(0x80, 0x20)`s the 32-byte word.  Reuses `Storage.tlcRetMem*`. -/
theorem tlcGetOperationStateReturn {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {v : UInt256} {mem : ByteArray}
    (h : RD timelockControllerBenchBytecode ee g s0 ⟨975⟩ (v :: R) mem
        (UInt256.ofNat 3) rdata acc k C)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlt : UInt256.lt v ⟨4⟩ ≠ ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDret timelockControllerBenchBytecode g s0 acc (UInt256.toByteArray v) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (mloadFreePtrValue (by rw [hsize]; decide) (by decide) hread64) (by decide) (by evm_ov),
    push2 ⟨521⟩, swap2, swap1, push2 ⟨5061⟩, jump (by jump_dest),
    jumpdest, push1 ⟨32⟩, dup2, add, push1 ⟨4⟩, dup4, lt, push2 ⟨5093⟩,
    jumpiT hlt (by jump_dest),
    jumpdest, swap2, swap1,
    raw mstore 6 (tlcRetMem mem v) (UInt256.ofNat 5) (by native_decide)
      mem_cost (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; rfl) (by native_decide)
      (by evm_ov),
    swap1, jump (by jump_dest),
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (tlcRetMem_mload64 hsize hread64 v) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray v) (by native_decide) mem_cost
      (by rw [show (UInt256.sub ((⟨128⟩ : UInt256) + ⟨32⟩) ⟨128⟩).toNat = 32 from by decide]
          exact tlcRetMem_read128 hsize v)
      (by evm_ov) ]

/-! ## EVM: reach the body and the decoder length check -/

/-- Reach the `getOperationState` body pc 944 (G254 arm 3). -/
theorem tlcReachGetOperationState {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 7)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨944⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x7958004c⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x79 0x58 0x00 0x4c ⟨0x7958004c⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG254Body 3 (by omega) ⟨944⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j <;> (rw [hsw]; native_decide))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard, push the return/decode continuations `⟨975⟩`/`⟨970⟩`, and run the
    `bytes32` decoder prologue @4702 to the availability `JUMPI` @4714.
    Stack: `[⟨4718⟩, ISZERO(SLT(size-4, 32)), ⟨0⟩, ⟨4⟩, size, ⟨970⟩, ⟨975⟩, sel]`. -/
theorem tlcGetOperationStateReachLenCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 7)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4714⟩
      [⟨4718⟩, UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩),
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨970⟩, ⟨975⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h944⟩ := tlcReachGetOperationState (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h957⟩ := tlcGuardPeelOk (gt := ⟨955⟩) h944 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, h957.push2 ⟨975⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨970⟩ (by native_decide) (by evm_ov)
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
    continuation @970, and enter the `_getOperationState` helper @2232 with `[id, ⟨975⟩, sel]`. -/
theorem tlcGetOperationStateReachCompute {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 7)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2232⟩
      [calldataWord I.calldata 4, ⟨975⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsz : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h4714⟩ := tlcGetOperationStateReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
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
    |>.push2 ⟨2232⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-! ## EVM: the `_getOperationState` helper @2232 and its four leaves

    From `[id, ⟨975⟩, sel]` at @2232, hash the slot `keccak(id ‖ 1)`, `SLOAD` the timestamp `t`, and
    case-split the four state leaves — each returns to the encoder continuation @975 with the state
    word `[state, sel]` on top. -/
theorem tlcGetOperationStateCompute {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 7)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨975⟩
      [tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp, tlcSelWord I]
      (twoWordHashMem (calldataWord I.calldata 4) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h2232⟩ := tlcGetOperationStateReachCompute (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz36 hbig hsize hsel
  have hkec := evm_run h2232 with [
    jumpdest, push0, dup2, dup2,
    raw mstore 0 (wordAt0Mem (calldataWord I.calldata 4) solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨32⟩,
    raw mstore 0 (twoWordHashMem (calldataWord I.calldata 4) ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3)
      (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) (UInt256.ofNat 3)
      (by native_decide) mem_cost
      (by rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (⟨64⟩ : UInt256).toNat = 64 from by decide]
          exact tlcTwoWordKeccakSlot ⟨1⟩ (calldataWord I.calldata 4))
      (by native_decide) (by evm_ov) ]
  obtain ⟨_, _, hsl⟩ := hkec.sload (by native_decide) (by evm_ov)
  -- `hsl` is at @2247 with the loaded timestamp `t = tlcGetTimestampWord σ I` on top.
  by_cases ht0 : tlcGetTimestampWord σ I = ⟨0⟩
  · -- Unset: `t = 0` ⇒ state 0.
    have hcond : UInt256.sub ⟨0⟩ (tlcGetTimestampWord σ I) = (⟨0⟩ : UInt256) := by
      rw [ht0]; exact u256_sub_self ⟨0⟩
    have h975 := evm_run hsl with [
      dup1, push0, sub, push2 ⟨2261⟩, jumpiNT hcond,
      pop, push0, swap3, swap2, pop, pop, jump (by jump_dest) ]
    exact ⟨_, _, by
      rw [show tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp = ⟨0⟩ from by
        unfold tlcGetOperationStateWord; rw [if_pos ht0]]
      exact h975⟩
  · -- `t ≠ 0`: pass the Unset `JUMPI` @2253, reach the Done check @2269.
    have hcond0 : UInt256.sub ⟨0⟩ (tlcGetTimestampWord σ I) ≠ (⟨0⟩ : UInt256) :=
      u256_zero_sub_ne_zero ht0
    have h2269 := evm_run hsl with [
      dup1, push0, sub, push2 ⟨2261⟩, jumpiT hcond0 (by jump_dest),
      jumpdest, push1 ⟨1⟩, dup2, sub, push2 ⟨2278⟩ ]
    by_cases ht1 : tlcGetTimestampWord σ I = ⟨1⟩
    · -- Done: `t = 1` ⇒ state 3.
      have hcond1 : UInt256.sub (tlcGetTimestampWord σ I) ⟨1⟩ = (⟨0⟩ : UInt256) := by
        rw [ht1]; exact u256_sub_self ⟨1⟩
      have h975 := evm_run h2269 with [
        jumpiNT hcond1,
        pop, push1 ⟨3⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
      exact ⟨_, _, by
        rw [show tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp = ⟨3⟩ from by
          unfold tlcGetOperationStateWord; rw [if_neg ht0, if_pos ht1]]
        exact h975⟩
    · -- `t ≠ 1`: pass the Done `JUMPI` @2269, reach the timestamp check @2286.
      have hcond1 : UInt256.sub (tlcGetTimestampWord σ I) ⟨1⟩ ≠ (⟨0⟩ : UInt256) :=
        u256_sub_ne_zero_of_ne ht1
      have h2286 := evm_run h2269 with [
        jumpiT hcond1 (by jump_dest),
        jumpdest, timestamp, dup2, gt, iszero, push2 ⟨2295⟩ ]
      by_cases htgt : UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp) = ⟨0⟩
      · -- Ready: `t ≤ block.timestamp` ⇒ state 2.
        have hcondr : UInt256.isZero
            (UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp))
              ≠ (⟨0⟩ : UInt256) := by
          rw [htgt]; decide
        have h975 := evm_run h2286 with [
          jumpiT hcondr (by jump_dest),
          jumpdest, pop, push1 ⟨2⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
        exact ⟨_, _, by
          rw [show tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp = ⟨2⟩ from by
            unfold tlcGetOperationStateWord
            rw [if_neg ht0, if_neg ht1,
              if_neg (fun hc => by rw [ugt_one hc] at htgt; exact absurd htgt (by decide))]]
          exact h975⟩
      · -- Waiting: `t > block.timestamp` ⇒ state 1.
        have hcondw : UInt256.isZero
            (UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp))
              = (⟨0⟩ : UInt256) :=
          isZero_eq_zero_of_ne htgt
        have h975 := evm_run h2286 with [
          jumpiNT hcondw,
          pop, push1 ⟨1⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
        exact ⟨_, _, by
          rw [show tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp = ⟨1⟩ from by
            unfold tlcGetOperationStateWord
            rw [if_neg ht0, if_neg ht1,
              if_pos (by by_contra hc; exact htgt (ugt_zero (Nat.le_of_not_lt hc)))]]
          exact h975⟩

/-- EVM: with zero callvalue and well-sized calldata, `getOperationState(id)` returns the `uint8`
    operation-state word. -/
theorem tlcGetOperationStateX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 7)) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray
        (tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp)) := by
  obtain ⟨_, _, h975⟩ := tlcGetOperationStateCompute (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz36 hbig hsize hsel
  exact tlcGetOperationStateReturn h975
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by unfold tlcGetOperationStateWord; split_ifs <;> decide) (by evm_ov)

/-- EVM revert path for a mis-sized calldata: the signed length check `SLT(size-4, 32) = 1` fails the
    `JUMPI`, falling into the decoder's `PUSH0 PUSH0 REVERT` stub. -/
theorem tlcGetOperationStateDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 7))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4714⟩ := tlcGetOperationStateReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel
  exact h4714.jumpiNT (by native_decide) (by rw [hslt]; decide) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## ABI decode (a single `bytes32`, exactly like `getTimestamp`) -/

theorem tlcDecodeGetOperationState_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (getOperationStateTransition.params.map Param.name)
      (transitionSignature getOperationStateTransition).paramTypes I.calldata
      = some (tlcGetTimestampStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = _
  exact decodeCalldata_bytes32_ok hsz36 hbig

theorem tlcDecodeGetOperationState_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (getOperationStateTransition.params.map Param.name)
      (transitionSignature getOperationStateTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_short hsz4 hshort

theorem tlcDecodeGetOperationState_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (getOperationStateTransition.params.map Param.name)
      (transitionSignature getOperationStateTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_huge hbig

/-! ## Solm body -/

/-- The Solm `getOperationState(id)` body returns the `uint8` operation state. -/
theorem tlcGetOperationStateBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcGetTimestampStore I)
      getOperationStateTransition.body
      (.returned { contract := contract, locals := tlcGetTimestampStore I }
        (initState cA gh bl σ σ₀ g A I)
        (some [(.int (Int.ofNat
          (tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp).toNat))])) := by
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
  have henv : evalExpr? config { contract := contract, locals := tlcGetTimestampStore I }
      (initState cA gh bl σ σ₀ g A I) (.env .timestamp)
      = .ok (.int (Int.ofNat (UInt256.ofNat I.header.timestamp).toNat)) := by
    simp only [evalExpr?, envValue, initState, pure]
  have heqF : ∀ n : UInt256, tlcGetTimestampWord σ I ≠ n →
      (Value.int (Int.ofNat (tlcGetTimestampWord σ I).toNat) == Value.int (Int.ofNat n.toNat)) = false :=
    fun n hn => by
      simp only [beq_eq_false_iff_ne, ne_eq, Value.int.injEq]
      intro hh; exact hn (u256_inj (Int.ofNat.inj hh))
  refine nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) ?_
  unfold operationStateExpr doneTimestamp
  by_cases h0 : tlcGetTimestampWord σ I = ⟨0⟩
  · rw [show tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp = ⟨0⟩ from by
      unfold tlcGetOperationStateWord; rw [if_pos h0]]
    have he0 : (Value.int (Int.ofNat (tlcGetTimestampWord σ I).toNat) == Value.int 0) = true := by
      rw [h0]; rfl
    simp only [evalExpr?, hstore, EvalResult.bind, bind, pure, evalBinaryOp?, he0]
    rfl
  · by_cases h1 : tlcGetTimestampWord σ I = ⟨1⟩
    · rw [show tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp = ⟨3⟩ from by
        unfold tlcGetOperationStateWord; rw [if_neg h0, if_pos h1]]
      have he0 : (Value.int (Int.ofNat (tlcGetTimestampWord σ I).toNat) == Value.int 0) = false :=
        heqF ⟨0⟩ h0
      have he1 : (Value.int (Int.ofNat (tlcGetTimestampWord σ I).toNat) == Value.int 1) = true := by
        rw [h1]; rfl
      simp only [evalExpr?, hstore, EvalResult.bind, bind, pure, evalBinaryOp?, he0, he1]
      rfl
    · have he0 : (Value.int (Int.ofNat (tlcGetTimestampWord σ I).toNat) == Value.int 0) = false :=
        heqF ⟨0⟩ h0
      have he1 : (Value.int (Int.ofNat (tlcGetTimestampWord σ I).toNat) == Value.int 1) = false :=
        heqF ⟨1⟩ h1
      by_cases htgt : (UInt256.ofNat I.header.timestamp).toNat < (tlcGetTimestampWord σ I).toNat
      · rw [show tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp = ⟨1⟩ from by
          unfold tlcGetOperationStateWord; rw [if_neg h0, if_neg h1, if_pos htgt]]
        have hg : decide (Int.ofNat (UInt256.ofNat I.header.timestamp).toNat
            < Int.ofNat (tlcGetTimestampWord σ I).toNat) = true :=
          decide_eq_true_eq.mpr (Int.ofNat_lt.mpr htgt)
        simp only [evalExpr?, hstore, henv, EvalResult.bind, bind, pure, evalBinaryOp?, he0, he1,
          gt_iff_lt, hg]
        rfl
      · rw [show tlcGetOperationStateWord (tlcGetTimestampWord σ I) I.header.timestamp = ⟨2⟩ from by
          unfold tlcGetOperationStateWord; rw [if_neg h0, if_neg h1, if_neg htgt]]
        have hg : decide (Int.ofNat (UInt256.ofNat I.header.timestamp).toNat
            < Int.ofNat (tlcGetTimestampWord σ I).toNat) = false :=
          decide_eq_false_iff_not.mpr (fun h => htgt (Int.ofNat_lt.mp h))
        simp only [evalExpr?, hstore, henv, EvalResult.bind, bind, pure, evalBinaryOp?, he0, he1,
          gt_iff_lt, hg]
        rfl

/-- ABI-encoding the `uint8` operation-state result is the EVM's returned word. -/
theorem tlcGetOperationStateUint8Encoding (t : UInt256) (ts : Nat) :
    encodeReturnValue? uint8 (.int (Int.ofNat (tlcGetOperationStateWord t ts).toNat))
      = some (UInt256.toByteArray (tlcGetOperationStateWord t ts)) := by
  simpa [uint8, uint8Int] using
    uint8ReturnEncoding (tlcGetOperationStateWord t ts)
      (Nat.lt_of_lt_of_le (tlcGetOperationStateWord_lt_4 t ts) (by decide))

/-! ## Refinement -/

/-- Refinement of `GetOperationState` (selector index 7). -/
theorem tlcGetOperationStateBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 7))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 7) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · -- execute: `36 ≤ size < 2^255 + 4`
        have hword : tlcGetTimestampWord σ_evm I = tlcGetTimestampWord σ_solm I := by
          simp only [tlcGetTimestampWord]
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner
            (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) ⟨0⟩
        exact tlcReEquivExecTransport hcode
          (tlcGetOperationStateX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize hsel)
          (tlcSelectorDispatchGetOperationState hsel)
          (tlcDecodeGetOperationState_ok hsz36 hbig)
          (tlcGetOperationStateBodyReturns (g := Sat256.ofUInt256 g) hwv hsz36)
          (by rw [← hword]) hAccounts
          (returnEquiv_of_encode
            (tlcGetOperationStateUint8Encoding (tlcGetTimestampWord σ_evm I) I.header.timestamp))
      · -- huge calldata: EVM reverts at the signed length check, Solm decode fails
        have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := Nat.not_lt.mp hbig
        have hrev := tlcGetOperationStateDecodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
          (solcDecodeLenCheckHuge_4_32 hhuge hsize)
        exact tlcReEquivDecodeFailed hcode hrev (tlcSelectorDispatchGetOperationState hsel)
          (tlcDecodeGetOperationState_none_huge hhuge)
    · -- short calldata: EVM reverts at the length check, Solm decode fails
      have hshort : I.calldata.size < 36 := by omega
      have hrev := tlcGetOperationStateDecodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
        (solcDecodeLenCheckShort_4_32 hsz hshort hsize)
      exact tlcReEquivDecodeFailed hcode hrev (tlcSelectorDispatchGetOperationState hsel)
        (tlcDecodeGetOperationState_none_short hsz hshort)
  · -- nonpayable guard: `callvalue ≠ 0`
    obtain ⟨_, _, h944⟩ := tlcReachGetOperationState (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨955⟩) h944 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchGetOperationState hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
