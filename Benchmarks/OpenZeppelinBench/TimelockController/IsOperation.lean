import Benchmarks.OpenZeppelinBench.TimelockController.GetTimestamp
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `isOperation(bytes32)` refinement

`isOperation` is a public non-payable `bool` getter.  The compiled body (pc 820, dispatch group G301
arm 2) is NOT a plain "load-and-compare": it decodes one `bytes32 id`, then calls the inlined
`_getOperationState` helper @2232 which hashes the `_timestamps` mapping slot `keccak(id ‖ 1)`,
`SLOAD`s the timestamp `t`, and returns the 4-way operation state
(`0=Unset` if `t=0`, `3=Done` if `t=1`, `1=Waiting` if `t>block.timestamp`, `2=Ready` otherwise),
after which the body returns the `bool` `state != Unset`.  Since `state = 0 ⟺ t = 0`, this equals the
trusted spec's `_timestamps[id] != 0`.  The proof therefore case-splits the EVM execution over the
four `_getOperationState` leaves and shows every leaf's `state != 0` word equals `t != 0`.

Front half (guard peel, `bytes32` decoder @4702, slot-1 mapping keccak) reuses `GetTimestamp`/`Storage`
infrastructure; the bool return encoder @509 mirrors `SupportsInterface`, generalized over the dirtied
scratch memory (`twoWordHashMem …`) via `Storage.tlcRetMem*`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- The 32-byte word `isOperation` returns for a stored timestamp `t`: `1` iff `t ≠ 0`. -/
def tlcIsOperationBoolWord (t : UInt256) : UInt256 := if t = ⟨0⟩ then ⟨0⟩ else ⟨1⟩

/-! ## Memory-generic bool-return encoder @509

    Structurally identical to `SupportsInterface.tlcSuppIfaceReturnBool`, but over any free-pointer
    preserving scratch memory (`size = 96`, `mem[0x40] = 0x80`) — a mapping getter dirties `[0,0x40)`,
    so the return runs over `twoWordHashMem …`, not `solcFreePtrMem`.  Reuses `Storage.tlcRetMem*`. -/
theorem tlcIsOperationReturnBool {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {val : UInt256} {mem : ByteArray}
    (h : RD timelockControllerBenchBytecode ee g s0 ⟨509⟩ (val :: R) mem
        (UInt256.ofNat 3) rdata acc k C)
    (hsize : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hnorm : UInt256.isZero (UInt256.isZero val) = val)
    (hov : R.length + 8 ≤ 1024) :
    RDret timelockControllerBenchBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost (mloadFreePtrValue (by rw [hsize]; decide) (by decide) hread64) (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (tlcRetMem mem val) (UInt256.ofNat 5) (by native_decide)
      mem_cost (by rw [hnorm]; rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, add, jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost (tlcRetMem_mload64 hsize hread64 val) (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by native_decide) mem_cost
      (by rw [show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide]
          exact tlcRetMem_read128 hsize val)
      (by evm_ov) ]

/-! ## EVM: reach the body and the decoder length check -/

/-- Reach the `isOperation` body pc 820 (G301 arm 2). -/
theorem tlcReachIsOperation {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 17)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨820⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x31d50750⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x31 0xd5 0x07 0x50 ⟨0x31d50750⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG301Body 2 (by omega) ⟨820⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j <;> (rw [hsw]; native_decide))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard, push the return/decode continuations `⟨509⟩`/`⟨846⟩`, and run the
    `bytes32` decoder prologue @4702 to the availability `JUMPI` @4714.
    Stack: `[⟨4718⟩, ISZERO(SLT(size-4, 32)), ⟨0⟩, ⟨4⟩, size, ⟨846⟩, ⟨509⟩, sel]`. -/
theorem tlcIsOperationReachLenCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 17)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4714⟩
      [⟨4718⟩, UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩),
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨846⟩, ⟨509⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h820⟩ := tlcReachIsOperation (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h833⟩ := tlcGuardPeelOk (gt := ⟨831⟩) h820 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, h833.push2 ⟨509⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨846⟩ (by native_decide) (by evm_ov)
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
    continuation @846, and enter the compute body @1956 with `[id, ⟨509⟩, sel]`. -/
theorem tlcIsOperationReachCompute {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 17)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1956⟩
      [calldataWord I.calldata 4, ⟨509⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsz : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h4714⟩ := tlcIsOperationReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
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
    |>.push2 ⟨1956⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-! ## EVM: the `_getOperationState` tail from @1967 to the bool-return encoder @509

    Common to all four operation-state leaves: from `[state, 0, 0, id, ⟨509⟩, sel]` at @1967, the
    enum range check (`state ≤ 3`, always taken) and `state != 0` (`EQ; ISZERO`) reach the encoder
    @509 with `[iszero(eq state 0), sel]`. -/
theorem tlcIsOperationTail {cA gh bl σ σ₀ A I} {g : Sat256} {R key : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1967⟩
      [R, ⟨0⟩, ⟨0⟩, key, ⟨509⟩, tlcSelWord I] mem aw ByteArray.empty (cA, σ) k C)
    (hbound : UInt256.isZero (UInt256.gt R ⟨3⟩) ≠ ⟨0⟩) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨509⟩
      [UInt256.isZero (UInt256.eq R ⟨0⟩), tlcSelWord I] mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨3⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.gt (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨1984⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) hbound (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-- The compute body: call `_getOperationState` @2232, resolve its four leaves, and reach the bool
    encoder @509 with `[isOperation(id) as bool word, sel]`.  `t := _timestamps[id]`. -/
theorem tlcIsOperationCompute {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 17)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨509⟩
      [tlcIsOperationBoolWord (tlcGetTimestampWord σ I), tlcSelWord I]
      (twoWordHashMem (calldataWord I.calldata 4) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h1956⟩ := tlcIsOperationReachCompute (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz36 hbig hsize hsel
  -- Set up the helper call and run the mapping keccak, up to the loaded slot value.
  have hkec := evm_run h1956 with [
    jumpdest, push0, dup1, push2 ⟨1967⟩, dup4, push2 ⟨2232⟩, jump (by jump_dest),
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
    have h1967 := evm_run hsl with [
      dup1, push0, sub, push2 ⟨2261⟩, jumpiNT hcond,
      pop, push0, swap3, swap2, pop, pop, jump (by jump_dest) ]
    obtain ⟨_, _, h509⟩ := tlcIsOperationTail h1967 (by decide)
    have hb : UInt256.isZero (UInt256.eq (⟨0⟩ : UInt256) ⟨0⟩)
        = tlcIsOperationBoolWord (tlcGetTimestampWord σ I) := by
      unfold tlcIsOperationBoolWord; rw [if_pos ht0]; decide
    rw [hb] at h509; exact ⟨_, _, h509⟩
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
      have h1967 := evm_run h2269 with [
        jumpiNT hcond1,
        pop, push1 ⟨3⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
      obtain ⟨_, _, h509⟩ := tlcIsOperationTail h1967 (by decide)
      have hb : UInt256.isZero (UInt256.eq (⟨3⟩ : UInt256) ⟨0⟩)
          = tlcIsOperationBoolWord (tlcGetTimestampWord σ I) := by
        unfold tlcIsOperationBoolWord; rw [if_neg ht0]; decide
      rw [hb] at h509; exact ⟨_, _, h509⟩
    · -- `t ≠ 1`: pass the Done `JUMPI` @2269, reach the timestamp check @2286.
      have hcond1 : UInt256.sub (tlcGetTimestampWord σ I) ⟨1⟩ ≠ (⟨0⟩ : UInt256) :=
        u256_sub_ne_zero_of_ne ht1
      have h2286 := evm_run h2269 with [
        jumpiT hcond1 (by jump_dest),
        jumpdest, timestamp, dup2, gt, iszero, push2 ⟨2295⟩ ]
      by_cases htgt : UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp) = ⟨0⟩
      · -- Ready: `t ≤ block.timestamp` ⇒ state 2.
        have hcondr : UInt256.isZero
            (UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp)) ≠ (⟨0⟩ : UInt256) := by
          rw [htgt]; decide
        have h1967 := evm_run h2286 with [
          jumpiT hcondr (by jump_dest),
          jumpdest, pop, push1 ⟨2⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
        obtain ⟨_, _, h509⟩ := tlcIsOperationTail h1967 (by decide)
        have hb : UInt256.isZero (UInt256.eq (⟨2⟩ : UInt256) ⟨0⟩)
            = tlcIsOperationBoolWord (tlcGetTimestampWord σ I) := by
          unfold tlcIsOperationBoolWord; rw [if_neg ht0]; decide
        rw [hb] at h509; exact ⟨_, _, h509⟩
      · -- Waiting: `t > block.timestamp` ⇒ state 1.
        have hcondw : UInt256.isZero
            (UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp)) = (⟨0⟩ : UInt256) :=
          isZero_eq_zero_of_ne htgt
        have h1967 := evm_run h2286 with [
          jumpiNT hcondw,
          pop, push1 ⟨1⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
        obtain ⟨_, _, h509⟩ := tlcIsOperationTail h1967 (by decide)
        have hb : UInt256.isZero (UInt256.eq (⟨1⟩ : UInt256) ⟨0⟩)
            = tlcIsOperationBoolWord (tlcGetTimestampWord σ I) := by
          unfold tlcIsOperationBoolWord; rw [if_neg ht0]; decide
        rw [hb] at h509; exact ⟨_, _, h509⟩

/-- EVM: with zero callvalue and well-sized calldata, `isOperation(id)` returns the bool word
    `_timestamps[id] != 0`. -/
theorem tlcIsOperationX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 17)) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (tlcIsOperationBoolWord (tlcGetTimestampWord σ I))) := by
  obtain ⟨_, _, h509⟩ := tlcIsOperationCompute (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz36 hbig hsize hsel
  exact tlcIsOperationReturnBool h509
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by unfold tlcIsOperationBoolWord; split <;> decide) (by evm_ov)

/-- EVM revert path for a mis-sized calldata: the signed length check `SLT(size-4, 32) = 1` fails the
    `JUMPI`, falling into the decoder's `PUSH0 PUSH0 REVERT` stub. -/
theorem tlcIsOperationDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 17))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4714⟩ := tlcIsOperationReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel
  exact h4714.jumpiNT (by native_decide) (by rw [hslt]; decide) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## ABI decode (a single `bytes32`, exactly like `getTimestamp`) -/

theorem tlcDecodeIsOperation_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (isOperationTransition.params.map Param.name)
      (transitionSignature isOperationTransition).paramTypes I.calldata
      = some (tlcGetTimestampStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = _
  exact decodeCalldata_bytes32_ok hsz36 hbig

theorem tlcDecodeIsOperation_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (isOperationTransition.params.map Param.name)
      (transitionSignature isOperationTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_short hsz4 hshort

theorem tlcDecodeIsOperation_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (isOperationTransition.params.map Param.name)
      (transitionSignature isOperationTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_huge hbig

/-! ## Solm body -/

/-- The Solm `isOperation(id)` body returns the bool `_timestamps[id] != 0`. -/
theorem tlcIsOperationBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcGetTimestampStore I)
      isOperationTransition.body
      (.returned { contract := contract, locals := tlcGetTimestampStore I }
        (initState cA gh bl σ σ₀ g A I)
        (some [(.bool (!((Int.ofNat (tlcGetTimestampWord σ I).toNat : Int) == 0)))])) := by
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
  refine nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) ?_
  unfold isOperationExpr
  simp only [evalExpr?, hstore, EvalResult.bind, bind, evalBinaryOp?, pure]
  simp

/-- ABI-encoding the `isOperation` result bool `_timestamps[id] != 0` is the EVM's returned word. -/
theorem tlcIsOperationBoolEncoding (w : UInt256) :
    encodeReturnValue? boolTy (.bool (!((Int.ofNat w.toNat : Int) == 0)))
      = some (UInt256.toByteArray (tlcIsOperationBoolWord w)) := by
  by_cases hz : w = ⟨0⟩
  · subst hz
    have hb : (!((Int.ofNat (⟨0⟩ : UInt256).toNat : Int) == 0)) = false := by native_decide
    rw [hb]; unfold tlcIsOperationBoolWord; rw [if_pos rfl]
    simpa [boolTy] using boolFalseReturnEncoding
  · have hne : w.toNat ≠ 0 := by intro hh; exact hz (by apply u256_inj; simpa using hh)
    have hb : (!((Int.ofNat w.toNat : Int) == 0)) = true := by simpa using hne
    rw [hb]; unfold tlcIsOperationBoolWord; rw [if_neg hz]
    simpa [boolTy] using boolTrueReturnEncoding

/-! ## Refinement -/

/-- Refinement of `IsOperation` (selector index 17). -/
theorem tlcIsOperationBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 17))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 17) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · -- execute: `36 ≤ size < 2^255 + 4`
        have hword : tlcGetTimestampWord σ_evm I = tlcGetTimestampWord σ_solm I := by
          simp only [tlcGetTimestampWord]
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner
            (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) ⟨0⟩
        exact tlcReEquivExecTransport hcode
          (tlcIsOperationX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize hsel)
          (tlcSelectorDispatchIsOperation hsel)
          (tlcDecodeIsOperation_ok hsz36 hbig)
          (tlcIsOperationBodyReturns (g := Sat256.ofUInt256 g) hwv hsz36) (by rw [← hword]) hAccounts
          (returnEquiv_of_encode (tlcIsOperationBoolEncoding (tlcGetTimestampWord σ_evm I)))
      · -- huge calldata: EVM reverts at the signed length check, Solm decode fails
        have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := Nat.not_lt.mp hbig
        have hrev := tlcIsOperationDecodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
          (solcDecodeLenCheckHuge_4_32 hhuge hsize)
        exact tlcReEquivDecodeFailed hcode hrev (tlcSelectorDispatchIsOperation hsel)
          (tlcDecodeIsOperation_none_huge hhuge)
    · -- short calldata: EVM reverts at the length check, Solm decode fails
      have hshort : I.calldata.size < 36 := by omega
      have hrev := tlcIsOperationDecodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
        (solcDecodeLenCheckShort_4_32 hsz hshort hsize)
      exact tlcReEquivDecodeFailed hcode hrev (tlcSelectorDispatchIsOperation hsel)
        (tlcDecodeIsOperation_none_short hsz hshort)
  · -- nonpayable guard: `callvalue ≠ 0`
    obtain ⟨_, _, h820⟩ := tlcReachIsOperation (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨831⟩) h820 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchIsOperation hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
