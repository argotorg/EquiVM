import Benchmarks.OpenZeppelinBench.TimelockController.IsOperation
import Benchmarks.OpenZeppelinBench.TimelockController.IsOperationDone
import Benchmarks.OpenZeppelinBench.TimelockController.GetOperationState
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Dispatch
import Benchmarks.OpenZeppelinBench.TimelockController.Routines

/-!
# OpenZeppelin TimelockController `isOperationReady(bytes32)` refinement

Near-copy of `isOperationDone`.  Both decode one `bytes32 id`, call the SAME inlined
`_getOperationState` helper @2232 (the 4-way state), then compare the state.  `isOperationReady`
returns the `bool` `state == Ready(2)`, i.e. `1 < _timestamps[id] ∧ _timestamps[id] ≤ block.timestamp`.

Differs from `isOperationDone` (imported, reused read-only) in: (a) body pc 614 (G350 arm 1);
(b) the compute body @1869 pushes the enum constant `2` (not `3`) but shares `isOperationDone`'s tail
JUMPDEST @1882, so the post-helper `EQ` tests `state == 2`; (c) the Solm side is the short-circuiting
`_timestamps[id] > 1 && _timestamps[id] <= block.timestamp`.  The front half (guard peel, decoder,
mapping keccak), the four helper leaves, and the bool-return encoder @509 are imported unchanged.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-- The 32-byte word `isOperationReady` returns for a stored timestamp `t` and block timestamp word
    `tsW`: `1` iff `1 < t ∧ t ≤ tsW` (the operation state is `Ready`). -/
def tlcIsOperationReadyBoolWord (t tsW : UInt256) : UInt256 :=
  if 1 < t.toNat ∧ t.toNat ≤ tsW.toNat then ⟨1⟩ else ⟨0⟩

/-! ## EVM: reach the body and the decoder length check -/

/-- Reach the `isOperationReady` body pc 614 (G350 arm 1). -/
theorem tlcReachIsOperationReady {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 16)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨614⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0x13bc9f20⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x13 0xbc 0x9f 0x20 ⟨0x13bc9f20⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG350Body 1 (by omega) ⟨614⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j; rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard, push the return/decode continuations `⟨509⟩`/`⟨640⟩`, and run the
    `bytes32` decoder prologue @4702 to the availability `JUMPI` @4714. -/
theorem tlcIsOperationReadyReachLenCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 16)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4714⟩
      [⟨4718⟩, UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩),
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨640⟩, ⟨509⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h614⟩ := tlcReachIsOperationReady (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h627⟩ := tlcGuardPeelOk (gt := ⟨625⟩) h614 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, h627.push2 ⟨509⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨640⟩ (by native_decide) (by evm_ov)
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

/-- After the length check passes, finish the decoder, jump back to the decode continuation @640,
    and enter the compute body @1869 with `[id, ⟨509⟩, sel]`. -/
theorem tlcIsOperationReadyReachCompute {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 16)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1869⟩
      [calldataWord I.calldata 4, ⟨509⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsz : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h4714⟩ := tlcIsOperationReadyReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
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
    |>.push2 ⟨1869⟩ (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-! ## EVM: the `isOperationReady` tail from @1882 to the bool-return encoder @509

    Shares `isOperationDone`'s tail JUMPDEST @1882: from `[state, 2, 0, id, ⟨509⟩, sel]`, the enum
    range check (`state ≤ 3`, always taken) and `state == 2` (`EQ`) reach the encoder @509 with
    `[eq state 2, sel]`. -/
theorem tlcIsOperationReadyTail {cA gh bl σ σ₀ A I} {g : Sat256} {R key : UInt256}
    {mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (h : RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1882⟩
      [R, ⟨2⟩, ⟨0⟩, key, ⟨509⟩, tlcSelWord I] mem aw ByteArray.empty (cA, σ) k C)
    (hbound : UInt256.isZero (UInt256.gt R ⟨3⟩) ≠ ⟨0⟩) :
    ∃ k' C', RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨509⟩
      [UInt256.eq R ⟨2⟩, tlcSelWord I] mem aw ByteArray.empty (cA, σ) k' C' := by
  exact ⟨_, _, h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨3⟩ (by native_decide) (by evm_ov)
    |>.dup2 (by native_decide) (by evm_ov)
    |>.gt (by native_decide) (by evm_ov)
    |>.iszero (by native_decide) (by evm_ov)
    |>.push2 ⟨1899⟩ (by native_decide) (by evm_ov)
    |>.jumpiT (by native_decide) hbound (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.eq (by native_decide) (by evm_ov)
    |>.swap3 (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-- The compute body: call `_getOperationState` @2232, resolve its four leaves, and reach the bool
    encoder @509 with `[isOperationReady(id) as bool word, sel]`.  `t := _timestamps[id]`. -/
theorem tlcIsOperationReadyCompute {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 16)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨509⟩
      [tlcIsOperationReadyBoolWord (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp),
        tlcSelWord I]
      (twoWordHashMem (calldataWord I.calldata 4) ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h1869⟩ := tlcIsOperationReadyReachCompute (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz36 hbig hsize hsel
  -- Set up the helper call and run the mapping keccak, up to the loaded slot value.
  have hkec := evm_run h1869 with [
    jumpdest, push0, push1 ⟨2⟩, jumpdest, push2 ⟨1882⟩, dup4, push2 ⟨2232⟩, jump (by jump_dest),
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
    have h1882 := evm_run hsl with [
      dup1, push0, sub, push2 ⟨2261⟩, jumpiNT hcond,
      pop, push0, swap3, swap2, pop, pop, jump (by jump_dest) ]
    obtain ⟨_, _, h509⟩ := tlcIsOperationReadyTail h1882 (by decide)
    have hb : UInt256.eq (⟨0⟩ : UInt256) ⟨2⟩
        = tlcIsOperationReadyBoolWord (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp) := by
      unfold tlcIsOperationReadyBoolWord
      rw [if_neg (fun h => absurd h.1 (show ¬ 1 < (tlcGetTimestampWord σ I).toNat by rw [ht0]; decide))]
      decide
    rw [hb] at h509; exact ⟨_, _, h509⟩
  · -- `t ≠ 0`: pass the Unset `JUMPI` @2253, reach the Done check @2269.
    have hne0 : (tlcGetTimestampWord σ I).toNat ≠ 0 :=
      fun hh => ht0 (by apply u256_inj; simpa using hh)
    have hcond0 : UInt256.sub ⟨0⟩ (tlcGetTimestampWord σ I) ≠ (⟨0⟩ : UInt256) :=
      u256_zero_sub_ne_zero ht0
    have h2269 := evm_run hsl with [
      dup1, push0, sub, push2 ⟨2261⟩, jumpiT hcond0 (by jump_dest),
      jumpdest, push1 ⟨1⟩, dup2, sub, push2 ⟨2278⟩ ]
    by_cases ht1 : tlcGetTimestampWord σ I = ⟨1⟩
    · -- Done: `t = 1` ⇒ state 3.
      have hcond1 : UInt256.sub (tlcGetTimestampWord σ I) ⟨1⟩ = (⟨0⟩ : UInt256) := by
        rw [ht1]; exact u256_sub_self ⟨1⟩
      have h1882 := evm_run h2269 with [
        jumpiNT hcond1,
        pop, push1 ⟨3⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
      obtain ⟨_, _, h509⟩ := tlcIsOperationReadyTail h1882 (by decide)
      have hb : UInt256.eq (⟨3⟩ : UInt256) ⟨2⟩
          = tlcIsOperationReadyBoolWord (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp) := by
        unfold tlcIsOperationReadyBoolWord
        rw [if_neg (fun h => absurd h.1 (show ¬ 1 < (tlcGetTimestampWord σ I).toNat by rw [ht1]; decide))]
        decide
      rw [hb] at h509; exact ⟨_, _, h509⟩
    · -- `t ≠ 1`: pass the Done `JUMPI` @2269, reach the timestamp check @2286.
      have hne1 : (tlcGetTimestampWord σ I).toNat ≠ 1 :=
        fun hh => ht1 (by apply u256_inj; simpa using hh)
      have h2gt : 1 < (tlcGetTimestampWord σ I).toNat := by omega
      have hcond1 : UInt256.sub (tlcGetTimestampWord σ I) ⟨1⟩ ≠ (⟨0⟩ : UInt256) :=
        u256_sub_ne_zero_of_ne ht1
      have h2286 := evm_run h2269 with [
        jumpiT hcond1 (by jump_dest),
        jumpdest, timestamp, dup2, gt, iszero, push2 ⟨2295⟩ ]
      by_cases htgt : UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp) = ⟨0⟩
      · -- Ready: `t ≤ block.timestamp` ⇒ state 2.
        have hle : (tlcGetTimestampWord σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat := by
          by_contra hh
          rw [ugt_one (Nat.lt_of_not_le hh)] at htgt; exact absurd htgt (by decide)
        have hcondr : UInt256.isZero
            (UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp)) ≠ (⟨0⟩ : UInt256) := by
          rw [htgt]; decide
        have h1882 := evm_run h2286 with [
          jumpiT hcondr (by jump_dest),
          jumpdest, pop, push1 ⟨2⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
        obtain ⟨_, _, h509⟩ := tlcIsOperationReadyTail h1882 (by decide)
        have hb : UInt256.eq (⟨2⟩ : UInt256) ⟨2⟩
            = tlcIsOperationReadyBoolWord (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp) := by
          unfold tlcIsOperationReadyBoolWord; rw [if_pos ⟨h2gt, hle⟩]; decide
        rw [hb] at h509; exact ⟨_, _, h509⟩
      · -- Waiting: `t > block.timestamp` ⇒ state 1.
        have hlt : ¬ (tlcGetTimestampWord σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat :=
          fun hle => htgt (ugt_zero hle)
        have hcondw : UInt256.isZero
            (UInt256.gt (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp)) = (⟨0⟩ : UInt256) :=
          isZero_eq_zero_of_ne htgt
        have h1882 := evm_run h2286 with [
          jumpiNT hcondw,
          pop, push1 ⟨1⟩, swap3, swap2, pop, pop, jump (by jump_dest) ]
        obtain ⟨_, _, h509⟩ := tlcIsOperationReadyTail h1882 (by decide)
        have hb : UInt256.eq (⟨1⟩ : UInt256) ⟨2⟩
            = tlcIsOperationReadyBoolWord (tlcGetTimestampWord σ I) (UInt256.ofNat I.header.timestamp) := by
          unfold tlcIsOperationReadyBoolWord; rw [if_neg (fun h => hlt h.2)]; decide
        rw [hb] at h509; exact ⟨_, _, h509⟩

/-- EVM: with zero callvalue and well-sized calldata, `isOperationReady(id)` returns the bool word
    `1 < _timestamps[id] ∧ _timestamps[id] ≤ block.timestamp`. -/
theorem tlcIsOperationReadyX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 16)) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (tlcIsOperationReadyBoolWord (tlcGetTimestampWord σ I)
        (UInt256.ofNat I.header.timestamp))) := by
  obtain ⟨_, _, h509⟩ := tlcIsOperationReadyCompute (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz36 hbig hsize hsel
  exact tlcIsOperationReturnBool h509
    (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by unfold tlcIsOperationReadyBoolWord; split <;> decide) (by evm_ov)

/-- EVM revert path for a mis-sized calldata: the signed length check fails the `JUMPI`, falling into
    the decoder's `PUSH0 PUSH0 REVERT` stub. -/
theorem tlcIsOperationReadyDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 16))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4714⟩ := tlcIsOperationReadyReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel
  exact h4714.jumpiNT (by native_decide) (by rw [hslt]; decide) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## ABI decode (a single `bytes32`, exactly like `isOperationDone`) -/

theorem tlcDecodeIsOperationReady_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (isOperationReadyTransition.params.map Param.name)
      (transitionSignature isOperationReadyTransition).paramTypes I.calldata
      = some (tlcGetTimestampStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = _
  exact decodeCalldata_bytes32_ok hsz36 hbig

theorem tlcDecodeIsOperationReady_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (isOperationReadyTransition.params.map Param.name)
      (transitionSignature isOperationReadyTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_short hsz4 hshort

theorem tlcDecodeIsOperationReady_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (isOperationReadyTransition.params.map Param.name)
      (transitionSignature isOperationReadyTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_huge hbig

/-! ## Solm body -/

/-- The Solm `isOperationReady(id)` body returns the short-circuiting bool
    `_timestamps[id] > 1 && _timestamps[id] <= block.timestamp`. -/
theorem tlcIsOperationReadyBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcGetTimestampStore I)
      isOperationReadyTransition.body
      (.returned { contract := contract, locals := tlcGetTimestampStore I }
        (initState cA gh bl σ σ₀ g A I)
        (some [(.bool (decide (1 < (tlcGetTimestampWord σ I).toNat
          ∧ (tlcGetTimestampWord σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat)))])) := by
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
  refine nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) ?_
  unfold isOperationReadyExpr isOperationPendingExpr doneTimestamp
  by_cases hp : 1 < (tlcGetTimestampWord σ I).toNat
  · by_cases hle : (tlcGetTimestampWord σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat
    · have hpI : decide ((Int.ofNat (tlcGetTimestampWord σ I).toNat : Int) > 1) = true :=
        decide_eq_true_eq.mpr (Int.ofNat_lt.mpr hp)
      have hleI : decide ((Int.ofNat (tlcGetTimestampWord σ I).toNat : Int)
          ≤ Int.ofNat (UInt256.ofNat I.header.timestamp).toNat) = true :=
        decide_eq_true_eq.mpr (Int.ofNat_le.mpr hle)
      have hr : decide (1 < (tlcGetTimestampWord σ I).toNat
          ∧ (tlcGetTimestampWord σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat) = true :=
        decide_eq_true_eq.mpr ⟨hp, hle⟩
      simp only [evalExpr?, hstore, henv, EvalResult.bind, bind, pure, evalBinaryOp?, gt_iff_lt,
        hpI, hleI, hr]
    · have hpI : decide ((Int.ofNat (tlcGetTimestampWord σ I).toNat : Int) > 1) = true :=
        decide_eq_true_eq.mpr (Int.ofNat_lt.mpr hp)
      have hleI : decide ((Int.ofNat (tlcGetTimestampWord σ I).toNat : Int)
          ≤ Int.ofNat (UInt256.ofNat I.header.timestamp).toNat) = false :=
        decide_eq_false (fun hh => hle (Int.ofNat_le.mp hh))
      have hr : decide (1 < (tlcGetTimestampWord σ I).toNat
          ∧ (tlcGetTimestampWord σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat) = false :=
        decide_eq_false (fun h => hle h.2)
      simp only [evalExpr?, hstore, henv, EvalResult.bind, bind, pure, evalBinaryOp?, gt_iff_lt,
        hpI, hleI, hr]
  · have hpI : decide ((Int.ofNat (tlcGetTimestampWord σ I).toNat : Int) > 1) = false :=
      decide_eq_false (fun hh => hp (Int.ofNat_lt.mp hh))
    have hr : decide (1 < (tlcGetTimestampWord σ I).toNat
        ∧ (tlcGetTimestampWord σ I).toNat ≤ (UInt256.ofNat I.header.timestamp).toNat) = false :=
      decide_eq_false (fun h => hp h.1)
    simp only [evalExpr?, hstore, henv, EvalResult.bind, bind, pure, evalBinaryOp?, gt_iff_lt,
      hpI, hr]

/-- ABI-encoding the `isOperationReady` result is the EVM's returned word. -/
theorem tlcIsOperationReadyBoolEncoding (t tsW : UInt256) :
    encodeReturnValue? boolTy (.bool (decide (1 < t.toNat ∧ t.toNat ≤ tsW.toNat)))
      = some (UInt256.toByteArray (tlcIsOperationReadyBoolWord t tsW)) := by
  by_cases hc : 1 < t.toNat ∧ t.toNat ≤ tsW.toNat
  · rw [decide_eq_true hc]; unfold tlcIsOperationReadyBoolWord; rw [if_pos hc]
    simpa [boolTy] using boolTrueReturnEncoding
  · rw [decide_eq_false hc]; unfold tlcIsOperationReadyBoolWord; rw [if_neg hc]
    simpa [boolTy] using boolFalseReturnEncoding

/-! ## Refinement -/

/-- Refinement of `IsOperationReady` (selector index 16). -/
theorem tlcIsOperationReadyBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 16))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 16) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · -- execute: `36 ≤ size < 2^255 + 4`
        have hword : tlcGetTimestampWord σ_evm I = tlcGetTimestampWord σ_solm I := by
          simp only [tlcGetTimestampWord]
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner
            (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) ⟨0⟩
        exact tlcReEquivExecTransport hcode
          (tlcIsOperationReadyX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize hsel)
          (tlcSelectorDispatchIsOperationReady hsel)
          (tlcDecodeIsOperationReady_ok hsz36 hbig)
          (tlcIsOperationReadyBodyReturns (g := Sat256.ofUInt256 g) hwv hsz36) (by rw [← hword])
          hAccounts
          (returnEquiv_of_encode (tlcIsOperationReadyBoolEncoding (tlcGetTimestampWord σ_evm I)
            (UInt256.ofNat I.header.timestamp)))
      · -- huge calldata: EVM reverts at the signed length check, Solm decode fails
        have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := Nat.not_lt.mp hbig
        have hrev := tlcIsOperationReadyDecodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
          (solcDecodeLenCheckHuge_4_32 hhuge hsize)
        exact tlcReEquivDecodeFailed hcode hrev (tlcSelectorDispatchIsOperationReady hsel)
          (tlcDecodeIsOperationReady_none_huge hhuge)
    · -- short calldata: EVM reverts at the length check, Solm decode fails
      have hshort : I.calldata.size < 36 := by omega
      have hrev := tlcIsOperationReadyDecodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
        (solcDecodeLenCheckShort_4_32 hsz hshort hsize)
      exact tlcReEquivDecodeFailed hcode hrev (tlcSelectorDispatchIsOperationReady hsel)
        (tlcDecodeIsOperationReady_none_short hsz hshort)
  · -- nonpayable guard: `callvalue ≠ 0`
    obtain ⟨_, _, h614⟩ := tlcReachIsOperationReady (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨625⟩) h614 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchIsOperationReady hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
