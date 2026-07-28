import Benchmarks.OpenZeppelinBench.TimelockController.Storage
import Benchmarks.OpenZeppelinBench.TimelockController.SolmDispatch

/-!
# OpenZeppelin TimelockController `getTimestamp(bytes32)` refinement

`getTimestamp` is a public non-payable `uint256` getter over the `_timestamps` mapping (base slot 1),
keyed by an ABI-decoded `bytes32` id.  Selector index 9, dispatch group G98 arm 2, body pc 1307.
The runtime peels its own non-payable guard, runs the modern word-argument decoder (`@4702`, a signed
`SLT(calldatasize - 4, 32)` availability check), hashes the mapping slot `keccak(id ‖ 1)`, `SLOAD`s
it, and returns the 32-byte word.  Template for arg-taking `uint256` mapping getters.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace OpenZeppelinBench.TimelockController

/-! ## Decoded argument, storage word, and ABI decode -/

/-- The ABI-decoded `bytes32` id (the 32-byte calldata word at offset 4), as a mapping key value. -/
abbrev tlcGetTimestampKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32)

/-- The decoded local store bound by `getTimestamp(bytes32 id)`. -/
abbrev tlcGetTimestampStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "id" (.fixedBytes abiBytes32Width ((I.calldata.toList.drop 4).take 32))

/-- The stored `_timestamps[id]` value (mapping slot `keccak(id ‖ 1)`). -/
def tlcGetTimestampWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4))

/-- The decoded `bytes32` key hashes to the same word the EVM `CALLDATALOAD(4)` loads. -/
theorem tlcGetTimestampKey_eq (I : ExecutionEnv) (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (tlcGetTimestampKey I) = calldataWord I.calldata 4 := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have key_eq : tlcGetTimestampKey I
      = .fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32))) := by
    simp only [tlcGetTimestampKey]
    rw [show abiBytes32Width = (⟨31, by decide⟩ : Fin 32) from rfl,
      toBytesBE_bytesToWord_of_length hlen]
  rw [key_eq, keyValueToWord_fixedBytes32, decode_word_at_eq_any I.calldata 4 (by omega)]

theorem tlcDecodeGetTimestamp_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4) :
    decodeCalldataWithMode config.abiDecodeMode (getTimestampTransition.params.map Param.name)
      (transitionSignature getTimestampTransition).paramTypes I.calldata
      = some (tlcGetTimestampStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = _
  exact decodeCalldata_bytes32_ok hsz36 hbig

theorem tlcDecodeGetTimestamp_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (getTimestampTransition.params.map Param.name)
      (transitionSignature getTimestampTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_short hsz4 hshort

theorem tlcDecodeGetTimestamp_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (getTimestampTransition.params.map Param.name)
      (transitionSignature getTimestampTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["id"] [bytes32] I.calldata = none
  exact decodeCalldata_bytes32_none_huge hbig

/-! ## EVM: reach the body and the length check -/

/-- Reach the `getTimestamp` body pc 1307 (G98 arm 2). -/
theorem tlcReachGetTimestamp {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 9)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1307⟩
      [tlcSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : tlcSelWord I = ⟨0xd45c4435⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xd4 0x5c 0x44 0x35 ⟨0xd45c4435⟩ (by native_decide)
      (by simpa [tlcSelBytes] using hsel)
  exact tlcReachG98Body 2 (by omega) ⟨1307⟩ hcode hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
    (by intro j hj; interval_cases j <;> (rw [hsw]; native_decide))
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide)

/-- Peel the non-payable guard and run the decoder prologue to the `SLT` availability `JUMPI` @4714.
    Stack: `[⟨4718⟩, ISZERO(SLT(size-4, 32)), ⟨0⟩, ⟨4⟩, size, ⟨1333⟩, ⟨581⟩, sel]`. -/
theorem tlcGetTimestampReachLenCheck {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 9)) :
    ∃ k C, RD timelockControllerBenchBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4714⟩
      [⟨4718⟩, UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩),
        ⟨0⟩, ⟨4⟩, UInt256.ofNat I.calldata.size, ⟨1333⟩, ⟨581⟩, tlcSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h1307⟩ := tlcReachGetTimestamp (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize hsel
  obtain ⟨_, _, h1320⟩ := tlcGuardPeelOk (gt := ⟨1318⟩) h1307 hwv (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by jump_dest)
    (by native_decide) (by native_decide)
  exact ⟨_, _, h1320.push2 ⟨581⟩ (by native_decide) (by evm_ov)
    |>.push2 ⟨1333⟩ (by native_decide) (by evm_ov)
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

/-- EVM: with zero callvalue and a well-sized calldata, `getTimestamp(id)` returns `_timestamps[id]`. -/
theorem tlcGetTimestampX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size) (hsel : selIs I (tlcSelBytes 9)) :
    RDret timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (tlcGetTimestampWord σ I)) := by
  have hsz : 4 ≤ I.calldata.size := by omega
  obtain ⟨_, _, h4714⟩ := tlcGetTimestampReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel
  have h1333 := h4714.jumpiT (by native_decide)
      (by rw [solcDecodeLenCheckOk_4_32 hsz36 hbig hsize]; decide) (by jump_dest) (by evm_ov)
    |>.jumpdest (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.calldataload (by native_decide) (by evm_ov)
    |>.swap2 (by native_decide) (by evm_ov)
    |>.swap1 (by native_decide) (by evm_ov)
    |>.pop (by native_decide) (by evm_ov)
    |>.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, h581⟩ := tlcMappingGetSlot1 h1333 (by jump_dest) (by simp)
  exact tlcReturnWordFromMem h581 (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
    (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64) (by simp)

/-- EVM revert path for a mis-sized calldata: the signed length check `SLT(size-4, 32) = 1`
    fails the `JUMPI`, falling into the `PUSH0 PUSH0 REVERT` stub. -/
theorem tlcGetTimestampDecodeRevert {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = timelockControllerBenchBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (tlcSelBytes 9))
    (hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩) :
    RDrev timelockControllerBenchBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, h4714⟩ := tlcGetTimestampReachLenCheck (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hsel
  exact h4714.jumpiNT (by native_decide) (by rw [hslt]; decide) (by evm_ov)
    |>.revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

/-! ## Solm body -/

/-- The Solm `getTimestamp(id)` body returns `_timestamps[id]`. -/
theorem tlcGetTimestampBodyReturns {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) (hsz36 : 36 ≤ I.calldata.size) :
    ExecTransitionBody config contract (initState cA gh bl σ σ₀ g A I) (tlcGetTimestampStore I)
      getTimestampTransition.body
      (.returned { contract := contract, locals := tlcGetTimestampStore I }
        (initState cA gh bl σ σ₀ g A I)
        (some [(.int (Int.ofNat (tlcGetTimestampWord σ I).toNat))])) := by
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
  refine nonpayableReturnExprBodyReturns (by simp only [initState]; exact hwv) ?_
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

/-! ## Refinement -/

theorem tlcGetTimestampBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = timelockControllerBenchBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsel : selIs I (tlcSelBytes 9))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (tlcSelBytes 9) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz36 : 36 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · -- execute: `36 ≤ size < 2^255 + 4`
        have hword : tlcGetTimestampWord σ_evm I = tlcGetTimestampWord σ_solm I := by
          simp only [tlcGetTimestampWord]
          exact accountMapEquiv_storage_findD hAccounts I.codeOwner
            (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) ⟨0⟩
        exact tlcReEquivExecTransport hcode
          (tlcGetTimestampX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz36 hbig hsize hsel)
          (tlcSelectorDispatchGetTimestamp hsel) (tlcDecodeGetTimestamp_ok hsz36 hbig)
          (tlcGetTimestampBodyReturns (g := Sat256.ofUInt256 g) hwv hsz36) (by rw [← hword]) hAccounts
          (returnEquiv_of_encode
            (by simpa [uint256] using uint256ReturnEncoding (tlcGetTimestampWord σ_evm I)))
      · -- huge calldata: `2^255 + 4 ≤ size`; EVM reverts at the signed length check, Solm decode fails
        have hhuge : 2 ^ 255 + 4 ≤ I.calldata.size := Nat.not_lt.mp hbig
        have hrev := tlcGetTimestampDecodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
          (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
          (solcDecodeLenCheckHuge_4_32 hhuge hsize)
        exact tlcReEquivDecodeFailed hcode hrev (tlcSelectorDispatchGetTimestamp hsel)
          (tlcDecodeGetTimestamp_none_huge hhuge)
    · -- short calldata: `size < 36`; EVM reverts at the length check, Solm decode fails
      have hshort : I.calldata.size < 36 := by omega
      have hrev := tlcGetTimestampDecodeRevert (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
        (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel
        (solcDecodeLenCheckShort_4_32 hsz hshort hsize)
      exact tlcReEquivDecodeFailed hcode hrev (tlcSelectorDispatchGetTimestamp hsel)
        (tlcDecodeGetTimestamp_none_short hsz hshort)
  · -- nonpayable guard: `callvalue ≠ 0`
    obtain ⟨_, _, h1307⟩ := tlcReachGetTimestamp (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
    have hrev := tlcGuardPeelRev (gt := ⟨1318⟩) h1307 hwv (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
    exact tlcNonpayableRevert hcode hrev (tlcSelectorDispatchGetTimestamp hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end OpenZeppelinBench.TimelockController
