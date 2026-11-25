import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ScalarDecode
import Benchmarks.Midnight.MappingMemory

variable {fork : Ethereum.Fork}

/-!
# Midnight `isLiquidationCursorEnabled(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9441; reach lemma `midnightReachIsLiquidationCursorEnabledBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem isLiquidationCursorEnabledBodyReturns (evm : EVM.State) (key : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork config contract evm ((∅ : Store).insert "arg0" (.int key.toNat))
      isLiquidationCursorEnabledTransition.body
      (.returned (calldataFrame contract ((∅ : Store).insert "arg0" (.int key.toNat)) ∅ evm) evm
        (some [wordToElem .bool (UInt256.land
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨8⟩ key))
          ⟨255⟩)])) := by
  apply guardedBoolMappingGetter evm key rfl rfl ?_ (by decide) (by decide) hwv hhi
  change some (StorageAddr.leaf (boolOffset0Loc (solcMappingSlot ⟨8⟩
    (keyValueToWord (.int (Int.ofNat key.toNat)))))) = _
  rw [keyValueToWord_uint256]

theorem isLiquidationCursorEnabledTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat}
    (rd : RD fork midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 9459)
      [solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret fork midnightBytecode g (initState σ σ₀ g A I) σ
      (UInt256.isZero (UInt256.isZero (UInt256.land
        (solcSlotWordAt (solcMappingSlot ⟨8⟩ (calldataWord I.calldata 4)) σ I) ⟨255⟩))).toByteArray := by
  have hr := midnightBlocks.midnight_block_9459 (by simp) rd
  simp only [midnightEntryMemory_zero] at hr
  change RDret fork _ _ _ _
    ((writeWord (mappingMemory (calldataWord I.calldata 4) ⟨8⟩)
      (memLoad (UInt256.ofNat 64) (mappingMemory (calldataWord I.calldata 4) ⟨8⟩)).toNat
      (UInt256.isZero (UInt256.isZero (UInt256.land
        (solcSlotWordAt (keccakWord
          (memLoad (UInt256.ofNat 800) (mappingMemory (calldataWord I.calldata 4) ⟨8⟩))
          (UInt256.ofNat 64) (mappingMemory (calldataWord I.calldata 4) ⟨8⟩)) σ I) ⟨255⟩)))).readWithPadding
      (memLoad (UInt256.ofNat 64) (mappingMemory (calldataWord I.calldata 4) ⟨8⟩)).toNat 32) at hr
  rw [mappingMemory_zero, mappingMemory_hash, mappingMemory_freePtr] at hr
  exact (mappingMemory_return _ _ _) ▸ hr

/-- `isLiquidationCursorEnabled(uint256)`: the theorem `Correct.lean` routes selector 24 to. -/
theorem midnightIsLiquidationCursorEnabledBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 24)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 24) rfl hsel
  have hd : dispatchMsg contract I.calldata = some isLiquidationCursorEnabledTransition := by
    apply midnightDispatch_isLiquidationCursorEnabled <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachIsLiquidationCursorEnabledBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_9441_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_9447_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have hret := isLiquidationCursorEnabledTraceReturn rd2
        have hdec := midnightDecodeUint256 "arg0" (by decide) (by decide) h36 hhi hsize
        have hbody := isLiquidationCursorEnabledBodyReturns (fork := fork) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (calldataWord I.calldata 4) hwv hhi
        exact hret.reEquivExecution hcode hd hdec hbody
          (returnEquiv_of_encode (boolWordReturnEncoding
            (solcSlotWordAt (solcMappingSlot ⟨8⟩ (calldataWord I.calldata 4)) σ I)))
      · have rd2 := midnightBlocks.midnight_block_9447_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 32) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h36) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeScalar_none_short "arg0" (.int (.uint ⟨256, by decide⟩))
            hsz (Nat.lt_of_not_ge h36) hsize)
    · have rd2 := midnightBlocks.midnight_block_9447_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 32) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeScalar_none_huge "arg0" (.int (.uint ⟨256, by decide⟩))
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_9441_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (isLiquidationCursorEnabledTransition.params.map Param.name)
        (transitionSignature isLiquidationCursorEnabledTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
