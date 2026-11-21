import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ScalarDecode
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.PackedFields

/-!
# Midnight `lossFactor(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 15802; reach lemma `midnightReachLossFactorBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem lossFactorBodyReturns (evm : EVM.State) (key : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm ((∅ : Store).insert "id" (wordBytes32Value key))
      lossFactorTransition.body
      (.returned (calldataFrame contract ((∅ : Store).insert "id" (wordBytes32Value key)) ∅ evm)
        evm (some [.int (Int.ofNat (UInt256.shiftRight
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨1⟩ key))
          (UInt256.ofNat 128)).toNat)])) := by
  apply guardedBytes32MappingFieldGetter (t := .int (.uint ⟨128, by decide⟩))
    (loc := {
      slot := solcMappingSlot ⟨1⟩ key, offset := 16, size := 16,
      hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) evm key
    rfl rfl ?_ ?_ (by decide) (by decide) (by decide) hwv hhi
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨1⟩
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE key))),
      offset := 16, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  · exact storageLocLoad_uint128_high evm _

theorem lossFactorTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat}
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 15820)
      [solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I) σ
      (UInt256.shiftRight (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4)) σ I)
        (UInt256.ofNat 128)).toByteArray := by
  have hr := midnightBlocks.midnight_block_15820 (by simp) rd
  change RDret _ _ _ _
    ((writeWord (mappingMemory (calldataWord I.calldata 4) ⟨1⟩)
      (memLoad (UInt256.ofNat 64) (mappingMemory (calldataWord I.calldata 4) ⟨1⟩)).toNat
      (UInt256.shiftRight (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (mappingMemory (calldataWord I.calldata 4) ⟨1⟩)) σ I)
        (UInt256.ofNat 128))).readWithPadding
      (memLoad (UInt256.ofNat 64) (mappingMemory (calldataWord I.calldata 4) ⟨1⟩)).toNat 32) at hr
  rw [mappingMemory_hash, mappingMemory_freePtr] at hr
  exact (mappingMemory_return _ _ _) ▸ hr

/-- `lossFactor(bytes32)`: the theorem `Correct.lean` routes selector 13 to. -/
theorem midnightLossFactorBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 13)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 13) rfl hsel
  have hd : dispatchMsg contract I.calldata = some lossFactorTransition := by
    apply midnightDispatch_lossFactor <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachLossFactorBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_15802_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_15808_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have hret := lossFactorTraceReturn rd2
        have hdec := midnightDecodeBytes32 "id" (by decide) (by decide) h36 hhi hsize
        have hbody := lossFactorBodyReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
          (calldataWord I.calldata 4) hwv hhi
        exact hret.reEquivExecution hcode hd hdec hbody
          (returnEquiv_of_encode (uintReturnEncoding ⟨128, by decide⟩ _
            (shiftRight128_lt _)))
      · have rd2 := midnightBlocks.midnight_block_15808_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 32) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h36) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeScalar_none_short "id" (.bytes abiBytes32Width)
            hsz (Nat.lt_of_not_ge h36) hsize)
    · have rd2 := midnightBlocks.midnight_block_15808_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 32) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeScalar_none_huge "id" (.bytes abiBytes32Width)
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_15802_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (lossFactorTransition.params.map Param.name)
        (transitionSignature lossFactorTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)


end Benchmarks.Midnight
