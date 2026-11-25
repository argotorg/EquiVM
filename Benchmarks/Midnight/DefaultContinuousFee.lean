import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.MappingMemory

variable {fork : Ethereum.Fork}

/-!
# Midnight `defaultContinuousFee(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 17989; reach lemma `midnightReachDefaultContinuousFeeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem defaultContinuousFeeBodyReturns (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody fork config contract evm
      ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat key.toNat)))
      defaultContinuousFeeTransition.body
      (.returned (calldataFrame contract
        ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat key.toNat))) ∅ evm) evm
        (some [.int (Int.ofNat (UInt256.land
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨5⟩ key))
          (UInt256.ofNat (2^32 - 1))).toNat)])) := by
  apply guardedAddressMappingGetter (t := .int (.uint ⟨32, by decide⟩))
    (loc := {
      slot := solcMappingSlot ⟨5⟩ key, offset := 0, size := 4,
      hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }) evm key
    rfl rfl ?_ ?_ (by decide) (by decide) hwv hhi
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨5⟩ (keyValueToWord (.address (AccountAddress.ofNat key.toNat))),
      offset := 0, size := 4, hbound := by decide, type := .int (.uint ⟨32, by decide⟩) }) = _
    rw [keyValueToWord_address_of_canonical key hcanon]
  · exact storageLocLoad_uint_offset0 evm _ 4 ⟨32, by decide⟩ (by decide) (by decide)

theorem defaultContinuousFeeTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {key : UInt256}
    (hcanon : key.toNat < EVM.addressModulus)
    (rd : RD fork midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 18022)
      [key, solcAddrMask, solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret fork midnightBytecode g (initState σ σ₀ g A I) σ
      (UInt256.land (solcSlotWordAt (solcMappingSlot ⟨5⟩ key) σ I)
        (UInt256.ofNat (2^32 - 1))).toByteArray := by
  have hr := midnightBlocks.midnight_block_18022 (by simp) rd
  simp only [solcAddrMask_clean hcanon] at hr
  have hmem : (UInt256.ofNat 5).toByteArray.write 0
      (key.toByteArray.write 0 midnightEntryMemory (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32 = mappingMemory key ⟨5⟩ := rfl
  rw [hmem, mappingMemory_hash, mappingMemory_freePtr] at hr
  exact (mappingMemory_return _ _ _) ▸ hr

/-- `defaultContinuousFee(address)`: the theorem `Correct.lean` routes selector 2 to. -/
theorem midnightDefaultContinuousFeeBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 2)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 2) rfl hsel
  have hd : dispatchMsg contract I.calldata = some defaultContinuousFeeTransition := by
    apply midnightDispatch_defaultContinuousFee <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachDefaultContinuousFeeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_17989_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_17995_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_18007 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_18007_stack, addressMask_computed] at rd3
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) hcanon rd3
          have hret := defaultContinuousFeeTraceReturn hcanon rd4
          have hdec := midnightDecodeAddress "arg0" (by decide) (by decide)
            h36 hhi hsize hcanon
          have hbody := defaultContinuousFeeBodyReturns (fork := fork)
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) (calldataWord I.calldata 4) hcanon hwv hhi
          exact hret.reEquivExecution hcode hd hdec hbody
            (returnEquiv_of_encode (uintReturnEncoding ⟨32, by decide⟩ _
              (u256LandMaskToNatLtOfToNat _ _ (by decide))))
        · have hr := midnightAddress4_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeAddress_none_noncanon "arg0" h36 hhi hsize hcanon)
      · have rd2 := midnightBlocks.midnight_block_17995_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 32) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h36) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeScalar_none_short "arg0" .address
            hsz (Nat.lt_of_not_ge h36) hsize)
    · have rd2 := midnightBlocks.midnight_block_17995_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 32) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeScalar_none_huge "arg0" .address
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_17989_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (defaultContinuousFeeTransition.params.map Param.name)
        (transitionSignature defaultContinuousFeeTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)



end Benchmarks.Midnight
