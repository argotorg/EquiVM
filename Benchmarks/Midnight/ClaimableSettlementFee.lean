import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.MappingMemory

/-!
# Midnight `claimableSettlementFee(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 15976; reach lemma `midnightReachClaimableSettlementFeeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem claimableSettlementFeeBodyReturns (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat key.toNat)))
      claimableSettlementFeeTransition.body
      (.returned (calldataFrame contract
        ((∅ : Store).insert "arg0" (.address (AccountAddress.ofNat key.toNat))) ∅ evm) evm
        (some [.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨6⟩ key)).toNat)])) := by
  apply guardedAddressMappingGetter (t := .int (.uint ⟨256, by decide⟩))
    (loc := {
      slot := solcMappingSlot ⟨6⟩ key, offset := 0, size := 32,
      hbound := by decide, type := .int (.uint ⟨256, by decide⟩) }) evm key
    rfl rfl ?_ ?_ (by decide) (by decide) hwv hhi
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot ⟨6⟩ (keyValueToWord (.address (AccountAddress.ofNat key.toNat))),
      offset := 0, size := 32, hbound := by decide, type := .int (.uint ⟨256, by decide⟩) }) = _
    rw [keyValueToWord_address_of_canonical key hcanon]
  · exact storageLocLoad_uint256 evm _

theorem claimableSettlementFeeTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {key : UInt256}
    (hcanon : key.toNat < EVM.addressModulus)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 16009)
      [key, solcAddrMask, solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I) σ
      (solcSlotWordAt (solcMappingSlot ⟨6⟩ key) σ I).toByteArray := by
  have hr := midnightBlocks.midnight_block_16009 (by simp) rd
  simp only [solcAddrMask_clean hcanon] at hr
  have hmem : (UInt256.ofNat 6).toByteArray.write 0
      (key.toByteArray.write 0 midnightEntryMemory (⟨0⟩ : UInt256).toNat 32)
      (UInt256.ofNat 32).toNat 32 = mappingMemory key ⟨6⟩ := rfl
  rw [hmem, mappingMemory_hash, mappingMemory_freePtr] at hr
  exact (mappingMemory_return _ _ _) ▸ hr

/-- `claimableSettlementFee(address)`: the theorem `Correct.lean` routes selector 10 to. -/
theorem midnightClaimableSettlementFeeBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 10)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 10) rfl hsel
  have hd : dispatchMsg contract I.calldata = some claimableSettlementFeeTransition := by
    apply midnightDispatch_claimableSettlementFee <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachClaimableSettlementFeeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_15976_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h36 : 36 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_15982_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 32) h36 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_15994 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_15994_stack, addressMask_computed] at rd3
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) hcanon rd3
          have hret := claimableSettlementFeeTraceReturn hcanon rd4
          have hdec := midnightDecodeAddress "arg0" (by decide) (by decide)
            h36 hhi hsize hcanon
          have hbody := claimableSettlementFeeBodyReturns
            (initState σ σ₀ (Sat256.ofUInt256 g) A I) (calldataWord I.calldata 4) hcanon hwv hhi
          exact hret.reEquivExecution hcode hd hdec hbody
            (returnEquiv_of_encode (uint256ReturnEncoding _))
        · have hr := midnightAddress4_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeAddress_none_noncanon "arg0" h36 hhi hsize hcanon)
      · have rd2 := midnightBlocks.midnight_block_15982_taken (by simp)
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
    · have rd2 := midnightBlocks.midnight_block_15982_taken (by simp)
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
  · have rd1 := midnightBlocks.midnight_block_15976_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (claimableSettlementFeeTransition.params.map Param.name)
        (transitionSignature claimableSettlementFeeTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)



end Benchmarks.Midnight
