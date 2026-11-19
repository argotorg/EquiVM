import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.PairDecode
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.PackedFields
import Benchmarks.Midnight.NestedStorage

/-!
# Midnight `consumed(address,bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2339; reach lemma `midnightReachConsumedBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def consumedArguments (user id : UInt256) : Store :=
  nestedMappingArguments (.address (AccountAddress.ofNat user.toNat)) (wordBytes32Value id)

theorem consumedBodyReturns (evm : EVM.State) (user id : UInt256)
    (hcanon : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm (consumedArguments user id) consumedTransition.body
      (.returned (calldataFrame contract (consumedArguments user id) ∅ evm) evm
        (some [.int (Int.ofNat (UInt256.land
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
            (solcMappingSlot (solcMappingSlot ⟨2⟩ user) id))
          (UInt256.ofNat (2^128 - 1))).toNat)])) := by
  apply guardedNestedMappingGetter (t := .int (.uint ⟨128, by decide⟩))
    (loc := {
      slot := solcMappingSlot (solcMappingSlot ⟨2⟩ user) id, offset := 0, size := 16,
      hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) evm _ _
    (.address (AccountAddress.ofNat user.toNat))
    (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))
    rfl ?_ rfl rfl ?_ ?_ (by decide) (by decide) (by decide) hwv hhi
  · have hlen : (EVM.Word.toBytesBE id).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size id
    simp [valueToKey?, hlen, abiBytes32Width]
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot
        (solcMappingSlot ⟨2⟩ (keyValueToWord (.address (AccountAddress.ofNat user.toNat))))
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
      offset := 0, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
      keyValueToWord_address_of_canonical user hcanon]
  · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)

theorem consumedTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {user : UInt256}
    (hcanon : user.toNat < EVM.addressModulus)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 2372)
      [user, solcAddrMask, solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I) σ
      (UInt256.land
        (solcSlotWordAt (solcMappingSlot (solcMappingSlot ⟨2⟩ user) (calldataWord I.calldata 36)) σ I)
        (UInt256.ofNat (2^128 - 1))).toByteArray := by
  have hr := midnightBlocks.midnight_block_2372 (by simp) rd
  simp only [uint128Mask_computed, solcAddrMask_clean hcanon, midnightEntryMemory_zero] at hr
  simp only [show (UInt256.ofNat 32).toNat = 32 from rfl,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, wordAt0_fold, twoWordHash_fold,
    mappingMemory_fold, mappingMemory_zero, mappingMemory_hash, nestedMappingMemory_fold,
    nestedMappingMemory_zero, nestedMappingMemory_hash, nestedMappingMemory_freePtr] at hr
  exact (nestedMappingMemory_return _ _ _ _) ▸ hr

/-- `consumed(address,bytes32)`: the theorem `Correct.lean` routes selector 49 to. -/
theorem midnightConsumedBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 49)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 49) rfl hsel
  have hd : dispatchMsg contract I.calldata = some consumedTransition := by
    apply midnightDispatch_consumed <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachConsumedBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_2339_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h68 : 68 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_2345_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 64) h68 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_2357 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_2357_stack, addressMask_computed] at rd3
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) hcanon rd3
          have hret := consumedTraceReturn hcanon rd4
          have hdec := midnightDecodePair_ok "arg0" "arg1"
            (by decide) (by decide) (by decide) (by decide) h68 hhi hsize
            (decodeAddressWord (by omega) hcanon) (decodeBytes32Word h68)
          have hbody := consumedBodyReturns
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (calldataWord I.calldata 4) (calldataWord I.calldata 36) hcanon hwv hhi
          exact hret.reEquivExecution hcode hd hdec hbody
            (returnEquiv_of_encode (uintReturnEncoding ⟨128, by decide⟩ _
              (u256LandMaskToNatLtOfToNat _ _ (by decide))))
        · have hr := midnightAddress4_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodePair_none_left "arg0" "arg1" .address (.bytes abiBytes32Width)
              h68 hhi hsize (decodeAddressWord_none (by omega) hcanon))
      · have rd2 := midnightBlocks.midnight_block_2345_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 64) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h68) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodePair_none_short "arg0" "arg1" .address (.bytes abiBytes32Width)
            hsz (Nat.lt_of_not_ge h68) hsize)
    · have rd2 := midnightBlocks.midnight_block_2345_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 64) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodePair_none_huge "arg0" "arg1" .address (.bytes abiBytes32Width)
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_2339_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (consumedTransition.params.map Param.name)
        (transitionSignature consumedTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)





end Benchmarks.Midnight
