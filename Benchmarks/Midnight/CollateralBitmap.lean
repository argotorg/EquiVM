import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.PairDecode
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.PositionStorage

/-!
# Midnight `collateralBitmap(bytes32,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3287; reach lemma `midnightReachCollateralBitmapBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem collateralBitmapBodyReturns (evm : EVM.State) (id user : UInt256)
    (hcanon : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm (positionArguments id user)
      collateralBitmapTransition.body
      (.returned (calldataFrame contract (positionArguments id user) ∅ evm) evm
        (some [.int (Int.ofNat (UInt256.shiftRight
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (positionSlot id user + ⟨2⟩))
          (UInt256.ofNat 128)).toNat)])) := by
  apply guardedPositionFieldGetter (t := .int (.uint ⟨128, by decide⟩))
    (loc := {
      slot := positionSlot id user + ⟨2⟩, offset := 16, size := 16,
      hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) evm id user
    rfl rfl ?_ ?_ hwv hhi
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot
        (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
        (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨2⟩,
      offset := 16, size := 16, hbound := by decide, type := .int (.uint ⟨128, by decide⟩) }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
      keyValueToWord_address_of_canonical user hcanon]
    rfl
  · exact storageLocLoad_uint128_high evm _

theorem collateralBitmapTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {user : UInt256}
    (hcanon : user.toNat < EVM.addressModulus)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 3312)
      [user, solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I) σ
      (UInt256.shiftRight (solcSlotWordAt (positionSlot (calldataWord I.calldata 4) user + ⟨2⟩) σ I)
        (UInt256.ofNat 128)).toByteArray := by
  have hr := midnightBlocks.midnight_block_3312 (by simp) rd
  simp only [addressMask_computed, solcAddrMask_clean hcanon,
    midnightEntryMemory_zero] at hr
  simp only [show (UInt256.ofNat 32).toNat = 32 from rfl,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, wordAt0_fold, midnightWordAt0_zero,
    twoWordHash_fold, mappingMemory_fold, mappingMemory_zero,
    mappingMemory_hash, nestedMappingMemory_fold, nestedMappingMemory_hash,
    nestedMappingMemory_freePtr] at hr
  exact (nestedMappingMemory_return _ _ _ _) ▸ hr

/-- `collateralBitmap(bytes32,address)`: the theorem `Correct.lean` routes selector 39 to. -/
theorem midnightCollateralBitmapBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 39)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 39) rfl hsel
  have hd : dispatchMsg contract I.calldata = some collateralBitmapTransition := by
    apply midnightDispatch_collateralBitmap <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachCollateralBitmapBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_3287_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h68 : 68 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_3293_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 64) h68 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_3305 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_3305_stack] at rd3
        by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress36_ok (by simp) (by jump_dest) hcanon rd3
          have hret := collateralBitmapTraceReturn hcanon rd4
          have hdec := midnightDecodeBytes32Address "id" "user"
            (by decide) (by decide) (by decide) (by decide) h68 hhi hsize hcanon
          have hbody := collateralBitmapBodyReturns
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)
            (calldataWord I.calldata 4) (calldataWord I.calldata 36) hcanon hwv hhi
          exact hret.reEquivExecution hcode hd hdec hbody
            (returnEquiv_of_encode (uintReturnEncoding ⟨128, by decide⟩ _
              (shiftRight128_lt _)))
        · have hr := midnightAddress36_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeBytes32Address_none_noncanon "id" "user" h68 hhi hsize hcanon)
      · have rd2 := midnightBlocks.midnight_block_3293_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 64) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h68) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodePair_none_short "id" "user" (.bytes abiBytes32Width) .address
            hsz (Nat.lt_of_not_ge h68) hsize)
    · have rd2 := midnightBlocks.midnight_block_3293_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 64) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodePair_none_huge "id" "user" (.bytes abiBytes32Width) .address
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_3287_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (collateralBitmapTransition.params.map Param.name)
        (transitionSignature collateralBitmapTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)




end Benchmarks.Midnight
