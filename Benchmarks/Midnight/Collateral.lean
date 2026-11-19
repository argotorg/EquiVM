import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.TripleDecode
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.CollateralStorage
import Benchmarks.Midnight.PackedArray

/-!
# Midnight `collateral(bytes32,address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 2010; reach lemma `midnightReachCollateralBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem collateralBodyReturns (evm : EVM.State) (id user index : UInt256)
    (hcanon : user.toNat < EVM.addressModulus) (hi : index.toNat < 128)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm (collateralArguments id user index)
      collateralTransition.body
      (.returned (calldataFrame contract (collateralArguments id user index) ∅ evm) evm
        (some [.int (Int.ofNat (collateralWord
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner) id user index).toNat)])) := by
  apply guardedReturnBody hwv hhi
  apply evalExpr_storage_scalar_value (loc := collateralLoc id user index)
    (er := collateralEvaledRef id user index) (t := .int (.uint ⟨128, by decide⟩))
  · simp [calldataFrame, collateralArguments, positionArguments]
  · exact (evalCollateralRef evm id user index).trans (if_pos hi)
  · rfl
  · rfl
  · change some (StorageAddr.leaf {
      slot := solcMappingSlot
        (solcMappingSlot ⟨0⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))))
        (keyValueToWord (.address (AccountAddress.ofNat user.toNat))) + ⟨3⟩ +
        UInt256.ofNat ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat / 2),
      offset := Fin.ofNat 32 ((keyValueToWord (.int (Int.ofNat index.toNat))).toNat % 2 * 16),
      size := 16, hbound := _, type := .int (.uint ⟨128, by decide⟩) }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32,
      keyValueToWord_address_of_canonical user hcanon,
      keyValueToWord_int_ofNat_of_lt (show index.toNat < UInt256.size from index.val.isLt),
      u256_ofNat_toNat]
    congr 3
    apply Fin.ext
    change (index.toNat % 2 * 16) % 32 = 16 * (index.toNat % 2)
    rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm]
  · exact collateralLoc_load evm id user index

theorem collateralBodyReverts (evm : EVM.State) (id user index : UInt256)
    (hi : ¬ index.toNat < 128) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm (collateralArguments id user index)
      collateralTransition.body .reverted := by
  apply guardedReturnReverts hwv hhi
  apply Reasoning.VyperBounded.evalExpr_storage_revert
  · simp [calldataFrame, collateralArguments, positionArguments]
  · exact (evalCollateralRef evm id user index).trans (if_neg hi)

theorem collateralTracePrepare {σ σ₀ A I} {g : Sat256} {k C : Nat} {user : UInt256}
    (hcanon : user.toNat < EVM.addressModulus)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 2035)
      [user, solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 19480)
      [positionSlot (calldataWord I.calldata 4) user + ⟨3⟩, calldataWord I.calldata 68,
       UInt256.ofNat 2101, UInt256.ofNat (2^128 - 1), UInt256.ofNat 32, solcSelectorWord I]
      (nestedMappingMemory (calldataWord I.calldata 4) user ⟨0⟩) aw' ByteArray.empty σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightBlocks.midnight_block_2035_packed
    (by simp) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_2035_stack,
    midnightBlocks.midnight_block_2035_memory, addressMask_computed, uint128Mask_computed,
    solcAddrMask_clean hcanon, midnightEntryMemory_zero] at rd1
  simp only [show (UInt256.ofNat 32).toNat = 32 from rfl,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, wordAt0_fold, midnightWordAt0_zero,
    twoWordHash_fold, mappingMemory_fold, mappingMemory_zero, mappingMemory_hash,
    nestedMappingMemory_fold, nestedMappingMemory_hash] at rd1
  exact ⟨_, _, _, rd1⟩

theorem collateralTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {user : UInt256}
    {aw : UInt256}
    (hi : (calldataWord I.calldata 68).toNat < 128)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 19480)
      [positionSlot (calldataWord I.calldata 4) user + ⟨3⟩, calldataWord I.calldata 68,
       UInt256.ofNat 2101, UInt256.ofNat (2^128 - 1), UInt256.ofNat 32, solcSelectorWord I]
      (nestedMappingMemory (calldataWord I.calldata 4) user ⟨0⟩) aw ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I) σ
      (collateralWord (fun slot ↦ solcSlotWordAt slot σ I)
        (calldataWord I.calldata 4) user (calldataWord I.calldata 68)).toByteArray := by
  obtain ⟨k1, C1, rd1⟩ := midnightUint128ArrayLocation (by simp) hi (by jump_dest) rd
  have hr := midnightBlocks.midnight_block_2101 (by simp) rd1
  rw [(uint128ArrayIndexFacts _ hi).2.2, nestedMappingMemory_freePtr] at hr
  exact (nestedMappingMemory_return _ _ _ _) ▸ hr

/-- `collateral(bytes32,address,uint256)`: the theorem `Correct.lean` routes selector 51 to. -/
theorem midnightCollateralBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 51)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 51) rfl hsel
  have hd : dispatchMsg contract I.calldata = some collateralTransition := by
    apply midnightDispatch_collateral <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachCollateralBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_2010_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h100 : 100 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_2016_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 96) h100 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_2028 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_2028_stack] at rd3
        by_cases hcanon : (calldataWord I.calldata 36).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress36_ok (by simp) (by jump_dest) hcanon rd3
          obtain ⟨aw5, k5, C5, rd5⟩ := collateralTracePrepare hcanon rd4
          have hdec := midnightDecodeTriple_ok "id" "user" "index"
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            h100 hhi hsize (decodeBytes32Word (by omega))
            (decodeAddressWord (by omega) hcanon) (decodeUint256Word h100)
          by_cases hi : (calldataWord I.calldata 68).toNat < 128
          · have hret := collateralTraceReturn hi rd5
            have hbody := collateralBodyReturns
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (calldataWord I.calldata 4) (calldataWord I.calldata 36)
              (calldataWord I.calldata 68) hcanon hi hwv hhi
            exact hret.reEquivExecution hcode hd hdec hbody
              (returnEquiv_of_encode (uintReturnEncoding ⟨128, by decide⟩ _
                (u256LandMaskToNatLtOfToNat _ _ (by decide))))
          · have rd6 := midnightBlocks.midnight_block_19480_taken (by simp)
              (by rw [ult_zero (Nat.le_of_not_lt hi)]; decide) (by jump_dest) rd5
            have hr := midnightBlocks.midnight_block_19161 (by simp
              [midnightBlocks.midnight_block_19480_taken_stack]) rd6
            exact hr.reEquivExecutionRevert hcode hd hdec
              (collateralBodyReverts _ _ _ _ hi hwv hhi)
        · have hr := midnightAddress36_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeTriple_none_middle "id" "user" "index"
              (.bytes abiBytes32Width) .address (.int (.uint ⟨256, by decide⟩)) h100 hhi hsize
              (decodeBytes32Word (by omega)) (decodeAddressWord_none (by omega) hcanon))
      · have rd2 := midnightBlocks.midnight_block_2016_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 96) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h100) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeTriple_none_short "id" "user" "index"
            (.bytes abiBytes32Width) .address (.int (.uint ⟨256, by decide⟩))
            hsz (Nat.lt_of_not_ge h100) hsize)
    · have rd2 := midnightBlocks.midnight_block_2016_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 96) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeTriple_none_huge "id" "user" "index"
          (.bytes abiBytes32Width) .address (.int (.uint ⟨256, by decide⟩))
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_2010_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (collateralTransition.params.map Param.name)
        (transitionSignature collateralTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)




end Benchmarks.Midnight
