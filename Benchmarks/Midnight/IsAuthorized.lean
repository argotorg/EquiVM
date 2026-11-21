import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.PairDecode
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.NestedStorage

/-!
# Midnight `isAuthorized(address,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 15107; reach lemma `midnightReachIsAuthorizedBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def isAuthorizedArguments (authorizer authorized : UInt256) : Store :=
  nestedMappingArguments (.address (AccountAddress.ofNat authorizer.toNat))
    (.address (AccountAddress.ofNat authorized.toNat))

theorem isAuthorizedBodyReturns (evm : EVM.State) (authorizer authorized : UInt256)
    (hc0 : authorizer.toNat < EVM.addressModulus) (hc1 : authorized.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody config contract evm (isAuthorizedArguments authorizer authorized)
      isAuthorizedTransition.body
      (.returned (calldataFrame contract (isAuthorizedArguments authorizer authorized) ∅ evm) evm
        (some [wordToElem .bool (UInt256.land
          (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
            (solcMappingSlot (solcMappingSlot ⟨3⟩ authorizer) authorized)) ⟨255⟩)])) := by
  apply guardedNestedMappingGetter (t := .bool)
    (loc := boolOffset0Loc (solcMappingSlot (solcMappingSlot ⟨3⟩ authorizer) authorized)) evm _ _
    (.address (AccountAddress.ofNat authorizer.toNat))
    (.address (AccountAddress.ofNat authorized.toNat))
    rfl rfl rfl rfl ?_ ?_ (by decide) (by decide) (by decide) hwv hhi
  · change some (StorageAddr.leaf (boolOffset0Loc (solcMappingSlot
      (solcMappingSlot ⟨3⟩ (keyValueToWord (.address (AccountAddress.ofNat authorizer.toNat))))
      (keyValueToWord (.address (AccountAddress.ofNat authorized.toNat)))))) = _
    rw [keyValueToWord_address_of_canonical authorizer hc0,
      keyValueToWord_address_of_canonical authorized hc1]
  · exact storageLocLoad_bool_offset0 evm _

theorem isAuthorizedTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat}
    {authorizer authorized : UInt256}
    (hc0 : authorizer.toNat < EVM.addressModulus) (hc1 : authorized.toNat < EVM.addressModulus)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) (UInt256.ofNat 15148)
      [authorized, solcAddrMask, authorizer, solcSelectorWord I] midnightEntryMemory
      (M (M (UInt256.ofNat 0) (UInt256.ofNat 64) ⟨32⟩) (UInt256.ofNat 800) ⟨32⟩)
      ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I) σ
      (UInt256.isZero (UInt256.isZero (UInt256.land
        (solcSlotWordAt (solcMappingSlot (solcMappingSlot ⟨3⟩ authorizer) authorized) σ I)
        ⟨255⟩))).toByteArray := by
  have hr := midnightBlocks.midnight_block_15148 (by simp) rd
  simp only [addressMask_computed, solcAddrMask_clean hc0, solcAddrMask_clean hc1] at hr
  simp only [show (UInt256.ofNat 32).toNat = 32 from rfl,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, wordAt0_fold, twoWordHash_fold,
    mappingMemory_fold, mappingMemory_hash, nestedMappingMemory_fold,
    nestedMappingMemory_hash, nestedMappingMemory_freePtr] at hr
  exact (nestedMappingMemory_return _ _ _ _) ▸ hr

/-- `isAuthorized(address,address)`: the theorem `Correct.lean` routes selector 17 to. -/
theorem midnightIsAuthorizedBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 17)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 17) rfl hsel
  have hd : dispatchMsg contract I.calldata = some isAuthorizedTransition := by
    apply midnightDispatch_isAuthorized <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachIsAuthorizedBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_15107_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h68 : 68 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_15113_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 64) h68 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_15125 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_15125_stack, addressMask_computed] at rd3
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) hcanon rd3
          have rd5 := midnightBlocks.midnight_block_15132 (by simp) (by jump_dest) rd4
          simp only [midnightBlocks.midnight_block_15132_stack, addressMask_computed] at rd5
          by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · obtain ⟨k6, C6, rd6⟩ := midnightAddress36_ok (by simp) (by jump_dest) hc1 rd5
            have hret := isAuthorizedTraceReturn hcanon hc1 rd6
            have hdec := midnightDecodePair_ok "arg0" "arg1"
              (by decide) (by decide) (by decide) (by decide) h68 hhi hsize
              (decodeAddressWord (by omega) hcanon) (decodeAddressWord h68 hc1)
            have hbody := isAuthorizedBodyReturns
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (calldataWord I.calldata 4) (calldataWord I.calldata 36) hcanon hc1 hwv hhi
            exact hret.reEquivExecution hcode hd hdec hbody
              (returnEquiv_of_encode (boolWordReturnEncoding _))
          · have hr := midnightAddress36_revert (by simp) hc1 rd5
            exact hr.reEquivDecodingFailed hcode hd
              (midnightDecodePair_none_right "arg0" "arg1" .address .address
                h68 hhi hsize (decodeAddressWord_none h68 hc1))
        · have hr := midnightAddress4_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodePair_none_left "arg0" "arg1" .address .address
              h68 hhi hsize (decodeAddressWord_none (by omega) hcanon))
      · have rd2 := midnightBlocks.midnight_block_15113_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 64) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h68) (by decide) hsize
            rw [hc]
            decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodePair_none_short "arg0" "arg1" .address .address
            hsz (Nat.lt_of_not_ge h68) hsize)
    · have rd2 := midnightBlocks.midnight_block_15113_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 64) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]
          decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodePair_none_huge "arg0" "arg1" .address .address
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_15107_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (isAuthorizedTransition.params.map Param.name)
        (transitionSignature isAuthorizedTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
